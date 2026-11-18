"""Exact mode-six script dispatch, BIOS fills, callback and saved native report."""
import copy
import json
import os
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match_evidence
import inert_spin_profile
import owner_admission_profile as owner
import scene_script_position as scene

ROOT = os.environ.get('FFTA_SCENE_SCRIPT_ROOT')


@unittest.skipUnless(ROOT, 'requires USA ROM, matching maps, source and saved scene report')
class SceneScript(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(ROOT).resolve()
        cls.rom = (cls.root/'baserom.bin').read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = inert_spin_profile.index_snapshot(cls.root)
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.address = 0x08118A08
        cls.offset = cls.address-0x08000000
        cls.body = cls.rom[cls.offset:cls.offset+184]
        cls.report = (cls.root/'docs/match/08118A08.md').read_text()
        row = next(line for line in cls.report.splitlines() if line.startswith('* owner runtime evidence:'))
        cls.manifest = json.loads(row.split('`')[1])['manifest']
        cls.bindings = cls.manifest['bindings']

    def verify(self, body, rom, bindings, selector=scene.SELECTOR):
        return owner.verify(body, self.address, rom, self.mapping, self.index, self.objects,
                            bindings=bindings, selector=selector)

    def test_report_and_actual_mode_six_effects(self):
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), self.address))
        contract = self.manifest['proof']['buffers']['conditional_local_calls']
        script = contract['script']
        self.assertEqual(script['entry']['signed_coordinates'], [104, 184])
        self.assertEqual(script['entry']['dispatch']['target'], 0x080E04D4)
        self.assertEqual([r['coordinate'] for r in script['entry']['signed_reads']], [12,14])
        self.assertFalse(script['entry']['actual_reaching_state_proved'])
        self.assertEqual(script['callback_effect']['payload_field_widths'], [[0,2],[2,1],[4,4]])
        self.assertFalse(contract['physical_noninterference_proved'])
        self.assertEqual([(r[1],r[2]) for r in contract['bios_fill']['sites']], [(-28,2),(-26,2)])

    def check_sibling(self, address, size, count, coordinates, script):
        path = self.root / 'docs/match' / f'{address:08X}.md'
        if not path.is_file():
            self.skipTest('requires this sibling source and saved report')
        text = path.read_text()
        self.assertTrue(match_evidence.report_matches(text,str(self.root),address))
        line = next(s for s in text.splitlines() if s.startswith('* owner runtime evidence:'))
        manifest = json.loads(line.split('`')[1])['manifest']
        contract = manifest['proof']['buffers']['conditional_local_calls']
        self.assertEqual(contract['bios_fill']['owner'][1], size)
        self.assertEqual(contract['script']['entry']['signed_coordinates'], coordinates)
        self.assertEqual(contract['script']['entry']['parameter_count'], count)
        self.assertEqual(contract['script']['entry']['parameter_data'], script)
        return manifest, contract

    def test_second_scene_script(self):
        self.check_sibling(0x08118B94, 184, 2, [56,280], 0x083A61C0)

    def test_overlay_scene_script(self):
        self.check_sibling(0x08118AC0, 210, 5, [216,248], 0x083A616C)

    def test_timed_scene_script(self):
        address = 0x08118C4C
        manifest, contract = self.check_sibling(address, 212, 4, [120, 248], 0x083A6208)
        self.assertEqual([(site - address, start, width, control)
                          for site, start, width, control, _ in contract['bios_fill']['sites']],
                         [(60, -28, 2, 0x01000040), (80, -26, 2, 0x01000070)])
        self.assertEqual([(event['site'] - address, event['target'], event['pointer_words'])
                          for event in contract['observations']], [
            (60, 0x0814186C, []), (80, 0x0814186C, []), (98, 0x080E03F8, [[-36, -24]]),
            (130, 0x080E05DC, []), (142, 0x080E5694, []), (182, 0x080DBED4, []),
            (188, 0x080E051C, [])])
        self.assertEqual(manifest['bindings']['data'],
                         [[112, 'data_03003920', 0], [124, 'data_083A6208', 0]])
        self.assertFalse(contract['actual_termination_proved'])
        self.assertFalse(contract['physical_noninterference_proved'])

    def test_timed_scene_rejects_owner_and_binding_changes(self):
        address = 0x08118C4C
        offset = address - 0x08000000
        manifest, _ = self.check_sibling(address, 212, 4, [120, 248], 0x083A6208)
        # First/second fills, outgoing position and parent, count/mode, ROM
        # script, wait callback, timer, expiry callback and final phase store.
        for delta in (60, 70, 72, 80, 90, 92, 94, 96, 108, 112, 116, 120,
                      124, 130, 148, 182, 200):
            rom = bytearray(self.rom)
            rom[offset + delta] ^= 2
            with self.subTest(delta=delta), self.assertRaises(ValueError):
                owner.verify(bytes(rom[offset:offset+212]), address, bytes(rom), self.mapping,
                             self.index, self.objects, bindings=manifest['bindings'], selector=scene.SELECTOR)
        bindings = copy.deepcopy(manifest['bindings'])
        bindings['data'][1][1] = 'data_083A61C0'
        with self.assertRaises(ValueError):
            owner.verify(self.rom[offset:offset+212], address, self.rom, self.mapping,
                         self.index, self.objects, bindings=bindings, selector=scene.SELECTOR)

    def test_forged_report(self):
        for old,new in [('"signed_coordinates":[104,184]','"signed_coordinates":[104,180]'),
                        ('"actual_reaching_state_proved":false','"actual_reaching_state_proved":true'),
                        ('"position_stack_argument":0','"position_stack_argument":4')]:
            changed = self.report.replace(old,new)
            self.assertNotEqual(changed,self.report)
            self.assertFalse(match_evidence.report_matches(changed,str(self.root),self.address))

    def test_owner_mode_position_fill_controls_and_parent(self):
        for offset in (48,50,60,80,88,90,92,94,96,98,108,112,116,120,124):
            rom = bytearray(self.rom)
            rom[self.offset+offset] ^= 2
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(bytes(rom[self.offset:self.offset+184]),bytes(rom),self.bindings)

    def test_script_switch_reads_geometry_ambient_abi_and_callback(self):
        for location in (0x14186C,0xE0400,0xE0432,0xE0464,0xE04D6,0xE04DA,0xE04DC,
                         0xD8B3A,0x1BB9A,0xE04E4,0xE04F2,0xE04FA,0xE0502,0xE0518,
                         0x595E,0x5A02,0xDFF18,0xDFF32,0xDFF34,0x142250):
            rom = bytearray(self.rom)
            rom[location] ^= 2
            with self.subTest(location=hex(location)), self.assertRaises(ValueError):
                self.verify(self.body, bytes(rom), self.bindings)

    def test_typed_object_relocations_and_prior_policies(self):
        for index in (0,1):
            bindings=copy.deepcopy(self.bindings)
            bindings['data'][index][2]=4
            with self.assertRaises(ValueError):
                self.verify(self.body,self.rom,bindings)
        for selector in ('bounded-buffer-bios-fill-source-v1','conditional-scheduler-entry-descriptor-calls-v1'):
            with self.assertRaises(ValueError):
                self.verify(self.body,self.rom,self.bindings,selector)


if __name__ == '__main__':
    unittest.main()
