"""One installed zero call followed by the existing direct scheduler descriptor ABI."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import conditional_local_buffer_profile as local
import match
import scheduler_zero_descriptor as descriptor


class DescriptorBoundsTests(unittest.TestCase):
    def test_scheduler_provider_loads_in_a_fresh_interpreter(self):
        tools = Path(descriptor.__file__).resolve().parent
        subprocess.run([sys.executable, '-B', '-c', 'import scheduler_zero_descriptor'],
                       cwd=tools, check=True)

    def test_requires_same_offset_28_bytes_and_no_other_alias(self):
        from types import SimpleNamespace
        proof = SimpleNamespace(access=lambda *args: None, observations={})
        stack = [None] * 9
        aliases = {match.ARM_REG_R0: -32}
        kwargs = (proof, descriptor.THUNK, aliases, stack, {}, {match.ARM_REG_R1: 28}, descriptor.INITIALIZE)
        descriptor.check_call(*kwargs)
        self.assertEqual(proof.observations[descriptor.INITIALIZE]['bytes'], 28)
        for index, value in ((2, {match.ARM_REG_R0: -28}), (2, {**aliases, match.ARM_REG_R0 + 4: -32}),
                             (3, stack[:-1]), (4, {-36: -32}), (5, {match.ARM_REG_R1: 24})):
            changed = list(kwargs)
            changed[index] = value
            with self.subTest(index=index), self.assertRaises(ValueError):
                descriptor.check_call(*changed)
        with self.assertRaises(ValueError):
            descriptor.check_call(proof, descriptor.scheduler.DIRECT, {match.ARM_REG_R3: -28},
                                  stack, {}, {}, descriptor.CREATE)
        self.assertIn(descriptor.SELECTOR, local.SELECTORS)


@unittest.skipUnless(os.getenv('FFTA_SCHEDULER_ZERO_ROOT'), 'needs FFTA USA ROM and indexed 080D376C source')
class NativeDescriptorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import inert_spin_profile
        import match_evidence
        cls.root = Path(os.environ['FFTA_SCHEDULER_ZERO_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        cls.start = descriptor.OWNER - descriptor.install.ROM_BASE
        cls.body = cls.rom[cls.start:cls.start+64]
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = inert_spin_profile.index_snapshot(cls.root)
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.report = (cls.root / 'docs/match/080D376C.md').read_text()
        line = next(s for s in cls.report.splitlines() if s.startswith('* owner runtime evidence:'))
        cls.manifest = json.loads(line.split('`')[1])['manifest']
        cls.bindings = cls.manifest['bindings']

    def verify(self, body, rom, bindings, policy=descriptor.SELECTOR):
        import owner_admission_profile as owner
        return owner.verify(body, descriptor.OWNER, rom, self.mapping, self.index, self.objects,
                            bindings=bindings, selector=policy)

    def test_real_report_replay_and_qualified_conclusions(self):
        import match_evidence
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), descriptor.OWNER))
        contract = self.manifest['proof']['buffers']['conditional_local_calls']
        image = contract['initializer']
        self.assertFalse(image['installed_identity_proved'])
        self.assertFalse(contract['actual_callback_effects_proved'])
        self.assertEqual(image['aligned_case']['steps'], 43)
        self.assertEqual(image['aligned_case']['writes'][1:],
                         [['destination', offset, 4] for offset in range(0, 28, 4)])
        self.assertEqual([row['local_offset'] for row in contract['observations']], [-32, -32])
        for old, new in [('"initialized_descriptor_bytes":28', '"initialized_descriptor_bytes":24'),
                         ('"installed_identity_proved":false', '"installed_identity_proved":true'),
                         ('"parent_value":0', '"parent_value":1')]:
            altered = self.report.replace(old, new)
            self.assertNotEqual(altered, self.report)
            self.assertFalse(match_evidence.report_matches(altered, str(self.root), descriptor.OWNER))

    def test_installer_slot_image_thunk_and_scheduler_dependency(self):
        for offset in (0x276, 0x2742, 0x2792, 0x27B0, 0x14186C, 0x36D4B8, 0xA38A42, 0x14224C, 0x5966):
            rom = bytearray(self.rom)
            rom[offset] ^= 2
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                self.verify(self.body, bytes(rom), self.bindings)

    def test_caller_count_descriptor_calls_callback_parent_and_result(self):
        # Change both caller and ROM together, so closure checks see the same
        # mutated owner. Either bound call or the complete native argument setup must refuse.
        for offset in (4, 6, 8, 10, 12, 14, 20, 22, 24, 26, 28, 30, 32, 36, 44, 52, 56, 60):
            rom = bytearray(self.rom)
            rom[self.start+offset] ^= 2
            body = bytes(rom[self.start:self.start+64])
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(body, bytes(rom), self.bindings)

    def test_original_typed_bindings_and_existing_selectors(self):
        import owner_admission_profile as owner
        for group, index, field, value in [('calls', 0, 1, '_call_via_r3'), ('calls', 1, 1, 'func_08005B6C'),
                                          ('data', 0, 2, 4), ('data', 1, 1, 'data_020159C0'),
                                          ('data', 2, 0, 56), ('functions', 0, 1, 'func_080D3818')]:
            bindings = copy.deepcopy(self.bindings)
            bindings[group][index][field] = value
            with self.subTest(group=group,index=index), self.assertRaises(ValueError):
                self.verify(self.body, self.rom, bindings)
        for policy in (local.SCHEDULER_ENTRY, local.SCHEDULER_CALL_SITES):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                owner.build(self.root, descriptor.OWNER, selector=policy)


if __name__ == '__main__':
    unittest.main()
