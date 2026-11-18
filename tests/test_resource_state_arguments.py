"""Caller initialization, the installed clear, and native resource setup replay."""
import json
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R0

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import match
import match_evidence
import named_data_buffer_profile as named
import owner_admission_profile as owner
import owner_graph_profile as graph
import resource_state_arguments as resource


def decode(data, start):
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return {item.address: item for item in decoder.disasm(data, start)}


class FormalTests(unittest.TestCase):
    def test_distinct_dominating_writes_to_private_words(self):
        start = 0x08001000
        ins = decode(bytes.fromhex('0090 0191 0292'), start)
        pred = {pc+2: {pc} for pc in ins}
        site = start + 6
        states = {pc: ('local',) * 3 for pc in (*ins, site)}
        self.assertEqual([row[0] for row in resource.argument_stores(ins, pred, states, site)['stores']], [0,4,8])
        with self.assertRaisesRegex(ValueError, 'three private'):
            resource.argument_stores(ins, pred, {**states, site: ('local','saved','local')}, site)
        with self.assertRaisesRegex(ValueError, 'dominate'):
            resource.argument_stores(ins, {**pred, site: {start,start+4}}, states, site)
        ins[start+2] = decode(bytes.fromhex('0180'), start+2)[start+2]
        with self.assertRaisesRegex(ValueError, 'unproved write'):
            resource.argument_stores(ins, pred, states, site)

    def test_undefined_caller_local_source_and_wrong_frame(self):
        start = 0x08002000
        ins = decode(bytes.fromhex('83b0 0198 0090'), start)
        pred = resource.predecessors({pc: [pc+2] for pc in ins})
        states = {start: (), start+2: ('local',)*3, start+4: ('local',)*3}
        with self.assertRaisesRegex(ValueError, 'reaching initialization'):
            resource.scalar_definitions(ins, pred, states, start, start+4, ARM_REG_R0)
        pc = 0x080216C8
        mov = decode(bytes.fromhex('6846'), pc)[pc]
        with self.assertRaisesRegex(ValueError, 'seven-word'):
            resource.ResourceArguments.read(SimpleNamespace(), mov, 6)

    def test_generic_verifier_stays_closed(self):
        data = bytes.fromhex('00b5 6846 8088 00bd')
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(data, 0x08001000, True, incoming_narrow_reads=True)
        with self.assertRaisesRegex(ValueError, 'authenticated Thumb owner'):
            match.verify_leaf_instructions(data, 0x08001000, True, resource_arguments=object())


@unittest.skipUnless(os.environ.get('FFTA_RESOURCE_STATE_ROOT'), 'set FFTA_RESOURCE_STATE_ROOT to the game fixture')
class NativeResourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_RESOURCE_STATE_ROOT']).resolve()
        cls.rom = (cls.root / 'baserom.bin').read_bytes()
        cls.mapping = (cls.root / 'config/functions.json').read_bytes()
        cls.index = (cls.root / 'symbols/functions.txt').read_bytes()
        cls.objects = (cls.root / 'config/data_symbols.json').read_bytes()
        cls.rows = json.loads(cls.mapping)
        cls.data = cls.rom[resource.ROOT-match.ROM_BASE:resource.ROOT-match.ROM_BASE+224]
        cls.buffers = SimpleNamespace(rom=cls.rom, mapping=cls.mapping, index=cls.index, objects=cls.objects)

    def test_reached_local_initializations_and_incomplete_outgoing_frame(self):
        start = 0x0809836C
        material = resource.caller_record(self.buffers, self.rows, start, resource.CALLERS[start])
        source = material['sites'][1]['sources']
        self.assertEqual([row['site'] for row in source[1][0]['local_writes']], [0x0809893A])
        self.assertEqual(len(source[0][0]['local_writes']), 6)
        # Remove the selector write immediately before the genuine BL in a different caller.
        changed = bytearray(self.rom)
        site = 0x08029CA4-match.ROM_BASE
        changed[site:site+2] = struct.pack('<H', 0x9200)
        args = SimpleNamespace(**{**vars(self.buffers), 'rom': changed})
        with self.assertRaises(ValueError):
            resource.caller_record(args, self.rows, 0x08029C34, resource.CALLERS[0x08029C34])

    def test_address_literal_and_installed_target_substitution(self):
        changed = bytearray(self.rom)
        struct.pack_into('<I', changed, 0x123457, resource.ROOT | 1)
        with self.assertRaisesRegex(ValueError, 'unexpected address literal'):
            resource.references_at(changed, resource.ROOT, resource.CALLERS)
        changed = bytearray(self.rom)
        struct.pack_into('<I', changed, resource.installed.POINTER-match.ROM_BASE, 0x03005EAD)
        with self.assertRaises(ValueError):
            resource.clear_effect(SimpleNamespace(**{**vars(self.buffers), 'rom': changed}))

    def test_actual_halfword_pairs_and_exact_clear_count(self):
        expected_calls = [[pc-resource.ROOT, '_call_via_r2' if pc == resource.CLEAR else f'func_{target:08X}']
                          for pc, target in sorted(resource.CALLS.items())]
        bindings = dict(calls=expected_calls, data=[[220,'g_callbacks_0836D4B8',0]], functions=[], switches=[])
        for pc, encoding in ((0x080216CA, 0x8C00), (0x080216CE, 0x4668),
                             (0x080216D2, 0x80E1), (0x0802167C, 0x2147)):
            with self.subTest(pc=hex(pc)):
                data = bytearray(self.data)
                struct.pack_into('<H', data, pc-resource.ROOT, encoding)
                refinement = owner.refine(data, resource.ROOT, self.mapping)
                ins, edges, _, calls, _ = graph.graph(data, resource.ROOT, refinement)
                with self.assertRaisesRegex(ValueError, 'expected'):
                    resource.ResourceArguments(self.buffers, data, resource.ROOT, ins, edges, calls, bindings)

    def test_cpu_table_lookup_and_setter_preserve_wide_argument(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_SP
        machine = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        machine.mem_map(match.ROM_BASE, 0x1000000)
        machine.mem_write(match.ROM_BASE, self.rom)
        state = 0x02000000
        machine.mem_map(state, 0x10000)
        sentinel = state + 0x4000
        stack = state + 0x8000
        for category in range(248):
            base, = struct.unpack_from('<I', self.rom, 0x390E44+4*category)
            for selector in range(12):
                machine.reg_write(UC_ARM_REG_R0, category)
                machine.reg_write(UC_ARM_REG_R1, selector)
                machine.reg_write(UC_ARM_REG_LR, sentinel | 1)
                machine.reg_write(UC_ARM_REG_SP, stack)
                machine.emu_start(resource.GETTER | 1, sentinel, count=40)
                self.assertEqual(machine.reg_read(UC_ARM_REG_R0), base+(selector&~3)*6+(12 if selector%4 in (1,2) else 0))
                self.assertEqual(machine.reg_read(UC_ARM_REG_SP), stack)
        for third in (0,0xFFFF,0x80001234,0xFFFF1234):
            machine.reg_write(UC_ARM_REG_R0, state)
            machine.reg_write(UC_ARM_REG_R1, 0xABCD)
            machine.reg_write(UC_ARM_REG_R2, third)
            machine.reg_write(UC_ARM_REG_LR, sentinel | 1)
            machine.emu_start(resource.PAIR | 1, sentinel, count=4)
            self.assertEqual(machine.mem_read(state+18,6), struct.pack('<HHH',0xABCD,0,third&0xFFFF))
            self.assertEqual(machine.reg_read(UC_ARM_REG_R2), third)

    def test_native_replay_evidence_tampering_and_old_selector(self):
        report = (self.root / 'docs/match/08021618.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, resource.ROOT))
        before = '"incoming_halfwords":[[134354632,0,2]'
        self.assertIn(before, report)
        self.assertFalse(match_evidence.report_matches(report.replace(before, before[:-2]+'4]'), self.root, resource.ROOT))
        with self.assertRaises(ValueError):
            owner.build(self.root, resource.ROOT, selector=named.THUNK_SELECTOR)
        evidence = json.loads(next(row.split('`')[1] for row in report.splitlines() if row.startswith('* owner runtime evidence:')))
        manifest = evidence['manifest']
        proof = manifest['proof']['buffers']['resource_arguments']
        self.assertEqual((len(proof['references']['thumb_bl']), len(proof['callers'])), (19,13))
        self.assertEqual((proof['lookup']['category_count'], proof['lookup']['distinct_subtables'],
                          proof['lookup']['pointer_words'], proof['lookup']['present']), (248,245,36072,6295))
        self.assertEqual(proof['clear']['count'], 72)
        self.assertEqual([row['alignment'] for row in proof['clear']['cases']], [0,1,2,3])
        self.assertFalse(proof['clear']['installed_identity_proved'])
        self.assertEqual(len(manifest['bindings']['calls']), 8)
        self.assertEqual(manifest['bindings']['data'], [[220,'g_callbacks_0836D4B8',0]])


if __name__ == '__main__':
    unittest.main()
