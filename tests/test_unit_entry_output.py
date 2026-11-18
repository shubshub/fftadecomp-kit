"""Native output cursor, callee exposure and same-extent consumer checks."""
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import unit_entry_output as unit


class BoundsTests(unittest.TestCase):
    def test_signed_low_halfword_and_capacity(self):
        for raw, result in [(0, 0), (20, 20), (0x10001, 1), (0x8000, 0), (0xFFFF, 0),
                            (0xFFFF7FFF, 32767), (0xFFFF8001, 0)]:
            effect = unit.cursor_extent(raw, 4*result)
            self.assertEqual((effect['iterations'], effect['end'], effect['return_value']), (result, 4*result, 1))
            if result:
                with self.assertRaises(ValueError):
                    unit.cursor_extent(raw, 4*result-1)
        for raw, size in [(-1, 80), (2**32, 80), (True, 80), (20, -80), (20, True)]:
            with self.assertRaises(ValueError):
                unit.cursor_extent(raw, size)

    def test_two_halfwords_constrain_selection_more_than_pointer_table(self):
        self.assertEqual(unit.heap_accesses(0), dict(clear_halfwords=[216, 212], read_word=3436))
        self.assertEqual(unit.heap_accesses(12), dict(clear_halfwords=[3384, 3380], read_word=3484))
        for index in (13, 42, -1, 2**32-1, True):
            with self.assertRaises(ValueError):
                unit.heap_accesses(index)


@unittest.skipUnless(os.getenv('FFTA_UNIT_OUTPUT_ROOT'), 'needs indexed USA ROM, source and report')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match_evidence
        cls.root = Path(os.environ['FFTA_UNIT_OUTPUT_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.report = (cls.root/'docs/match/08027528.md').read_text()
        cls.manifest = json.loads(next(line.split('`')[1] for line in cls.report.splitlines()
                                      if line.startswith('* owner runtime evidence:')))['manifest']

    def body(self, address, size):
        start = address-match.ROM_BASE
        return self.rom[start:start+size]

    def cfg(self, body, address):
        import owner_admission_profile as owner
        refinement = owner.refine(body, address, self.mapping)
        ins, edges, _, calls, _ = unit.graph.graph(body, address, refinement)
        return ins, edges, calls, refinement

    def test_same_producer_two_real_buffer_origins(self):
        menu, heap = unit.MENU, 0x08099A70
        for address, size, call in [(menu, 50, menu+14), (heap, 316, heap+48)]:
            ins, edges, calls, _ = self.cfg(self.body(address, size), address)
            if address == menu:
                self.assertEqual(unit.op(ins[address+2]), 'sub sp, #0x50')
                self.assertEqual(unit.op(ins[call-4]), 'mov r1, sp')
            else:
                self.assertEqual([unit.op(ins[k]) for k in (call-14, call-12, call-8, call-6, call-4)],
                                 ['movs r0, #0x50', 'bl #0x8022840', 'mov sb, r0', 'adds r0, r6, #0',
                                  'mov r1, sb'])
                self.assertFalse(any(call-14 < target <= call and site < call-14
                                     for site, targets in edges.items() for target in targets))
            self.assertEqual(unit.counted_call(ins, edges, calls, call, 80)['end'], 80)
            with self.assertRaises(ValueError):
                unit.counted_call(ins, edges, calls, call, 79)
            with self.assertRaises(ValueError):
                unit.counted_call(ins, {**edges, address: (call,)}, calls, call, 80)

    def test_producer_mutations(self):
        address = unit.PRODUCER
        body = self.body(address, 100)
        ins, _, calls, _ = self.cfg(body, address)
        unit.check_producer(body, ins, calls)
        for offset in (4, 6, 22, 26, 28, 30, 36, 40, 52, 54, 56, 60, 62, 66, 68, 70, 74, 76, 82, 84, 90, 92, 96):
            mutated = bytearray(body)
            mutated[offset] ^= 2
            cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            changed = {i.address: i for i in cs.disasm(mutated[:90], address)}
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                unit.check_producer(bytes(mutated), changed, calls)

    def test_cursor_saves_stale_argument_and_search(self):
        for addr, site, half in [(unit.ALLOC, unit.ALLOC+2, 0x1C0A), (unit.SELECT, unit.SELECT+2, 0x1C3F),
                                  (unit.INITIALIZE, 0x0809DED2, 0x9107),
                                  (0x08006EC0, 0x08006ECE, 0xAB06), (0x08006FCC, 0x080070C2, 0xBC70)]:
            size = unit.PINS[addr][0]
            body = bytearray(self.body(addr, size))
            struct.pack_into('<H', body, site-addr, half)
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                ins, edges, calls, _ = self.cfg(bytes(body), addr)
                unit.helper_cursor(addr, ins, edges, calls)
        bad = bytearray(self.rom)
        bad[0x6C96] ^= 1
        with self.assertRaises(ValueError):
            unit.native_producer(bytes(bad), self.mapping, self.index, self.objects)

    def test_report_replay_and_root_mutations(self):
        import match_evidence
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), unit.MENU))
        bad = self.report.replace('"consumer_load":', '"consumer_load":1,"consumer_load":')
        self.assertNotEqual(bad, self.report)
        self.assertFalse(match_evidence.report_matches(bad, str(self.root), unit.MENU))
        body = self.body(unit.MENU, 50)
        bindings = self.manifest['bindings']
        for offset in (2, 10, 12, 18, 20, 22, 24, 30, 32, 34, 38, 40, 42):
            mutated = bytearray(body)
            mutated[offset] ^= 1
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                ins, edges, calls, ref = self.cfg(bytes(mutated), unit.MENU)
                unit.prove(bytes(mutated), unit.MENU, self.rom, self.mapping, self.index, self.objects,
                           bindings=bindings, ins=ins, edges=edges, calls=calls, refinement=ref)
        ins, edges, calls, ref = self.cfg(body, unit.MENU)
        with self.assertRaises(ValueError):
            unit.prove(body, unit.MENU, self.rom, self.mapping, self.index, self.objects,
                       bindings={**bindings, 'data': [[4, 'x', 0]]}, ins=ins, edges=edges, calls=calls, refinement=ref)


if __name__ == '__main__':
    unittest.main()
