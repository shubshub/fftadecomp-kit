"""Verify the caller's four-byte equipment array and its six outgoing stack arguments."""
from pathlib import Path
import os
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import positioned_equipment_chance as chance
import unit_equipment_attribute as equipment


class SelectionBounds(unittest.TestCase):
    def test_two_halfwords_for_five_equipment_slots(self):
        for mask in range(32):
            with self.subTest(mask=mask):
                if mask.bit_count() > 2:
                    with self.assertRaisesRegex(ValueError, 'crosses the saved registers'):
                        chance.selection_accesses(mask)
                else:
                    self.assertEqual(chance.selection_accesses(mask)['append_offsets'],
                                     [24, 26][:mask.bit_count()])
        for mask in (-1, 32, True):
            with self.assertRaises(ValueError):
                chance.selection_accesses(mask)


@unittest.skipUnless(os.getenv('FFTA_POSITIONED_CHANCE_ROOT'), 'requires the reviewed C and USA ROM')
class PositionedChanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_POSITIONED_CHANCE_ROOT']).resolve()
        cls.built = owner.build(cls.root, chance.OWNER, selector=equipment.named.EQUIPMENT_SELECTOR)
        cls.raw, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, _ = cls.built

    def test_exact_body_and_original_roles(self):
        self.assertEqual(self.raw, self.rom[0x12C8DC:0x12C95E])
        entries, rows = equipment.indices(self.mapping, self.index)
        entry = equipment.span_record(chance.OWNER, chance.END, entries, rows, self.rom)
        self.assertEqual(entry['instrs'], self.manifest['proof']['instructions'])
        self.assertEqual(entry['instrs'], 62)
        self.assertEqual(self.manifest['bindings'], equipment.bindings(chance.CALLS))
        image = match.elf_image(self.built[-1])
        original = equipment.bindings(chance.CALLS)
        targets = {f'func_{v:08X}': (v, False) for v in chance.CALLS.values()}
        equipment.check_original(image, chance.OWNER, original, targets)
        wrong = equipment.bindings(chance.CALLS | {14:chance.CHANCE})
        with self.assertRaises(ValueError):
            equipment.check_original(image, chance.OWNER, wrong, targets)

    def test_complete_direct_call_inventory_and_dispatch_tables(self):
        sites, owners = chance.caller_inventory(self.rom, self.mapping, self.index)
        self.assertEqual((len(sites), len(owners)), (12, 10))
        self.assertEqual(next(row['sites'] for row in owners if row['owner'] == 0x0812DBA8),
                         [0x0812DF34, 0x0812DF42, 0x0812DF68])
        omitted = bytearray(self.rom)
        omitted[0x12DF42:0x12DF46] = bytes(4)
        self.assertNotIn(0x0812DF42, chance.direct_sites(omitted))
        with self.assertRaisesRegex(ValueError, 'incoming BL inventory'):
            chance.caller_inventory(omitted, self.mapping, self.index)
        for pc in (0x0812DCBC, 0x0812DE68, 0x0812DE90, 0x0812DF5C):
            changed = bytearray(self.rom)
            changed[pc-equipment.BASE] ^= 1
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                chance.dispatch_routes(changed)

    def test_stack_slots_and_control_flow_mutations(self):
        md = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        def instructions(data):
            return {i.address:i for i in md.disasm(bytes(data), chance.OWNER)}
        chance.frame_accesses(instructions(self.raw))
        for pc in (0x0812C8DE, 0x0812C8E8, 0x0812C8EE, 0x0812C8F2, 0x0812C90C,
                   0x0812C930, 0x0812C932, 0x0812C934, 0x0812C944, 0x0812C950, 0x0812C956):
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                changed = bytearray(self.raw)
                changed[pc-chance.OWNER] ^= 1
                chance.frame_accesses(instructions(changed))

    def test_changed_producer_and_equipment_query(self):
        for pc, check in [(0x0812E566,equipment.producer), (0x0812E540,equipment.producer),
                          (0x0812E54A,equipment.producer), (0x0812E5A6,equipment.producer),
                          (0x080CA7C4,equipment.equipment_access)]:
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                changed = bytearray(self.rom)
                changed[pc-equipment.BASE] ^= 1
                check(changed)

    def test_source_bound_to_array_and_reader(self):
        original = self.root/'src/0812C8DC.c'
        with tempfile.TemporaryDirectory() as tempdir:
            root = Path(tempdir)
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            header = root/chance.HEADER_PATH
            header.write_bytes((self.root/chance.HEADER_PATH).read_bytes())
            (root/'src').mkdir()
            dest = root/'src/0812C8DC.c'
            for src, replacement in [('u16 entries[2]', 'u16 entries[3]'), ('entries[0]', 'entries[1]'),
                                     ('target->direction', 'source->direction'),
                                     ('u32 mode, u32 unused', 'u8 mode, u32 unused')]:
                self.assertIn(src, original.read_text())
                dest.write_text(original.read_text().replace(src, replacement))
                with self.subTest(src=src), self.assertRaises(ValueError):
                    equipment.check_source(root, chance.OWNER)
            dest.write_bytes(original.read_bytes())
            equipment.check_source(root, chance.OWNER)
            header_text = header.read_text()
            for old, new in [('0xF6 - 0xEB', '0xF5 - 0xEB'), ('u32 check_position', 'u8 check_position'),
                             ('struct Unit {', 'struct PositionedUnit {')]:
                with self.subTest(old=old):
                    self.assertIn(old, header_text)
                    header.write_text(header_text.replace(old, new))
                    with self.assertRaisesRegex(ValueError, 'unit fields or helper declarations'):
                        equipment.check_source(root, chance.OWNER)

    def test_saved_report_replays_source_and_frame(self):
        import match_evidence
        report = (self.root/'docs/match/0812C8DC.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, chance.OWNER))
        for old, new in [('"frame_read_offset":24', '"frame_read_offset":26'),
                         ('"local":[-24,-20]', '"local":[-24,-18]'),
                         ('None establishes this live equipment', 'Each establishes this live equipment'),
                         ('**MATCH - byte identical** - 130/130', '**MATCH - byte identical** - 128/130')]:
            self.assertIn(old, report)
            with self.subTest(old=old):
                self.assertFalse(match_evidence.report_matches(report.replace(old, new), self.root, chance.OWNER))

    def test_native_producer_and_evaluator_arguments(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg

        cpu, call, write, _ = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        cases = {}
        for group, row, slots, selected in equipment.scene_rows(self.rom):
            cases.setdefault(len(selected), (equipment.GROUPS[group][1]+48*row, selected))
        self.assertEqual(set(cases), {0, 1, 2})
        frame_sp = 0x03007F00-48
        records = {}
        def trace(machine, pc, width, context):
            registers = tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
            if pc == chance.CHANCE:
                sp = machine.reg_read(reg.UC_ARM_REG_SP)
                records['args'] = registers + struct.unpack('<6I', machine.mem_read(sp, 24))
                records['selected'] = struct.unpack('<2H', machine.mem_read(sp+24, 4))
            elif pc == equipment.WRAPPER:
                records['wrapper'] = registers[:2]
            elif pc == 0x0812E540:
                records.setdefault('writes', []).append(machine.reg_read(reg.UC_ARM_REG_R6)-frame_sp)
            elif pc == 0x0812C940:
                records['base'] = registers[0]
            elif pc == chance.STATUS:
                records['status'] = registers[0]
        for pc in (chance.CHANCE, equipment.WRAPPER, 0x0812E540, 0x0812C940, chance.STATUS):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        for count, (definition, selected) in cases.items():
            call(0x080C9644, source, definition, 0)
            call(0x080C9644, target, definition, 0)
            write(source+0xE9, 'B', 0)
            write(source+0xF6, 'bbb', 2, 3, 1)
            write(target+0xF6, 'bbb', 3, 3, 2)
            for mode in (0, 1, 2, 0x100, 0x101, 0xFFFFFF01):
                for flagged in (False, True):
                    flags = cpu.mem_read(target+0xEA,1)[0] & ~2
                    write(target+0xEA,'B',flags | (2 if flagged else 0))
                    records.clear()
                    result = call(chance.OWNER, source, target, mode, 0)
                    self.assertEqual(records['wrapper'], (source, frame_sp+24))
                    self.assertEqual(records.get('writes', []), [24, 26][:count])
                    emitted = [x for x in records['selected'] if x]
                    self.assertCountEqual(emitted, selected)
                    self.assertEqual(records['args'], (source,target,records['selected'][0],2,3,3,3,2,(mode & 255)==1,1))
                    base = records['base']
                    self.assertEqual(records.get('status'), target if base else None)
                    self.assertEqual(result, 100 if base and flagged else base)


if __name__ == '__main__':
    unittest.main()
