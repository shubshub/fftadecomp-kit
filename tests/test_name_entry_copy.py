"""The initialized ten-halfword name buffer, boot provenance, and original ELF roles."""
import copy
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import name_entry_copy as name
import owner_admission_profile as owner


class CopyControl(unittest.TestCase):
    def test_bounded_count_and_cpu_mode(self):
        units = name.installation.plain_copy_units
        self.assertEqual(units(10, 20), (10, 2))
        self.assertEqual(units(0x04000005, 20), (5, 4))
        for control in (0, 11, 0x01000001, 0x04000006, 0x00200001):
            with self.subTest(control=control), self.assertRaises(ValueError):
                units(control, 20)


@unittest.skipUnless(os.getenv('FFTA_NAME_ENTRY_ROOT'), 'requires original ROM and compiled name-entry source')
class NameEntry(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_NAME_ENTRY_ROOT']).resolve()
        with patch.object(owner.small_copy_binding, 'check_linked', wraps=owner.small_copy_binding.check_linked) as verified:
            (cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom,
             cls.count, cls.elf) = owner.build(cls.root, name.OWNER, selector=name.buffers.THUNK_SELECTOR)
        cls.linked, _, cls.targets = verified.call_args.args

    def test_names_frame_and_producer_replay(self):
        report = (self.root / 'docs/match/0812A878.md').read_text()
        self.assertEqual((len(self.body), self.count), (164, 72))
        self.assertEqual(self.body, self.rom[0x12A878:0x12A91C])
        self.assertTrue(match_evidence.report_matches(report, self.root, name.OWNER))
        self.assertIn('* control flow: ' + name.buffers.NAME_ENTRY_CONTROL_FLOW, report.splitlines())
        for old, new in (('"final_halfwords":10', '"final_halfwords":9'),
                         ('"zero_terminator":[18,20]', '"zero_terminator":[16,18]'),
                         ('"clearer_save":[-40,-36]', '"clearer_save":[-36,-32]')):
            changed = report.replace(old, new)
            self.assertNotEqual(changed, report)
            self.assertFalse(match_evidence.report_matches(changed, self.root, name.OWNER))
        environment = copy.deepcopy(self.manifest['proof']['environment'])
        environment['sources']['installed_zero_effects.py'] = '0' * 64
        with patch.object(name, 'environment_fingerprint', return_value=environment):
            self.assertFalse(match_evidence.report_matches(report, self.root, name.OWNER))

    def test_both_indexes_must_count_reachable_instructions(self):
        mapping_row = b'"end": "0x0812A91C",\n    "instrs": 72'
        index_row = b'0812A878 0812A91C   164  72 return'
        self.assertEqual(self.mapping.count(mapping_row), 1)
        self.assertEqual(self.index.count(index_row), 1)
        for map_count, text_count in ((82, 82), (71, 71), (72, 82), (82, 72)):
            mapping = self.mapping.replace(mapping_row, mapping_row[:-2] + str(map_count).encode())
            index = self.index.replace(index_row, index_row.replace(b' 72 ', f' {text_count} '.encode()))
            with self.subTest(map_count=map_count, text_count=text_count), self.assertRaises(ValueError):
                owner.verify(self.body, name.OWNER, self.rom, mapping, index, self.objects,
                             bindings=name.BINDINGS, selector=name.buffers.THUNK_SELECTOR)

    def test_wrong_source_extent_or_callback_declaration(self):
        with tempfile.TemporaryDirectory() as workspace:
            root = Path(workspace)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            path = root/'src/0812A878.c'
            source = (self.root/'src/0812A878.c').read_text()
            for changed in (source.replace('name[20]', 'name[19]').replace('sizeof(name)', '20'),
                            source.replace('void *destination, u32 size', 'u8 *destination, u8 size')):
                self.assertNotEqual(changed, source)
                path.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'reviewed state'):
                    name.check_source(root)

    def test_real_elf_externals_require_correct_size_and_relocation_roles(self):
        image = match.elf_image(self.elf)
        for symbol in (name.VIA, name.CPUSET, name.TABLE):
            mutated = copy.deepcopy(image)
            next(row for row in mutated['symbols'] if row['name'] == symbol)['size'] = 4
            with self.subTest(symbol=symbol), self.assertRaises(ValueError):
                owner.original_bindings(mutated, name.OWNER, self.rom, self.mapping, self.objects,
                                        selector=name.buffers.THUNK_SELECTOR, index=self.index)
        roles = {name.VIA: (name.thunk.ALIASES[name.VIA], False),
                 name.CPUSET: (name.bios.ADDRESS, False), name.TABLE: (name.boot.POINTER, True)}
        for kind, i, field, replacement in (('calls', 0, 1, 'func_0814224C'),
                                           ('calls', 1, 0, 62), ('data', 0, 2, 4)):
            changed = copy.deepcopy(name.BINDINGS)
            changed[kind][i][field] = replacement
            with self.assertRaisesRegex(ValueError, 'original calls'):
                name.check_original(image, changed, roles)

    def test_linked_object_and_thumb_target_types(self):
        for symbol, wrong_type in ((name.TABLE, 2), (name.CPUSET, 1), (name.VIA, 1)):
            linked = copy.deepcopy(self.linked)
            next(row for row in linked['symbols'] if row['name'] == symbol)['type'] = wrong_type
            with self.subTest(symbol=symbol), self.assertRaisesRegex(ValueError, 'typed original binding'):
                owner.small_copy_binding.check_linked(linked, name.OWNER, self.targets)

    def test_clear_producer_rejects_wrong_rom_dependencies(self):
        for offset in (0x254, 0x2796, 0x36D4B8, 0xA38A2C, 0x14186C, 0x14224C):
            changed = bytearray(self.rom)
            changed[offset] ^= 2
            with self.subTest(address=hex(offset)), self.assertRaises(ValueError):
                name.callback(bytes(changed), self.mapping, self.index)

    def test_native_scan_rejects_different_frame_bounds_and_store(self):
        for offset in (2, 14, 0x32, 0x56, 0x6A, 0x96):
            changed = bytearray(self.body)
            changed[offset] ^= 1
            refinement = owner.refine(bytes(changed), name.OWNER, self.mapping)
            ins = name.graph.graph(bytes(changed), name.OWNER, refinement)[0]
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                name.scan(ins)

    def test_thumb_name_cells_and_cpuset_operands(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR, UC_HOOK_CODE
        from unicorn import arm_const as arm

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        base = match.ROM_BASE
        state, output, sp = 0x02001000, 0x02003000, 0x03007E00
        cpu.mem_map(base, len(self.rom))
        cpu.mem_write(base, self.rom)
        cpu.mem_map(0x02000000, 0x4000)
        cpu.mem_map(0x03000000, 0x8000)
        provider = self.manifest['proof']['provider']
        src, end = provider['installation']['source']
        cpu.mem_write(name.boot.DESTINATION, self.rom[src-base:end-base])
        copies, clear = [], []

        def read_args(cpu):
            return tuple(cpu.reg_read(r) for r in (arm.UC_ARM_REG_R0, arm.UC_ARM_REG_R1, arm.UC_ARM_REG_R2))

        def bios(cpu, interrupt, context):
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), name.bios.ADDRESS + 2)
            source, destination, control = read_args(cpu)
            self.assertTrue(1 <= control <= 10)
            copies.append((source, destination, control))
            cpu.mem_write(destination, bytes(cpu.mem_read(source, 2*control)))
            for reg in (arm.UC_ARM_REG_R0, arm.UC_ARM_REG_R1, arm.UC_ARM_REG_R2, arm.UC_ARM_REG_R3, arm.UC_ARM_REG_R12):
                cpu.reg_write(reg, 0xDDDDDDDD)

        def entered_clear(cpu, address, size, context):
            clear.append(read_args(cpu))

        cpu.hook_add(UC_HOOK_INTR, bios)
        cpu.hook_add(UC_HOOK_CODE, entered_clear, begin=name.boot.DESTINATION, end=name.boot.DESTINATION)
        blank, glyph = b'\x40\x73', b'\x91\x41'
        cases = [[blank]*first + [cell]*(9-first-trailing) + [blank]*trailing
                 for first in range(10) for trailing in range(10-first)
                 for cell in (b'\x40\x72', glyph, b'\0\xf9')]
        cases.extend(([glyph, blank, b'\0\xf9', glyph, blank, b'\0\x4f', blank, blank, blank],
                      [blank, b'\0\xf9', blank, glyph, blank, b'\x40\x72', glyph, blank, blank]))
        for cells in cases:
            for destination in (output, state+0x312):
                cpu.mem_write(sp-48,b'\xa5'*64)
                cpu.mem_write(destination-1,b'\xcc'*22)
                cpu.mem_write(state+0x312,b''.join(cells))
                cpu.reg_write(arm.UC_ARM_REG_SP,sp)
                cpu.reg_write(arm.UC_ARM_REG_LR,base|1)
                cpu.reg_write(arm.UC_ARM_REG_R0,state)
                cpu.reg_write(arm.UC_ARM_REG_R1,destination)
                saved = tuple(range(arm.UC_ARM_REG_R4, arm.UC_ARM_REG_R11+1))
                for reg in saved:
                    cpu.reg_write(reg,reg+0x1000)
                clear.clear()
                copies.clear()
                cpu.emu_start(name.OWNER|1, base, count=2000)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), base)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
                self.assertTrue(all(cpu.reg_read(reg) == reg+0x1000 for reg in saved))
                self.assertEqual(clear,[(sp-36,20,name.boot.DESTINATION|1)])
                expected_cells = list(cells)
                while expected_cells and expected_cells[0] == blank:
                    expected_cells.pop(0)
                length = len(expected_cells)
                expected_copies = [(state+0x324-2*length,sp-36,length)] if length else []
                self.assertEqual(copies,expected_copies+[(sp-36,destination,10)])
                while expected_cells and (expected_cells[-1] == blank or expected_cells[-1][0] == 0):
                    expected_cells.pop()
                self.assertEqual(cpu.mem_read(destination-1,22),
                                 b'\xcc'+b''.join(expected_cells).ljust(20,b'\0')+b'\xcc')
                self.assertEqual(cpu.mem_read(sp-48,8),b'\xa5'*8)
                self.assertEqual(cpu.mem_read(sp,16),b'\xa5'*16)
