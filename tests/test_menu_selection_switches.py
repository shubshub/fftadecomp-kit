"""Original USA menu query, native C, two original guarded tables and real caller contexts."""
import copy
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import match
import match_evidence as evidence
import menu_selection_switches as menu
import multiple_switch_native_profile as multiple
import owner_admission_profile as owner


def patch_at(blob, offset, replacement):
    return blob[:offset] + replacement + blob[offset+len(replacement):]


def symbol_offset(image, name):
    for section, rows in image['symbol_tables'].items():
        for index, row in enumerate(rows):
            if row['name'] == name:
                return image['sections'][section][4] + 16*index
    raise AssertionError(name)


@unittest.skipUnless(os.environ.get("FFTA_MENU_SELECTION_ROOT"), "needs the original ROM and indexed menu source")
class MenuSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MENU_SELECTION_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        args = SimpleNamespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
            assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(cls.root))
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, cls.root, menu.OWNER, 'src/0804E224.c')
            cls.body, cls.bindings = owner.object_bytes(runner, workspace, args, original, menu.OWNER,
                cls.rom, cls.mapping, cls.objects, selector=multiple.SELECTOR, index=cls.index)
            cls.original = runner.read_binary(workspace + '/f.o')
            cls.linked = runner.read_binary(workspace + '/f.elf')

    def verify(self, **changes):
        args = dict(raw_object=self.original, linked_file=self.linked, address=menu.OWNER, rom=self.rom,
                    mapping=self.mapping, index=self.index, reported_bindings=self.bindings, objects=self.objects)
        return menu.verify_original(**dict(args, **changes))

    def test_original_and_canonical_saved_evidence(self):
        self.assertEqual(self.body, self.rom[menu.OWNER-menu.BASE:menu.OWNER-menu.BASE+306])
        proof, count = self.verify()
        self.assertEqual(count, 80)
        self.assertEqual(len(proof['bindings']['switches']), 31)
        self.assertEqual(proof['bindings']['data'], [[0x128, 'g_table_08529EE4', 0]])
        report = (self.root / 'docs/match/0804E224.md').read_text()
        self.assertTrue(evidence.report_matches(report, str(self.root), menu.OWNER))
        for token in ('306/306', '"id_count":300', '"rom_stride":2', '"known_caller_state":2'):
            self.assertIn(token, report)
            self.assertFalse(evidence.report_matches(report.replace(token, 'altered'), str(self.root), menu.OWNER))
        changed = copy.deepcopy(proof)
        changed['lookup']['rom_stride'] = 4
        with self.assertRaisesRegex(ValueError, "manifest differs"):
            self.verify(manifest=changed)
        with self.assertRaises(ValueError):
            multiple.verify_original(self.original, self.linked, menu.OWNER, self.rom, self.mapping,
                                     self.index, self.bindings)

    def test_original_and_linked_symbol_and_relocation_roles(self):
        for name in ('func_08005BFC', 'g_table_08529EE4'):
            for key, blob in [('raw_object', self.original), ('linked_file', self.linked)]:
                image = match.elf_image(blob)
                pos = symbol_offset(image, name)
                for field, value in [(4, b'\x04'), (8, b'\x04'), (12, b'\x11' if key == 'raw_object'
                         else b'\x10'), (14, b'\x01')]:
                    with self.subTest(key=key, name=name, field=field), self.assertRaises(ValueError):
                        self.verify(**{key: patch_at(blob, pos+field, value)})
        image = match.elf_image(self.original)
        text_offset = image['sections'][image['text_index']][4]
        for offset in (2, 0x24, 0x28, 0x7c, 0x80, 0x128, 306):
            value = bytes([self.original[text_offset+offset] ^ 4])
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(raw_object=patch_at(self.original, text_offset+offset, value))
        rel = image['sections'][image['relocations'][0]]
        for pos in range(rel[4], rel[4]+rel[5], 8):
            if struct.unpack_from('<I', self.original, pos)[0] in (2, 0x128, 0x80):
                with self.subTest(pos=pos), self.assertRaises(ValueError):
                    self.verify(raw_object=patch_at(self.original, pos+4, b'\x08'))

    def test_range_guards_lookup_width_and_caller_identity(self):
        proof, _ = self.verify()
        for offset in (8, 0xe, 0x14, 0x28, 0x52, 0x5c, 0x68, 0x80, 0xfe, 0x114, 0x120, 0x124):
            at = menu.OWNER-menu.BASE+offset
            rom = patch_at(self.rom, at, bytes([self.rom[at] ^ 4]))
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(rom=rom)
        for addr in (menu.GETTER, 0x0804CBD4, 0x0804CBE4, 0x0804CD06, 0x0804E1E8, 0x0804D5A4, 0x0804E9C8,
                     0x0804E9CC, 0x080CE8AC, 0x080CE8CE, 0x080CE8D4, 0x080CE8F0, 0x080CE8F4, 0x080CED2C, menu.IDS+600, *(site-2 for site in menu.CALL_SITES)):
            at = addr-menu.BASE
            with self.subTest(addr=hex(addr)), self.assertRaises(ValueError):
                menu.context(patch_at(self.rom, at, bytes([self.rom[at] ^ 1])))
        for arm, slot in ((0, 1), (1, 1), (1, 7)):
            switches = copy.deepcopy(proof['switches'])
            switches[arm]['relocations'][slot][1] += 4
            with self.subTest(arm=arm, slot=slot), self.assertRaises(ValueError):
                menu.lookup_semantics(self.rom, switches)
        mapping = self.mapping.replace(b'"0x0804E224"', b'"0x0804E226"')
        self.assertTrue(mapping != self.mapping, "the dual-index negative must change the owner row")
        with self.assertRaises(ValueError):
            self.verify(mapping=mapping)

    def execute(self, body, mode, selection, ident=0, site=None, dispatch=False):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R5
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        task, data, context = 0x02001000, 0x02002000, 0x02000400
        global_ptr, stack, exit_pc = 0x0201F544, 0x03007E00, 0x0804D800
        for start, length in ((0x08005000, 0x1000), (0x0804c000, 0x3000), (menu.IDS & ~4095, 0x2000),
                              (0x02000000, 0x40000), (0x03000000, 0x8000)):
            cpu.mem_map(start, length)
            if start >= menu.BASE:
                cpu.mem_write(start, self.rom[start-menu.BASE:start-menu.BASE+length])
        cpu.mem_write(menu.OWNER, body)
        cpu.mem_write(global_ptr, struct.pack('<I', context))
        cpu.mem_write(context+8, struct.pack('<H', 2))
        cpu.mem_write(context+0x1c, struct.pack('<II', task, task))
        cpu.mem_write(task+24, struct.pack('<IHhB', data, 0, selection, mode))
        index = ((selection-1 + 0x8000) & 0xffff) - 0x8000
        target, width, expected = None, 0, 0
        if mode == 1:
            expected = -1
            if selection != -1:
                target, width = data+0x524+4*index, 4
                expected = {0x3b: 1, 0x3c: 2, 0x3d: 3, 0x3e: 4, 0x4f: 5, 0x3f: 6}.get(ident, -1)
                cpu.mem_write(target, struct.pack('<I', ident))
        elif mode in (3, 4, 5, 6):
            target = data+0x424+4*index
            width, expected = (2, 0xcdef) if mode == 5 else (4, 0x89abcdef)
            cpu.mem_write(target, struct.pack('<I', 0x89abcdef))
        elif mode == 8:
            target, width = menu.IDS+2*index, 2
            expected, = struct.unpack_from('<H', self.rom, target-menu.BASE)
        reads, calls = [], []
        def watch_read(uc, kind, address, size, value, userdata):
            if (data+0x300 <= address < 0x02040000 and address not in (global_ptr, global_ptr+4)
                    or menu.IDS-6 <= address < menu.IDS+0x1000):
                reads.append((address, size))
        def watch_call(uc, address, size, userdata):
            if address in (menu.OWNER, menu.GETTER):
                calls.append((address, uc.reg_read(UC_ARM_REG_R0)))
        cpu.hook_add(UC_HOOK_MEM_READ, watch_read)
        cpu.hook_add(UC_HOOK_CODE, watch_call)
        cpu.reg_write(UC_ARM_REG_SP, stack)
        cpu.reg_write(UC_ARM_REG_LR, exit_pc|1)
        cpu.reg_write(UC_ARM_REG_R5, global_ptr)
        start = 0x0804CBB4 if dispatch else site-4
        zero_exit = dispatch and selection == 0
        end = exit_pc if zero_exit else (menu.CALL_SITES[0] if dispatch else site)+4
        cpu.emu_start(start|1, end, count=250)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), end)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), stack-40 if dispatch and not zero_exit else stack)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_R5), global_ptr)
        getter_call = [(menu.GETTER, task)]
        self.assertEqual(calls, (getter_call if dispatch else []) + ([] if zero_exit else [(menu.OWNER, task)]+getter_call))
        self.assertEqual(reads, [] if target is None or zero_exit else [(target, width)])
        self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), 0 if zero_exit else expected & 0xffffffff)
        return target

    def test_original_cpu_guarded_cases_six_call_sites_and_invalid_selections(self):
        cases = [(1, 1, item) for item in range(0x3a, 0x51)] + [(1, -1, 0), (1, 64, 0x4f)]
        cases.extend((mode, selection, 0) for mode in (3, 4, 5, 6) for selection in (1, 64))
        cases.extend((mode, 1, 0) for mode in (0, 2, 7, 9, 255))
        cases.extend([(8, 1, 0), (8, 300, 0), (8, 301, 0), (8, 0, 0), (5, 0, 0), (3, -32768, 0)])
        start = menu.OWNER-menu.BASE
        for body in (self.rom[start:start+306], self.body):
            for i, case in enumerate(cases):
                with self.subTest(case=case):
                    self.execute(body, *case, site=menu.CALL_SITES[i % len(menu.CALL_SITES)])
            self.execute(body, 5, 1, dispatch=True)
            self.execute(body, 5, 0, dispatch=True)
            self.assertEqual(self.execute(body, 8, 301, dispatch=True), menu.IDS+600)
            self.assertEqual(self.execute(body, 5, 0, site=menu.CALL_SITES[1]), 0x02002000+0x420)
            self.assertEqual(self.execute(body, 3, -32768, site=menu.CALL_SITES[1]), 0x02002000+0x424+32767*4)


if __name__ == '__main__':
    unittest.main()
