"""Native source, mixed object/scalar layout, and the menu runner's physical slot-2 call."""
import copy
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence as evidence
import menu_runner_switches as menu
import multiple_switch_native_profile as multiple
import owner_admission_profile as owner


def changed(blob, pos):
    return blob[:pos] + bytes([blob[pos] ^ 1]) + blob[pos+1:]


@unittest.skipUnless(os.environ.get('FFTA_MENU_RUNNER_ROOT'), 'needs the indexed game, original ROM and 08034E88 source')
class MenuRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MENU_RUNNER_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        args = SimpleNamespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
            assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(cls.root))
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, cls.root, menu.OWNER, 'src/08034E88.c')
            cls.body, cls.bindings = owner.object_bytes(runner, workspace, args, original, menu.OWNER,
                cls.rom, cls.mapping, cls.objects, selector=multiple.SELECTOR, index=cls.index)
            cls.original = runner.read_binary(workspace+'/f.o')
            cls.linked = runner.read_binary(workspace+'/f.elf')

    def verify(self, **changes):
        args = dict(raw_object=self.original, linked_file=self.linked, address=menu.OWNER, rom=self.rom,
                    mapping=self.mapping, index=self.index, reported_bindings=self.bindings, objects=self.objects)
        return menu.verify_original(**dict(args, **changes))

    def test_native_and_saved_replay(self):
        proof, count = self.verify()
        self.assertEqual((len(self.body), count), (364, 89))
        self.assertEqual(self.body, self.rom[0x34e88:0x34ff4])
        self.assertEqual([len(self.bindings[k]) for k in ('calls','switches','data')], [19, 31, 3])
        report = (self.root/'docs/match/08034E88.md').read_text()
        self.assertTrue(evidence.report_matches(report, str(self.root), menu.OWNER))
        for original in ('364/364', '"tail_value":20', '"slot":2', '"selector_offsets":[1208,1209,1210]'):
            self.assertIn(original, report)
            self.assertFalse(evidence.report_matches(report.replace(original, 'changed'), str(self.root), menu.OWNER))
        modified = copy.deepcopy(proof)
        modified['registration']['count'] = 3
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest=modified)
        with self.assertRaisesRegex(ValueError, 'data target'):
            multiple.verify_original(self.original, self.linked, menu.OWNER, self.rom, self.mapping, self.index, self.bindings)

    def test_raw_linked_symbol_roles_and_relocations(self):
        for name in ('g_state_03002810', 'func_08043468'):
            for key, blob in [('raw_object', self.original), ('linked_file', self.linked)]:
                image = match.elf_image(blob)
                for section, rows in image['symbol_tables'].items():
                    for i, symbol in enumerate(rows):
                        if symbol['name'] == name:
                            pos = image['sections'][section][4] + 16*i
                            for field in (4, 8, 12, 14):
                                with self.subTest(key=key, name=name, field=field), self.assertRaises(ValueError):
                                    self.verify(**{key: changed(blob, pos+field)})
        for key, blob in [('raw_object', self.original), ('linked_file', self.linked)]:
            image = match.elf_image(blob)
            text = image['sections'][image['text_index']][4]
            # Arithmetic, both guards, interposed object(s) and scalar, bases, entries, tail and pool.
            for off in (2, 0xe, 0x14, 0x24, 0x28, 0x2c, 0x30, 0xb2, 0xc0, 0xc4, 0xc8,
                        0xcc, 0x10c, 0x14a, 0x154, 0x15a, 0x164, 0x168):
                with self.subTest(key=key, off=off), self.assertRaises(ValueError):
                    self.verify(**{key: changed(blob, text+off)})
        rel = match.elf_image(self.original)
        section = rel['sections'][rel['relocations'][0]]
        for pos in range(section[4], section[4]+section[5], 8):
            if struct.unpack_from('<I', self.original, pos)[0] in (2, 0x24, 0x28, 0xc0, 0xc8, 0x10c, 0x164):
                with self.subTest(pos=pos), self.assertRaises(ValueError):
                    self.verify(raw_object=changed(self.original, pos+4))

    def test_provider_dispatch_and_maps(self):
        for offset in (0x317d6, 0x317d8, 0x317da, 0x31810, 0x31814, 0x31818, 0x31fe0, 0x31fe4,
                       0x31fe6, 0x32018, 0x32044, 0x31870, 0x31872, 0x31874, 0x31884, 0x6a90, 0x6ae8,
                       0x6af0, 0x6af6, 0x6a30, 0x6a34, 0x6a6a, 0x14224c):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                menu.registration(changed(self.rom, offset))
        for key, blob, prefix, value in [('mapping', self.mapping, b'0x', b'08034E88'), ('index', self.index, b'', b'08034E88'),
                                  ('objects', self.objects, b'', b'g_state_03002810')]:
            modified = blob.replace(prefix+value, prefix+value[:-1]+b'7')
            self.assertNotEqual(modified, blob)
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.verify(**{key: modified})
        proof, _ = self.verify()
        for idx, slot in ((0, 1), (0, 2), (1, 1), (1, 2), (1, 18)):
            mod = copy.deepcopy(proof['switches'])
            mod[idx]['relocations'][slot][1] += 2
            with self.subTest(idx=idx, slot=slot), self.assertRaises(ValueError):
                menu.selector_calls(self.rom, mod)

    def test_original_runner_both_tables_all_byte_values(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_R0,
            UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6,
            UC_ARM_REG_R7, UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11)
        registers = (UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6, UC_ARM_REG_R7,
                     UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11)
        for body in (self.rom[0x34e88:0x34ff4], self.body):
            cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
            for start, length in ((0x08000000, len(self.rom)), (0x02000000, 0x40000), (0x03000000, 0x8000)):
                cpu.mem_map(start, length)
            cpu.mem_write(0x08000000, self.rom)
            cpu.mem_write(menu.OWNER, body)
            sp = 0x03006000
            cpu.reg_write(UC_ARM_REG_SP, sp)

            def run(start, end):
                cpu.emu_start(start | 1, end, count=500)
                self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), end)
                self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), sp)

            def word(address):
                return struct.unpack('<I', cpu.mem_read(address, 4))[0]

            run(0x080317d2, 0x080317de)
            self.assertEqual((word(menu.RUNNER+8), word(menu.RUNNER+12)), (0x030009b0, 0x03000ec8))
            cpu.mem_write(0x03000eca, b'\xff')
            run(0x08031fde, 0x08031fea)
            self.assertEqual((word(0x030009b8), bytes(cpu.mem_read(0x03000eca, 1))), (menu.OWNER | 1, b'\0'))
            # Distinct live state objects let returning ordinary callees replace the global before every next phase.
            states = (0x02004000, 0x02005000, 0x02006000, 0x02007000)
            ordinary = set(menu.FIRST.values()) | set(menu.SECOND.values()) | {menu.INITIAL, menu.TAIL}
            observed, reads = [], []

            def on_code(uc, pc, size, data):
                if pc == menu.OWNER:
                    self.assertEqual((uc.reg_read(UC_ARM_REG_R0), uc.reg_read(UC_ARM_REG_R1)), (2, 0x03000eca))
                if pc in ordinary:
                    observed.append((pc, None if pc == menu.INITIAL else uc.reg_read(UC_ARM_REG_R0)))
                    next_state = {menu.INITIAL: states[1], **dict.fromkeys(menu.FIRST.values(), states[2]),
                                  **dict.fromkeys(menu.SECOND.values(), states[3])}.get(pc)
                    if next_state:
                        uc.mem_write(menu.STATE, struct.pack('<I', next_state))
                    for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3):
                        uc.reg_write(reg, 0xbadf00d)
                    uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))

            def on_read(uc, access, address, size, value, data):
                if address == menu.STATE or states[0] <= address < states[-1]+0x1000:
                    reads.append((address, size))

            modeled_calls = cpu.hook_add(UC_HOOK_CODE, on_code)
            cpu.hook_add(UC_HOOK_MEM_READ, on_read)
            cases = [(i, (i+17) & 255, 255-i) for i in range(256)]
            cases += [(a, b, c) for a in [0, *menu.FIRST] for b in [0, *menu.SECOND] for c in (19, 20, 21)]
            for a, b, c in cases:
                state2 = states[2] if a in menu.FIRST else states[1]
                state3 = states[3] if b in menu.SECOND else state2
                for ptr in states:
                    cpu.mem_write(ptr+0x4b8, b'\xfe\xfe\xfe')
                cpu.mem_write(states[1]+0x4b8, bytes([a]))
                cpu.mem_write(state2+0x4b9, bytes([b]))
                cpu.mem_write(state3+0x4ba, bytes([c]))
                cpu.mem_write(menu.STATE, struct.pack('<I', states[0]))
                # Alternate the two actual runner paths (scan all five slots, or select slot 2 directly).
                cpu.mem_write(menu.RUNNER+5, bytes([0 if a % 2 == 0 else 3]))
                for i, reg in enumerate(registers):
                    cpu.reg_write(reg, 0xab1000+i)
                observed.clear()
                reads.clear()
                run(0x08031870, 0x08031878)
                expected = [(menu.INITIAL, None)]
                if a in menu.FIRST:
                    expected.append((menu.FIRST[a], 0))
                if b in menu.SECOND:
                    expected.append((menu.SECOND[b], 1))
                if c == 20:
                    expected.append((menu.TAIL, 2))
                self.assertEqual(observed, expected)
                self.assertEqual(reads, [(menu.STATE, 4), (states[1]+0x4b8, 1), (menu.STATE, 4), (state2+0x4b9, 1),
                                         (menu.STATE, 4), (state3+0x4ba, 1)])
                self.assertEqual(cpu.mem_read(menu.RUNNER+4, 1), b'\x01')
                self.assertEqual([cpu.reg_read(r) for r in registers], [0xab1000+i for i in range(8)])

            # An additional complete dispatch executes both callees for real. The first moves
            # the sliding object, and the final selector clears active[2] in its 0xFF state.
            cpu.hook_del(modeled_calls)
            actual = []
            def observe_actual(uc, pc, size, data):
                if pc in ordinary:
                    actual.append(pc)
            cpu.hook_add(UC_HOOK_CODE, observe_actual)
            state, sliding = states[0], 0x02016000
            cpu.mem_write(menu.STATE, struct.pack('<I', state))
            cpu.mem_write(state+4, struct.pack('<I', sliding))
            cpu.mem_write(sliding+0x18, bytes([9]))
            cpu.mem_write(state+0x4b8, bytes([0, 0, 20]))
            cpu.mem_write(state+0x954+2*0xcc+0x33, bytes([255]))
            run(0x08031870, 0x08031878)
            self.assertEqual(actual, [0x08034c94, 0x0804b7e8])
            self.assertEqual(cpu.mem_read(sliding+0x18, 1), bytes([7]))
            self.assertEqual(cpu.mem_read(state+0x4ba, 1), bytes([0]))


if __name__ == '__main__':
    unittest.main()
