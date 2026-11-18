import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import affine_oam_slot as affine


@unittest.skipUnless(
    os.getenv('FFTA_AFFINE_OAM_ROOT'), 'requires the USA ROM, native agbcc and reviewed game sources'
)
class AffineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path

        cls.root = Path(os.environ['FFTA_AFFINE_OAM_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.bodies = affine.compile_bodies(cls.root, cls.rom)

    def test_bindings_and_compiler_controls(self):
        import plausible
        from match_evidence import report_matches

        path = self.root / affine.SOURCE
        text = path.read_text()
        header = (self.root / affine.HEADER).read_bytes()
        self.assertEqual(
            len(affine.qualifier_offsets(text, self.root, self.root, plausible.include_closure(self.root, path))),
            2,
        )
        self.assertFalse(plausible.check_file(path))
        for before, after in (
            ('const volatile', 'const'),
            ('volatile AffineMatrix *slots', 'AffineMatrix *slots'),
            ('< 32', '<= 32'),
            ('data_030032B0[2][32]', 'data_030032B0[1][64]'),
            ('return index;', 'return index + 1;'),
            ('slots[index].pd =', 'slots[index].pb ='),
        ):
            with self.subTest(after=after):
                self.assertIn(before, text)
                self.assertFalse(affine.source_offsets(text.replace(before, after), header))
        for variant in self.bodies:
            changed = self.bodies.copy()
            body = bytearray(changed[variant])
            body[0x20] ^= 1
            changed[variant] = body
            with self.assertRaises(ValueError):
                affine.check_bodies(changed)
        for sibling in ('0800105C', '08001194'):
            sibling_path = self.root / 'src' / f'{sibling}.c'
            sibling_source = sibling_path.read_text()
            self.assertIn('extern AffineMatrix data_030032B0[2][32];', sibling_source)
            self.assertIn('extern u8 data_03003270[2][32];', sibling_source)
            self.assertFalse(plausible.check_file(sibling_path))
            report = (self.root / 'docs/match' / f'{sibling}.md').read_text()
            self.assertTrue(report_matches(report, self.root, int(sibling, 16)))

    def test_original_provider_and_negative_edges(self):
        affine.provider(self.rom)
        rom = bytearray(self.rom)
        for offset in (
            0xD8,
            0x23C,
            0x138,
            0x1B4,
            0x1C0,
            0x294,
            0x2C4,
            0x38C,
            0x149434,
            0x4D8,
            0x1136,
            0x1144,
            0x119E,
            0x1228,
            0x47A,
            0x1CD6,
            0x1922,
            0x192C,
            0x1948,
            0x1B06,
            0x1B08,
            0x141894,
            0x12F2,
            0x1378,
            0x137C,
            0x1456,
            0x145E,
            0x1466,
            0x146A,
            0x146E,
            0x14BC,
            0x14C0,
            0x14C4,
            0x2796,
            0x36D4B8,
            0xA38A2C,
        ):
            rom[offset] ^= 1
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                affine.provider(rom)
            rom[offset] ^= 1

    def machine(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(affine.BASE, 0x400000)
        uc.mem_write(affine.BASE, self.rom[:0x400000])
        uc.mem_map(0x02000000, 0x10000)
        uc.mem_map(0x03000000, 0x8000)
        uc.mem_map(0x04000000, 0x1000)
        uc.mem_map(0x07000000, 0x1000)
        return uc

    def call(self, uc, address, *arguments):
        from unicorn.arm_const import (
            UC_ARM_REG_R0,
            UC_ARM_REG_R1,
            UC_ARM_REG_R2,
            UC_ARM_REG_R3,
            UC_ARM_REG_PC,
            UC_ARM_REG_LR,
            UC_ARM_REG_SP,
        )

        stack, stop = 0x03007E00, 0x03007000
        for reg, value in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), arguments):
            uc.reg_write(reg, value)
        for i, value in enumerate(arguments[4:]):
            uc.mem_write(stack + 4 * i, struct.pack('<I', value))
        uc.reg_write(UC_ARM_REG_SP, stack)
        uc.reg_write(UC_ARM_REG_LR, stop | 1)
        uc.emu_start(address | 1, stop, count=100000)
        self.assertEqual(uc.reg_read(UC_ARM_REG_PC), stop)
        self.assertEqual(uc.reg_read(UC_ARM_REG_SP), stack)
        return uc.reg_read(UC_ARM_REG_R0)

    def test_original_install_and_interrupt_dispatch(self):
        from unicorn.arm_const import UC_ARM_REG_CPSR, UC_ARM_REG_PC, UC_ARM_REG_SP

        uc = self.machine()
        # First three vector stores executed by Thumb startup, including +8.
        uc.emu_start(0x080002AF, 0x080002C6, count=24)
        self.assertEqual(struct.unpack('<I', uc.mem_read(0x030008D8, 4))[0], 0x080004B1)
        # Present IRQ IE/IF bit zero. Run the ARM dispatcher in IRQ mode; it
        # switches to System mode and branches to the installed Thumb handler.
        uc.mem_write(0x04000200, struct.pack('<HH', 1, 1))
        uc.reg_write(UC_ARM_REG_CPSR, 0x1F)
        uc.reg_write(UC_ARM_REG_SP, 0x03007EC0)
        uc.reg_write(UC_ARM_REG_CPSR, 0x92)
        uc.reg_write(UC_ARM_REG_SP, 0x03007FA0)
        uc.emu_start(0x080000FC, 0x080004B0, count=100)
        self.assertEqual(uc.reg_read(UC_ARM_REG_PC), 0x080004B0)
        self.assertEqual(uc.reg_read(UC_ARM_REG_CPSR) & 0x3F, 0x3F)

    def test_allocate_reuse_short_circuit_and_full(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_WRITE, UC_MEM_READ

        owner, src, used, slots = affine.OWNER, 0x02000020, 0x03003270, 0x030032B0
        target = (0x1234, 0x9876, 0x4060, 0x0234)
        packed = struct.pack('<4H', *target)
        for bank in (0, 1):
            for kind in ('empty', 'occupied', 'full', 'found-in-last'):
                outputs = []
                for variant in ('original', 'ordinary'):
                    uc = self.machine()
                    uc.mem_write(owner, self.bodies[variant])
                    uc.mem_write(src, packed)
                    uc.mem_write(0x03000028, bytes((bank,)))
                    table = slots + bank * 256
                    flags = used + bank * 32
                    uc.mem_write(slots, b'\xb6' * 512)
                    uc.mem_write(used, bytes((1,)) * 64)
                    if kind == 'empty':
                        uc.mem_write(flags, bytes(32))
                    elif kind == 'occupied':
                        # Holes precede an equal occupied entry. The first
                        # pass must find it without claiming the hole.
                        uc.mem_write(flags, bytes(4))
                        uc.mem_write(table + 5 * 8, packed)
                    elif kind == 'found-in-last':
                        for i in range(4):
                            near = list(target)
                            near[i] ^= 1
                            uc.mem_write(table + 8 * i, struct.pack('<4H', *near))
                        uc.mem_write(table + 31 * 8, packed)
                    events = []

                    def log(machine, op, addr, width, value, _):
                        events.append((op, addr, width))

                    for base, end in ((src, src + 7), (used, slots + 511)):
                        uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, log, begin=base, end=end)
                    before = bytes(uc.mem_read(used, 64 + 512))
                    result = self.call(uc, owner, src)
                    after = bytes(uc.mem_read(used, 64 + 512))
                    self.assertEqual(result, {'empty': 0, 'full': 0, 'occupied': 5, 'found-in-last': 31}[kind])
                    writes = [(addr, width) for op, addr, width in events if op == UC_MEM_WRITE]
                    if kind == 'empty':
                        self.assertEqual(writes, [(flags, 1)] + [(table + 2 * i, 2) for i in range(4)])
                        expected = bytearray(before)
                        expected[bank * 32] = 1
                        expected[64 + bank * 256 : 72 + bank * 256] = packed
                        self.assertEqual(after, expected)
                        matrix_events = [e for e in events if e[1] >= slots or src <= e[1] < src + 8]
                        trace = []
                        for i in range(4):
                            trace.append((UC_MEM_READ, src + 2 * i, 2))
                            if variant == 'original':
                                trace.append((UC_MEM_READ, table + 2 * i, 2))
                            trace.append((UC_MEM_WRITE, table + 2 * i, 2))
                        self.assertEqual(matrix_events, trace)
                    else:
                        self.assertEqual(writes, [])
                        self.assertEqual(before, after)
                    if kind == 'found-in-last':
                        for i in range(4):
                            row = [
                                (op, addr - table - 8 * i, width)
                                for op, addr, width in events
                                if table + 8 * i <= addr < table + 8 * (i + 1)
                            ]
                            width = 2 if variant == 'original' else 4
                            self.assertEqual(row, [(UC_MEM_READ, k, width) for k in range(0, 2 * i + 1, width)])
                    outputs.append((result, after))
                self.assertEqual(*outputs)

    def test_obj_affine_set_stack_copy_flipped_bank_and_vblank_upload(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_PC

        uc = self.machine()
        uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        # The original reset functions invoke the installed clear code.
        uc.mem_write(0x03003270, b'\xa5' * 576)
        self.call(uc, 0x0800105C)
        self.assertEqual(uc.mem_read(0x03003270, 576), bytes(576))
        sprite = 0x02000400
        uc.mem_write(sprite, struct.pack('<H', 1) + bytes(16))
        regs = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        bios_results = []

        def bios(u, _, __):
            pc = u.reg_read(UC_ARM_REG_PC)
            self.assertEqual(u.mem_read(pc - 2, 2), b'\x0f\xdf')
            source, dest, count, stride = (u.reg_read(reg) for reg in regs)
            sx, sy, angle = struct.unpack('<hhH', u.mem_read(source, 6))
            self.assertEqual((count, stride, angle), (1, 2, 0))
            matrix = struct.pack('<4h', sx, 0, 0, sy)  # ObjAffineSet at angle zero.
            bios_results.append(matrix)
            u.mem_write(dest, matrix)

        def dma(u, _, addr, width, value, __):
            control = int.from_bytes(u.mem_read(0x040000B8, 4), 'little')
            if control >> 31:
                self.assertEqual(control >> 24, 0x84)
                src, dst = struct.unpack('<II', u.mem_read(0x040000B0, 8))
                u.mem_write(dst, bytes(u.mem_read(src, 4 * (control & 65535))))
                u.mem_write(0x040000B8, bytes(4))

        inputs = []

        def enter(u, _, __, ___):
            p = u.reg_read(UC_ARM_REG_R0)
            if p == 0x02000200:
                return
            self.assertTrue(0x03007D00 <= p < 0x03007E00)
            inputs.append(bytes(u.mem_read(p, 8)))

        uc.hook_add(UC_HOOK_INTR, bios)
        uc.hook_add(UC_HOOK_MEM_READ, dma, begin=0x040000B8, end=0x040000BB)
        uc.hook_add(UC_HOOK_CODE, enter, begin=affine.OWNER, end=affine.OWNER)
        for bank in (0, 1):
            self.assertEqual(uc.mem_read(0x03000028, 1), bytes((bank,)))
            self.call(uc, 0x08001194)
            # Reserve a distinct slot so the returned matrix index is observable.
            matrix = 0x02000200
            uc.mem_write(matrix, struct.pack('<4H', 1, 2, 3, 4))
            self.assertEqual(self.call(uc, affine.OWNER, matrix), 0)
            sx, sy = 0x100 + bank * 7, 0x200 + bank * 11
            self.call(uc, 0x080018A0, sprite, 40, 60, 0, 0, 0, 0, 0, 0, sx, sy, 0, 0)
            self.assertEqual(inputs[-1], bios_results[-1])
            self.assertEqual(uc.mem_read(0x030032B0 + 256 * bank + 8, 8), bios_results[-1])
            attr1 = int.from_bytes(uc.mem_read(0x03000030 + 1024 * bank + 2, 2), 'little')
            self.assertEqual((attr1 >> 9) & 31, 1)
            self.call(uc, 0x080012BC)
            previous = [0x100, 0, 0, 0x200] if bank else [0, 0, 0, 0]
            self.assertEqual(
                [int.from_bytes(uc.mem_read(0x07000026 + 8 * i, 2), 'little') for i in range(4)], previous
            )
            self.call(uc, 0x08001CD0)
            self.call(uc, 0x080012BC)
            self.assertEqual(
                [int.from_bytes(uc.mem_read(0x07000006 + 32 + 8 * i, 2), 'little') for i in range(4)],
                [sx, 0, 0, sy],
            )
            self.assertEqual(
                [int.from_bytes(uc.mem_read(0x07000006 + 8 * i, 2), 'little') for i in range(4)], [1, 2, 3, 4]
            )

    def test_receipt_requires_complete_extent_and_lifetime(self):
        from match_evidence import report_matches
        from pathlib import Path

        p = self.root / 'docs/match/08000FC8.md'
        text = p.read_text()
        self.assertIn(affine.record(self.root), text)
        self.assertTrue(report_matches(text, self.root, affine.OWNER))
        for changed in (
            text.replace('exclusive writer bank', 'shared writer bank'),
            text.replace('* compiled : `', '* compiled : `00'),
            text.replace('08001948', '0800194A'),
        ):
            self.assertFalse(report_matches(changed, self.root, affine.OWNER))


if __name__ == '__main__':
    unittest.main()
