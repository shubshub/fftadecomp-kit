import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import bg_affine_rows as affine


def signed(value, bits):
    return (value + (1 << (bits - 1))) % (1 << bits) - (1 << (bits - 1))


def transform(source):
    # Exact cardinal angles are enough to exercise all four distinct coefficient fields.
    tx, ty, px, py, sx, sy, angle = struct.unpack_from('<iihhhhH', source)
    sine, cosine = {0: (0, 1), 0x4000: (1, 0), 0x8000: (0, -1), 0xC000: (-1, 0)}[angle]
    pa, pb, pc, pd = (sx * cosine, -sx * sine, sy * sine, sy * cosine)
    return (pa, pb, pc, pd, signed(tx - pa * px - pb * py, 32), signed(ty - pc * px - pd * py, 32))


@unittest.skipUnless(os.getenv('FFTA_BG_AFFINE_ROWS_ROOT'), 'requires USA ROM, agbcc and the reviewed producer')
class NativeAffineRows(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path

        cls.root = Path(os.environ['FFTA_BG_AFFINE_ROWS_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.bodies = affine.compile_bodies(cls.root, cls.rom)

    def cpu(self, kind='qualified'):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(affine.BASE, 0x400000)
        uc.mem_write(affine.BASE, self.rom[:0x400000])
        uc.mem_write(affine.OWNER, self.bodies[kind])
        for base, size in ((0x02000000, 0x20000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
            uc.mem_map(base, size)
        uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        return uc

    def call(self, uc, entry, *args, return_at=None):
        from unicorn.arm_const import (
            UC_ARM_REG_R0,
            UC_ARM_REG_R1,
            UC_ARM_REG_R2,
            UC_ARM_REG_R3,
            UC_ARM_REG_SP,
            UC_ARM_REG_PC,
            UC_ARM_REG_LR,
        )

        stack = 0x03007F00
        for reg, value in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), args):
            uc.reg_write(reg, value & 0xFFFFFFFF)
        for i, arg in enumerate(args[4:]):
            uc.mem_write(stack + i * 4, struct.pack('<I', arg & 0xFFFFFFFF))
        uc.reg_write(UC_ARM_REG_SP, stack)
        stop = return_at or 0x03007000
        uc.reg_write(UC_ARM_REG_LR, stop | 1)
        uc.emu_start(entry | 1, stop, count=2500000)
        self.assertEqual(uc.reg_read(UC_ARM_REG_PC), stop)
        self.assertEqual(uc.reg_read(UC_ARM_REG_SP), stack)
        return uc.reg_read(UC_ARM_REG_R0)

    def services(self, uc, state, seen, *, owner_frame=None):
        from unicorn import UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        def bios(u, _, __):
            ins = bytes(u.mem_read(u.reg_read(UC_ARM_REG_PC) - 2, 2))
            src, dst, count = (u.reg_read(reg) for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            if ins == b'\x0b\xdf':
                self.assertEqual(count, 8)
                u.mem_write(dst, bytes(u.mem_read(src, 16)))
                return
            if ins == b'\x08\xdf':
                from math import isqrt

                u.reg_write(UC_ARM_REG_R0, isqrt(src))
                return
            if ins == b'\x06\xdf':
                from unicorn.arm_const import UC_ARM_REG_R3

                a, b = signed(src, 32), signed(dst, 32)
                self.assertNotEqual(b, 0)
                q = abs(a) // abs(b)
                if (a < 0) != (b < 0):
                    q = -q
                for reg, value in ((UC_ARM_REG_R0, q), (UC_ARM_REG_R1, a - q * b), (UC_ARM_REG_R3, abs(q))):
                    u.reg_write(reg, value & 0xFFFFFFFF)
                return
            self.assertEqual(ins, b'\x0e\xdf')
            self.assertEqual(count, 1)
            sp = u.reg_read(UC_ARM_REG_SP)
            if owner_frame is not None:
                self.assertEqual(sp, owner_frame)
            if src == state + 12:
                self.assertEqual(dst, sp + 36)
            else:
                self.assertEqual((src, dst), (sp, sp + 20))
            self.assertEqual((src | dst) % 4, 0)
            source = bytes(u.mem_read(src, 20))
            seen.append((src == state + 12, source))
            u.mem_write(dst, struct.pack('<hhhhii', *transform(source)))

        uc.hook_add(UC_HOOK_INTR, bios)

    def test_clockwise_matrix_halfwords_and_complete_rows(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ

        state, bank = 0x02001000, 0x02005000
        for kind in ('qualified', 'ordinary'):
            for mode, center, r1, r23 in (
                (0, 79, 7, 13),
                (1, 4, 8, 1),
                (2, 157, 1, 5),
                (3, 77, 2, 7),
                (7, -2, 3, 4),
                (1, 32767, 32767, 0),
                (2, 0, 0, 0),
            ):
                with self.subTest(kind=kind, mode=mode, center=center):
                    payload = bytearray(0x2B8)
                    ox, oy, screen_x = 7, -9, -13
                    tx, ty = (ox + screen_x) * 256, (oy + center) * 256
                    struct.pack_into('<Hhhhh', payload, 0, mode, screen_x, center, ox, oy)
                    struct.pack_into('<iihhhhH', payload, 12, 0, 0, 12, -1, -271, 326, 0x4000)
                    struct.pack_into('<h', payload, 0x28, -7)
                    struct.pack_into('<hH', payload, 0x2E, -83, 0xC000)
                    struct.pack_into('<HH', payload, 0x34, r1, r23)
                    for i in range(160):
                        struct.pack_into('<h', payload, 0x38 + 2 * i, i - 88)
                        struct.pack_into('<h', payload, 0x178 + 2 * i, 113 - i)
                    uc = self.cpu(kind)
                    uc.mem_write(state, bytes(payload))
                    uc.mem_write(bank - 16, b'\xa5' * (162 * 16))
                    events = []
                    seen = []
                    self.services(uc, state, seen, owner_frame=0x03007F00 - 92)
                    uc.hook_add(
                        UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                        lambda _, access, a, w, v, d: events.append((a - bank, w, access == UC_MEM_READ)),
                        begin=bank - 16,
                        end=bank + 161 * 16 - 1,
                    )
                    self.call(uc, affine.OWNER, state, bank)
                    radius = r1 if mode == 1 else r23 if mode in (2, 3) else 0
                    first = max(0, signed(center - radius, 16)) if mode else 0
                    last = signed(center + radius, 16) if mode else 159
                    expected = bytearray()
                    for i in range(160):
                        inside = first <= i <= last
                        args = (
                            (tx, ty, -7, center, 113 - i, -83, 0xC000)
                            if inside
                            else (tx, ty, 12, center, -271, 326, 0x4000)
                        )
                        pa, pb, pc, pd, dx, dy = transform(struct.pack('<iihhhhH', *args))
                        dy += (oy + i + (i - 88 if inside else 0)) * 256
                        expected.extend(struct.pack('<hhhhii', pa, pb, pc, pd, dx, signed(dy, 32)))
                    self.assertEqual(
                        bytes(uc.mem_read(bank - 16, 162 * 16)), b'\xa5' * 16 + expected + b'\xa5' * 16
                    )
                    self.assertEqual(
                        [external for external, _ in seen],
                        [True] + [False] * sum(first <= i <= last for i in range(160)),
                    )
                    self.assertEqual(
                        events,
                        [
                            (byte, 1, read)
                            for byte in range(2560)
                            for read in ((True, False) if kind == 'qualified' else (False,))
                        ],
                    )

    def test_original_constructors_frame_dma_and_release(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1

        obj, slot, dma = 0x02011000, 0x02009148, 0x040000B0
        payload = obj + 32
        banks = (payload + 0x2B8, payload + 0x2B8 + 161 * 16)
        for mode, (constructor, _, _) in enumerate(affine.CONSTRUCTORS):
            for bg in (2, 3):
                with self.subTest(mode=mode, bg=bg):
                    uc = self.cpu()
                    uc.mem_write(slot + 16, b'\xff' * 8)
                    uc.mem_write(banks[1] + 161 * 16, b'\xa5' * 16)
                    allocations, frees, seen = [], [], []

                    def allocate(u, a, w, d):
                        size = u.reg_read(UC_ARM_REG_R1)
                        allocations.append(size)
                        u.mem_write(obj, b'\xa5' * size)
                        u.reg_write(UC_ARM_REG_R0, obj)
                        u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))

                    def release(u, a, w, d):
                        frees.append(u.reg_read(UC_ARM_REG_R1))
                        u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))

                    for site, service in ((0x08007138, allocate), (0x08007170, release)):
                        uc.hook_add(UC_HOOK_CODE, service, begin=site, end=site)
                    immediate = []

                    def complete_dma(u, access, addr, width, value, data):
                        src, dst, control = struct.unpack('<3I', u.mem_read(dma, 12))
                        if control != 0x80000027:
                            return
                        self.assertEqual((src, dst), (0x03000942, 0x04000008))
                        u.mem_write(dst, bytes(u.mem_read(src, 2 * (control & 0xFFFF))))
                        u.mem_write(dma + 8, b'\0' * 4)
                        immediate.append(control)

                    uc.hook_add(UC_HOOK_MEM_READ, complete_dma, begin=dma + 8, end=dma + 11)
                    self.services(uc, payload, seen)
                    self.assertEqual(self.call(uc, constructor, bg, 20, 70, 6, 7, 9, 12), obj)
                    self.assertEqual(allocations, [32 + 0x2B8 + 2 * 161 * 16])
                    word = lambda a: int.from_bytes(uc.mem_read(a, 4), 'little')
                    destination = 0x04000020 + 16 * (bg - 2)
                    self.assertEqual(
                        (word(slot), word(obj), word(obj + 4), word(obj + 8)),
                        (obj, affine.OWNER | 1, destination, 0x22600008),
                    )
                    self.assertEqual(struct.unpack('<3I', uc.mem_read(obj + 20, 12)), (payload, *banks))
                    self.assertEqual(int.from_bytes(uc.mem_read(payload, 2), 'little'), mode)
                    for frame, bank in enumerate(reversed(banks)):
                        # Make the next bank distinguishable even when the mode's update is stationary.
                        uc.mem_write(payload + 8, struct.pack('<h', 9 + frame))
                        old = bytes(uc.mem_read(banks[frame], 161 * 16))
                        self.call(uc, 0x0800C64C, obj)
                        self.call(uc, 0x0800A646, return_at=0x0800A64A)
                        self.assertEqual(bytes(uc.mem_read(banks[frame], 161 * 16)), old)
                        self.assertEqual(bytes(uc.mem_read(bank, 16)), bytes(uc.mem_read(bank + 160 * 16, 16)))
                        self.assertEqual(
                            bytes(uc.mem_read(0x03000942 + destination - 0x04000008, 16)),
                            bytes(uc.mem_read(bank, 16)),
                        )
                        self.call(uc, 0x080004BC, return_at=0x080004C0)
                        self.call(uc, 0x080004D0, return_at=0x080004D4)
                        self.assertEqual(len(immediate), frame + 1)
                        self.assertEqual(bytes(uc.mem_read(destination, 16)), bytes(uc.mem_read(bank, 16)))
                        self.call(uc, 0x080004DC, return_at=0x080004E0)
                        src, dst, control = struct.unpack('<3I', uc.mem_read(dma, 12))
                        self.assertEqual((src, dst, control), (bank + 16, destination, 0xA2600008))
                        # HBlank, 16-bit units, eight transfers, increment source, reload destination.
                        for hblank in range(160):
                            for j in range(control & 0xFFFF):
                                uc.mem_write(dst + 2 * j, bytes(uc.mem_read(src, 2)))
                                src += 2
                            self.assertEqual(
                                bytes(uc.mem_read(dst, 16)), bytes(uc.mem_read(bank + 16 * (hblank + 1), 16))
                            )
                        self.assertEqual(src, bank + 161 * 16)
                    # The allocator frees immediately; the VBlank stop/program sequence must occur
                    # before the retired bank is reused while HBlank DMA might still be active.
                    self.call(uc, 0x0800C668, obj)
                    self.assertEqual((frees, word(slot)), ([obj], 0))
                    self.call(uc, 0x080004BC, return_at=0x080004C0)
                    self.call(uc, 0x080004DC, return_at=0x080004E0)
                    self.assertEqual(word(dma + 8), 0)
                    self.assertEqual(uc.mem_read(banks[1] + 161 * 16, 16), b'\xa5' * 16)
                    self.assertGreaterEqual(sum(base for base, _ in seen), 2)

    def test_exhausted_slots_and_channels(self):
        from unicorn import UcError, UC_ERR_READ_UNMAPPED
        from unicorn.arm_const import UC_ARM_REG_PC

        uc = self.cpu()
        uc.mem_write(0x02009148, struct.pack('<4I', *(0x02011000 + i * 32 for i in range(4))))
        self.assertEqual(self.call(uc, 0x0800C3CC, affine.OWNER | 1, 0x2B8, 16, 0x04000020), 0)
        # The first constructor immediately sends this null result to C614.
        with self.assertRaises(UcError) as caught:
            self.call(uc, 0x0800CF08, 2, 20, 70, 9, 12)
        self.assertEqual(caught.exception.errno, UC_ERR_READ_UNMAPPED)
        self.assertEqual(uc.reg_read(UC_ARM_REG_PC), 0x0800C618)
        uc = self.cpu()
        uc.mem_write(0x03002BC0, struct.pack('<4H', 1, 1, 1, 1))
        self.assertEqual(self.call(uc, 0x080009AC, 0x02011010, 0x04000030, 0x22600008), 0xFFFFFFFF)
        self.call(uc, 0x080004DC, return_at=0x080004E0)
        self.assertEqual(uc.mem_read(0x040000B0, 48), bytes(48))

    def test_qualified_view_native_controls_provider_and_saved_report(self):
        from match_evidence import report_matches
        import plausible

        path = self.root / affine.SOURCE
        source = path.read_text()
        self.assertEqual(
            len(affine.qualifier_offsets(source, self.root, self.root, plausible.include_closure(self.root, path))),
            1,
        )
        self.assertFalse(plausible.check_file(path))
        header = (self.root / affine.HEADER).read_bytes()
        for replacement in (
            ('volatile AffineLine', 'AffineLine'),
            ('s16 pa;', 's16 px;'),
            ('i < 160', 'i <= 160'),
            ('* 256', '* 128'),
            ('line_scale_x[i]', 'line_scale_x[0]'),
        ):
            self.assertFalse(affine.source_offset(source.replace(*replacement), header))
        for kind, body in self.bodies.items():
            changed = self.bodies.copy()
            altered = bytearray(body)
            altered[affine.SHAPES[kind][2][0]] ^= 1
            changed[kind] = altered
            with self.assertRaises(ValueError):
                affine.check_bodies(changed)
        rom = bytearray(self.rom)
        for at in (
            0xCFC0,
            0xD08C,
            0xD164,
            0xD238,
            0xCF4A,
            0xD018,
            0xD0EC,
            0xD1C4,
            0x149820,
            0x149824,
            0xA646,
            0xC43C,
            0xC4FE,
            0xC50E,
            0xC520,
            0xC52E,
            0xC580,
            0x718,
            0xD08,
            0xD90,
            0x3A08,
            0x36D480,
            0xC5BA,
            0xC5C4,
            0x9CA,
            0x936,
            0xC68E,
            0x4BC,
            0x4DC,
            0x149434,
            0x141864,
            0x36D4B8,
        ):
            with self.subTest(offset=hex(at)), self.assertRaises(ValueError):
                rom[at] ^= 1
                try:
                    affine.provider(rom)
                finally:
                    rom[at] ^= 1
        text = (self.root / 'docs/match/0800D3BC.md').read_text()
        self.assertTrue(report_matches(text, self.root, affine.OWNER))
        for original, replacement in (
            ('606/606 bytes', '604/606 bytes'),
            ('bank +16', 'bank +2'),
            ('no teardown', 'teardown'),
            ('BgAffineSet', 'CpuSet'),
        ):
            self.assertIn(original, text)
            self.assertFalse(report_matches(text.replace(original, replacement), self.root, affine.OWNER))
