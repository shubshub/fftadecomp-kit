import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import blend_ramp as ramp


@unittest.skipUnless(os.getenv('FFTA_BLEND_RAMP_ROOT'), 'requires USA ROM, agbcc and the reviewed BLDALPHA writer')
class NativeBlendRamp(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path

        cls.root = Path(os.environ['FFTA_BLEND_RAMP_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.bodies = ramp.compile_bodies(cls.root, cls.rom)

    def cpu(self, kind='qualified'):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(ramp.BASE, 0x400000)
        uc.mem_write(ramp.BASE, self.rom[:0x400000])
        uc.mem_write(ramp.OWNER, self.bodies[kind])
        for address, size in ((0x02000000, 0x20000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
            uc.mem_map(address, size)
        uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        return uc

    def call(self, *args, **kwargs):
        from test_bg_affine_rows import NativeAffineRows

        return NativeAffineRows.call(self, *args, **kwargs)

    def test_guarded_ramps_and_all_payload_accesses(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ

        obj, payload = 0x02011000, 0x02012000
        # Explicit step sequences also test the half-step tie rule in 076A0.
        for first, count, av, bv, eva, evb in (
            (-32768, 255, (255, 0), (0, 255), [], []),
            (-2, 5, (1, 9), (14, 2), [5, 7, 9], [8, 5, 2]),
            (12, 5, (9, 1), (2, 14), [9, 7, 5, 3, 1], [2, 5, 8, 11, 14]),
            (0, 3, (0, 1), (255, 254), [0, 1, 1], [255, 254, 254]),
            (158, 5, (2, 6), (6, 2), [2, 3], [6, 5]),
            (159, 0, (33, 4), (65, 8), [33], [65]),
            (4, 1, (254, 5), (111, 6), [254], [111]),
            (160, 255, (6, 8), (9, 7), [], []),
        ):
            for kind in self.bodies:
                with self.subTest(first=first, count=count, kind=kind):
                    uc = self.cpu(kind)
                    uc.mem_write(obj + 16, struct.pack('<II', 320, payload))
                    uc.mem_write(payload - 2, b'\xa5' * 324)
                    events = []
                    uc.hook_add(
                        UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                        lambda u, op, a, w, v, d: events.append((a - payload, w, op == UC_MEM_READ)),
                        begin=payload - 2,
                        end=payload + 321,
                    )
                    self.call(uc, ramp.OWNER, obj, first, count, av[0], bv[0], av[1], bv[1])
                    want, accesses = bytearray(b'\xa5' * 324), []
                    for row, (a, b) in enumerate(zip(eva, evb), max(0, first)):
                        for lane, value in enumerate((a, b)):
                            pos = 2 * row + (1 - lane if kind == 'reversed' else lane)
                            want[2 + pos] = value
                            if kind != 'ordinary':
                                accesses.append((pos, 1, True))
                            accesses.append((pos, 1, False))
                    self.assertEqual(events, accesses)
                    self.assertEqual(uc.mem_read(payload - 2, 324), want)
                    self.assertEqual(bool(uc.mem_read(obj + 12, 1)[0] & 1), first < 160)

    def test_command_constructor_frame_dma_and_release(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        uc = self.cpu()
        obj, slot, dma, destination = 0x02011000, 0x02009148, 0x040000B0, 0x04000052
        command, entries, state = 0x02000800, 0x02000900, 0x02000A00
        payload = obj + 32
        banks = (payload + 320, payload + 320 + 324)
        size = 32 + 320 + 2 * 324
        word = lambda addr: int.from_bytes(uc.mem_read(addr, 4), 'little')
        uc.mem_write(slot + 16, b'\xff' * 8)
        uc.mem_write(obj + size, b'\xa5' * 8)
        uc.mem_write(command + 4, struct.pack('<I', entries))
        uc.mem_write(command + 0x14, bytes((0x17, 0, 0x31, 0, 2)))
        uc.mem_write(entries, bytes((0, 3, 2, 9, 6, 1, 0x44, 0x66, 159, 3, 13, 2, 10, 11, 0x88, 0x99)))
        allocations, frees, copies, vblanks = [], [], [], []

        def allocate(u, a, w, d):
            allocations.append(u.reg_read(UC_ARM_REG_R1))
            self.assertEqual(allocations, [size])
            u.mem_write(obj, b'\xa5' * size)
            u.reg_write(UC_ARM_REG_R0, obj)
            u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))

        def release(u, a, w, d):
            frees.append(u.reg_read(UC_ARM_REG_R1))
            u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))

        def cpuset(u, irq, d):
            src, dst, control = (u.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            self.assertEqual(u.mem_read(u.reg_read(UC_ARM_REG_PC) - 2, 2), b'\x0b\xdf')
            self.assertIn(control, (1, 160))
            u.mem_write(dst, bytes(u.mem_read(src, control * 2)))
            copies.append((src, dst, control))

        def finish_immediate(u, op, at, width, v, d):
            src, dst, control = struct.unpack('<III', u.mem_read(dma, 12))
            if control == 0x80000027:
                self.assertEqual((src, dst), (0x03000942, 0x04000008))
                u.mem_write(dst, bytes(u.mem_read(src, 78)))
                u.mem_write(dma + 8, bytes(4))
                vblanks.append(control)

        for address, hook in ((0x08007138, allocate), (0x08007170, release)):
            uc.hook_add(UC_HOOK_CODE, hook, begin=address, end=address)
        uc.hook_add(UC_HOOK_INTR, cpuset)
        uc.hook_add(UC_HOOK_MEM_READ, finish_immediate, begin=dma + 8, end=dma + 11)
        self.assertEqual(self.call(uc, 0x080D96F0, 0, command, state), 0)
        self.assertEqual(
            (word(slot), word(state + 4), word(obj), word(obj + 4), word(obj + 8)),
            (obj, obj, 0x0800DEC1, destination, 0x22600001),
        )
        self.assertEqual(struct.unpack('<3I', uc.mem_read(obj + 20, 12)), (payload, *banks))
        first = bytes((2, 9, 4, 5, 6, 1)) + bytes((0x17, 0x31)) * 156 + bytes((13, 2))
        self.assertEqual(uc.mem_read(payload, 320), first)
        for frame, bank in enumerate(reversed(banks)):
            if frame:
                self.call(uc, ramp.OWNER, obj, 0, 1, 16, 0, 1, 2)
            rows = bytes(uc.mem_read(payload, 320))
            other = bytes(uc.mem_read(banks[frame], 324))
            self.call(uc, 0x0800A646, return_at=0x0800A64A)
            self.assertEqual(uc.mem_read(banks[frame], 324), other)
            self.assertIn((payload, bank, 160), copies)
            self.assertEqual(uc.mem_read(bank, 322), rows + rows[:2])
            self.assertEqual(uc.mem_read(0x0300098C, 2), rows[:2])
            self.call(uc, 0x080004BC, return_at=0x080004C0)
            self.call(uc, 0x080004D0, return_at=0x080004D4)
            self.assertEqual(len(vblanks), frame + 1)
            self.assertEqual(uc.mem_read(destination, 2), rows[:2])
            self.call(uc, 0x080004DC, return_at=0x080004E0)
            src, dst, control = struct.unpack('<3I', uc.mem_read(dma, 12))
            self.assertEqual((src, dst, control), (bank + 2, destination, 0xA2600001))
            for hblank in range(160):
                uc.mem_write(dst, bytes(uc.mem_read(src, 2)))
                src += 2
                i = (hblank + 1) % 160
                self.assertEqual(uc.mem_read(destination, 2), rows[2 * i : 2 * i + 2])
            self.assertEqual(src, bank + 322)
        uc.mem_write(command, b'\x01\x00')
        self.call(uc, 0x080D96F0, 0, command, state)
        self.assertEqual((frees, word(slot)), ([obj], 0))
        self.call(uc, 0x080004BC, return_at=0x080004C0)
        self.call(uc, 0x080004DC, return_at=0x080004E0)
        self.assertEqual(word(dma + 8), 0)
        self.assertEqual(uc.mem_read(obj + size, 8), b'\xa5' * 8)

    def test_ordinary_writers_and_inactive_getter(self):
        from unicorn import UC_HOOK_INTR, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        uc = self.cpu()
        obj, payload, source = 0x02011000, 0x02012000, 0x02000800
        self.assertEqual(self.call(uc, 0x0800C614, obj), 0)
        uc.mem_write(obj + 16, struct.pack('<II', 0x2B8, payload))
        uc.mem_write(source, bytes.fromhex('34127856'))
        accesses = []
        uc.hook_add(
            UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
            lambda u, op, a, w, v, d: accesses.append((op, a - payload, w)),
            begin=payload,
            end=payload + 0x2B7,
        )
        # The same getter also delivers a parameter block. DBE8 updates ordinary
        # signed halfwords at +0x178; it does not treat that block as BLDALPHA rows.
        self.call(uc, 0x0800DBE8, obj, 2, 2, source)
        self.assertEqual(accesses, [(UC_MEM_WRITE, 0x17C, 2), (UC_MEM_WRITE, 0x17E, 2)])
        self.assertEqual(uc.mem_read(payload + 0x17C, 4), bytes.fromhex('34127856'))
        # DAB8 uses an independent whole-row packed halfword fill.
        fills = []

        def cpuset(u, irq, data):
            src, dst, control = (u.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            self.assertEqual((dst, control), (payload + 6, 0x01000002))
            fills.append(bytes(u.mem_read(src, 2)))
            u.mem_write(dst, fills[-1] * 2)

        uc.hook_add(UC_HOOK_INTR, cpuset)
        uc.mem_write(obj + 16, struct.pack('<II', 320, payload))
        self.call(uc, 0x0800DAB8, obj, 3, 2, 4, 12)
        self.assertEqual(fills, [bytes((4, 12))])
        self.assertEqual(uc.mem_read(payload + 6, 4), bytes((4, 12, 4, 12)))

    def test_source_rom_and_receipt_controls(self):
        import plausible
        from match_evidence import report_matches

        path = self.root / ramp.SOURCE
        source = path.read_text()
        self.assertFalse(plausible.check_file(path))
        closure = plausible.include_closure(self.root, path)
        for old, new in (
            ('row >= 0', 'row > 0'),
            ('row < 160', 'row <= 160'),
            ('lines[160]', 'lines[161]'),
            ('volatile BlendTable', 'BlendTable'),
            ('evb = b.x', 'evb = a.x'),
        ):
            self.assertIn(old, source)
            self.assertFalse(ramp.qualifier_offsets(source.replace(old, new), self.root, self.root, closure))
        rom = bytearray(self.rom)
        for at in (
            0xD9722,
            0xD9740,
            0xD9758,
            0xD976C,
            0xD630,
            0xD640,
            0xD65C,
            0xD660,
            0x75F0,
            0x76B0,
            0xDEC4,
            0xC43C,
            0xC4FE,
            0xC520,
            0xC52E,
            0xA646,
            0xC5C4,
            0x718,
            0x9CA,
            0x936,
            0xC68E,
            0x4BC,
            0x4D0,
            0x4DC,
            0x14186C,
            0x149434,
            0x36D480,
        ):
            with self.subTest(changed=hex(at)), self.assertRaises(ValueError):
                rom[at] ^= 1
                try:
                    ramp.provider(rom)
                finally:
                    rom[at] ^= 1
        report = (self.root / 'docs/match/0800DB0C.md').read_text()
        self.assertTrue(report_matches(report, self.root, ramp.OWNER))
        for old, new in (
            ('218/218 bytes', '216/218 bytes'),
            ('320-byte payload', '322-byte payload'),
            ('BLDALPHA 04000052', 'BLDALPHA 04000050'),
            ('A2600001', 'A2600002'),
        ):
            self.assertIn(old, report)
            self.assertFalse(report_matches(report.replace(old, new), self.root, ramp.OWNER))
