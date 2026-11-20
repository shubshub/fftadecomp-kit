import argparse
from copy import deepcopy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import scanline_pair as pair


@unittest.skipUnless(os.getenv('FFTA_SCANLINE_PAIR_ROOT'), 'requires the reviewed game source, USA ROM and native agbcc')
class NativePair(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path

        cls.root = Path(os.environ['FFTA_SCANLINE_PAIR_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.bodies = pair.compile_bodies(cls.root, cls.rom)

    def cpu(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(pair.BASE, 0x400000)
        cpu.mem_write(pair.BASE, self.rom[:0x400000])
        for start, size in ((0x02000000, 0x40000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
            cpu.mem_map(start, size)
        return cpu

    def call(self, cpu, address, *args):
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_SP
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3

        stop, sp = 0x03007000, 0x03007F00
        for reg, arg in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), args):
            cpu.reg_write(reg, arg)
        cpu.reg_write(UC_ARM_REG_SP, sp)
        cpu.reg_write(UC_ARM_REG_LR, stop | 1)
        cpu.emu_start(address | 1, stop, count=100000)
        self.assertEqual((cpu.reg_read(UC_ARM_REG_PC), cpu.reg_read(UC_ARM_REG_SP)), (stop, sp))

    def test_both_bodies_read_planes_and_store_one_pair_per_row(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ, UC_MEM_WRITE

        planes, out = 0x02001400, 0x02010000
        for qualified, body in zip((True, False), self.bodies):
            cpu = self.cpu()
            cpu.mem_write(pair.OWNER, body)
            accesses = []
            cpu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                         lambda uc, op, addr, width, val, data: accesses.append((op, addr, width)),
                         begin=0x02000000, end=0x0203FFFF)
            # Rotate all sixteen input bit positions through both planes. The
            # address trace also checks there are exactly two loads per row,
            # no bank accesses beyond 639, no plane writes, and no extra rows.
            for bit in range(16):
                values = [1 << ((bit + i + i//160) % 16) for i in range(320)]
                cpu.mem_write(planes, struct.pack('<320H', *values))
                cpu.mem_write(out-1, b'\xA5' * 642)
                accesses.clear()
                self.call(cpu, pair.OWNER, planes, out)
                expected = []
                for row in range(160):
                    for lane in range(2):
                        expected.append((UC_MEM_READ, planes + lane*320 + row*2, 2))
                        for address in (out+4*row+2*lane, out+4*row+2*lane+1):
                            if qualified:
                                expected.append((UC_MEM_READ, address, 1))
                            expected.append((UC_MEM_WRITE, address, 1))
                self.assertEqual(accesses, expected)
                rendered = b''.join(struct.pack('<HH', *item) for item in zip(values[:160], values[160:]))
                self.assertEqual(bytes(cpu.mem_read(out-1, 642)), b'\xA5' + rendered + b'\xA5')

    def test_scene_call_forwards_mode_one_and_selects_bg2(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_R4
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3

        cpu = self.cpu()
        parent, descriptor, state, obj = 0x02012000, 0x02013000, 0x02014000, 0x02020000
        cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        captures = []

        def spawn(uc, pc, size, data):
            self.assertEqual(uc.reg_read(UC_ARM_REG_R0), 0x080D8E01)
            self.assertEqual(uc.reg_read(UC_ARM_REG_R1), 0x16C)
            self.assertEqual(uc.reg_read(UC_ARM_REG_R3), parent)
            captures.append(bytes(uc.mem_read(uc.reg_read(UC_ARM_REG_R2), 28)))
            uc.reg_write(UC_ARM_REG_R0, state)
            uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))

        def allocate(uc, pc, size, data):
            self.assertEqual(uc.reg_read(UC_ARM_REG_R1), 32+640+2*644)
            uc.reg_write(UC_ARM_REG_R0, obj)
            uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))

        def fill(uc, irq, data):
            self.assertEqual(bytes(uc.mem_read(uc.reg_read(UC_ARM_REG_PC)-2, 2)), b'\x0B\xDF')
            src, dst, control = (uc.reg_read(reg) for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            self.assertEqual(control, 0x010000A0)
            uc.mem_write(dst, bytes(uc.mem_read(src, 2))*160)

        cpu.hook_add(UC_HOOK_CODE, spawn, begin=0x08005B6C, end=0x08005B6C)
        cpu.hook_add(UC_HOOK_CODE, allocate, begin=0x08007138, end=0x08007138)
        cpu.hook_add(UC_HOOK_INTR, fill)
        # Enter the scene's argument setup, continue through the original
        # spawner, and stop as it returns to the surrounding scene phase.
        cpu.reg_write(UC_ARM_REG_R4, parent)
        cpu.reg_write(UC_ARM_REG_SP, 0x03007F00)
        cpu.emu_start(0x080EA5B7, 0x080EA5C4, count=500)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), 0x080EA5C4)
        self.assertEqual(len(captures), 1)
        self.assertEqual(struct.unpack_from('<I', captures[0], 4), (0x08398A78,))
        self.assertEqual(struct.unpack_from('<3H', captures[0], 20), (1, 2, 0))
        cpu.mem_write(descriptor, captures[0])
        cpu.mem_write(descriptor, struct.pack('<H', 0))
        self.call(cpu, 0x080D8E00, parent, descriptor, state)
        self.assertEqual(bytes(cpu.mem_read(state+8, 4)), bytes((1, 2, 0, 2)))
        cpu.mem_write(0x03000952, struct.pack('<2H', 0xA123, 0xB456))
        cpu.mem_write(descriptor, struct.pack('<H', 0x100))
        self.call(cpu, 0x080D8E00, parent, descriptor, state)
        self.assertEqual(struct.unpack('<2I', cpu.mem_read(obj, 8)), (pair.OWNER | 1, 0x04000018))
        self.assertEqual(bytes(cpu.mem_read(obj+32, 640)),
                         struct.pack('<160H', *([0xA123]*160)) + struct.pack('<160H', *([0xB456]*160)))

    def test_original_constructor_and_two_bank_frames(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_LR, UC_ARM_REG_PC

        obj = 0x02020000
        # All four same-background horizontal/vertical pairs are valid direct
        # constructor parameters. The pinned scene supplies only BG2.
        for bg in range(4):
            dest = 0x04000010 + 4*bg
            cpu = self.cpu()
            cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
            cpu.mem_write(0x02009158, b'\xFF' * 8)
            cpu.mem_write(obj-4, b'\xA5' * (32+640+2*644+8))
            def allocate(uc, pc, size, data):
                self.assertEqual(uc.reg_read(UC_ARM_REG_R1), 32+640+2*644)
                uc.reg_write(UC_ARM_REG_R0, obj)
                uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))
            def cpuset(uc, irq, data):
                self.assertEqual(bytes(uc.mem_read(uc.reg_read(UC_ARM_REG_PC)-2, 2)), b'\x0B\xDF')
                src, dst, count = (uc.reg_read(reg) for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
                self.assertEqual(count, 2)
                uc.mem_write(dst, bytes(uc.mem_read(src, 4)))

            cpu.hook_add(UC_HOOK_CODE, allocate, begin=0x08007138, end=0x08007138)
            cpu.hook_add(UC_HOOK_INTR, cpuset)
            self.call(cpu, 0x0800CE08, 1, 0x4321, dest)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), obj)
            self.assertEqual(struct.unpack('<III', cpu.mem_read(obj, 12)), (pair.OWNER | 1, dest, 0x22600002))
            size, width, payload, bank0, bank1 = struct.unpack('<HHIII', cpu.mem_read(obj+16, 16))
            self.assertEqual((size, width, payload, bank0, bank1), (640, 4, obj+32, obj+672, obj+1316))
            self.assertEqual(bytes(cpu.mem_read(payload, 640)), struct.pack('<320H', *([0x4321]*320)))
            for frame, (back, front) in enumerate(((bank1, bank0), (bank0, bank1))):
                values = [(i*0x10B + frame*0x100D) & 0xFFFF for i in range(320)]
                cpu.mem_write(payload, struct.pack('<320H', *values))
                previous = bytes(cpu.mem_read(front, 644))
                self.call(cpu, 0x0800C64C, obj)
                self.call(cpu, 0x0800C4B4)
                self.assertEqual(int.from_bytes(cpu.mem_read(obj+14, 2), 'little'), 1-frame)
                rows = b''.join(struct.pack('<HH', *item) for item in zip(values[:160], values[160:]))
                self.assertEqual(bytes(cpu.mem_read(back, 644)), rows+rows[:4])
                self.assertEqual(bytes(cpu.mem_read(front, 644)), previous)
                self.assertEqual(bytes(cpu.mem_read(0x03000942+dest-0x04000008, 4)), rows[:4])
                self.call(cpu, 0x080008E0)
                self.assertEqual(struct.unpack('<III', cpu.mem_read(0x040000B0, 12)), (back+4, dest, 0xA2600002))
            self.assertEqual(bytes(cpu.mem_read(obj-4, 4)), b'\xA5'*4)
            self.assertEqual(bytes(cpu.mem_read(bank1+644, 4)), b'\xA5'*4)

    def test_source_header_provider_and_report_rejection(self):
        from match_evidence import report_matches

        text = (self.root / pair.SOURCE).read_text()
        header = (self.root / pair.HEADER).read_bytes()
        offsets = pair.source_offsets(text, header)
        self.assertEqual(offsets, {text.index('volatile'), text.rindex('volatile')})
        for old, new in (('first[160]', 'first[159]'), ('++', '--'), ('planes->first', 'planes->second'),
                         ('volatile u16 second', 'u16 second'), ('packed', 'aligned(4)'),
                         ('const ScanlinePlanes', 'volatile ScanlinePlanes')):
            self.assertIn(old, text)
            self.assertFalse(pair.source_offsets(text.replace(old, new), header))
        self.assertFalse(pair.source_offsets(text, header.replace(b'#endif', b'#define out bogus\n#endif')))
        self.assertFalse(pair.qualifier_offsets(text, self.root, self.root, ({pair.SOURCE, pair.HEADER, 'x.h'}, [])))
        pair.provider(self.rom)
        altered = bytearray(self.rom)
        for site in (0xEA5BA, 0xEA614, 0xD97D0, 0xD8EDE, 0x149AD4, 0xCE5A, 0x149810, 0x149808,
                     0x14981A, 0xC3CC, 0xC4FE, 0x8E0, 0xA38A2C, 0xDE8E, 0x2FFFFF):
            altered[site] ^= 1
            with self.assertRaises(ValueError):
                pair.provider(altered)
            altered[site] ^= 1
        report = (self.root / 'docs/match/0800DE70.md').read_text()
        self.assertTrue(report_matches(report, str(self.root), pair.OWNER))
        for old, new in (('BG2HOFS', 'WIN0H'), ('two 644-byte', 'two 640-byte'),
                         (self.bodies[0].hex(), self.bodies[0].hex()+'0000'), (pair.STRIPPED[1], '0'*64)):
            self.assertIn(old, report)
            self.assertFalse(report_matches(report.replace(old, new), str(self.root), pair.OWNER))
        record = next(line for line in report.splitlines() if line.startswith('* allowlisted volatile scanline pair:'))
        self.assertFalse(report_matches(report.replace(record, ''), str(self.root), pair.OWNER))
        self.assertFalse(report_matches(report.replace(record, record+'\n'+record), str(self.root), pair.OWNER))

    def test_elf_relocation_extent_binding_and_lane_mutations(self):
        import match

        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(self.root))
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, args, str(self.root), pair.OWNER, pair.SOURCE)
        for mode in ('relocation', 'extent', 'binding', 'wrong-lane', 'missing-read', 'overrun'):
            wrong = deepcopy(image)
            if mode == 'relocation':
                wrong['relocations'] = [1]
            elif mode in ('extent', 'binding'):
                symbol, _ = match.function_record(wrong, 'func_0800DE70', pair.OWNER, True)
                symbol['size' if mode == 'extent' else 'bind'] = 0
            else:
                site = {'wrong-lane': 0x20, 'missing-read': 0x1E, 'overrun': 0x44}[mode]
                code = bytearray(wrong['text'])
                code[site] ^= 0x40
                wrong['text'] = bytes(code)
            with self.assertRaises(ValueError):
                pair.check_object(wrong, pair.QUALIFIED)


if __name__ == '__main__':
    unittest.main()
