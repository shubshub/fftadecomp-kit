import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import window_scanline as window


class WindowFieldTests(unittest.TestCase):
    def test_rewrite_is_confined_to_one_packed_pair(self):
        declaration = 'typedef struct __attribute__((packed)) { volatile u8 right : 8; volatile u8 left : 8; } WindowLine;'
        source = declaration + '\nvolatile u16 other;'
        self.assertEqual(window.rewrite_element(source), declaration.replace('volatile ', '') + '\nvolatile u16 other;')
        swapped = window.rewrite_element(source, swap=True)
        self.assertIn('volatile u8 left : 8; volatile u8 right : 8;', swapped)
        for changed in (source + source, source.replace('u8 left', 'u16 left'),
                        source.replace('packed', 'aligned(8)'), source.replace('right : 8', 'right : 7')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                window.rewrite_element(changed)

    def test_general_provider_does_not_admit_other_writers(self):
        for address in (0x0800CF08, 0x0800D23C, 0x080D9C58, 0x080D9F60):
            with self.subTest(address=address), self.assertRaises(ValueError):
                window.provider_evidence(b'', address)


@unittest.skipUnless(os.getenv('FFTA_WINDOW_SCANLINE_ROOT'), 'requires the USA ROM, both reviewed sources and native agbcc')
class NativeWindowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_WINDOW_SCANLINE_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.bodies = {a: window.compile_bodies(cls.root, a, cls.rom) for a in window.OWNER_SHAPES}

    def test_qualified_stripped_and_swapped_compiler_effects(self):
        for address, bodies in self.bodies.items():
            actual, control, swapped = bodies
            start = address - window.BASE
            self.assertEqual(actual, self.rom[start:start + len(actual)])
            window.check_bodies(address, actual, control, swapped)
            for index, src in enumerate(bodies):
                for site in (4, len(src)//2, len(src)-4):
                    changed = bytearray(src)
                    changed[site] ^= 1
                    variant = list(bodies)
                    variant[index] = changed
                    with self.subTest(address=hex(address), compile=index, site=site), self.assertRaises(ValueError):
                        window.check_bodies(address, *variant)
            # Keep every other perturbed instruction correct but make just one
            # read access the original field through an alias.
            site = 0x84 if address == window.RECT else 0xEA
            wrong = bytearray(swapped)
            wrong[site:site+2] = actual[site:site+2]
            with self.assertRaises(ValueError):
                window.check_bodies(address, actual, control, wrong)

    def test_source_qualified_members_and_valid_provider(self):
        import plausible
        header = (self.root / window.HEADER).read_bytes()
        for address in self.bodies:
            name = f'src/{address:08X}.c'
            source = (self.root / name).read_text()
            closure = ({window.HEADER, name}, [])
            self.assertEqual(len(window.qualifier_offsets(source, self.root, self.root, address, closure)), 2)
            self.assertFalse(plausible.check_file(self.root / name))
            self.assertFalse(window.qualifier_offsets(source, self.root, self.root, address, (set(), [])))
            self.assertFalse(window.source_offsets(source, header.replace(b'#endif', b'#define left right\n#endif'), address))
            mutations = [('right : 8', 'right : 7'), ('volatile u8 left', 'volatile u16 left'),
                         ('u8 right : 8;', 'u8 right : 8; u8 extra[6];')]
            if address == window.RECT:
                mutations += [('state->object', '(void *)task'), ('        lines[row].left =',
                              '        (void)lines[row].right;\n        lines[row].left =')]
            else:
                mutations += [('right >', 'right >='), ('row < 160', 'row < 161'),
                              ('right--;', 'right = 0;'), ('radius >> 1, buffer', 'radius >> 1, (u8 *)buffer + 2')]
            for before, after in mutations:
                with self.subTest(address=hex(address), change=after):
                    self.assertIn(before, source)
                    self.assertFalse(window.source_offsets(source.replace(before, after), header, address))
            for wrong in (0x0800CF08, 0x0800D23C):
                self.assertFalse(window.source_offsets(source, header, wrong))
        # Actual #168 nonvolatile parameter-record uses of the same accessor.
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        for a, mnemonic in ((0x0800CF58, 'strh'), (0x0800D2DA, 'strb')):
            i = next(decoder.disasm(self.rom[a-window.BASE:a-window.BASE+2], a))
            self.assertEqual(i.mnemonic, mnemonic)

    def test_constructor_bank_rotation_dma_programming_and_release(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_R0,
                                      UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        word = lambda value: struct.pack('<I', value)
        for bank in (0, 1):
            with self.subTest(bank=bank):
                uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
                uc.mem_map(window.BASE, 0x400000)
                uc.mem_write(window.BASE, self.rom[:0x400000])
                uc.mem_map(0x02000000, 0x20000)
                uc.mem_map(0x03000000, 0x8000)
                uc.mem_map(0x04000000, 0x1000)
                # Supply the reviewed boot image and success-returning ordinary
                # allocation. The event, initializer and manager run original instructions.
                uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
                task, obj, descriptor, manager = 0x02010000, 0x02011000, 0x02012000, 0x02013000
                registers = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
                slot, dma, stop = 0x02009148, 0x040000B0, 0x03007000
                uc.mem_write(0x02008FF0, word(manager))
                uc.mem_write(slot+16, b'\xff'*8)
                allocations, frees = [], []
                def allocate(u, _, __, ___):
                    allocated = (task, obj)[len(allocations)]
                    size = u.reg_read(UC_ARM_REG_R1)
                    allocations.append(size)
                    u.mem_write(allocated, b'\xa5'*size)
                    u.reg_write(UC_ARM_REG_R0, allocated)
                    u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))
                def free(u, _, __, ___):
                    frees.append(u.reg_read(UC_ARM_REG_R1))
                    u.reg_write(UC_ARM_REG_PC, u.reg_read(UC_ARM_REG_LR))
                def cpuset(u, _, __):
                    pc = u.reg_read(UC_ARM_REG_PC)
                    self.assertEqual(u.mem_read(pc-2, 2), b'\x0b\xdf')
                    source, destination, count = (u.reg_read(k) for k in registers[:3])
                    self.assertIn(count, (1,160))
                    u.mem_write(destination, bytes(u.mem_read(source, 2*count)))
                for site, callback in ((0x08007138, allocate), (0x08007170, free)):
                    uc.hook_add(UC_HOOK_CODE, callback, begin=site, end=site)
                uc.hook_add(UC_HOOK_INTR, cpuset)
                def call(address, *args):
                    for register, value in zip(registers, args):
                        uc.reg_write(register, value)
                    uc.reg_write(UC_ARM_REG_SP, 0x03007F00)
                    uc.reg_write(UC_ARM_REG_LR, stop|1)
                    uc.emu_start(address|1, stop, count=200000)
                    self.assertEqual(uc.reg_read(UC_ARM_REG_PC), stop)
                    return uc.reg_read(UC_ARM_REG_R0)
                readword = lambda addr: int.from_bytes(uc.mem_read(addr, 4), 'little')
                self.assertEqual(call(0x080DAB84, bank, 73, 145, 0), task)
                self.assertEqual(allocations, [36, 1000])
                self.assertEqual(readword(task+0x1C), obj)
                self.assertEqual(readword(slot), obj)
                dest = 0x04000040 + 2*bank
                self.assertEqual(readword(obj+4), dest)
                payload = call(0x0800C614, obj)
                self.assertEqual(payload, obj+32)
                self.assertEqual(uc.mem_read(payload, 320), bytes((145,73))*160)
                buffers = (readword(obj+24), readword(obj+28))
                self.assertEqual(buffers, (payload+320, payload+644))
                for frame, expectedbank in enumerate(reversed(buffers)):
                    data = bytes((i+frame*17)%256 for i in range(320))
                    uc.mem_write(payload, data)
                    call(0x0800C64C, obj)
                    call(0x0800C4B4)
                    self.assertEqual(uc.mem_read(expectedbank, 322), data + data[:2])
                    call(0x080008E0)
                    self.assertEqual(struct.unpack('<III', uc.mem_read(dma, 12)),
                                     (expectedbank+2, dest, 0xA2600001))
                    self.assertEqual(uc.mem_read(0x0300097A+2*bank, 2), data[:2])
                uc.mem_write(descriptor, word(1))
                call(0x080D9C58, task, descriptor, task+0x18)
                self.assertEqual(frees, [obj])
                self.assertEqual(readword(slot), 0)

    def test_pipeline_and_bank_dependencies(self):
        rom = bytearray(self.rom)
        for address in self.bodies:
            window.provider_evidence(rom, address)
            sites = (0x149B2C, 0x149B30, 0x36D470, 0x36D4B8, 0x02796, 0xA38A2C, 0xDABA4,
                     0x59FE, 0x5A08, 0xD9C92, 0xD9C9A, 0xD9CA0, 0xD9CCE, 0xC46E, 0xC476,
                     0xC618, 0xC620, 0xC4EA, 0xC50E, 0xC520, 0xC52E, 0xC576, 0xC580,
                     0xDAE72, 0x14186C, 0x009AC, 0x00980, 0xC694)
            if address == window.ELLIPSE:
                sites += (0xEEC50, 0xEEC58, 0xEEC64, 0xEEC66, 0xEEC68, 0xDAD56, 0xDAD6A, 0xDA128)
            for site in sites:
                rom[site] ^= 2
                with self.subTest(address=hex(address), site=hex(site)), self.assertRaises(ValueError):
                    window.provider_evidence(rom, address)
                rom[site] ^= 2

    def test_replay_keeps_conditions_and_exact_extent(self):
        import match_evidence
        for address in self.bodies:
            report = (self.root / 'docs/match' / f'{address:08X}.md').read_text()
            record = window.record(self.root, address)
            self.assertIn(record, report)
            self.assertTrue(match_evidence.report_matches(report, self.root, address))
            for changed in (report.replace(record + '\n', ''), report.replace(record, record + '\n' + record),
                            report.replace('requires signed y <= 160', 'proves signed y <= 160')
                            if address == window.ELLIPSE else report.replace('caller unknown', 'caller authenticated'),
                            report.replace('* compiled : `', '* compiled : `00')):
                with self.subTest(address=hex(address)):
                    self.assertFalse(match_evidence.report_matches(changed, self.root, address))

    def execute_writer(self, address, body, x, y, size, height=0):
        """Run the original code and its callees in RAM, servicing the two BIOS arithmetic SWIs."""
        import math
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_HOOK_INTR
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_R0,
                                      UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        machine = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        machine.mem_map(window.BASE, 0x150000)
        machine.mem_write(window.BASE, self.rom[:0x150000])
        machine.mem_write(address, body)
        machine.mem_map(0x02000000, 0x10000)
        machine.mem_map(0x03000000, 0x8000)
        task, obj, buffer, stack, stop = 0x02001000, 0x02002000, 0x02003000, 0x03007000, 0x03006000
        initial = bytes((i*41+7) % 256 for i in range(512))
        machine.mem_write(buffer, initial)
        if address == window.RECT:
            machine.mem_write(task+0x1C, struct.pack('<I', obj))
            machine.mem_write(obj+0x10, struct.pack('<HHI', 320, 2, buffer))
            machine.mem_write(stack, struct.pack('<I', height))
            arguments = (task, x, y, size)
        else:
            arguments = (x, y, size, buffer)
        for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                             UC_ARM_REG_SP, UC_ARM_REG_LR), (*arguments, stack, stop|1)):
            machine.reg_write(reg, val & 0xFFFFFFFF)
        events = []
        def access(uc, kind, location, width, value, _):
            if address <= uc.reg_read(UC_ARM_REG_PC) < address+len(body):
                events.append((kind, location-buffer, width))
        def interrupt(uc, _, __):
            pc = uc.reg_read(UC_ARM_REG_PC)
            swinum = uc.mem_read(pc-2, 1)[0]
            a = uc.reg_read(UC_ARM_REG_R0)
            if swinum == 8:
                uc.reg_write(UC_ARM_REG_R0, math.isqrt(a))
                return
            self.assertEqual(swinum, 6)
            b = uc.reg_read(UC_ARM_REG_R1)
            a, b = (n-2**32 if n >= 2**31 else n for n in (a,b))
            q = (1 if a*b >= 0 else -1) * (abs(a)//abs(b))
            for reg, val in ((UC_ARM_REG_R0, q), (UC_ARM_REG_R1, a-b*q), (UC_ARM_REG_R3, abs(q))):
                uc.reg_write(reg, val & 0xFFFFFFFF)
        machine.hook_add(UC_HOOK_MEM_READ|UC_HOOK_MEM_WRITE, access, begin=buffer, end=buffer+511)
        machine.hook_add(UC_HOOK_INTR, interrupt)
        machine.emu_start(address|1, stop, count=250000)
        self.assertEqual(machine.reg_read(UC_ARM_REG_PC), stop)
        return bytes(machine.mem_read(buffer, 512)), events

    def test_real_execution_and_nonvolatile_counterfactual(self):
        from unicorn import UC_MEM_READ, UC_MEM_WRITE
        for address, cases in ((window.RECT, ((0,0,0,0), (2,1,10,9), (239,159,5,7), (100,50,5,3),
                                               (255,160,100,160), (65535,65535,2,1))),
                               (window.ELLIPSE, ((90,-1,32), (90,0,32), (90,1,32),
                                                (120,80,32), (199,159,32), (100,160,32), (90,70,31)))):
            for args in cases:
                actual, original_access = self.execute_writer(address, self.bodies[address][0], *args)
                control, stripped_access = self.execute_writer(address, self.bodies[address][1], *args)
                with self.subTest(address=hex(address), args=args):
                    self.assertEqual(actual, control)
                    self.assertEqual([e for e in original_access if e[0] == UC_MEM_WRITE],
                                     [e for e in stripped_access if e[0] == UC_MEM_WRITE])
                    self.assertTrue(all(width == 1 and 0 <= rowbyte < 320
                                        for _, rowbyte, width in original_access))
                    if address == window.RECT:
                        self.assertEqual(original_access, [e for _, pos, width in stripped_access
                                         for e in ((UC_MEM_READ,pos,width), (UC_MEM_WRITE,pos,width))])
                    elif args[1] >= 1:
                        self.assertGreater(len(original_access), len(stripped_access))
        # Genuine counterexample for the ellipse's first loop's retained precondition.
        _, outside = self.execute_writer(window.ELLIPSE, self.bodies[window.ELLIPSE][0], 100, 161, 32)
        self.assertIn((UC_MEM_WRITE, 321, 1), outside)


if __name__ == '__main__':
    unittest.main()
