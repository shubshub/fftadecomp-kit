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
        for address in (0x0800CF08, 0x0800D23C, 0x080D9C58, 0x080DA2D4):
            with self.subTest(address=address), self.assertRaises(ValueError):
                window.provider_evidence(b'', address)


@unittest.skipUnless(os.getenv('FFTA_WINDOW_SCANLINE_ROOT'), 'requires the USA ROM, the reviewed sources and native agbcc')
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
            site = {window.CIRCLE: 0x74, window.RECT: 0x84, window.ELLIPSE: 0xEA, window.SCALED_ELLIPSE: 0xBE,
                    window.LEFT_EDGE: 0x134, window.RIGHT_EDGE: 0x136}[address]
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
            elif address == window.CIRCLE:
                mutations += [('(u16)row < 160', '(u16)row <= 160'), ('mode != 2', 'mode != 1'),
                              ('y - offset', 'y + offset'), ('decision >= 0', 'decision > 0')]
            elif address == window.SCALED_ELLIPSE:
                mutations += [('(u16)row < 160', '(u16)row <= 160'), ('mode != 2', 'mode != 1'),
                              ('offset++', 'offset--'), ('func_08141898(x_scale)', 'func_08141898(y_scale)'),
                              ('func_08141870(size,', 'func_08141870(x_scale,')]
            elif address in window.EDGES:
                mutations += [('upper_y < 160', 'upper_y <= 160'), ('lower_y >= 0', 'lower_y > 0'),
                              ('(u16)y1 < 160', '(u16)y1 <= 160'), ('error += adjustment', 'error -= adjustment'),
                              ('clamp_x(upper_x)' + (' + 1' if address == window.RIGHT_EDGE else ''),
                               'clamp_x(upper_x) + 2')]
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
        from math import isqrt
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
                def bios(u, _, __):
                    pc = u.reg_read(UC_ARM_REG_PC)
                    swi = u.mem_read(pc-2, 1)[0]
                    if swi == 8:
                        u.reg_write(UC_ARM_REG_R0, isqrt(u.reg_read(UC_ARM_REG_R0)))
                        return
                    if swi == 6:
                        # The diameter-32 provider supplies only positive operands.
                        numerator, divisor = (u.reg_read(reg) for reg in registers[:2])
                        quotient, remainder = divmod(numerator, divisor)
                        for reg, value in ((UC_ARM_REG_R0, quotient), (UC_ARM_REG_R1, remainder),
                                           (UC_ARM_REG_R3, quotient)):
                            u.reg_write(reg, value)
                        return
                    self.assertEqual(u.mem_read(pc-2, 2), b'\x0b\xdf')
                    source, destination, count = (u.reg_read(k) for k in registers[:3])
                    self.assertIn(count, (1,160))
                    u.mem_write(destination, bytes(u.mem_read(source, 2*count)))
                for site, callback in ((0x08007138, allocate), (0x08007170, free)):
                    uc.hook_add(UC_HOOK_CODE, callback, begin=site, end=site)
                uc.hook_add(UC_HOOK_INTR, bios)
                def call(address, *args):
                    for register, value in zip(registers, args):
                        uc.reg_write(register, value)
                    uc.reg_write(UC_ARM_REG_SP, 0x03007F00)
                    if len(args) > 4:
                        uc.mem_write(0x03007F00, b''.join(word(value) for value in args[4:]))
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
                # This wrapper is also the scene's real provider for the circle.
                call(0x080DAC40, task, 100, 80, 2)
                self.assertEqual(uc.mem_read(payload+160, 2), bytes((103,98)))
                # Use the original DABC4 mode dispatch, accessor and both edge
                # writers. The first submitted bank must contain their actual pixels.
                call(0x080DABC4, task, 30, 10, 30, 12, 0)
                call(0x080DABC4, task, 240, 10, 240, 12, 1)
                self.assertEqual(uc.mem_read(payload+20, 6), bytes((241,30))*3)
                raster_calls = []
                def enter_raster(u, _, __, ___):
                    stack = u.reg_read(UC_ARM_REG_SP)
                    raster_calls.append((*[u.reg_read(r) for r in registers],
                                         *struct.unpack('<III', u.mem_read(stack,12))))
                uc.hook_add(UC_HOOK_CODE, enter_raster, begin=window.SCALED_ELLIPSE, end=window.SCALED_ELLIPSE)
                call(0x080DAD3C, task, 100, 80, 32)
                self.assertEqual(raster_calls, [(100,80,256,256,1024,payload,2)])
                self.assertEqual(uc.mem_read(payload+160, 2), bytes((116,84)))
                rendered = bytes(uc.mem_read(payload, 320))
                buffers = (readword(obj+24), readword(obj+28))
                self.assertEqual(buffers, (payload+320, payload+644))
                for frame, expectedbank in enumerate(reversed(buffers)):
                    data = rendered if frame == 0 else bytes((i+17)%256 for i in range(320))
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
            elif address == window.SCALED_ELLIPSE:
                sites += (0xEEC58, 0xEEC66, 0xEEC68, 0xDAD50, 0xDAD56, 0xDAD6A,
                          0xDA214, 0xDA248, 0x141870, 0x141898)
            elif address == window.CIRCLE:
                sites += (0xE0DC4, 0xE0DC8, 0xE0DD2, 0xE0DD6, 0xE0DFE, 0xE0E0A,
                          0xE0E32, 0xDAC56, 0xDAC5A, 0xDAC5C, 0xDAC6C, 0xDAC74, 0xDA8E2, 0xDAD26)
            elif address in window.EDGES:
                sites += (0x112116, 0x11211A, 0x1121F4, 0x1121F6, 0x1121FA, 0x11220E, 0x112214,
                          0xDABEA, 0xDABEE, 0xDABF0, 0xDABF8, 0xDAC0E, 0xDAC10, 0xDAC2A, 0xDAC2C)
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
                            report.replace({window.RECT: 'caller unknown', window.ELLIPSE: 'requires signed y <= 160',
                                            window.CIRCLE: 'the same live tasks must reach phase 0x101',
                                            window.SCALED_ELLIPSE: 'scene scales 256/1024, size 256',
                                            **dict.fromkeys(window.EDGES, 'phase 0x100 must retain its live +0x44 task')}[address],
                                           'unconditional'),
                            report.replace('* compiled : `', '* compiled : `00')):
                with self.subTest(address=hex(address)):
                    self.assertFalse(match_evidence.report_matches(changed, self.root, address))

    def execute_writer(self, address, body, x, y, size, height=0, scales=None):
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
        elif address == window.SCALED_ELLIPSE:
            x_scale, y_scale = scales
            arguments = (x, y, size, x_scale)
            machine.mem_write(stack, struct.pack('<III', y_scale, buffer, height))
        elif address in window.EDGES:
            arguments = (x, y, size, height)
            machine.mem_write(stack, struct.pack('<I', buffer))
        else:
            arguments = (x, y, size, buffer)
            if address == window.CIRCLE:
                machine.mem_write(stack, struct.pack('<I', height))
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
        first, last = (0x02000000, 0x0200FFFF) if address == window.SCALED_ELLIPSE else (buffer, buffer+511)
        machine.hook_add(UC_HOOK_MEM_READ|UC_HOOK_MEM_WRITE, access, begin=first, end=last)
        machine.hook_add(UC_HOOK_INTR, interrupt)
        machine.emu_start(address|1, stop, count=250000)
        self.assertEqual(machine.reg_read(UC_ARM_REG_PC), stop)
        return bytes(machine.mem_read(buffer, 512)), events

    def test_circle_pixels_modes_and_all_four_store_sites(self):
        from unicorn import UC_MEM_READ, UC_MEM_WRITE
        actual, stripped, swapped = self.bodies[window.CIRCLE]
        for site in (0x74, 0x90, 0xCC, 0xE8):
            changed = bytearray(actual)
            changed[site-8] = 160  # Admit row 160 instead of stopping at 159.
            with self.subTest(site=site), self.assertRaisesRegex(ValueError, 'circle row guard'):
                window.check_bodies(window.CIRCLE, changed, stripped, swapped)
        # The halfword conversion precedes the unsigned row check. Horizontal
        # bounds are clipped on one side each and finally narrowed to bytes.
        signed = lambda n: (n + 32768) % 65536 - 32768
        for x, y, radius in ((100,80,0), (100,80,2), (2,0,12), (239,159,8), (120,80,80),
                             (-3,-1,7), (32767,32766,4), (-32768,-32768,5)):
            for mode in (0, 1, 2, 3):
                expected = bytearray((i*41+7) % 256 for i in range(512))
                sites = []
                dx, dy, error = radius, 0, 3-2*radius
                while radius and dx >= dy:
                    for span, step in ((dx, dy), (dy, dx)):
                        lo = max(0, signed(x-span)) & 255
                        hi = min(240, signed(x+span+1)) & 255
                        for row, disabled in ((y+step, 1), (y-step, 2)):
                            row &= 65535
                            if row < 160 and mode != disabled:
                                sites.extend((2*row+1, 2*row))
                                expected[2*row:2*row+2] = bytes((hi, lo))
                    if error >= 0:
                        dx -= 1
                        error -= 4*dx
                    dy += 1
                    error += 2 + 4*dy
                with self.subTest(x=x, y=y, r=radius, mode=mode):
                    for index, qualified in ((0, True), (1, False)):
                        pixels, events = self.execute_writer(window.CIRCLE, self.bodies[window.CIRCLE][index],
                                                             x, y, radius, mode)
                        self.assertEqual(pixels, expected)
                        kinds = (UC_MEM_READ, UC_MEM_WRITE) if qualified else (UC_MEM_WRITE,)
                        self.assertEqual(events, [(kind, byte, 1) for byte in sites for kind in kinds])

    def test_edge_pixels_guards_and_exclusive_right_bound(self):
        from unicorn import UC_MEM_READ, UC_MEM_WRITE
        cases = ((10,0,80,0), (80,159,10,159), (-5,159,300,159), (120,-1,60,-1),
                 (15,160,10,160), (16,1,90,9), (90,9,16,1), (16,9,90,1),
                 (-20,-2,250,163), (240,158,240,161), (308,0,-68,248),
                 (-32768,20,-32767,21), (32767,20,32766,22))
        clip = lambda x: max(0, min(240, x))
        for address in window.EDGES:
            actual, stripped, swapped = self.bodies[address]
            right = address == window.RIGHT_EDGE
            # Independent mutations of unsigned horizontal, top signed high/low,
            # lower signed high/low and the exclusive coordinate adjustment.
            lower = 0x140 if right else 0x13E
            for site in (0x2A, 0x10E, 0x112, lower, lower+4) + ((0x134, 0x164) if right else ()):
                changed = bytearray(actual)
                changed[site] ^= 1
                with self.subTest(site=hex(site)), self.assertRaisesRegex(ValueError, 'edge row guard'):
                    window.check_bodies(address, changed, stripped, swapped)
            for x1, y1, x2, y2 in cases:
                expected = bytearray((i*41+7)%256 for i in range(512))
                stores = []
                if y1 == y2:
                    if 0 <= y1 < 160:
                        lo, hi = sorted((clip(x1), clip(x2)))
                        stores = [(2*y1+1, lo), (2*y1, hi)]
                else:
                    ax, ay, bx, by = (x1,y1,x2,y2) if y1 < y2 else (x2,y2,x1,y1)
                    rows = by-ay+1
                    for i in range((rows+1)//2):
                        # Closed form of the two-ended rasterizer, independent
                        # of the ROM's nested incremental error loop.
                        steps = (i*abs(bx-ax) + rows-1-rows//2)//rows
                        offset = steps if bx >= ax else -steps
                        for x, y in ((ax+offset, ay+i), (bx-offset, by-i)):
                            if 0 <= y < 160:
                                stores.append((2*y + (0 if right else 1), clip(x) + int(right)))
                for byte, value in stores:
                    expected[byte] = value
                for index, events in ((0, (UC_MEM_READ, UC_MEM_WRITE)), (1, (UC_MEM_WRITE,))):
                    with self.subTest(address=hex(address), xy=(x1,y1,x2,y2), compile=index):
                        output, trace = self.execute_writer(address, self.bodies[address][index], x1,y1,x2,y2)
                        self.assertEqual(output, expected)
                        self.assertEqual(trace, [(event, byte, 1) for byte, _ in stores for event in events])

    def test_scaled_ellipse_pixels_modes_and_qualifier_controls(self):
        from math import isqrt
        from unicorn import UC_MEM_READ, UC_MEM_WRITE
        address = window.SCALED_ELLIPSE
        actual, stripped, swapped = self.bodies[address]
        for site in (0xB4, 0xD6, 0xBA, 0xDC):
            changed = bytearray(actual)
            changed[site] ^= 1
            with self.subTest(site=hex(site)), self.assertRaisesRegex(ValueError, 'scaled ellipse row guard'):
                window.check_bodies(address, changed, stripped, swapped)
        # Recompute the decision surfaces from the coordinates before every
        # step, independently of the incremental additions in the compiled code.
        signed_half = lambda n: (n + 32768) % 65536 - 32768
        for x,y,size,a,b in ((100,80,0,0,0), (100,80,256,256,1024), (100,80,256,1024,256),
                             (100,-2,32,4,16), (238,159,40,4,9), (-20,160,50,9,3),
                             (32767,32767,16,4,9), (-32768,-32768,16,4,9)):
            for mode in (0,1,2,3):
                expected = bytearray((i*41+7)%256 for i in range(512))
                sites = []
                width = initial = size//isqrt(a) if size else 0
                offset = 0
                while width > 0:
                    lo = max(0, signed_half(x-width)) & 255
                    hi = min(240, signed_half(x+width+1)) & 255
                    for row, suppressed in ((y+offset,1), (y-offset,2)):
                        row &= 65535
                        if row < 160 and mode != suppressed:
                            sites.extend((2*row+1, 2*row))
                            expected[2*row:2*row+2] = bytes((hi,lo))
                    common = 2*a*(width*width-initial*initial) + 2*b*offset*offset
                    vertical = common + 2*a*(initial-width) + 4*b*offset + a + 2*b - 2*isqrt(a)*size
                    horizontal = common + 4*a*(initial-width) + 2*b*offset + 2*a + b - 4*isqrt(a)*size
                    if vertical < 0:
                        offset += 1
                    elif horizontal >= 0:
                        width -= 1
                    else:
                        width -= 1
                        offset += 1
                for body, events in ((actual, (UC_MEM_READ, UC_MEM_WRITE)), (stripped, (UC_MEM_WRITE,))):
                    with self.subTest(x=x,y=y,size=size,scales=(a,b),mode=mode):
                        pixels, trace = self.execute_writer(address, body, x,y,size,mode,(a,b))
                        self.assertEqual(pixels, expected)
                        self.assertEqual(trace, [(kind, byte, 1) for byte in sites for kind in events])

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
