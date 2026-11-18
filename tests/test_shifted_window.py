import math
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import window_scanline as window


def interpolated(start, end, duration, elapsed):
    # E0608 starts the remainder at duration//2. E064C advances the
    # current position while the remainder is strictly negative.
    steps = (min(elapsed, duration) * abs(end - start) + duration - 1 - duration // 2) // duration
    return start + (steps if end >= start else -steps)


@unittest.skipUnless(os.getenv('FFTA_SHIFTED_WINDOW_ROOT'), 'requires the USA ROM, reviewed writer and agbcc')
class ShiftedWindowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_SHIFTED_WINDOW_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.address = window.SHIFTED_ELLIPSE
        cls.bodies = window.compile_bodies(cls.root, cls.address, cls.rom)

    def test_reviewed_source_and_independent_compiler_controls(self):
        source = (self.root / 'src/0811435C.c').read_text()
        header = (self.root / window.HEADER).read_bytes()
        self.assertEqual(len(window.source_offsets(source, header, self.address)), 2)
        for original, replacement in (
            ('y - row >= 0', 'y - row > 0'), ('y + row < 160', 'y + row <= 160'),
            ('.left - motion.current', '.right - motion.current'),
            ('value > 240', 'value > 241'), ('lines = func_080DABB4(task)', 'lines = task'),
            ('u8 left : 8', 'u8 left : 7'), ('row--', 'row++'),
        ):
            self.assertIn(original, source)
            self.assertFalse(window.source_offsets(source.replace(original, replacement), header, self.address))
        self.assertFalse(window.source_offsets(source, header, window.CIRCLE))
        self.assertEqual([len(body) for body in self.bodies], [220, 212, 220])
        real = self.bodies[0]
        self.assertEqual(real, self.rom[self.address-window.BASE:self.address-window.BASE+220])
        for which, site in ((0, 0x60), (0, 0x9A), (1, 0x78), (2, 0x78), (2, 0xC4)):
            bodies = list(self.bodies)
            altered = bytearray(bodies[which])
            altered[site] ^= 0x40
            bodies[which] = altered
            with self.subTest(control=which, site=site), self.assertRaises(ValueError):
                window.check_bodies(self.address, *bodies)

    def test_caller_interpolators_live_payload_and_hardware_dependencies(self):
        rom = bytearray(self.rom)
        window.provider_evidence(rom, self.address)
        for site in (0x08114504, 0x08114516, 0x081146CC, 0x081146F8,
                     0x081147DC, 0x081147E8, 0x081147EE, 0x081147F0,
                     0x0811480C, 0x0811481E, 0x08114820, 0x080DAC80,
                     0x080DABB4, 0x0800C618, 0x080E0622, 0x080E066E,
                     0x080DA132, 0x080D9FD4, 0x08141870, 0x08141898,
                     0x08149B30, 0x080DAE72, 0x0800C520, 0x08149434, 0x08000980):
            rom[site-window.BASE] ^= 2
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                window.provider_evidence(rom, self.address)
            rom[site-window.BASE] ^= 2

    def test_original_object_requires_four_direct_relocations(self):
        import argparse
        import copy
        import match

        args = argparse.Namespace(cpp=match.DEFAULT_CPP, cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(self.root), timeout=match.SIGNED_REPLAY_TIMEOUT)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, args, self.root, self.address, 'src/0811435C.c')
        mapping = match.mapping_snapshot(self.root)

        def bind(obj):
            return match.call_bindings(obj, 'func_0811435C', self.address, mapping, len(self.rom), self.rom)

        calls, _, data = bind(image)
        sites = (self.address + offset for offset in (0x22, 0x34, 0x3A, 0x50))
        self.assertEqual(sorted(calls.items()), list(zip(sites, window.CALLEES[self.address])))
        self.assertFalse(data)
        section, = image['relocations']
        relocs = list(struct.iter_unpack('<II', image['section_data'][section]))
        for pos, (site, info) in enumerate(relocs):
            self.assertEqual(info & 255, 10)  # R_ARM_THM_CALL
            changed = copy.deepcopy(image)
            raw = bytearray(image['section_data'][section])
            struct.pack_into('<I', raw, pos*8+4, info & ~255 | 2)  # R_ARM_ABS32
            changed['section_data'][section] = bytes(raw)
            with self.subTest(site=site), self.assertRaises(ValueError):
                bind(changed)

    def test_saved_report_requires_both_independent_proofs(self):
        import match_evidence
        from named_data_buffer_profile import ROOT_SCRATCH_SCHEMA, SCRATCH_SCHEMA
        report = (self.root / 'docs/match/0811435C.md').read_text()
        record = window.record(self.root, self.address)
        self.assertIn(record, report)
        self.assertTrue(match_evidence.report_matches(report, self.root, self.address))
        for altered in (report.replace(record + '\n', ''), report.replace(record, record + '\n' + record),
                        report.replace('original initialized scene interpolators', 'arbitrary interpolators'),
                        report.replace(ROOT_SCRATCH_SCHEMA, SCRATCH_SCHEMA),
                        report.replace('* compiled : `', '* compiled : `00')):
            self.assertNotEqual(altered, report)
            self.assertFalse(match_evidence.report_matches(altered, self.root, self.address))

    def test_original_scene_calls_and_every_byte_access(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ, UC_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3,
                                       UC_ARM_REG_R7, UC_ARM_REG_SP, UC_ARM_REG_PC)
        tasks = (0x02001000, 0x02001200)
        planes = (0x02006000, 0x02007000)
        scene, stack = 0x02003000, 0x03007000
        regs = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)

        def bios(uc, _, __):
            service = uc.mem_read(uc.reg_read(UC_ARM_REG_PC)-2, 1)[0]
            a = uc.reg_read(UC_ARM_REG_R0)
            if service == 8:
                uc.reg_write(UC_ARM_REG_R0, math.isqrt(a))
            else:
                self.assertEqual(service, 6)
                a, b = (v if v < 2**31 else v-2**32 for v in (a, uc.reg_read(UC_ARM_REG_R1)))
                self.assertNotEqual(b, 0)
                q = (1 if a*b >= 0 else -1) * (abs(a)//abs(b))
                for reg, val in ((regs[0], q), (regs[1], a-q*b), (regs[3], abs(q))):
                    uc.reg_write(reg, val & 0xFFFFFFFF)

        for build, body in enumerate(self.bodies):
            with self.subTest(build=build):
                uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
                uc.mem_map(window.BASE, 0x150000)
                uc.mem_write(window.BASE, self.rom[:0x150000])
                uc.mem_write(self.address, body)
                uc.mem_map(0x02000000, 0x10000)
                uc.mem_map(0x03000000, 0x8000)
                for index, (task, plane) in enumerate(zip(tasks, planes)):
                    obj = 0x02002000 + index * 128
                    uc.mem_write(task+0x1C, struct.pack('<I', obj))
                    uc.mem_write(obj+0x10, struct.pack('<HHI', 320, 2, plane))
                    uc.mem_write(plane-4, b'\xa5' * 4 + bytes((41*n+7) % 256 for n in range(320)) + b'\xa5' * 4)
                uc.mem_write(scene+0x2C, struct.pack('<II', *tasks))
                uc.reg_write(UC_ARM_REG_R7, scene)
                uc.reg_write(UC_ARM_REG_SP, stack)
                uc.hook_add(UC_HOOK_INTR, bios)
                accesses, calls = [], []
                bank = None
                initial = None

                def run(begin, end):
                    uc.emu_start(begin | 1, end, count=750000)
                    self.assertEqual(uc.reg_read(UC_ARM_REG_PC), end)

                def entry(machine, pc, size, user):
                    nonlocal bank
                    task, x, y, width = (machine.reg_read(reg) for reg in regs)
                    height, shift = struct.unpack('<II', machine.mem_read(stack, 8))
                    bank = tasks.index(task)
                    calls.append((bank, x, y, width, height, shift))
                    accesses.clear()

                def after_geometry(machine, pc, size, user):
                    nonlocal initial
                    # DABB4 is called after DAC80 has run the genuine ellipse.
                    initial = bytes(machine.mem_read(planes[bank], 320))

                def access(machine, kind, location, width, value, user):
                    pc = machine.reg_read(UC_ARM_REG_PC)
                    if self.address <= pc < self.address + len(body):
                        accesses.append((kind, location - planes[bank], width))
                    elif window.CIRCLE <= pc < window.ELLIPSE:
                        self.assertTrue(planes[bank] <= location < planes[bank]+320)
                        self.assertEqual(width, 1)

                def returned(machine, pc, size, user):
                    if pc == 0x08114824 and bank == 0:
                        return  # the second window was skipped this frame
                    _, _, y, _, height, shift = calls[-1]
                    expected = bytearray(initial)
                    want = []
                    for elapsed in range(1, height+1):
                        row = height-elapsed
                        displacement = interpolated(shift, 0, height, elapsed)
                        for line, top in ((y-row, True), (y+row, False)):
                            if not 0 <= line < 160:
                                continue
                            fields = (0, 1) if build == 2 else (1, 0)
                            for lane in fields:
                                offset = 2*line+lane
                                value = expected[offset]
                                expected[offset] = min(240, value+displacement) if top else max(0, value-displacement)
                                kinds = (UC_MEM_READ, UC_MEM_WRITE) if build == 1 else (
                                    UC_MEM_READ, UC_MEM_READ, UC_MEM_WRITE)
                                want.extend((kind, offset, 1) for kind in kinds)
                    self.assertEqual(accesses, want)
                    self.assertEqual(machine.mem_read(planes[bank]-4, 328), b'\xa5'*4 + expected + b'\xa5'*4)

                for site, handler in ((self.address, entry), (0x080DABB4, after_geometry),
                                      (0x081147F4, returned), (0x08114824, returned)):
                    uc.hook_add(UC_HOOK_CODE, handler, begin=site, end=site)
                uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, access, begin=0x02000000, end=0x0200FFFF)
                run(0x081146C4, 0x081146FC)
                # Original phase code updates bank 1 immediately and bank 0 when
                # the frame count exceeds seven. Include one saturated step.
                for frame in range(21):
                    uc.mem_write(scene, struct.pack('<H', frame))
                    calls.clear()
                    run(0x081147C8, 0x08114826)
                    expected_calls = []
                    for index, elapsed, start, duration in ((0, frame+1, 5, 20), (1, frame-7, 4, 12)):
                        if elapsed > 0:
                            w = interpolated(start, 40, duration, elapsed)
                            h = interpolated(2*start, 80, duration, elapsed)
                            expected_calls.append((index, 160-index, 72-index, w, h, h >> 3))
                    self.assertEqual(calls, expected_calls)
