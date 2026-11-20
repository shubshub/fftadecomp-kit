from copy import deepcopy
from os import environ
from pathlib import Path
from struct import pack, unpack
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
from rompath import rom_path
import window_task as task


@unittest.skipUnless(environ.get('FFTA_WINDOW_TASK_ROOT'), 'requires USA ROM and recovered window task')
class NativeWindowTask(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(environ['FFTA_WINDOW_TASK_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = match.mapping_snapshot(cls.root)
        cls.objects = match.data_snapshot(cls.root)

    def test_original_registration_rows_and_lifecycle(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn import UC_MEM_READ, UC_MEM_WRITE, UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0 as R0, UC_ARM_REG_R1 as R1, UC_ARM_REG_R2 as R2
        from unicorn.arm_const import UC_ARM_REG_R3 as R3, UC_ARM_REG_R4 as R4
        from unicorn.arm_const import UC_ARM_REG_PC as PC, UC_ARM_REG_SP as SP, UC_ARM_REG_LR as LR

        manager, event, header, obj = 0x02001000, 0x02002000, 0x02018000, 0x02020000
        for window, left, right in ((0, 0, 240), (1, 177, 47)):
            with self.subTest(window=window):
                cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
                cpu.mem_map(0x08000000, 0x400000)
                cpu.mem_write(0x08000000, self.rom[:0x400000])
                for base, size in ((0x02000000, 0x40000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
                    cpu.mem_map(base, size)
                cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
                cpu.mem_write(0x02008FF0, pack('<I', manager))
                cpu.mem_write(0x02009158, b'\xff'*8)
                cpu.mem_write(obj-4, b'\xa5'*1008)
                cpu.mem_write(header-4, b'\xa5'*44)
                cpu.mem_write(0x04000040, b'\x5a'*4)
                allocated, freed, trace = [], [], []

                def heap(uc, pc, size, user):
                    amount = uc.reg_read(R1)
                    if pc == 0x08007138:
                        self.assertIn(amount, (36, 1000))
                        allocated.append(amount)
                        uc.reg_write(R0, header if amount == 36 else obj)
                    else:
                        freed.append(amount)
                    uc.reg_write(PC, uc.reg_read(LR))

                for pc in (0x08007138, 0x08007170):
                    cpu.hook_add(UC_HOOK_CODE, heap, begin=pc, end=pc)

                def access(uc, kind, address, width, value, user):
                    if task.OWNER <= uc.reg_read(PC) < task.OWNER + 156:
                        trace.append((kind, address, width))

                cpu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, access, begin=obj-4, end=obj+1003)

                def call(address, *args):
                    stop, sp = 0x03007000, 0x03007F00
                    for reg, value in zip((R0, R1, R2, R3), args):
                        cpu.reg_write(reg, value)
                    for n in range(8):
                        cpu.reg_write(R4+n, 0x45700000+n)
                    cpu.reg_write(SP, sp)
                    cpu.reg_write(LR, stop|1)
                    cpu.emu_start(address|1, stop, count=100000)
                    self.assertEqual((cpu.reg_read(PC), cpu.reg_read(SP)), (stop, sp))
                    self.assertEqual([cpu.reg_read(R4+n) for n in range(8)], [0x45700000+n for n in range(8)])
                    return cpu.reg_read(R0)

                self.assertEqual(call(task.SPAWNER, window, left, right, 0), header)
                self.assertEqual(allocated, [36, 1000])
                self.assertEqual(unpack('<I', cpu.mem_read(header, 4))[0], task.OWNER|1)
                self.assertEqual(unpack('<H', cpu.mem_read(header+20, 2))[0], 0x100)
                self.assertEqual(unpack('<I', cpu.mem_read(header+28, 4))[0], obj)
                self.assertEqual(unpack('<2I', cpu.mem_read(obj, 8)), (task.CALLBACK|1, 0x04000040+2*window))
                self.assertEqual(unpack('<HHIII', cpu.mem_read(obj+16, 16)), (320, 2, obj+32, obj+352, obj+676))
                self.assertEqual(bytes(cpu.mem_read(obj+32, 320)), bytes((right, left))*160)
                self.assertEqual(bytes(cpu.mem_read(obj+352, 648)), bytes(648))
                expected = [(kind, obj+32+row*2+lane, 1) for row in range(160)
                            for lane in (1,0) for kind in (UC_MEM_READ,UC_MEM_WRITE)]
                self.assertEqual(trace, expected)
                self.assertEqual(bytes(cpu.mem_read(0x04000040, 4)), b'\x5a'*4)

                for phase, flag, after, flags in ((0x100, 0, 0x100, 1), (0x100, 1, 0x101, 3),
                                                 (0x101, 0, 2, 3), (0x8765, 1, 0x8765, 3), (1, 1, 1, 3)):
                    cpu.mem_write(event, pack('<H', phase))
                    cpu.mem_write(header+24, bytes([flag]))
                    self.assertEqual(call(task.OWNER, header, event, header+24), 0)
                    self.assertEqual(bytes(cpu.mem_read(event, 2)), pack('<H', after))
                    self.assertEqual(bytes(cpu.mem_read(obj+12, 2)), pack('<H', flags))
                self.assertEqual(freed, [obj])
                self.assertEqual(bytes(cpu.mem_read(0x02009148, 4)), bytes(4))
                self.assertEqual(bytes(cpu.mem_read(header-4, 4)) + bytes(cpu.mem_read(header+36, 4)), b'\xa5'*8)
                self.assertEqual(bytes(cpu.mem_read(obj-4, 4)) + bytes(cpu.mem_read(obj+1000, 4)), b'\xa5'*8)

    def test_qualifier_and_relocations_refuse_substitution(self):
        import plausible
        path = self.root/task.SOURCE
        closure = plausible.include_closure(self.root, path)
        source = path.read_text()
        self.assertEqual(len(task.qualifier_offsets(source, self.root, self.root, closure)), 2)
        self.assertFalse(task.qualifier_offsets(source.replace('u16 row;', 'u32 row;'),
                                               self.root, self.root, closure))
        self.assertFalse(task.qualifier_offsets(source.replace('volatile', '', 1),
                                               self.root, self.root, closure))
        data = self.rom[task.OWNER-0x08000000:task.OWNER-0x08000000+156]
        for section in ('data', 'functions', 'calls'):
            manifest = deepcopy(task.MANIFEST)
            manifest[section].clear()
            with self.assertRaises(ValueError):
                match.verify_function_addresses(data, task.OWNER, self.rom, self.mapping, self.objects, manifest)

    def test_report_binds_both_compiler_controls_and_index_premise(self):
        from match_evidence import report_matches
        report = (self.root/'docs/match/080D9C58.md').read_text()
        self.assertTrue(report_matches(report, self.root, task.OWNER))
        self.assertFalse(report_matches(report.replace('39/19', '38/20'), self.root, task.OWNER))
        self.assertFalse(report_matches(report.replace(task.STRIPPED, '0'*64), self.root, task.OWNER))


if __name__ == '__main__':
    unittest.main()
