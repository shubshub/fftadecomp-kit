import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import scanline_constructor as constructor
import test_scanline_pair as scanline


@unittest.skipUnless(os.getenv('FFTA_SCANLINE_CONSTRUCTOR_ROOT'), 'requires the USA ROM and the recovered constructor')
class NativeConstructor(unittest.TestCase):
    cpu = scanline.NativePair.cpu
    call = scanline.NativePair.call

    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_SCANLINE_CONSTRUCTOR_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()

    def test_all_modes_write_only_their_planes(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1

        obj, dest = 0x02020000, 0x04000010
        for mode, callback in enumerate((0x0800DE65, 0x0800DE71, 0x0800D325)):
            for initial in (0, 0xA761, 0xFFFF):
                with self.subTest(mode=mode, initial=initial):
                    cpu = self.cpu()
                    width = 2 << mode
                    payload = 160 * width
                    bank = (161 * width + 3) & ~3
                    total = 32 + payload + 2 * bank
                    cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
                    cpu.mem_write(obj-4, b'\xA5' * (total+8))
                    cpu.mem_write(dest, b'\x5A' * 8)
                    stores = []

                    def allocate(uc, pc, n, context):
                        self.assertEqual(uc.reg_read(UC_ARM_REG_R1), total)
                        uc.reg_write(UC_ARM_REG_R0, obj)
                        uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))

                    def trace(uc, kind, address, size, value, context):
                        if uc.reg_read(UC_ARM_REG_PC) == 0x0800CEE6:
                            stores.append((address, size, value))

                    cpu.hook_add(UC_HOOK_CODE, allocate, begin=0x08007138, end=0x08007138)
                    cpu.hook_add(UC_HOOK_MEM_WRITE, trace)
                    self.call(cpu, constructor.OWNER, mode, initial, dest)
                    self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), obj)
                    self.assertEqual(struct.unpack('<2I', cpu.mem_read(obj, 8)), (callback, dest))
                    self.assertEqual(struct.unpack('<HHIII', cpu.mem_read(obj+16, 16)),
                                     (payload, width, obj+32, obj+32+payload, obj+32+payload+bank))
                    self.assertEqual(stores, [(a, 2, initial) for a in range(obj+32, obj+32+payload, 2)])
                    self.assertEqual(bytes(cpu.mem_read(obj+32, payload)), struct.pack('<H', initial)*(payload//2))
                    self.assertEqual(bytes(cpu.mem_read(obj+32+payload, 2*bank)), bytes(2*bank))
                    self.assertEqual(bytes(cpu.mem_read(obj-4, 4)) + bytes(cpu.mem_read(obj+total, 4)), b'\xA5'*8)
                    self.assertEqual(bytes(cpu.mem_read(dest, 8)), b'\x5A'*8)

    def test_source_and_elf_bindings_are_required(self):
        import tempfile
        constructor.check_source(self.root)
        with tempfile.TemporaryDirectory(dir=self.root/'build') as scratch:
            tree = Path(scratch)
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            source = (self.root/constructor.SOURCE).read_text()
            for old, new in (('tables[4]', 'tables[3]'), ('j < 160', 'j < 159'),
                             ('sizeof(element_sizes)', 'sizeof(callbacks)')):
                self.assertIn(old, source)
                (tree/constructor.SOURCE).write_text(source.replace(old, new))
                with self.assertRaises(ValueError):
                    constructor.check_source(tree)
        bad = copy.deepcopy(constructor.BINDINGS)
        bad['data'][0][1] = 'data_08149818'
        with self.assertRaises(ValueError):
            constructor.check_original({}, bad, {})

    def test_exact_report_replay(self):
        from match_evidence import report_matches
        report = (self.root/'docs/match/0800CE08.md').read_text()
        self.assertTrue(report_matches(report, str(self.root), constructor.OWNER))
        for term in ('254/254 bytes', 'descriptor paths', '"payload_bytes":1280'):
            self.assertIn(term, report)
            self.assertFalse(report_matches(report.replace(term, term+'x', 1), str(self.root), constructor.OWNER))


if __name__ == '__main__':
    unittest.main()
