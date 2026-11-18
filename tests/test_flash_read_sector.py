"""Exercise FLASH512 ReadFlash on initialized cartridges and the original game header scan."""
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_read_sector as flash
import match_evidence as evidence
import software_float_profile as runtime
import test_flash_program_byte as program_tests


@unittest.skipUnless(os.environ.get('FFTA_FLASH_READ_ROOT'), 'needs the original game and ReadFlash C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_READ_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.original = cls.rom[flash.ADDRESS - flash.bank.BASE:flash.END - flash.bank.BASE]
        cls.linked, cls.report = flash.build(cls.root, flash.ADDRESS)

    def test_report_and_read_provenance(self):
        self.assertEqual((self.linked, len(self.linked)), (self.original, 156))
        self.assertTrue(evidence.report_matches(self.report, str(self.root), flash.ADDRESS))
        for fragment in ('"copied_halfwords":18', '"bytes":128', '"width":1', flash.SCHEMA):
            altered = self.report.replace(fragment, fragment + '0')
            self.assertNotEqual(altered, self.report)
            self.assertFalse(evidence.report_matches(altered, str(self.root), flash.ADDRESS))
        inputs = evidence.mapping_snapshot(self.root), runtime.index_snapshot(self.root), evidence.data_snapshot(self.root)
        for site in (flash.CORE + 0x10, flash.CORE_END, flash.ADDRESS + 0x22, flash.ADDRESS + 0x60,
                     flash.ADDRESS + 0x84, flash.ADDRESS + 0x88, 0x0813ae96, 0x0813af12):
            with self.subTest(site=site), self.assertRaises(ValueError):
                rom = bytearray(self.rom)
                rom[site - flash.bank.BASE] ^= 1
                flash.native_proof(rom[flash.ADDRESS-flash.bank.BASE:flash.END-flash.bank.BASE], rom, *inputs)

    def test_original_game_header_read_into_caller_stack(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_SP
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        sample = bytes(range(128))
        for label, body in (('original', self.original), ('linked', self.linked)):
            with self.subTest(label=label):
                cpu, chip, commands, reads = helper.machine(self.rom[0x141fc8:0x142000], 0xd4bf)
                cpu.mem_write(flash.ADDRESS, body)
                cpu.mem_map(0x0813a000, 4096)
                cpu.mem_write(0x0813a000, self.rom[0x13a000:0x13b000])
                chip.storage[:128] = sample
                calls = []
                def entered(uc, pc, size, unused):
                    calls.append(tuple(uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)))
                cpu.hook_add(UC_HOOK_CODE, entered, begin=flash.ADDRESS, end=flash.ADDRESS)
                helper.invoke(cpu, flash.CALLER, end=0x0813ae9c, limit=5000)
                destination = cpu.reg_read(UC_ARM_REG_SP)
                self.assertEqual(calls, [(0, 0, destination, 128)])
                self.assertEqual(reads, list(range(128)))
                self.assertFalse(commands)
                self.assertEqual(cpu.mem_read(destination, 128), sample)

    def test_offset_width_extent_and_no_write_for_zero(self):
        from unicorn import UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R3, UC_ARM_REG_PC, UC_ARM_REG_SP
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        sample = bytes(range(256)) * 16
        for label, body in (('original', self.original), ('linked', self.linked)):
            for ident, sector in ((0xd4bf, 0), (0x1b32, 7), (0x1cc2, 15), (0x6bad, 9)):
                cpu, chip, commands, reads = helper.machine(self.rom[0x141fc8:0x142000], ident)
                cpu.mem_write(flash.ADDRESS, body)
                cpu.ctl_flush_tb()
                entry_sp = cpu.reg_read(UC_ARM_REG_SP)
                local = entry_sp - 148
                base = sector * 4096
                chip.storage[base:base+4096] = sample
                outputs, local_writes = [], []
                def writing(uc, access, address, size, value, unused):
                    if helper.source - 1 <= address < helper.source + 4097:
                        outputs.append((address, size, value))
                    elif local <= address < local + 128 and flash.ADDRESS <= uc.reg_read(UC_ARM_REG_PC) < flash.END:
                        local_writes.append((address, size, value))
                cpu.hook_add(UC_HOOK_MEM_WRITE, writing)
                for offset, count in ((0, 0), (4095, 1), (79, 193), (0, 4096)):
                    with self.subTest(body=label, ident=ident, offset=offset, count=count):
                        for log in (commands, reads, outputs, local_writes):
                            log.clear()
                        cpu.mem_write(helper.source-1, bytes([0xab]) * 4098)
                        cpu.reg_write(UC_ARM_REG_R3, count)
                        helper.invoke(cpu, flash.ADDRESS, (sector, offset, helper.source), limit=60000)
                        self.assertEqual(reads, list(range(base+offset, base+offset+count)))
                        self.assertFalse(commands)
                        selected = sample[offset:offset+count]
                        self.assertEqual(outputs, [(helper.source+i, 1, value) for i, value in enumerate(selected)])
                        self.assertEqual(cpu.mem_read(helper.source-1, count+2), bytes([0xab])+selected+bytes([0xab]))
                        self.assertEqual(local_writes, [(local+i, 2, struct.unpack_from('<H', self.rom, 0x141af0+i)[0])
                                                       for i in range(0, 36, 2)])
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), entry_sp)


if __name__ == '__main__':
    unittest.main()
