"""Original initialized FLASH512 size-limited verification, including the zero-length API case."""
import os
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_sized_verify as flash
import match_evidence as evidence
import software_float_profile as runtime
import test_flash_program_byte as program_tests


@unittest.skipUnless(os.environ.get('FFTA_FLASH_SIZED_VERIFY_ROOT'), 'needs the original game and sized verification C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_SIZED_VERIFY_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.original = cls.rom[flash.ADDRESS - flash.bank.BASE:flash.END - flash.bank.BASE]
        cls.linked, cls.report = flash.build(cls.root, flash.ADDRESS)

    def test_report_count_abi_and_copy_provenance(self):
        self.assertEqual((self.linked, len(self.linked)), (self.original, 152))
        self.assertTrue(evidence.report_matches(self.report, str(self.root), flash.ADDRESS))
        for fragment in ('"destination_from_entry_sp":-272', '"count":"incoming u32 r2"', '"zero_count_reads":0'):
            altered = self.report.replace(fragment, fragment + '1')
            self.assertNotEqual(altered, self.report)
            self.assertFalse(evidence.report_matches(altered, str(self.root), flash.ADDRESS))
        self.assertFalse(evidence.report_matches(self.report, str(self.root), flash.full.ADDRESS))
        inputs = evidence.mapping_snapshot(self.root), runtime.index_snapshot(self.root), evidence.data_snapshot(self.root)
        for site in (flash.ADDRESS + 6, flash.ADDRESS + 0x2a, flash.ADDRESS + 0x58, flash.ADDRESS + 0x84,
                     flash.CALLER + 4, flash.CALLER + 0x30, flash.full.COMPARE_END):
            with self.subTest(site=site), self.assertRaises(ValueError):
                rom = bytearray(self.rom)
                rom[site - flash.bank.BASE] ^= 1
                flash.native_proof(rom[flash.ADDRESS-flash.bank.BASE:flash.END-flash.bank.BASE], rom, *inputs)

    def test_original_program_then_verify_forwards_size(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        sample = bytes(range(256)) * 16
        for label, body in (('original', self.original), ('linked', self.linked)):
            with self.subTest(label=label):
                cpu, chip, commands, reads = helper.machine(self.rom[0x141fc8:0x142000], 0x1cc2)
                cpu.mem_write(flash.ADDRESS, body)
                cpu.ctl_flush_tb()
                cpu.mem_write(helper.source, sample)
                incoming = []
                def entry(uc, pc, size, unused):
                    reads.clear()
                    incoming.append(tuple(uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2)))
                cpu.hook_add(UC_HOOK_CODE, entry, begin=flash.ADDRESS, end=flash.ADDRESS)
                self.assertEqual(helper.invoke(cpu, flash.CALLER, (1, helper.source, 193), limit=12000000), 0)
                self.assertTrue(commands)
                self.assertEqual(chip.storage[4096:8192], sample)
                self.assertEqual(incoming, [(1, helper.source, 193)])
                self.assertEqual(reads, list(range(4096, 4096+193)))

    def test_exact_sector_prefixes(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_SP
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        sample = bytes(range(256)) * 16
        for label, body in (('original', self.original), ('linked', self.linked)):
            for ident, sector in ((0xd4bf, 0), (0x1b32, 7), (0x1cc2, 15), (0x6bad, 9)):
                cpu, chip, commands, reads = helper.machine(self.rom[0x141fc8:0x142000], ident)
                cpu.mem_write(flash.ADDRESS, body)
                cpu.ctl_flush_tb()
                local = cpu.reg_read(UC_ARM_REG_SP) - 272
                callback, source_reads = [], []
                def enter(uc, pc, size, unused):
                    callback.append(tuple(uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2)))
                def source(uc, access, address, size, value, unused):
                    source_reads.append((address, size))
                cpu.hook_add(UC_HOOK_CODE, enter, begin=local, end=local)
                cpu.hook_add(UC_HOOK_MEM_READ, source, begin=helper.source, end=helper.source+4095)
                base = sector * 4096
                for count in (0, 1, 193, 4096):
                    offsets = [None]
                    if count:
                        offsets.extend(sorted({0, count-1}))
                    if count < 4096:
                        offsets.append(count)
                    for offset in offsets:
                        with self.subTest(body=label, ident=ident, count=count, offset=offset):
                            cpu.mem_write(helper.source, sample)
                            chip.storage[base:base+4096] = sample
                            if offset is not None:
                                chip.storage[base+offset] ^= 0x80
                            for log in (reads, commands, callback, source_reads):
                                log.clear()
                            result = helper.invoke(cpu, flash.ADDRESS, (sector, helper.source, count), limit=60000)
                            mismatch = offset is not None and offset < count
                            consumed = offset+1 if mismatch else count
                            self.assertEqual(result, program_tests.BUS+base+offset if mismatch else 0)
                            self.assertEqual(reads, list(range(base, base+consumed)))
                            self.assertEqual(source_reads, [(helper.source+i, 1) for i in range(consumed)])
                            self.assertEqual(callback, [(helper.source, program_tests.BUS+base, count)])
                            self.assertFalse(commands)
                            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), local+272)
                            self.assertEqual(cpu.mem_read(local, 48), self.rom[0x141bb0:0x141be0])


if __name__ == '__main__':
    unittest.main()
