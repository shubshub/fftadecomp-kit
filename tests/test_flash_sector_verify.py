"""Exercise the full-sector verifier from an initialized flash cartridge and its actual local Thumb entry."""
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_sector_verify as flash
import match_evidence as evidence
import software_float_profile as runtime
import test_flash_program_byte as program_tests


@unittest.skipUnless(os.environ.get('FFTA_FLASH_VERIFY_ROOT'), 'needs original game and full-sector verification C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_VERIFY_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.original = cls.rom[flash.ADDRESS - flash.bank.BASE:flash.END - flash.bank.BASE]
        cls.linked, cls.report = flash.build(cls.root, flash.ADDRESS)

    def test_complete_replay_and_provenance(self):
        self.assertEqual((self.linked, len(self.linked)), (self.original, 152))
        self.assertTrue(evidence.report_matches(self.report, str(self.root), flash.ADDRESS))
        for fragment in ('"copied_halfwords":24', '"padding_ROM_credit":0', '"sector_bytes":4096', flash.SCHEMA):
            with self.subTest(fragment=fragment):
                altered = self.report.replace(fragment, fragment + '1')
                self.assertNotEqual(altered, self.report)
                self.assertFalse(evidence.report_matches(altered, str(self.root), flash.ADDRESS))
        self.assertFalse(evidence.report_matches(self.report, str(self.root), flash.COMPARE))
        inputs = evidence.mapping_snapshot(self.root), runtime.index_snapshot(self.root), evidence.data_snapshot(self.root)
        for address in (flash.COMPARE + 0x10, flash.COMPARE_END, flash.ADDRESS + 0x5c,
                        flash.ADDRESS + 0x82, flash.CALLER + 0x2e, flash.THUNK, flash.bank.SETUPS[0] + 28):
            with self.subTest(address=address), self.assertRaises(ValueError):
                rom = bytearray(self.rom)
                rom[address - flash.bank.BASE] ^= 1
                data = rom[flash.ADDRESS - flash.bank.BASE:flash.END - flash.bank.BASE]
                flash.native_proof(data, rom, *inputs)

    def test_program_then_verify_enters_with_same_sector_and_source(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_SP
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
                def entering(uc, address, size, unused):
                    incoming.append((uc.reg_read(UC_ARM_REG_R0), uc.reg_read(UC_ARM_REG_R1)))
                cpu.hook_add(UC_HOOK_CODE, entering, begin=flash.ADDRESS, end=flash.ADDRESS)
                sp = cpu.reg_read(UC_ARM_REG_SP)
                self.assertEqual(helper.invoke(cpu, flash.CALLER, (1, helper.source), limit=12000000), 0)
                self.assertEqual(incoming, [(1, helper.source)])
                self.assertEqual(chip.storage[4096:8192], sample)
                self.assertEqual(reads[-4096:], list(range(4096, 8192)))
                self.assertTrue(commands)
                self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), sp)

    def test_true_initialized_sector_matches_and_mismatches(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        sample = bytes(range(256)) * 16
        for label, body in (('original', self.original), ('linked', self.linked)):
            for ident, sector in ((0xd4bf, 0), (0x1b32, 7), (0x1cc2, 15), (0x6bad, 9)):
                cpu, chip, commands, reads = helper.machine(self.rom[0x141fc8:0x142000], ident)
                cpu.mem_write(flash.ADDRESS, body)
                cpu.ctl_flush_tb()
                local = cpu.reg_read(UC_ARM_REG_SP) - 268
                copies, calls, waitcnt, banks = [], [], [], []
                def store(uc, access, address, size, value, unused):
                    if flash.ADDRESS <= uc.reg_read(UC_ARM_REG_PC) < flash.END:
                        if address == flash.OBJECTS[flash.WAIT]:
                            waitcnt.append((size, value))
                        elif local <= address < local + 256:
                            copies.append((address, size, value))
                def entered(uc, address, size, unused):
                    if address == flash.bank.OWNER:
                        banks.append(address)
                    else:
                        calls.append(tuple(uc.reg_read(reg) for reg in
                                           (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_SP)))
                cpu.hook_add(UC_HOOK_MEM_WRITE, store)
                cpu.hook_add(UC_HOOK_CODE, entered, begin=local, end=local)
                cpu.hook_add(UC_HOOK_CODE, entered, begin=flash.bank.OWNER, end=flash.bank.OWNER)
                start = sector * 4096
                for mismatch in (None, 0, 2039, 4095):
                    with self.subTest(body=label, ident=ident, mismatch=mismatch):
                        cpu.mem_write(helper.source, sample)
                        chip.storage[start:start+4096] = sample
                        if mismatch is not None:
                            chip.storage[start+mismatch] ^= 0x80
                        for log in (reads, commands, copies, calls, waitcnt, banks):
                            log.clear()
                        cpu.mem_write(flash.OBJECTS[flash.WAIT], struct.pack('<H', 0x4318))
                        result = helper.invoke(cpu, flash.ADDRESS, (sector, helper.source), limit=60000)
                        self.assertEqual(result, 0 if mismatch is None else program_tests.BUS + start + mismatch)
                        self.assertEqual(reads, list(range(start, start + (4096 if mismatch is None else mismatch+1))))
                        self.assertFalse(commands or banks)
                        self.assertEqual(copies, [(local+i, 2, struct.unpack_from('<H', self.rom, 0x141bb0+i)[0])
                                                  for i in range(0, 48, 2)])
                        self.assertEqual(calls, [(helper.source, program_tests.BUS + start, 4096, local)])
                        self.assertEqual(waitcnt, [(2, 0x431b)])
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), local + 268)


if __name__ == '__main__':
    unittest.main()
