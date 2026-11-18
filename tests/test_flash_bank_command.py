"""Exercise FLASH512_V130's original bank command, sector guards and cartridge readback."""
from pathlib import Path
import os
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_bank_command as flash
import match_evidence
import plausible


class BankedFlash:
    """Model only the unlock and bank command, and reads of differently seeded banks."""
    def __init__(self, banks):
        self.banks = banks
        self.bank = 0
        self.prefix = []

    def write(self, offset, value):
        command = [(0x5555, 0xaa), (0x2aaa, 0x55), (0x5555, 0xb0)]
        if self.prefix == command:
            if offset == 0 and value in range(self.banks):
                self.bank = value
            self.prefix.clear()
        elif (offset, value) == command[len(self.prefix)]:
            self.prefix.append((offset, value))
        else:
            self.prefix.clear()

    def read(self, offset):
        return (0x33, 0xa7)[self.bank] ^ (offset & 0xff)


class ProtocolTests(unittest.TestCase):
    def test_unlock_order_and_fixed_bank_port(self):
        seq = [(0x5555, 0xaa), (0x2aaa, 0x55), (0x5555, 0xb0), (0, 1)]
        for writes in (seq[1:], seq[:2]+seq[3:], seq[:1]+seq[2:], seq[1:2]+seq[:1]+seq[2:],
                       seq[:3]+[(1, 1)], [(0x5554, 0xaa)]+seq[1:]):
            chip = BankedFlash(2)
            for off, byte in writes:
                chip.write(off, byte)
            self.assertEqual(chip.read(9), 0x33 ^ 9)
        chip = BankedFlash(2)
        for off, byte in seq:
            chip.write(off, byte)
        self.assertEqual(chip.read(9), 0xa7 ^ 9)


@unittest.skipUnless(os.environ.get('FFTA_FLASH_BANK_ROOT'), 'needs indexed original game and SwitchFlashBank C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_BANK_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        cls.qualified, cls.ordinary = flash.compile_bodies(cls.root)

    def test_canonical_report_and_control(self):
        self.assertEqual(self.qualified, self.rom[0x14189c:0x1418c0])
        self.assertEqual([len(self.qualified), len(self.ordinary)], [36, 28])
        report = (self.root/'docs/match/0814189C.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, str(self.root), flash.OWNER))
        for expected in ('36/36', flash.STRIPPED, 'B0@0E005555', '128-KiB'):
            self.assertIn(expected, report)
            self.assertFalse(match_evidence.report_matches(report.replace(expected, 'altered'), str(self.root), flash.OWNER))

    def test_qualifiers_are_owner_role_and_source_bound(self):
        path = self.root/flash.SOURCE
        text = path.read_text()
        closure = plausible.include_closure(self.root, path)
        def offsets(src, c=closure):
            return flash.qualifier_offsets(src, self.root, self.root, c)
        self.assertEqual(len(offsets(text)), 4)
        self.assertFalse(offsets(text, ({'src/08141FC8.c', flash.HEADER}, [])))
        for before, after in [('0xAA', '0xAB'), ('0xB0', '0xA0'), ('u8 *)', 'u16 *)'),
            ('0x0E000000 =', '(0x0E000000 + bank) ='), ('= bank;', '= 1;'), ('u8 bank)', 'u32 bank)'),
            ('    *(volatile', '    if (bank) *(volatile'), ('#include', '#define bank b\n#include')]:
            with self.subTest(before=before):
                modified = text.replace(before, after, 1)
                self.assertNotEqual(modified, text)
                self.assertFalse(offsets(modified))
        for off in (0x14189c, 0x1418a4, 0x1418b4, 0x1418b8, 0x1418bc, 0x141b3c, 0x141b44, 0x141b68,
                    0x141c04, 0x141c0c, 0x141c30, 0x141c90, 0x141c98, 0x141cc0, 0x141dce,
                    0x141e0c, 0x36ce38, *(p-flash.BASE+20 for p in flash.SETUPS), flash.SETUPS[-1]-flash.BASE+40):
            with self.subTest(off=off), self.assertRaises(ValueError):
                flash.provider(self.rom[:off] + bytes([self.rom[off]^1]) + self.rom[off+1:])

    def machine(self, body, banks):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_SP
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for start, size in [(0x08141000, 0x2000), (0x0836c000, 0x2000), (0x02000000, 0x40000),
                            (0x03000000, 0x8000), (0x04000000, 0x1000), (flash.BUS, 0x10000)]:
            cpu.mem_map(start, size)
            if flash.BASE <= start < 0x09000000:
                cpu.mem_write(start, self.rom[start-flash.BASE:start-flash.BASE+size])
        cpu.mem_write(flash.OWNER, body)
        cpu.reg_write(UC_ARM_REG_SP, 0x03007000)
        chip, stores = BankedFlash(banks), []
        def write(uc, kind, address, size, value, data):
            self.assertEqual(size, 1)
            stores.append((address-flash.BUS, value))
            chip.write(address-flash.BUS, value)
        def read(uc, kind, address, size, value, data):
            self.assertEqual(size, 1)
            uc.mem_write(address, bytes([chip.read(address-flash.BUS)]))
        cpu.hook_add(UC_HOOK_MEM_WRITE, write, begin=flash.BUS, end=flash.BUS+65535)
        cpu.hook_add(UC_HOOK_MEM_READ, read, begin=flash.BUS, end=flash.BUS+65535)
        return cpu, stores

    def run_to(self, cpu, start, end):
        from unicorn.arm_const import UC_ARM_REG_PC
        cpu.emu_start(start|1, end, count=300)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), end)

    def test_all_argument_bytes_ordered_bus_cycles_and_banked_reads(self):
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_SP
        sentinel = 0x08141898
        for body, stripped in ((self.rom[0x14189c:0x1418c0], False), (self.qualified, False), (self.ordinary, True)):
            for banks in (1, 2):
                cpu, stores = self.machine(body, banks)
                for bank in [*range(256), 1, 0]:
                    stores.clear()
                    cpu.reg_write(UC_ARM_REG_LR, sentinel|1)
                    cpu.reg_write(UC_ARM_REG_R0, 0x847a5200 | bank)
                    self.run_to(cpu, flash.OWNER, sentinel)
                    expected = [(0x5555, 0xaa), (0x2aaa, 0x55), (0x5555, 0xb0), (0, bank)]
                    self.assertEqual(stores, expected[1:] if stripped else expected)
                    self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), 0x03007000)
                    # The SDK command's width is known for every input byte. Only make
                    # bank-content assertions for commands selecting an implemented bank.
                    if bank in (0, 1):
                        cpu.reg_write(UC_ARM_REG_R0, flash.BUS+0x254)
                        self.run_to(cpu, 0x08141aac, sentinel)
                        chosen = int(banks == 2 and bank == 1 and not stripped)
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_R0), (0x33, 0xa7)[chosen] ^ 0x54)

    def test_three_real_sector_guards_four_identified_descriptors(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_PC, UC_ARM_REG_SP
        cpu, stores = self.machine(self.qualified, 2)
        sentinel, global_type, synthetic = 0x08141898, 0x0200f370, 0x02008000
        def return_flash_id(uc, pc, size, data):
            uc.reg_write(UC_ARM_REG_R0, ident)
            uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))
        cpu.hook_add(UC_HOOK_CODE, return_flash_id, begin=0x081418c0, end=0x081418c0)
        for ident, setup in zip((0xd4bf, 0x1b32, 0x1cc2, 0x6bad), flash.SETUPS):
            cpu.reg_write(UC_ARM_REG_SP, 0x03007000)
            cpu.reg_write(UC_ARM_REG_LR, sentinel|1)
            self.run_to(cpu, 0x08141d9c, sentinel)
            self.assertEqual(struct.unpack('<I', cpu.mem_read(global_type,4))[0], setup+20)
            for start, end, _, _ in flash.CALLERS:
                cpu.reg_write(UC_ARM_REG_SP, 0x03007000)
                cpu.reg_write(UC_ARM_REG_R0, 16)
                stores.clear()
                self.run_to(cpu, start, end)
                self.assertEqual(stores, [])
        cpu.mem_write(global_type, struct.pack('<I', synthetic))
        cpu.mem_write(synthetic, struct.pack('<I', 0x20000))
        for start, end, _, _ in flash.CALLERS:
            for sector in (0, 15, 16, 31, 0x1020, 0xfff0):
                stores.clear()
                cpu.reg_write(UC_ARM_REG_R0, sector)
                cpu.reg_write(UC_ARM_REG_SP, 0x03007000)
                self.run_to(cpu, start, end)
                self.assertEqual(stores, [(0x5555, 0xaa), (0x2aaa, 0x55), (0x5555, 0xb0), (0, (sector>>4)&255)])


if __name__ == '__main__':
    unittest.main()
