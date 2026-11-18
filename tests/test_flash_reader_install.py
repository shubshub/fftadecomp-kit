"""Prove the FLASH512_V130 reader installer from its original O1 object and actual sector caller."""
import argparse
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_reader_install as install
import library_units as units
import match
import match_evidence as evidence
import test_flash_program_byte as program_tests


@unittest.skipUnless(os.environ.get('FFTA_FLASH_INSTALL_ROOT'), 'needs original game and SetReadFlash1 C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_INSTALL_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.original = cls.rom[install.ADDRESS - install.erase.BASE:install.END - install.erase.BASE]
        cls.linked, cls.report = install.build(cls.root, install.ADDRESS)
        tool = units.resolve(install.TOOLCHAIN)
        args = argparse.Namespace(cc=tool['cc'], flags=tool['flags'], cpp=match.DEFAULT_CPP,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, _ = match.compile_object(runner, workspace, args, cls.root, install.ADDRESS,
                                                  'src/08141AB0.c')

    def test_report_and_excluded_credit(self):
        self.assertEqual(self.original, self.linked)
        self.assertEqual(len(self.linked), 62)
        self.assertTrue(evidence.report_matches(self.report, str(self.root), install.ADDRESS))
        for fragment in ('"excluded_ROM_credit":0', '"destination_from_entry_sp":-84', install.SCHEMA):
            with self.subTest(fragment=fragment):
                altered = self.report.replace(fragment, fragment + '0')
                self.assertNotEqual(altered, self.report)
                self.assertFalse(evidence.report_matches(altered, str(self.root), install.ADDRESS))
        self.assertFalse(evidence.report_matches(self.report, str(self.root), install.READER))

    def test_original_and_duplicate_relocation_identity(self):
        image = match.elf_image(self.raw)
        install.original_literals(image)
        def section(name):
            return image['sections'][image['section_names'].index(name)][4]
        symbols = next(iter(image['symbol_tables'].values()))
        owner_id = next(i for i, s in enumerate(symbols) if s['name'] == install.NAME)
        for label, offset, value in (
                ('duplicate addend', section('.rodata') + 4, 1),
                ('live addend', section('.text') + 28, 1),
                ('self instead of reader', section('.rel.rodata') + 13, owner_id),
                ('self instead of slot', section('.rel.text') + 5, owner_id),
                ('wrong relocation type', section('.rel.rodata') + 20, 3),
                ('duplicate offset', section('.rel.rodata') + 16, 4),
                ('short owner', section('.symtab') + 16 * owner_id + 8, 60),
                ('hidden owner', section('.symtab') + 16 * owner_id + 13, 2)):
            with self.subTest(label=label):
                changed = bytearray(self.raw)
                self.assertNotEqual(changed[offset], value)
                changed[offset] = value
                with self.assertRaises(ValueError):
                    install.original_literals(match.elf_image(changed))

    def test_sector_caller_installs_and_executes_unsigned_byte_reader(self):
        from unicorn import UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_PC, UC_ARM_REG_SP
        helper = program_tests.NativeTests()
        helper.rom = self.rom
        for label, body in (('original', self.original), ('linked', self.linked)):
            with self.subTest(label=label):
                cpu, chip, _, reads = helper.machine(self.rom[0x141fc8:0x142000], 0xd4bf)
                cpu.mem_write(install.ADDRESS, body)
                local = cpu.reg_read(UC_ARM_REG_SP) - 84
                writes = []
                def watch(uc, access, address, width, value, data):
                    if install.ADDRESS <= uc.reg_read(UC_ARM_REG_PC) < install.END:
                        writes.append((address, width, value))
                cpu.hook_add(UC_HOOK_MEM_WRITE, watch)
                helper.invoke(cpu, install.erase.OWNER, (1,), end=0x08141f7a)
                self.assertEqual(cpu.reg_read(UC_ARM_REG_SP), local)
                self.assertEqual(writes, [(local - 4, 4, 0x08141f7b), (install.GLOBAL, 4, local | 1),
                                          (local, 2, 0x7800), (local + 2, 2, 0x4770)])
                entry, = struct.unpack('<I', cpu.mem_read(install.GLOBAL, 4))
                self.assertEqual(entry, local | 1)
                self.assertEqual(cpu.mem_read(local, 4), self.rom[0x141aac:0x141ab0])
                for offset, value in enumerate((0, 127, 128, 255), start=0xe000):
                    chip.storage[offset] = value
                    self.assertEqual(helper.invoke(cpu, entry, (program_tests.BUS + offset,)), value)
                self.assertEqual(reads, list(range(0xe000, 0xe004)))


if __name__ == '__main__':
    unittest.main()
