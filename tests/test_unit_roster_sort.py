import os
from pathlib import Path
import tempfile
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import unit_roster_sort as roster


@unittest.skipUnless(os.getenv('FFTA_ROSTER_SORT_ROOT'), 'requires the USA ROM, roster source and agbcc')
class UnitRosterSortTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ROSTER_SORT_ROOT']).resolve()
        cls.result = owner.build(cls.root, roster.OWNER, selector=roster.named.ROSTER_SORT_SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_original_object_and_report(self):
        import match
        from match_evidence import report_matches

        report = owner.render(roster.OWNER, self.result)
        self.assertTrue(report_matches(report, self.root, roster.OWNER))
        self.assertIn('"reverse_reads":192', report)
        self.assertFalse(report_matches(report.replace('"reverse_reads":192', '"reverse_reads":8'),
                                        self.root, roster.OWNER))
        self.assertEqual(self.body, self.rom[0x71DC8:0x72130])
        image = match.elf_image(self.elf)
        actual, targets = owner.original_bindings(image, roster.OWNER, self.rom, self.mapping, self.objects,
                                                  selector=roster.named.ROSTER_SORT_SELECTOR, index=self.index)
        self.assertEqual(actual, roster.bindings())
        self.assertEqual(targets, {'g_state_02000000': (roster.BASE, True),
                                   'func_08087D98': (roster.SORT, False)})

    def test_refuses_changed_native_dependencies_and_roles(self):
        for site in (0x08071E04, 0x08071EC8, 0x08087DBE, 0x08087E62, 0x0808A138,
                     0x08073B8C, 0x080306DC, 0x08061220, 0x080B8182):
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site - 0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    owner.verify(self.body, roster.OWNER, bytes(rom), self.mapping, self.index, self.objects,
                                 bindings=roster.bindings(), selector=roster.named.ROSTER_SORT_SELECTOR)
        for name in ('calls', 'data', 'switches'):
            invalid = roster.bindings()
            invalid[name].pop()
            with self.assertRaises(ValueError):
                owner.verify(self.body, roster.OWNER, self.rom, self.mapping, self.index, self.objects,
                             bindings=invalid, selector=roster.named.ROSTER_SORT_SELECTOR)

    def test_source_array_and_field_layout_controls(self):
        with tempfile.TemporaryDirectory(dir=self.root / 'build') as directory:
            tree = Path(directory)
            (tree / 'src').mkdir()
            (tree / 'include').mkdir()
            header = 'include/ffta.h'
            source = 'src/08071DC8.c'
            (tree / header).write_bytes((self.root / header).read_bytes())
            original = (self.root / source).read_text()
            for old, new in (('units[24]', 'units[23]'), ('list[24]', 'list[25]'),
                             ('s32 key;', 'u32 key;'), ('u16 value;', 's16 value;')):
                with self.subTest(old=old):
                    self.assertIn(old, original)
                    (tree / source).write_text(original.replace(old, new))
                    with self.assertRaisesRegex(ValueError, 'roster declarations'):
                        roster.check_source(tree, roster.OWNER)

    def setUp(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        self.cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for base, length in ((0x02000000, 0x40000), (0x03000000, 0x8000), (0x08000000, 0x100000)):
            self.cpu.mem_map(base, length)
        self.cpu.mem_write(0x08000000, self.rom[:0x100000])
        self.stack = 0x03007000
        self.output = 0x02010011
        self.stop = 0x080000B0

    def execute(self, addr, end):
        from unicorn.arm_const import UC_ARM_REG_PC
        self.cpu.emu_start(addr | 1, end, count=160000)
        self.assertEqual(self.cpu.reg_read(UC_ARM_REG_PC), end)

    def prepare(self, slots, seed=0):
        data = bytearray(roster.STRIDE * roster.COUNT)
        self.fields = {}
        for i in slots:
            rank = (i * 3) % 7
            fields = (255 - rank, 65535 - rank, rank * 257, 32768 + rank, rank, 2 - i % 2)
            self.fields[i] = fields
            for offset, width, value in zip((9, 0x1A, 0x1E, 0xD6, 6, 4), (1, 2, 2, 2, 1, 1), fields):
                start = i * roster.STRIDE + offset
                data[start:start + width] = value.to_bytes(width, 'little')
        self.cpu.mem_write(roster.BASE + 0x80, bytes(data))
        self.cpu.mem_write(self.stack - 1280, bytes([seed]) * 1280)

    def run_sort(self, mode, end=None):
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_SP

        self.cpu.mem_write(self.output - 5, b'\x51' * 34)
        self.cpu.reg_write(UC_ARM_REG_LR, self.stop | 1)
        self.cpu.reg_write(UC_ARM_REG_SP, self.stack)
        self.cpu.reg_write(UC_ARM_REG_R0, mode)
        self.cpu.reg_write(UC_ARM_REG_R1, self.output)
        self.execute(roster.OWNER, self.stop if end is None else end)
        self.assertEqual(bytes(self.cpu.mem_read(self.output - 5, 5)), b'\x51' * 5)
        self.assertEqual(bytes(self.cpu.mem_read(self.output + 24, 5)), b'\x51' * 5)
        if end is None:
            self.assertEqual(self.cpu.reg_read(UC_ARM_REG_SP), self.stack)
        return bytes(self.cpu.mem_read(self.output, 24))

    def test_all_sort_modes_all_nonempty_lengths(self):
        for count in range(1, 25):
            slots = sorted((i * 13) % 24 for i in range(count))
            for mode in range(1, 7):
                for descending in (False, True):
                    with self.subTest(count=count, mode=mode, descending=descending):
                        self.prepare(slots, seed=0x5A if descending else 0xA8)
                        output = self.run_sort(mode | (0 if descending else 0x80))
                        self.assertEqual(output[count:], b'\xff' * (24 - count))
                        self.assertEqual(sorted(output[:count]), slots)
                        if mode == 6:
                            keys = [self.fields[i][5] for i in output[:count]]
                            self.assertEqual(keys, sorted(keys, reverse=descending))
                        else:
                            expected = sorted(slots, key=lambda i: (self.fields[i][mode-1], i),
                                              reverse=descending)
                            self.assertEqual(list(output[:count]), expected)

    def test_reverse_native_copy_reads_full_frame_only_and_suffix_is_dead(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_PC

        original = [1, 7, 16, 22]
        local = self.stack - 216
        reads, writes = [], []
        def access(cpu, kind, addr, size, value, records):
            records.append((cpu.reg_read(UC_ARM_REG_PC), addr, size))
        self.cpu.hook_add(UC_HOOK_MEM_READ, access, reads, begin=local, end=local+191)
        self.cpu.hook_add(UC_HOOK_MEM_WRITE, access, writes, begin=local, end=local+191)
        for mode in (2, 0x82):
            results = []
            for seed in (0x00, 0xDB):
                self.prepare(original, seed)
                reads.clear()
                writes.clear()
                results.append(self.run_sort(mode))
                suffix = local + 8 * len(original)
                self.assertFalse(any(addr + size > suffix for _, addr, size in writes))
                copied = [(addr, size) for pc, addr, size in reads if pc == 0x08087DBE]
                self.assertEqual(copied, [] if mode & 0x80 else [(local+i, 4) for i in range(0, 192, 4)])
                self.assertFalse(any(addr + size > suffix and pc != 0x08087DBE for pc, addr, size in reads))
            self.assertEqual(*results)

    def test_default_all_mode_bytes_and_empty_precondition(self):
        from unicorn.arm_const import UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3
        for slots in ([], [0, 1, 2], [0, 4, 7, 23]):
            self.prepare(slots)
            for mode in range(256):
                if 1 <= (mode & 0x7f) <= 6:
                    continue
                expected = [i if mode & 0x80 else (len(slots) - 1 - i) % 256 for i in slots]
                self.assertEqual(self.run_sort(mode), bytes(expected + [255] * (24 - len(slots))))
        self.prepare([])
        for mode in (1, 0x86):
            self.run_sort(mode, end=roster.SORT)
            self.assertEqual(self.cpu.reg_read(UC_ARM_REG_R1), 0)
            self.assertEqual(self.cpu.reg_read(UC_ARM_REG_R2), 0xffffffff)
            self.assertEqual(self.cpu.reg_read(UC_ARM_REG_R3), int(mode < 128))

    def test_original_mode_producers_and_both_consuming_calls(self):
        from unicorn.arm_const import (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R4, UC_ARM_REG_R7, UC_ARM_REG_R8,
                                      UC_ARM_REG_R9, UC_ARM_REG_SP)
        state = 0x020020D0
        self.execute(0x080306D8, 0x080306DE)
        self.assertEqual(bytes(self.cpu.mem_read(state + 20, 1)), b'\x80')
        self.cpu.reg_write(UC_ARM_REG_R4, 0)
        for current in range(5):
            self.cpu.mem_write(state + 21, bytes([current]))
            self.execute(0x08073C48, 0x08073C5E)
            self.assertEqual(bytes(self.cpu.mem_read(state + 21, 1)), bytes([(current + 1) % 5]))
        self.cpu.reg_write(UC_ARM_REG_R7, state)
        self.cpu.mem_write(state + 21, b'\x03')
        self.execute(0x08073B82, 0x08073B90)
        self.assertEqual(self.cpu.reg_read(UC_ARM_REG_R0), 0x83)
        self.cpu.reg_write(UC_ARM_REG_R1, 0x83)
        self.execute(0x08073BA8, 0x08073BAE)
        self.assertEqual(bytes(self.cpu.mem_read(state + 20, 1)), b'\x03')
        self.prepare([0, 1, 16])
        for call, resume, register in ((0x0806121A, 0x08061224, UC_ARM_REG_R9),
                                       (0x080B817C, 0x080B8186, UC_ARM_REG_R8)):
            self.cpu.reg_write(UC_ARM_REG_SP, self.stack)
            self.cpu.reg_write(register, self.output)
            self.execute(call, resume)
            expected = sorted(self.fields, key=lambda i: (self.fields[i][2], i), reverse=True)
            self.assertEqual(bytes(self.cpu.mem_read(self.output, 24)), bytes(expected + [255] * 21))
