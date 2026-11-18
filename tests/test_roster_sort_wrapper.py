import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import unit_roster_sort as roster


@unittest.skipUnless(os.getenv('FFTA_ROSTER_SORT_ROOT'), 'requires USA ROM, sort sources and agbcc')
class RosterSortWrapperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ROSTER_SORT_ROOT']).resolve()
        cls.selector = roster.named.ROSTER_SORT_SELECTOR
        cls.result = owner.build(cls.root, roster.SORT, selector=cls.selector)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_complete_original_and_replay(self):
        import match
        from match_evidence import report_matches

        report = owner.render(roster.SORT, self.result)
        self.assertEqual(self.body, self.rom[0x87D98:0x87F0A])
        actual, targets = owner.original_bindings(match.elf_image(self.elf), roster.SORT, self.rom,
                self.mapping, self.objects, selector=self.selector, index=self.index)
        self.assertEqual(actual, dict(calls=[[n, 'func_0808A0B4'] for n in (166, 180, 336, 350)],
                                      data=[], functions=[], switches=[]))
        self.assertEqual(targets, {'func_0808A0B4': (roster.PARTITION, False)})
        self.assertTrue(report_matches(report, self.root, roster.SORT))
        self.assertIn('"reverse_reads":192', report)
        self.assertFalse(report_matches(report.replace('"reverse_reads":192', '"reverse_reads":8'),
                                        self.root, roster.SORT))

    def test_changed_original_caller_child_and_roles(self):
        import match
        original, _ = owner.original_bindings(match.elf_image(self.elf), roster.SORT, self.rom,
                self.mapping, self.objects, selector=self.selector, index=self.index)
        for site in (0x08071E68, 0x08087DB4, 0x08087DBC, 0x08087E5C, 0x08087E66, 0x0808A138):
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site - match.ROM_BASE] ^= 1
                with self.assertRaises(ValueError):
                    owner.verify(self.body, roster.SORT, bytes(rom), self.mapping, self.index, self.objects,
                                 bindings=original, selector=self.selector)
        original['calls'].pop()
        with self.assertRaisesRegex(ValueError, 'wrapper roles'):
            owner.verify(self.body, roster.SORT, self.rom, self.mapping, self.index, self.objects,
                         bindings=original, selector=self.selector)

    def test_signed_layout_local_capacity_and_abi(self):
        with tempfile.TemporaryDirectory(dir=self.root / 'build') as name:
            tree = Path(name)
            (tree / 'src').mkdir()
            (tree / 'include').mkdir()
            header = 'include/ffta.h'
            source = 'src/08087D98.c'
            (tree / header).write_bytes((self.root / header).read_bytes())
            original = (self.root / source).read_text()
            for old, new in (('s32 key;', 'u32 key;'), ('s32 descending)', 'u8 descending)'),
                             ('copy[24]', 'copy[23]'), ('extern void', 'extern s32')):
                with self.subTest(old=old):
                    self.assertIn(old, original)
                    (tree / source).write_text(original.replace(old, new))
                    with self.assertRaisesRegex(ValueError, 'sort pair declarations'):
                        roster.check_source(tree, roster.SORT)

    def setUp(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
        self.uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.uc.mem_map(0x02000000, 0x40000)
        self.uc.mem_map(0x03000000, 0x8000)
        self.uc.mem_map(0x08000000, 0x100000)
        self.uc.mem_write(0x08000000, self.rom[:0x100000])

    def call(self, addr, *args):
        from test_bg_affine_rows import NativeAffineRows
        NativeAffineRows.call(self, self.uc, addr, *args)

    def test_inclusive_subranges_and_reverse_prefix(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_PC
        base = 0x02010008
        records = [(key, i-17) for i, key in enumerate((7, -0x80000000, 0x7fffffff, -1, 7, 0) * 4)]
        original = b''.join(struct.pack('<ii', *row) for row in records)
        trace = []
        def access(cpu, kind, addr, size, value, _):
            trace.append((cpu.reg_read(UC_ARM_REG_PC), kind, addr - base, size))
        self.uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, access, begin=base-8, end=base+199)
        for left, right in ((0, 0), (23, 23), (3, 9), (2, 23), (0, 23)):
            for direction in (0, 1, -1, 0x100):
                with self.subTest(left=left, right=right, direction=direction):
                    self.uc.mem_write(base-8, b'X' * 8 + original + b'Y' * 8)
                    trace.clear()
                    self.call(roster.SORT, base, left, right, direction)
                    result = list(struct.iter_unpack('<ii', self.uc.mem_read(base, 192)))
                    if direction:
                        self.assertEqual([(off, size) for pc, kind, off, size in trace
                                          if kind == UC_MEM_READ],
                                         [(off, 4) for off in range(0, 192, 4)])
                        self.assertTrue(all(pc == 0x08087DBE for pc, kind, _, _ in trace
                                            if kind == UC_MEM_READ))
                        self.assertEqual([(pc, off, size) for pc, kind, off, size in trace
                                          if kind != UC_MEM_READ],
                                         [(0x08087E66, off, 4) for off in range(0, 8*(right+1), 4)])
                        result[:right+1] = reversed(result[:right+1])
                    else:
                        self.assertTrue(trace)
                        self.assertTrue(all(8 * left <= off and off + size <= 8 * (right+1)
                                            for _, _, off, size in trace))
                    self.assertEqual(result[:left], records[:left])
                    self.assertEqual(result[right+1:], records[right+1:])
                    active = result[left:right+1]
                    self.assertCountEqual(active, records[left:right+1])
                    self.assertEqual([key for key, value in active], sorted(key for key, value in active))
                    self.assertEqual(bytes(self.uc.mem_read(base-8, 8)), b'X' * 8)
                    self.assertEqual(bytes(self.uc.mem_read(base+192, 8)), b'Y' * 8)

    def test_equal_keys_can_exchange_payloads(self):
        base = 0x02010008
        self.uc.mem_write(base, struct.pack('<iiii', -3, 12, -3, 19))
        self.call(roster.SORT, base, 0, 1, 0)
        self.assertEqual(struct.unpack('<iiii', self.uc.mem_read(base, 16)), (-3, 19, -3, 12))

    def test_real_caller_supplies_its_24_record_frame(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3
        calls = []
        def enter(cpu, addr, size, _):
            calls.append(tuple(cpu.reg_read(reg) for reg in
                               (UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)))
        self.uc.hook_add(UC_HOOK_CODE, enter, begin=roster.SORT, end=roster.SORT)
        for i in (0, 9, 23):
            self.uc.mem_write(roster.BASE + 0x80 + i * roster.STRIDE + 4, b'\x01')
        frame = 0x03007F00 - 216
        for mode in range(1, 7):
            for flag in (0, 0x80):
                calls.clear()
                self.call(roster.OWNER, mode | flag, 0x02011000)
                self.assertEqual(calls, [(frame, frame, 0, 2, int(flag == 0))])
