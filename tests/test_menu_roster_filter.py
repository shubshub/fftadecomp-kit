import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import menu_roster_filter as filt
import owner_admission_profile as admission


@unittest.skipUnless(os.getenv('FFTA_ROSTER_FILTER_ROOT'), 'requires USA ROM, agbcc and original roster filter')
class MenuRosterFilterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ROSTER_FILTER_ROOT']).resolve()
        cls.result = admission.build(cls.root, filt.OWNER, selector=filt.named.ROSTER_FILTER_SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_original_elf_and_report(self):
        import match
        from match_evidence import report_matches
        original, targets = admission.original_bindings(match.elf_image(self.elf), filt.OWNER,
                    self.rom, self.mapping, self.objects, selector=filt.named.ROSTER_FILTER_SELECTOR, index=self.index)
        self.assertEqual(original, filt.bindings())
        self.assertEqual(targets, {'g_state_02000000': (0x02000000, True), 'data_0200F428': (filt.SLOT, True),
                                  'func_08071DC8': (filt.roster.OWNER, False)})
        report = admission.render(filt.OWNER, self.result)
        self.assertTrue(report_matches(report, self.root, filt.OWNER))
        for old, new in (('"other_scene_size":7548', '"other_scene_size":12192'),
                         ('"excluded_kinds":[0,2,15]', '"excluded_kinds":[2,15]')):
            self.assertIn(old, report)
            self.assertFalse(report_matches(report.replace(old, new), self.root, filt.OWNER))

    def test_producer_filter_lifetime_and_consumer_mutations(self):
        for site in (0x0805454A, 0x08071E04, 0x08087DBE, 0x0808A138, 0x08054468,
                     0x080544F8, 0x08050F98, 0x08055C7E, 0x08022840, 0x08007170):
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site - 0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    admission.verify(self.body, filt.OWNER, bytes(rom), self.mapping, self.index, self.objects,
                                     bindings=filt.bindings(), selector=filt.named.ROSTER_FILTER_SELECTOR)

    def test_source_extent_and_relocation_addend(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            file = Path('src/0805451C.c')
            text = (self.root/file).read_text()
            for old, new in (('indices[24]', 'indices[23]'), ('units[24]', 'units[31]'),
                             ('unknown_00[4]', 'unknown_00[5]')):
                self.assertIn(old, text)
                (tree/file).write_text(text.replace(old, new))
                with self.assertRaisesRegex(ValueError, 'roster fields'):
                    filt.check_source(tree, filt.OWNER)
        actual = filt.bindings()
        actual['data'][0][2] = 0
        with self.assertRaises(ValueError):
            admission.verify(self.body, filt.OWNER, self.rom, self.mapping, self.index, self.objects,
                             bindings=actual, selector=filt.named.ROSTER_FILTER_SELECTOR)

    def call(self, cpu, address, *args, return_at=None):
        from test_bg_affine_rows import NativeAffineRows
        if return_at is None:
            return NativeAffineRows.call(self, cpu, address, *args)
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_SP
        for reg, value in zip((UC_ARM_REG_R0, UC_ARM_REG_R1), args):
            cpu.reg_write(reg, value)
        cpu.reg_write(UC_ARM_REG_SP, 0x03007F00)
        cpu.reg_write(UC_ARM_REG_LR, 0x03007001)
        cpu.emu_start(address | 1, return_at, count=500000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), return_at)
        return cpu.reg_read(UC_ARM_REG_R0)

    def test_real_heap_menu_constructor_filter_sorter_consumer_and_release(self):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R7

        cpu = TransferTaskTests.cpu(self)
        allocation, releases = [], []
        def trace(machine, address, width, context):
            context.append(machine.reg_read(UC_ARM_REG_R0))
        cpu.hook_add(UC_HOOK_CODE, trace, allocation, begin=0x08022840, end=0x08022840)
        cpu.hook_add(UC_HOOK_CODE, trace, releases, begin=0x08022854, end=0x08022854)
        self.call(cpu, 0x080227E8)
        state = 0x02012000
        cpu.mem_write(state, b'\x00')
        self.call(cpu, filt.BANK, 0, state, return_at=0x08054422)
        word = lambda address: int.from_bytes(cpu.mem_read(address, 4), 'little')
        bank = word(filt.SLOT)
        self.assertEqual(allocation, [filt.SIZE])
        self.assertTrue(0x020159D0 <= bank < bank + filt.SIZE <= 0x02040000)
        self.assertEqual(bytes(cpu.mem_read(bank, filt.SIZE)), bytes(filt.SIZE))

        def run(mode, rows):
            data = bytearray(24 * 0x108)
            for slot, kind, active in rows:
                data[slot * 0x108 + 4] = kind
                data[slot * 0x108 + 9] = 35 - slot
                data[slot * 0x108 + 0xF0] = active
            cpu.mem_write(0x02000080, bytes(data))
            cpu.mem_write(0x020020E4, bytes([mode]))
            cpu.mem_write(bank+filt.LIST-1, b'\xDA' * 27)
            cpu.reg_write(UC_ARM_REG_R7, filt.SLOT)
            self.call(cpu, 0x08055C72, return_at=0x08055C80)
            count = cpu.reg_read(UC_ARM_REG_R0)
            self.assertEqual(bytes(cpu.mem_read(bank+filt.LIST+24, 2)), bytes([count, 0xDA]))
            self.assertEqual(bytes(cpu.mem_read(bank+filt.LIST-1, 1)), b'\xDA')
            result = bytes(cpu.mem_read(bank+filt.LIST, count))
            self.assertEqual(bytes(cpu.mem_read(bank+filt.LIST+count, 24-count)), b'\xDA'*(24-count))
            return list(result)

        dense = [(i, 1, 1) for i in range(24)]
        self.assertEqual(run(0, dense), list(reversed(range(24))))
        self.assertEqual(run(0x80, dense), list(range(24)))
        self.assertEqual(run(1, dense), list(range(24)))
        self.assertEqual(run(0x81, dense), list(reversed(range(24))))
        sparse = [(0, 3, 1), (2, 2, 1), (5, 15, 1), (9, 6, 0), (16, 7, 1), (23, 8, 2)]
        self.assertEqual(run(0x81, sparse), [23, 16, 0])
        self.assertEqual(run(1, sparse), [0, 16, 23])
        self.assertEqual(run(0, [(0, 1, 1), (2, 1, 1)]), [])
        self.assertEqual(run(0x80, []), [])
        self.assertEqual(filt.index_domain()['reverse_default_witness']['output'], [1, 253])

        cpu.mem_write(state, b'\xfe')
        self.call(cpu, filt.BANK, 0, state, return_at=0x08054500)
        self.assertEqual(releases, [bank])
        self.assertEqual(word(filt.SLOT), 0)
        cpu.mem_write(state, b'\x00')
        self.call(cpu, 0x08050F1C, 0, state, return_at=0x08050F52)
        self.assertEqual(allocation, [filt.SIZE, 0x1D7C])
        self.assertTrue(word(filt.SLOT))
        self.assertLess(allocation[-1], filt.LIST)
