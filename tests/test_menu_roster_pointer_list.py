import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import menu_roster_pointer_list as listing
import owner_admission_profile as admission

SELECTOR = listing.filters.named.ROSTER_FILTER_SELECTOR


@unittest.skipUnless(os.getenv('FFTA_ROSTER_POINTER_ROOT'), 'requires the USA ROM, source and agbcc')
class MenuRosterPointerListTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ROSTER_POINTER_ROOT']).resolve()
        cls.result = admission.build(cls.root, listing.OWNER, selector=SELECTOR)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_original_bindings_and_saved_receipt(self):
        import match
        from match_evidence import report_matches
        address = listing.OWNER
        original, targets = admission.original_bindings(match.elf_image(self.elf), address, self.rom,
                    self.mapping, self.objects, selector=SELECTOR, index=self.index)
        self.assertEqual(original, listing.bindings())
        self.assertEqual(targets, {'g_state_020020D0': (listing.STATE, True), 'g_state_02000080': (listing.ROSTER, True),
                                 'func_08071DC8': (listing.filters.roster.OWNER, False),
                                 'func_080C7EA4': (listing.ACCESSOR, False)})
        self.assertEqual(self.body, self.rom[0x67FFC:0x6807C])
        report = admission.render(address, self.result)
        self.assertTrue(report_matches(report, self.root, address))
        self.assertIn('"enabled_allocation":22', report)
        self.assertFalse(report_matches(report.replace('"enabled_allocation":22', '"enabled_allocation":24'),
                                        self.root, address))

    def test_original_code_and_role_mutations(self):
        for site in (0x0806802C, 0x08068032, 0x0806805A, 0x08071E04, 0x080C7EC4, 0x080C7FD8,
                     0x08064F16, 0x08064F76, 0x08065024, 0x080652A2, 0x080661C0, 0x08066404,
                     0x0806643C, 0x08393A24+7*16+4):
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site-0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    admission.verify(self.body, listing.OWNER, bytes(rom), self.mapping, self.index, self.objects,
                                     bindings=listing.bindings(), selector=SELECTOR)
        for key in ('calls', 'data'):
            bindings = listing.bindings()
            bindings[key].pop()
            with self.assertRaises(ValueError):
                admission.verify(self.body, listing.OWNER, self.rom, self.mapping, self.index, self.objects,
                                 bindings=bindings, selector=SELECTOR)

    def test_declared_accessor_and_roster_capacity(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as directory:
            tree = Path(directory)
            (tree/'src').mkdir()
            (tree/'include').mkdir()
            (tree/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            file = Path('src/08067FFC.c')
            text = (self.root/file).read_text()
            for old, new in (('extern s32 func_080C7EA4', 'extern u8 func_080C7EA4'),
                             ('g_state_02000080[24]', 'g_state_02000080[]'), ('indices[24]', 'indices[23]')):
                self.assertIn(old, text)
                (tree/file).write_text(text.replace(old, new))
                with self.assertRaisesRegex(ValueError, 'accessor return'):
                    listing.check_source(tree)

    def call(self, cpu, address, *args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self, cpu, address, *args)

    def make_cpu(self, mode, records):
        from test_packed_transfer_task import TransferTaskTests
        cpu = TransferTaskTests.cpu(self)
        units = bytearray(24*0x108)
        for slot, kind, flags in records:
            base = slot*0x108
            units[base+4] = kind
            units[base+9] = 35-slot
            struct.pack_into('<H', units, base+0x28, flags)
        cpu.mem_write(listing.ROSTER, bytes(units))
        cpu.mem_write(listing.STATE+0x14, bytes([mode]))
        return cpu

    def test_optional_output_count_and_order(self):
        records = [(i, kind, 0) for i, kind in enumerate((1, 2, 8, 0x5E, 10, 4, 9, 12, 3, 0, 5))]
        for mode, accepted in ((1, [0,8,10]), (0x81, [10,8,0]), (0x80, [0,8,10])):
            cpu = self.make_cpu(mode, records)
            output = 0x02012004
            cpu.mem_write(output-4, b'\xa5'*104)
            self.assertEqual(self.call(cpu, listing.OWNER, 0), len(accepted))
            self.assertEqual(bytes(cpu.mem_read(output-4,104)), b'\xa5'*104)
            self.assertEqual(self.call(cpu, listing.OWNER, output), len(accepted))
            expected = b''.join(struct.pack('<I', listing.ROSTER+0x108*i) for i in accepted)
            self.assertEqual(bytes(cpu.mem_read(output-4,104)), b'\xa5'*4 + expected + b'\xa5'*(100-len(expected)))
            # The accessor has an integer result for all selectors; only selector one returns this byte.
            cpu.mem_write(listing.ROSTER, b'\x00\x00\x00\x80')
            self.assertEqual(self.call(cpu, listing.ACCESSOR, listing.ROSTER, 0), 0x80000000)
            self.assertEqual(self.call(cpu, listing.ACCESSOR, listing.ROSTER, 1), 1)
        self.assertEqual(self.call(self.make_cpu(0x80, []), listing.OWNER, 0), 0)
        cpu = self.make_cpu(0x80, [(i, 1, 0) for i in range(24)])
        output = 0x02012004
        cpu.mem_write(output-4, b'X'*104)
        self.assertEqual(self.call(cpu, listing.OWNER, output), 24)
        self.assertEqual(struct.unpack('<24I', cpu.mem_read(output,96)),
                         tuple(listing.ROSTER+0x108*i for i in range(24)))
        self.assertEqual((cpu.mem_read(output-4,4), cpu.mem_read(output+96,4)), (b'XXXX', b'XXXX'))

    def test_original_scheduler_list_count_pointer_consumption_and_separate_byte_capacity(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_SP
        for flagged in (0, 21):
            cpu = self.make_cpu(0x80, [(i, 1, 4 if i == flagged else 0) for i in range(22)])
            read_word = lambda address: int.from_bytes(cpu.mem_read(address,4), 'little')
            requests, events, enabled_writes = [], [], []
            def observe(machine, address, width, context):
                r0 = machine.reg_read(UC_ARM_REG_R0)
                if address in (0x08022840, 0x08005B28):
                    requests.append(r0)
                if address == listing.EVENT:
                    events.append(int.from_bytes(machine.mem_read(machine.reg_read(UC_ARM_REG_R1),2),'little'))
            for address in (listing.EVENT, 0x08005B28, 0x08022840):
                cpu.hook_add(UC_HOOK_CODE, observe, begin=address, end=address)
            self.call(cpu, 0x080227E8)
            self.call(cpu, listing.BANK, 0, 0x02012000)
            bank = read_word(listing.SLOT)
            manager = read_word(bank)
            self.assertTrue(0x020159D0 <= bank < manager < bank+0x3800 <= 0x02040000)
            task = self.call(cpu, 0x08064FA0, 7)
            context = task+24
            self.assertEqual((read_word(context), cpu.mem_read(context+8,1)[0]), (bank,7))
            word = bytes([0xCE])*4
            cpu.mem_write(bank+listing.TABLE-4, word)
            cpu.mem_write(bank+listing.TABLE+0x5E0, word)
            def store(machine, access, address, width, value, context_):
                if machine.reg_read(UC_ARM_REG_PC) == 0x0806643C:
                    enabled_writes.append(address - read_word(context+0x98))
            cpu.hook_add(UC_HOOK_MEM_WRITE, store)
            cpu.reg_write(UC_ARM_REG_R0, manager)
            cpu.reg_write(UC_ARM_REG_LR, 0x03007001)
            cpu.reg_write(UC_ARM_REG_SP, 0x03007F00)
            cpu.emu_start(0x08005A25, 0x0806645A, count=500000)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), 0x0806645A)
            self.assertEqual((requests,events), ([0x3800,22],[0,0x100]))
            self.assertEqual(enabled_writes, [flagged])
            self.assertEqual(int.from_bytes(cpu.mem_read(bank+14,2),'little'),22)
            self.assertEqual(struct.unpack('<22I', cpu.mem_read(bank+listing.TABLE,88)),
                             tuple(listing.ROSTER+0x108*i for i in range(22)))
            self.assertEqual(bytes(cpu.mem_read(bank+listing.TABLE+88, 0x5E0-88)), bytes(0x5E0-88))
            for guard in (bank+listing.TABLE-4, bank+listing.TABLE+0x5E0):
                self.assertEqual(cpu.mem_read(guard,4), word)

    def test_live_allocation_release(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0
        cpu = self.make_cpu(0x80, [])
        calls = []
        cpu.hook_add(UC_HOOK_CODE, lambda m,a,w,c: calls.append(m.reg_read(UC_ARM_REG_R0)),
                     begin=0x08022854, end=0x08022854)
        self.call(cpu, 0x080227E8)
        phase = 0x02012000
        self.call(cpu, listing.BANK, 0, phase)
        bank = int.from_bytes(cpu.mem_read(listing.SLOT,4),'little')
        self.assertTrue(bank)
        cpu.mem_write(phase, b'\xff')
        self.call(cpu, listing.BANK, 0, phase)
        self.assertEqual(calls,[bank])
        self.assertEqual(cpu.mem_read(listing.SLOT,4),bytes(4))
        self.assertEqual(cpu.mem_read(phase,1), b'\x02')
