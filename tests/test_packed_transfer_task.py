import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import packed_transfer_task as task


@unittest.skipUnless(os.getenv('FFTA_TRANSFER_TASK_ROOT'), 'requires USA ROM, agbcc and the transfer task source')
class TransferTaskTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_TRANSFER_TASK_ROOT']).resolve()
        cls.result = owner.build(cls.root, task.OWNER, selector=task.SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result
        cls.report = owner.render(task.OWNER, cls.result)

    def test_report_and_native_count_domain(self):
        from match_evidence import report_matches

        self.assertEqual(self.body, self.rom[0x5EF8:0x5FC4])
        self.assertTrue(report_matches(self.report, self.root, task.OWNER))
        for old, new in (('"max_count":5453', '"max_count":5454'), ('204/204 bytes', '203/204 bytes'),
                         ('"allocation_success_proved":false', '"allocation_success_proved":true')):
            self.assertIn(old, self.report)
            self.assertFalse(report_matches(self.report.replace(old, new), self.root, task.OWNER))
        self.assertEqual(task.count_domain(self.rom)['counts_checked'], 65536)
        self.assertEqual(task.allocation(5453), (65500, 65528, 65512))
        self.assertLess(task.allocation(5454)[1], task.allocation(5454)[2])
        self.assertEqual(task.allocation(5456)[:2], (0, 28))
        for value in (-1, 65536, True):
            with self.assertRaises(ValueError):
                task.allocation(value)

    def test_provider_mutations(self):
        for address in (0x08006896, 0x08005970, 0x08005984, 0x08005A70, 0x080058E0,
                        0x08006EC0, 0x081443FC, 0x0836D4B8, 0x08A38A2C):
            with self.subTest(address=hex(address)):
                bad = bytearray(self.rom)
                bad[address - 0x08000000] ^= 1
                with self.assertRaises(ValueError):
                    owner.verify(self.body, task.OWNER, bytes(bad), self.mapping, self.index, self.objects,
                                 bindings=task.bindings(), selector=task.SELECTOR)

    def test_original_relocations_and_source_controls(self):
        import match

        image = match.elf_image(self.elf)
        valid, targets = owner.original_bindings(image, task.OWNER, self.rom, self.mapping, self.objects,
                                                selector=task.SELECTOR, index=self.index)
        self.assertEqual(valid, task.bindings())
        for name in ('func_081443FC', '_call_via_r2'):
            bad = copy.deepcopy(valid)
            bad['calls'][0][1] = name
            with self.assertRaises(ValueError):
                task.check_original(bad, targets, image)
        symbol = next(s for s in image['symbols'] if s['name'] == 'memcpy')
        for site, override in ((0x38, {}), (0x3a, {'size': 12}), (0x3a, {'section': 1})):
            with self.assertRaises(ValueError):
                task.original_target(image, task.OWNER, site, {**symbol, **override})
        with tempfile.TemporaryDirectory(dir=self.root / 'build') as directory:
            tree = Path(directory)
            (tree / 'src').mkdir()
            (tree / 'include').mkdir()
            (tree / 'include/ffta.h').write_bytes((self.root / 'include/ffta.h').read_bytes())
            original = (self.root / task.SOURCE).read_text()
            for old, new in (('payload->entries[index] = entries[index];',
                              'memcpy(&payload->entries[index], &entries[index], sizeof(TransferEntry));'),
                             ('__attribute__((packed)) TransferEntry', 'TransferEntry'),
                             ('sizeof(payload->progress)', 'sizeof(payload->progress) - 1')):
                self.assertIn(old, original)
                (tree / task.SOURCE).write_text(original.replace(old, new))
                with self.assertRaisesRegex(ValueError, 'packed entry assignment'):
                    task.check_source(tree, task.OWNER)

    def cpu(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_PC

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for address, size in ((0x08000000, len(self.rom)), (0x02000000, 0x40000),
                              (0x03000000, 0x8000), (0x04000000, 0x1000)):
            cpu.mem_map(address, size)
        cpu.mem_write(0x08000000, self.rom)

        def cpuset(machine, _, context):
            self.assertEqual(bytes(machine.mem_read(machine.reg_read(UC_ARM_REG_PC) - 2, 2)), b'\x0b\xdf')
            source, dest, control = (machine.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            width = 4 if control & (1 << 26) else 2
            count = control & 0x1fffff
            filling = bool(control & (1 << 24))
            value = bytes(machine.mem_read(source, width if filling else width * count))
            machine.mem_write(dest, value * count if filling else value)

        cpu.hook_add(UC_HOOK_INTR, cpuset)
        self.call(cpu, 0x08002768)
        self.assertEqual(bytes(cpu.mem_read(0x03005E78, 176)), self.rom[0xA38A2C:0xA38ADC])
        return cpu

    def call(self, cpu, address, *arguments):
        from test_bg_affine_rows import NativeAffineRows

        return NativeAffineRows.call(self, cpu, address, *arguments)

    def scenario(self, kinds, *, process=True):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        cpu = self.cpu()
        manager = self.call(cpu, 0x08005C14, 0x02020000, 0x18000)
        cpu.mem_write(0x02008FF0, struct.pack('<I', manager))
        allocations, releases, copies, clears, phases = [], [], [], [], []

        def value(address, width=4):
            return int.from_bytes(cpu.mem_read(address, width), 'little')

        def trace(machine, address, size, context):
            first, second, third = (machine.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))
            if address == task.COPY:
                copies.append((first, second, third))
            elif address == task.OWNER:
                phases.append(value(second, 2))
            elif address == 0x03005E78:
                clears.append((first, second))
            elif address == 0x08007170:
                releases.append(second)
            else:
                allocations.append(second)

        for pc in (task.OWNER, task.COPY, 0x03005E78, 0x08007170, 0x08007138):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        cpu.ctl_flush_tb()

        entries, source, output = 0x0200C001, 0x0201D000, 0x0201D400
        pattern = bytes.fromhex('d49321f0162544bd')
        records = b''.join(struct.pack('<IIHBB', 0x67452301 if kind == 15 else source,
                                       output + i * 8, 8, kind, i & 255) for i, kind in enumerate(kinds))
        if records:
            cpu.mem_write(entries, records)
        cpu.mem_write(source, pattern)
        obj = self.call(cpu, 0x08006878, entries, len(kinds), 0)
        payload = obj + 24
        buffer = value(payload + 8)
        self.assertTrue(buffer)
        self.assertEqual(value(manager + 4), obj)
        self.assertEqual(value(obj), task.OWNER | 1)
        self.assertEqual((value(payload, 2), value(payload + 2, 2), value(payload + 4, 2)), (len(kinds), 0, 0x800))
        self.assertEqual(copies, [(payload + 52 + i * 12, entries + i * 12, 12) for i in range(len(kinds))])
        self.assertEqual(bytes(cpu.mem_read(payload + 52, len(records))), records)
        self.assertEqual(allocations, [92 + 12 * len(kinds), 2048])
        self.assertIn((obj, allocations[0]), clears)

        def finish_dma(machine, access, address, width, data, context):
            if address not in (0x040000B8, 0x040000C4, 0x040000D0, 0x040000DC):
                return
            src, dst, control = struct.unpack('<III', machine.mem_read(address - 8, 12))
            if control & 0x80000000:
                self.assertEqual(control & 0xffff, 2)
                fixed = bool(control & 0x01000000)
                chunk = bytes(machine.mem_read(src, 4 if fixed else 8))
                machine.mem_write(dst, chunk * 2 if fixed else chunk)
                machine.mem_write(address, struct.pack('<I', control & 0x7fffffff))

        cpu.hook_add(UC_HOOK_MEM_READ, finish_dma, begin=0x040000B8, end=0x040000DC)
        if process:
            for _ in range(len(kinds) + 3):
                self.call(cpu, 0x08005A24, manager)
                if value(0x03002BCC):
                    self.call(cpu, 0x080007C8)
            if all(kind in (0, 15) for kind in kinds):
                self.assertEqual((value(obj + 20, 2), value(payload + 2, 2)), (2, len(kinds)))
                self.assertEqual(clears.count((payload + 12, 12)), len(kinds))
                for i, kind in enumerate(kinds):
                    expected = pattern if kind == 0 else bytes.fromhex('01234567') * 2
                    self.assertEqual(bytes(cpu.mem_read(output + i * 8, 8)), expected)
            else:
                self.assertEqual((value(obj + 20, 2), value(payload + 2, 2)), (256, 0))
        self.call(cpu, 0x08005BA8, obj, 3)
        for _ in range(3):
            if value(manager + 4):
                self.call(cpu, 0x08005A24, manager)
        self.assertEqual((value(manager + 4), phases[0], phases[-1]), (0, 0, 1))
        self.assertEqual(releases, [buffer, obj])

    def test_real_scheduler_heap_iwram_clear_transfer_queue_and_destruction(self):
        for kinds in ((), (0,), (15,), (0, 15), (7,)):
            with self.subTest(kinds=kinds):
                self.scenario(kinds)

    def test_largest_nonwrapping_copy_with_real_heap(self):
        self.scenario([7] * task.MAX_COUNT, process=False)

    def test_heap_success_is_a_separate_premise(self):
        cpu = self.cpu()
        heap = self.call(cpu, 0x080070C8, 0x02020000, 0x1000)
        self.assertEqual(self.call(cpu, 0x08007138, heap, 0x2000), 0)
        self.assertTrue(self.call(cpu, 0x08007138, heap, 0x800))
