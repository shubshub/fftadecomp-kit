"""Original equipment initialization, two-halfword selection, and the actual battle caller."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import named_data_buffer_profile as named
import owner_admission_profile as owner
import unit_equipment_attribute as equip


class CursorCases(unittest.TestCase):
    def test_each_valid_five_slot_selection_and_each_halfword(self):
        rows = equip.cursor_cases()
        self.assertEqual({row['mask'] for row in rows}, {m for m in range(32) if m.bit_count() <= 2})
        for row in rows:
            offsets = list(range(0, row['mask'].bit_count()*2, 2))
            self.assertEqual(row['write_offsets'], offsets)
            self.assertEqual(row['last_miss_read_offsets'], offsets)
            for search in row['searches']:
                stop = search['match_index']
                end = search['count'] if stop is None else stop + 1
                self.assertEqual(search['read_offsets'], offsets[:end])


@unittest.skipUnless(os.environ.get('FFTA_EQUIPMENT_ATTRIBUTE_ROOT'), 'requires the reviewed source and USA ROM')
class EquipmentAttributeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_EQUIPMENT_ATTRIBUTE_ROOT']).resolve()
        built = owner.build(cls.root, equip.OWNER, selector=named.EQUIPMENT_SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = built

    def call(self, cpu, address, *args):
        from test_bg_affine_rows import NativeAffineRows
        return NativeAffineRows.call(self, cpu, address, *args)

    def test_exact_owner_and_live_report(self):
        self.assertEqual(self.body, self.rom[0x12F5E0:0x12F690])
        self.assertEqual(self.manifest['bindings'], equip.bindings())
        report = (self.root/'docs/match/0812F5E0.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, equip.OWNER))
        for old, new in (('"local":[-28,-24]', '"local":[-28,-20]'),
                         ('At most two nonzero', 'At most five nonzero'),
                         ('"selected":2', '"selected":1')):
            changed = report.replace(old, new, 1)
            self.assertNotEqual(changed, report)
            self.assertFalse(match_evidence.report_matches(changed, self.root, equip.OWNER))

    def test_exact_original_symbols_and_static_rows(self):
        image = match.elf_image(self.elf)
        def bind(img):
            return owner.original_bindings(img, equip.OWNER, self.rom, self.mapping, self.objects,
                                           selector=named.EQUIPMENT_SELECTOR, index=self.index)
        actual, targets = bind(image)
        equip.check_original(image, equip.OWNER, actual, targets)
        for key, value in (('size', 4), ('type', 2), ('bind', 2), ('name', 'func_08130822')):
            altered = copy.deepcopy(image)
            next(s for s in altered['symbols'] if s['name'] == 'func_08130820')[key] = value
            with self.subTest(field=key), self.assertRaises(ValueError):
                bind(altered)
        rows = equip.scene_rows(self.rom)
        self.assertEqual(len(rows), 42)
        self.assertEqual([sum(len(r[3]) == n for r in rows) for n in range(3)], [12, 29, 1])
        corrupted = bytearray(self.rom)
        struct.pack_into('<I', corrupted, equip.SCENES-equip.BASE+40+4, equip.GROUPS[2][1])
        with self.assertRaises(ValueError):
            equip.scene_rows(corrupted)

    def test_original_scene_dispatch_initializes_every_reviewed_row(self):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE, UC_PROT_READ, UC_PROT_EXEC
        from unicorn import arm_const as reg
        cpu = TransferTaskTests.cpu(self)
        cpu.mem_protect(equip.BASE, len(self.rom), UC_PROT_READ | UC_PROT_EXEC)
        unit_bank = 0x02002FC4
        inputs, results = [], []

        def record_input(machine, pc, size, context):
            inputs.append(tuple(machine.reg_read(r) for r in (
                reg.UC_ARM_REG_R0, reg.UC_ARM_REG_R1, reg.UC_ARM_REG_R2)))

        def record_equipment(machine, pc, size, context):
            unit, source, _ = inputs[-1]
            results.append((source, bytes(machine.mem_read(unit+42, 10))))

        cpu.hook_add(UC_HOOK_CODE, record_input, begin=0x080C9644, end=0x080C9644)
        cpu.hook_add(UC_HOOK_CODE, record_equipment, begin=0x0812571A, end=0x0812571A)
        for group, (count, source) in equip.GROUPS.items():
            inputs.clear()
            results.clear()
            cpu.mem_write(unit_bank, bytes(12*264))
            cpu.reg_write(reg.UC_ARM_REG_R0, group)
            cpu.reg_write(reg.UC_ARM_REG_SP, 0x03007F00)
            cpu.reg_write(reg.UC_ARM_REG_LR, 0x03007001)
            cpu.emu_start(0x081256D5, 0x08125732, count=500000)
            self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_PC), 0x08125732)
            expected = [source+48*i for i in range(count)]
            self.assertEqual([(ptr, mode) for _, ptr, mode in inputs], [(ptr, 0) for ptr in expected])
            self.assertTrue(all(unit in range(unit_bank, unit_bank+12*264, 264) for unit, _, _ in inputs))
            self.assertEqual(results, [(ptr, self.rom[ptr-equip.BASE+8:ptr-equip.BASE+18]) for ptr in expected])

    def test_battle_caller_on_every_reviewed_scene_definition(self):
        from test_packed_transfer_task import TransferTaskTests
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_PROT_READ, UC_PROT_EXEC
        from unicorn import arm_const as reg
        cpu = TransferTaskTests.cpu(self)
        cpu.mem_protect(equip.BASE, len(self.rom), UC_PROT_READ | UC_PROT_EXEC)
        unit = 0x02002FC4
        registers = list(range(reg.UC_ARM_REG_R4, reg.UC_ARM_REG_R11+1))
        seen = []
        local = []
        accesses = []

        def enter(machine, pc, size, context):
            args = [machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(3)]
            seen.append([pc, *args])
            if pc == equip.WRAPPER:
                local.append(args[1])

        def touch(machine, access, address, size, value, context):
            if local and local[0] <= address < local[0]+4:
                accesses.append((machine.reg_read(reg.UC_ARM_REG_PC), address-local[0], size))

        for target in (equip.OWNER, equip.WRAPPER, equip.SORT, equip.COLLECT, equip.SLOT, equip.FLAG,
                       equip.ITEM, equip.DEFAULT):
            cpu.hook_add(UC_HOOK_CODE, enter, begin=target, end=target)
        cpu.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE, touch, begin=0x03007E00, end=0x03007F00)
        action_table = 0x55187C
        def flag29(i):
            return struct.unpack_from('<I', self.rom, action_table+28*i+16)[0] & (1 << 18)
        action10 = next(i for i in range(1, 500) if flag29(i))
        action12 = next(i for i in range(1, 500) if not flag29(i))

        def item_value(entry, field):
            raw = struct.unpack_from('<b', self.rom, equip.ITEMS-equip.BASE + 32*entry +
                                     {10: 16, 12: 18}[field])[0]
            if cpu.mem_read(0x0200203D, 1)[0]:
                return raw
            if (field, entry) in ((10, 0x33), (12, 0x94)):
                raw += cpu.mem_read(0x02002030 + (1 if field == 10 else 2), 1)[0]
            return min(255, raw & 0xFFFFFFFF)

        cases = 0
        for group, index, items, selected in equip.scene_rows(self.rom):
            source = equip.GROUPS[group][1]+48*index
            cpu.mem_write(unit, bytes(264))
            local.clear()
            self.call(cpu, 0x080C9644, unit, source, 0)
            self.assertEqual(struct.unpack('<5H', cpu.mem_read(unit+42, 10)), tuple(items))
            for status in (0, 1):
                cpu.mem_write(unit+0xE9, bytes([status]))
                for action, field in ((0, 10), (action10, 10), (action12, 12)):
                    for entry in (0, next((item for item in items if item), 1)):
                        seen.clear()
                        local.clear()
                        accesses.clear()
                        saved = {r: 0x43210000+r for r in registers}
                        for r, value in saved.items():
                            cpu.reg_write(r, value)
                        value = self.call(cpu, 0x0812F690, unit, action, entry, 17)
                        self.assertEqual({r: cpu.reg_read(r) for r in registers}, saved)
                        total = 0
                        if not status:
                            if field == 10:
                                idx = cpu.mem_read(unit+5, 1)[0]
                                total = item_value(entry, field) if entry else self.rom[0x521A14+52*idx+51]
                            total += sum(item_value(item, field) for item in items if item and
                                         (field != 10 or item not in selected))
                        self.assertEqual(value, (17+total) & 0xFFFFFFFF)
                        self.assertEqual([r[1:] for r in seen if r[0] == equip.OWNER], [[unit, entry, field]])
                        self.assertEqual(sum(row[0] == equip.COLLECT for row in seen), int(not status))
                        self.assertEqual(sum(row[0] == equip.SLOT for row in seen), 10*int(not status))
                        self.assertEqual(len(local), int(not status))
                        writes = [off for pc, off, width in accesses if pc == 0x0812E540]
                        self.assertEqual(writes, list(range(0, len(selected)*2, 2)) if not status else [])
                        self.assertTrue(all(off in (0, 2) and width == 2 for _, off, width in accesses))
                        cases += 1
        self.assertEqual(cases, 504)
