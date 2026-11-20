"""Original equipment collection, list traversal, data roles and the eight evaluator arguments."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import equipment_selection_list as selection
import match
import match_evidence
import owner_admission_profile as owner
import unit_equipment_attribute as equipment


@unittest.skipUnless(os.environ.get('FFTA_EQUIPMENT_SELECTION_ROOT'), 'needs original ROM and reviewed source')
class SelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_EQUIPMENT_SELECTION_ROOT']).resolve()
        cls.raw, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, elf = owner.build(
            cls.root, selection.OWNER, selector=equipment.named.EQUIPMENT_SELECTOR)
        cls.image = match.elf_image(elf)
        cls.refinement = owner.refine(cls.raw, selection.OWNER, cls.mapping)

    def test_original_and_relocation_roles(self):
        self.assertEqual(self.raw, self.rom[0x13569C:0x135750])
        bindings = self.manifest['bindings']
        targets = {f'func_{a:08X}': (a, False) for a in selection.CALLS.values()}
        targets.update({name: (value, True) for name, value in selection.OBJECTS.items()})
        equipment.check_original(self.image, selection.OWNER, bindings, targets)
        for kind, index, field, change in [('calls', 1, 1, 'func_081343C8'), ('data', 0, 0, 0x8c),
                                            ('data', 0, 1, selection.TABLE_NAME), ('data', 1, 2, 16)]:
            bad = copy.deepcopy(bindings)
            bad[kind][index][field] = change
            with self.subTest(kind=kind, field=field), self.assertRaises(ValueError):
                equipment.check_original(self.image, selection.OWNER, bad, targets)
        with self.assertRaises(ValueError):
            equipment.check_original(self.image, selection.OWNER, bindings,
                                     targets | {selection.TABLE_NAME: (selection.TABLE, False)})

    def test_reached_instruction_count_in_both_indexes(self):
        self.assertEqual(self.refinement['instrs'], 79)
        self.assertEqual(self.manifest['proof']['instructions'], 79)
        owner.verify(self.raw, selection.OWNER, self.rom, self.mapping, self.index, self.objects,
                     bindings=self.manifest['bindings'], selector=equipment.named.EQUIPMENT_SELECTOR)
        rows = json.loads(self.mapping)
        item = next(row for row in rows if int(row['rom'], 16) == selection.OWNER)
        self.assertEqual(item['instrs'], 79)
        item['instrs'] = 90
        old_map = json.dumps(rows).encode()
        line = next(line for line in self.index.splitlines() if line.startswith(b'0813569C '))
        fields = line.split()
        self.assertEqual(fields[3], b'79')
        fields[3] = b'90'
        old_index = self.index.replace(line, b' '.join(fields))
        for mapping, index in ((old_map, self.index), (self.mapping, old_index), (old_map, old_index)):
            with self.subTest(json_stale=mapping is old_map, text_stale=index is old_index), self.assertRaises(ValueError):
                owner.verify(self.raw, selection.OWNER, self.rom, mapping, index, self.objects,
                             bindings=self.manifest['bindings'], selector=equipment.named.EQUIPMENT_SELECTOR)

    def test_frame_calls_and_literals(self):
        ins, _, _, _, words = equipment.graph.graph(self.raw, selection.OWNER, self.refinement)
        selection.owner_frame(ins)
        selection.list_partition(self.raw, self.refinement, ins, words)
        for pc in (0x081356A6,0x081356B2,0x081356B6,0x081356C0,0x081356C4,0x081356DA,0x081356E0,
                   0x081356EE,0x081356F0,0x081356F2,0x081356F4,0x08135702,0x08135708,0x08135710,
                   0x0813571A,0x0813573C,0x08135740,0x0813574E):
            bad = bytearray(self.raw)
            bad[pc-selection.OWNER] ^= 8 if pc == 0x0813574E else 1
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            decoded = {i.address: i for i in decoder.disasm(bytes(bad), selection.OWNER)}
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                selection.owner_frame(decoded)
        for offset in (0x88, 0x8c, 0x90, 0x94):
            bad = bytearray(self.raw)
            bad[offset] ^= 1
            with self.subTest(pool=offset), self.assertRaises(ValueError):
                selection.list_partition(bad, self.refinement, ins, words)

    def test_only_direct_caller(self):
        self.assertEqual(selection.caller_sites(self.rom, self.mapping), [0x080C26CA])
        for pc in (0x080C26C0, 0x080C26C8, 0x080C26CA):
            bad = bytearray(self.rom)
            bad[pc-equipment.BASE] ^= 1
            with self.subTest(pc=hex(pc)), self.assertRaises(ValueError):
                selection.caller_sites(bad, self.mapping)

    def test_bound_source_and_signed_report(self):
        dest = Path('src/0813569C.c')
        src = (self.root/dest).read_text()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            (root/'src').mkdir()
            for old, new in [('items[2]', 'items[3]'), ('items[0]', 'items[1]'), ('u32 mode)', 'u8 mode)'),
                             ('u8 unknown_00[16]', 'u8 unknown_00[8]')]:
                self.assertIn(old, src)
                (root/dest).write_text(src.replace(old, new))
                with self.subTest(old=old), self.assertRaises(ValueError):
                    equipment.check_source(root, selection.OWNER)
        report = (self.root/'docs/match/0813569C.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, selection.OWNER))
        for old, new in [('"local":[-36,-32]', '"local":[-36,-30]'), ('s16(effect)', 'u16(effect)'),
                         ('at most two qualifying', 'any number of qualifying')]:
            self.assertIn(old, report)
            self.assertFalse(match_evidence.report_matches(report.replace(old, new), self.root, selection.OWNER))

    def test_native_collection_and_evaluator(self):
        from test_battle_action_value import battle_environment, signed16
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, _ = battle_environment(self)
        source, target, sp = 0x02002FC4, 0x020030CC, 0x03007F00-52
        cases = {}
        for group, row, _, selected in equipment.scene_rows(self.rom):
            cases.setdefault(len(selected), (equipment.GROUPS[group][1]+48*row, selected))
        self.assertEqual(set(cases), {0, 1, 2})
        captures = {}
        def trace(machine, pc, width, context):
            r = tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
            if pc == equipment.WRAPPER and r[1] == sp+16:
                captures['wrapper'] = r[:2]
            elif pc == 0x0812E540 and sp+16 <= machine.reg_read(reg.UC_ARM_REG_R6) <= sp+20:
                captures['append'].append(machine.reg_read(reg.UC_ARM_REG_R6)-sp)
            elif pc == selection.EFFECT and machine.reg_read(reg.UC_ARM_REG_SP) == sp:
                captures['items'] = struct.unpack('<2H', machine.mem_read(sp+16, 4))
                captures['effects'].append(r+struct.unpack('<2I', machine.mem_read(sp, 8)))
            elif pc == 0x081356EC:
                captures['amounts'].append(signed16(r[0]) & 0xffffffff)
            elif pc == selection.EVALUATE and machine.reg_read(reg.UC_ARM_REG_SP) == sp:
                captures['evaluations'].append(r+struct.unpack('<4I', machine.mem_read(sp, 16)))
        for pc in (equipment.WRAPPER, 0x0812E540, selection.EFFECT, 0x081356EC, selection.EVALUATE):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        signed_amounts = []
        for n, (definition, selected) in cases.items():
            call(0x080C9644, source, definition, 0)
            call(0x080C9644, target, definition, 0)
            write(source+0xe9, 'B', 0)
            for mode in (0, 1, 0x100, 0x101, 255, 0xffffffff):
                for entries, result in (([], 0), ([0, 0], 0), ([84, 0], 1), ([0, 84], 2)):
                    with self.subTest(count=n, mode=mode, entries=entries):
                        captures.update(append=[], effects=[], evaluations=[], amounts=[])
                        write(selection.STATE+0x3c33, 'B', len(entries))
                        if entries:
                            write(selection.STATE+0x3c34, 'H'*len(entries), *entries)
                        self.assertEqual(call(selection.OWNER, source, target, 1, mode), result)
                        self.assertEqual(captures['wrapper'], (source, sp+16))
                        self.assertEqual(captures['append'], [16, 18][:n])
                        reached = entries[:result] if result else entries
                        self.assertEqual(len(captures['amounts']), len(reached))
                        signed_amounts.extend(captures['amounts'])
                        if reached:
                            self.assertCountEqual([i for i in captures['items'] if i], selected)
                            self.assertEqual(captures['effects'], [(source,target,1,captures['items'][0],0,2)]*len(reached))
                        self.assertEqual(captures['evaluations'], [
                            (source,target,1,mode & 255,0,amount,0,selection.TABLE+16*index)
                            for index, amount in zip(reached, captures['amounts'])])
        self.assertTrue(any(value >= 0xffff8000 for value in signed_amounts))

    def test_native_third_entry_reaches_saved_register(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, _, write, _ = battle_environment(self)
        source, entry_sp = 0x02002FC4, 0x03007F00
        write(source+42, '5H', 106, 107, 162, 0, 0)
        offsets = []
        def stop_before_overrun(machine, pc, width, context):
            offsets.append(machine.reg_read(reg.UC_ARM_REG_R6) - (entry_sp-52))
            if len(offsets) == 3:
                machine.emu_stop()
        cpu.hook_add(UC_HOOK_CODE, stop_before_overrun, begin=0x0812E540, end=0x0812E540)
        cpu.reg_write(reg.UC_ARM_REG_SP, entry_sp)
        cpu.reg_write(reg.UC_ARM_REG_R0, source)
        cpu.reg_write(reg.UC_ARM_REG_R1, source)
        cpu.reg_write(reg.UC_ARM_REG_LR, 0x03007001)
        cpu.emu_start(selection.OWNER | 1, 0x03007000, count=100000)
        self.assertEqual(offsets, [16, 18, 20])
        self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_PC), 0x0812E540)


if __name__ == '__main__':
    unittest.main()
