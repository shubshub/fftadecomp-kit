"""Action predicate ELF roles, negative proofs and native equipment boundary."""
from copy import deepcopy
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import action_slot_predicate as predicate
import match
import match_evidence
import owner_admission_profile as owner
import unit_equipment_attribute as equipment


@unittest.skipUnless(os.getenv('FFTA_ACTION_SLOT_ROOT'), 'requires the USA ROM and recovered source')
class ActionSlotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ACTION_SLOT_ROOT']).resolve()
        cls.data, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, elf = owner.build(
            cls.root, predicate.OWNER, selector=equipment.named.EQUIPMENT_SELECTOR)
        cls.image = match.elf_image(elf)

    def test_report_graph_and_backward_exit(self):
        report = (self.root / 'docs/match/081306E0.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, predicate.OWNER))
        self.assertEqual(self.data, self.rom[0x1306E0:0x13079C])
        self.assertEqual(self.manifest['proof']['instructions'], 64)
        self.assertEqual(self.manifest['proof']['case_offsets'], list(predicate.CASES))
        old = owner.refine(self.data, predicate.OWNER, self.mapping)
        self.assertFalse(old['cfg_closed'])
        self.assertIn('unresolved jump at 0x08130754', old['partial_reasons'])
        for offset in (0x0E, 0x18, 0x22, 0x68, 0x6A, 0x76, 0x78, 0x98, 0xA4, 0xBA):
            bad = bytearray(self.data)
            bad[offset] ^= 1
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                predicate.control_flow(bytes(bad), predicate.OWNER, self.mapping)
        with self.assertRaises(ValueError):
            predicate.control_flow(self.data, predicate.OWNER + 4, self.mapping)

    def test_reject_changed_bindings_and_historical_index(self):
        original = self.manifest['bindings']
        targets = {f'func_{a:08X}': (a, False) for a in predicate.CALLS.values()}
        targets[predicate.STATE_NAME] = (predicate.STATE, True)
        predicate.check_original(self.image, original, targets)
        for group, row, value in [('calls', 6, 'func_0812F328'), ('switches', 8, 0xB2),
                                  ('data', 0, 'data_0200F3F4')]:
            bad = deepcopy(original)
            bad[group][row][1] = value
            with self.subTest(group=group), self.assertRaises(ValueError):
                predicate.check_original(self.image, bad, targets)
        maps = json.loads(self.mapping)
        next(row for row in maps if row['rom'] == '0x081306E0')['instrs'] = 94
        with self.assertRaises(ValueError):
            owner.verify(self.data, predicate.OWNER, self.rom, json.dumps(maps).encode(),
                         self.index, self.objects, bindings=original, selector=equipment.named.EQUIPMENT_SELECTOR)

    def test_native_slot_results_with_actual_equipment_producer(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, _ = battle_environment(self)
        source, target = 0x02002FC4, 0x02003200
        write(source+42, '5H', 106, 0, 0, 0, 0)
        current = 0
        calls = []
        def helper(machine, pc, size, unused):
            nonlocal current
            r0 = machine.reg_read(reg.UC_ARM_REG_R0)
            if pc == 0x0812F2A4:
                self.assertEqual((r0, machine.reg_read(reg.UC_ARM_REG_R1), machine.reg_read(reg.UC_ARM_REG_R2)), (74,106,0))
            elif pc == 0x0812F328:
                current = r0
            elif pc == 0x08130FBC:
                machine.reg_write(reg.UC_ARM_REG_R0, int(current in eligible))
            elif pc == 0x0812F358:
                machine.reg_write(reg.UC_ARM_REG_R0, kinds[current])
            elif pc == 0x08131B20:
                machine.reg_write(reg.UC_ARM_REG_R0, score & 0xFFFFFFFF)
            calls.append((pc,r0))
            machine.reg_write(reg.UC_ARM_REG_PC, machine.reg_read(reg.UC_ARM_REG_LR))
        for addr in set(predicate.CALLS.values()) - {equipment.WRAPPER}:
            cpu.hook_add(UC_HOOK_CODE,helper,begin=addr,end=addr)
        self.assertEqual(call(predicate.OWNER,source,target,0),1)
        self.assertEqual(calls,[])
        for kinds, eligible, score, answer, slots in [
                ((0,8,0),(0,1,2),0,1,2), ((8,5,0),(1,),-1,0,2), ((0,0,1),(2,),0,0,3),
                ((5,0,0),(0,),1,1,1), ((0,9,255),(0,1,2),1,0,3),
                *[((kind,8,0),(0,1),7,0,1) for kind in (2,3,4,6,7)]]:
            calls.clear()
            write(predicate.STATE+0x26, 'H', 0xA481)
            self.assertEqual(call(predicate.OWNER,source,target,74),answer)
            self.assertEqual([v for a,v in calls if a == 0x0812F328],list(range(slots)))
            self.assertEqual(cpu.mem_read(predicate.STATE,8),struct.pack('<II',source,target))
            self.assertEqual(cpu.mem_read(predicate.STATE+0x26,2),struct.pack('<H',0xA483))

    def test_third_qualifying_item_reaches_saved_r4(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, _, write, _ = battle_environment(self)
        source, entry_sp = 0x02002FC4, 0x03007F00
        write(source+42,'5H',106,107,162,0,0)
        writes = []
        def stop_before_third(machine, pc, size, unused):
            writes.append(machine.reg_read(reg.UC_ARM_REG_R6) - entry_sp)
            if len(writes) == 3:
                machine.emu_stop()
        cpu.hook_add(UC_HOOK_CODE,stop_before_third,begin=0x0812E540,end=0x0812E540)
        cpu.reg_write(reg.UC_ARM_REG_R0,source)
        cpu.reg_write(reg.UC_ARM_REG_R1,source)
        cpu.reg_write(reg.UC_ARM_REG_R2,0)
        cpu.reg_write(reg.UC_ARM_REG_SP,entry_sp)
        cpu.reg_write(reg.UC_ARM_REG_LR,0x03007001)
        cpu.emu_start(predicate.OWNER|1,0x03007000,count=100000)
        self.assertEqual(writes,[-24,-22,-20])
        self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_PC),0x0812E540)


if __name__ == '__main__':
    unittest.main()
