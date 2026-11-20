"""Original RNG, selection, effect, and both dispatch paths for 0813325C."""
from collections import defaultdict
import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import random_equipment_removal as effect

equipment, removal = effect.equipment, effect.removal


@unittest.skipUnless(os.getenv('FFTA_RANDOM_EQUIPMENT_ROOT'), 'requires original ROM and recovered handler')
class RandomEquipmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_RANDOM_EQUIPMENT_ROOT']).resolve()
        built = owner.build(cls.root, effect.OWNER, selector=equipment.named.EQUIPMENT_SELECTOR)
        cls.raw, cls.manifest, _, _, _, cls.objects, cls.rom, _, elf = built
        cls.image = match.elf_image(elf)

    def test_report_and_exact_runtime_identity(self):
        self.assertEqual(self.raw, self.rom[0x13325C:0x1332F8])
        self.assertEqual(self.manifest['proof']['runtime_calls'], [[0x2C, '__modsi3']])
        for off, name in ((0x2C, 'func_08142950'), (0x2A, '__modsi3'), (0x2C, '__umodsi3')):
            bad = copy.deepcopy(self.manifest['bindings'])
            bad['calls'][2] = [off, name]
            with self.subTest(off=off, name=name), self.assertRaises(ValueError):
                effect.check_original(self.image, bad, effect.TARGETS)
        report = (self.root/'docs/match/0813325C.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, effect.OWNER))
        self.assertIn('"divisors":[1,2]', report)
        self.assertFalse(match_evidence.report_matches(report.replace('"divisors":[1,2]', '"divisors":[1,3]'),
                                                      self.root, effect.OWNER))

    def test_local_extent_index_and_callers(self):
        source = (self.root/'src/0813325C.c').read_text()
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'include').mkdir()
            (root/'src').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            for old, new in (('items[2]', 'items[3]'), ('% count', '/ count'), ('item == items[index]', 'item != items[index]')):
                self.assertIn(old, source)
                (root/'src/0813325C.c').write_text(source.replace(old, new))
                with self.subTest(old=old), self.assertRaises(ValueError):
                    equipment.check_source(root, effect.OWNER)
        for off in (6, 0x12, 0x20, 0x2A, 0x32, 0x52, 0x80, 0x8A):
            bad = bytearray(self.raw)
            bad[off] ^= 1
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            with self.subTest(off=off), self.assertRaises(ValueError):
                effect.frame({i.address:i for i in decoder.disasm(bytes(bad), effect.OWNER)})
        for pc in (effect.GUARD+16, removal.TABLE+12*65, removal.TABLE+12*66,
                   0x0855187C+28*289+13, 0x0855187C+28*225+12):
            bad = bytearray(self.rom)
            bad[pc-equipment.BASE] ^= 1
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                effect.routes(bad, self.objects)

    def test_full_reachable_remainder_domain(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
        from unicorn import arm_const as reg
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        code, ram = 0x08142000, 0x03000000
        cpu.mem_map(code, 0x1000)
        cpu.mem_write(code, self.rom[code-equipment.BASE:code-equipment.BASE+0x1000])
        cpu.mem_map(ram, 0x2000)
        cpu.reg_write(reg.UC_ARM_REG_SP, ram+0x1F00)
        cpu.reg_write(reg.UC_ARM_REG_LR, ram | 1)
        for count in (1, 2):
            for rng in range(32768):
                cpu.reg_write(reg.UC_ARM_REG_R0, rng)
                cpu.reg_write(reg.UC_ARM_REG_R1, count)
                cpu.emu_start(effect.shuffle.REMAINDER | 1, ram, count=512)
                self.assertEqual((cpu.reg_read(reg.UC_ARM_REG_PC), cpu.reg_read(reg.UC_ARM_REG_R0)),
                                 (ram, rng % count))
            self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_SP), ram+0x1F00)

    def test_live_dispatch_and_inventory(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, _ = battle_environment(self)
        source, scene_target, party_target = 0x02002FC4, 0x020030CC, 0x02000080
        rows = {}
        for group, row, slots, items in equipment.scene_rows(self.rom):
            rows.setdefault(len(items), (equipment.GROUPS[group][1]+48*row, slots, items))
        seen = defaultdict(list)

        def observe(machine, pc, width, context):
            link = machine.reg_read(reg.UC_ARM_REG_LR) & ~1
            r0, r1, r2 = (machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(3))
            if pc == effect.OWNER:
                seen[pc].append((link, machine.reg_read(reg.UC_ARM_REG_SP)))
            elif pc == 0x0812E540:
                seen[pc].append(machine.reg_read(reg.UC_ARM_REG_R6))
            elif pc == 0x081332AE:
                seen[pc].append(r0)
            elif pc == effect.GUARD or effect.OWNER <= link < effect.END:
                seen[pc].append((r0,r1,r2))

        for pc in (effect.GUARD, effect.OWNER, 0x0812E540, 0x081332AE, *effect.CALLS.values()):
            cpu.hook_add(UC_HOOK_CODE, observe, begin=pc, end=pc)
        state = removal.STATE
        for action, variant in ((225,0), (289,1)):
            for n, seed, flag, target, duplicate in (
                    (0,0,0,scene_target,False), (1,0,0,scene_target,False),
                    (2,0,0,scene_target,False), (2,3,0,party_target,False),
                    (2,3,0,scene_target,True), (2,3,16,scene_target,False)):
                with self.subTest(action=action, n=n, seed=seed, flag=flag, target=target, duplicate=duplicate):
                    record, slots, items = rows[n]
                    call(0x080C9644, source, record, 0)
                    call(0x080C9644, target, record, 0)
                    if duplicate:
                        slots, items = [106,106,0,0,0], [106,106]
                        write(target+42, '5H', *slots)
                    call(0x0812F2A4, action, 0, 0)
                    call(0x0812F328, variant)
                    write(state, 'I', source)
                    write(state+8, 'I', target)
                    write(state+0x26, 'H', flag)
                    write(state+0x18, 'H', 0x7F7F)
                    write(0x030034B0, 'I', seed)
                    next_seed = (seed*0x41C64E6D + 0x3039) & 0xFFFFFFFF
                    rng = (next_seed >> 16) & 0x7FFF
                    picked = items[rng % n] if n else 0
                    if target == party_target:
                        write(0x02001940, 'HBB', picked, 7, 0)
                    seen.clear()
                    call(removal.DISPATCH)
                    if action == 289:
                        self.assertEqual(len(seen[effect.GUARD]), 1)
                    if action == 289 and flag:
                        self.assertFalse(seen[effect.OWNER])
                    else:
                        link, entry_sp = seen[effect.OWNER][0]
                        self.assertEqual(link, 0x08133258 if action == 289 else 0x081338BE)
                    self.assertEqual(len(seen[removal.WRAPPER]), int(not flag))
                    if not flag:
                        local = entry_sp-28
                        self.assertEqual(seen[removal.WRAPPER][0][:2], (target, local))
                        self.assertEqual(seen[0x0812E540], [local+2*i for i in range(n)])
                    if flag or not n:
                        self.assertFalse(seen[effect.shuffle.RNG] or seen[effect.shuffle.REMAINDER] or seen[removal.REFRESH])
                        self.assertEqual(struct.unpack('<I', cpu.mem_read(0x030034B0,4))[0], seed)
                        self.assertEqual(struct.unpack('<H', cpu.mem_read(state+0x18,2))[0], 0x7F7F)
                        continue
                    self.assertEqual(len(seen[effect.shuffle.RNG]), 1)
                    self.assertEqual(seen[effect.shuffle.REMAINDER][0][:2], (rng,n))
                    self.assertEqual(struct.unpack('<I', cpu.mem_read(0x030034B0,4))[0], next_seed)
                    self.assertEqual(set(seen[0x081332AE]), {local+2*(rng % n)})
                    slot = slots.index(picked)
                    self.assertEqual([r[1] for r in seen[equipment.SLOT]], list(range(29,30+slot)))
                    self.assertEqual(seen[removal.CLEAR], [(target,0,slot)])
                    self.assertEqual(seen[removal.VALIDATE][0][:2], (target,1))
                    self.assertEqual(seen[effect.MEMBER][0][0], target)
                    self.assertEqual([r[:2] for r in seen[effect.INVENTORY]],
                                     [(picked,1)] if target == party_target else [])
                    self.assertEqual(len(seen[removal.REFRESH]), 1)
                    self.assertEqual(struct.unpack('<H', cpu.mem_read(state+0x18,2))[0], picked)
                    if target == party_target:
                        self.assertEqual(cpu.mem_read(0x02001942,1)[0], 6)


if __name__ == '__main__':
    unittest.main()
