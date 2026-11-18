"""Exact equipment output, action variants and public byte return."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import battle_eligibility as guard
import match
import match_evidence
import owner_admission_profile as owner
import unit_equipment_attribute as equip
from test_battle_action_value import battle_environment, signed16


@unittest.skipUnless(os.environ.get('FFTA_BATTLE_ELIGIBILITY_ROOT'), 'requires original actors and eligibility C')
class EligibilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_BATTLE_ELIGIBILITY_ROOT']).resolve()
        cls.built = owner.build(cls.root, guard.OWNER, selector=equip.named.EQUIPMENT_SELECTOR)
        cls.rom = cls.built[6]

    def test_literal_and_original_compiler_roles(self):
        raw, manifest, _, mapping, index, objects, rom, _, elf = self.built
        self.assertEqual(raw, rom[0xC48A4:0xC4964])
        image = match.elf_image(elf)
        def bindings(obj):
            return owner.original_bindings(obj, guard.OWNER, rom, mapping, objects,
                                          selector=equip.named.EQUIPMENT_SELECTOR, index=index)
        original, targets = bindings(image)
        self.assertEqual(original, manifest['bindings'])
        self.assertEqual(original['data'], [[72, 'data_0200F3F0', 0]])
        self.assertEqual(len(original['calls']), 10)
        self.assertEqual(targets[guard.STATE_NAME], (guard.STATE, True))
        for name, field, value in ((guard.STATE_NAME, 'size', 4), ('func_08131378', 'bind', 2),
                                   ('func_0812F0D8', 'type', 2)):
            altered = copy.deepcopy(image)
            next(s for s in altered['symbols'] if s['name'] == name)[field] = value
            with self.subTest(name=name, field=field), self.assertRaises(ValueError):
                bindings(altered)

    def test_live_report_and_shared_byte_return(self):
        report = (self.root/'docs/match/080C48A4.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, guard.OWNER))
        for old, new in (('"local":[-28,-24]','"local":[-28,-20]'),
                         ('at most two','at most five'), ('"variants":[0,1,2]','"variants":[0,1]')):
            changed = report.replace(old, new)
            self.assertNotEqual(changed, report)
            self.assertFalse(match_evidence.report_matches(changed, self.root, guard.OWNER))
        self.assertEqual(self.built[0][176:180], bytes.fromhex('0006000e'))

    def test_original_equipment_and_all_three_native_variant_exits(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, _ = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        trace = {}

        def record(machine, pc, size, context):
            args = tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
            trace.setdefault(pc, []).append(args)

        sites = (guard.OWNER, 0x080C48B6, 0x080C48BA, 0x080C48C8, 0x080C48F8,
                 0x080C4918, 0x080C492E, 0x080C493C, 0x080C4946, 0x080C4904, 0x080C490A)
        for site in sites:
            cpu.hook_add(UC_HOOK_CODE, record, begin=site, end=site)

        states, counts, verified = set(), set(), 0
        target_definition = equip.GROUPS[2][1] + 48
        for group, row, slots, selected in equip.scene_rows(self.rom):
            call(0x080C9644, source, equip.GROUPS[group][1]+48*row, 0)
            call(0x080C9644, target, target_definition, 0)
            write(source+0xF6, 'BB', 6, 6)
            write(target+0xF6, 'BB', 7, 6)
            self.assertEqual(struct.unpack('<5H', cpu.mem_read(source+42, 10)), tuple(slots))
            selected = [] if cpu.mem_read(source+0xE9, 1)[0] & 1 else sorted(selected, reverse=True,
                key=lambda item: struct.unpack_from('<b', self.rom, equip.ITEMS-equip.BASE+32*item+16)[0])
            counts.add(len(selected))
            health = bytes(cpu.mem_read(target+24, 2))
            for defeated in (False, True):
                cpu.mem_write(target+24, bytes(2) if defeated else health)
                for actor in (source, target):
                    for action in (0, 1, 19, 40, 55):
                        trace.clear()
                        result = call(guard.OWNER, source, actor, action)
                        self.assertIn(result, (0, 1))
                        self.assertEqual(trace[0x080C48B6][0][:2], (source, 0x03007F00-28))
                        self.assertEqual(trace[0x080C48BA][0][0], len(selected))
                        self.assertEqual(trace[0x080C48C8][0][0], 0x03007F00-28)
                        attempts = [args[0] for args in trace.get(0x080C492E, [])]
                        if action == 0:
                            self.assertEqual(attempts, [])
                            self.assertEqual(result, int(actor != source and bool(int.from_bytes(cpu.mem_read(actor+24, 2), 'little'))))
                        elif not trace[0x080C48F8][0][0] and actor == source:
                            self.assertEqual((result, attempts), (0, []))
                        else:
                            self.assertEqual(trace[0x080C4918][0][:3], (action, selected[0] if selected else 0, 0))
                            self.assertEqual(struct.unpack('<II', cpu.mem_read(guard.STATE,8)), (source,actor))
                            checks = [args[0] & 255 for args in trace[0x080C493C]]
                            eligible = iter(args[0] & 255 for args in trace.get(0x080C4946, []))
                            successes = [(i, next(eligible)) for i, allowed in enumerate(checks) if allowed]
                            winning = next((i for i, chance in successes if chance), None)
                            self.assertEqual(attempts, list(range(3 if winning is None else winning+1)))
                            self.assertEqual(result, int(winning is not None))
                            if winning is not None:
                                self.assertEqual(trace[0x080C4904][0][0], winning)
                                self.assertEqual(trace[0x080C490A][0][0], actor)
                                self.assertTrue(int.from_bytes(cpu.mem_read(guard.STATE+38, 2),'little') & (1 << winning))
                                self.assertEqual(int.from_bytes(cpu.mem_read(guard.STATE+8,4),'little'), actor)
                            states.add(winning)
                        verified += 1
        self.assertEqual(counts, {0,1,2})
        self.assertEqual(states, {0,1,2,None})
        self.assertEqual(verified, 840)

    def test_three_original_caller_sites_on_initialized_game_actors(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, allocate = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        left, right = allocate(0x24), allocate(0x24)
        context, group, other = allocate(0x224), allocate(0x290C), allocate(0x290C)
        grid, positions = allocate(1024), allocate(1024)
        call(0x080C9644, source, equip.GROUPS[37][1]+3*48, 0)
        call(0x080C9644, target, equip.GROUPS[2][1]+48, 0)
        write(source+0xF6, 'BB', 6, 6)
        write(target+0xF6, 'BB', 7, 6)
        write(left, 'I', source)
        write(right, 'I', target)
        write(context, 'II', left, right)
        write(context+12, 'II', group, other)
        write(group, 'I', right)
        write(group+0x324, 'H', 1)
        write(group+0x2908, 'H', 1)
        calls = []

        def enter(machine, pc, size, context):
            lr = machine.reg_read(reg.UC_ARM_REG_LR)
            args = [machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(3)]
            calls.append(((lr & ~1)-4, args))

        cpu.hook_add(UC_HOOK_CODE, enter, begin=guard.OWNER, end=guard.OWNER)
        self.assertGreater(signed16(call(0x080BDECC, left, right, 0, 0)), 0)
        self.assertEqual(calls, [(0x080BDEEC, [source,target,0])])
        calls.clear()
        write(group+16, 'h', -1)
        self.assertEqual(call(0x080BE1F4,context,grid,group,7,6,0,0,positions), 1)
        self.assertEqual(calls, [(0x080BE278, [source,target,0])])
        self.assertEqual(bytes(cpu.mem_read(grid+4*(6*16+7),4)), bytes([255])*4)
        calls.clear()
        write(group+16, 'h', 1)
        write(target+24, 'H', 0)
        self.assertEqual(call(0x080BFDB0,context), 0)
        self.assertEqual(calls, [(0x080BFDF8, [source,target,0])])
