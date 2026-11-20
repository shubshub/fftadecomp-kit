"""The action-67 dispatch, live slot updates, and limits of its two-entry frame."""
import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import equipment_removal_effect as effect
import match
import match_evidence
import owner_admission_profile as owner


@unittest.skipUnless(os.getenv('FFTA_EQUIPMENT_REMOVAL_ROOT'), 'needs the original USA game and recovered source')
class EquipmentRemoval(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_EQUIPMENT_REMOVAL_ROOT']).resolve()
        cls.raw, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, elf = owner.build(
            cls.root, effect.OWNER, selector=effect.equipment.named.EQUIPMENT_SELECTOR)
        cls.image = match.elf_image(elf)

    def test_exact_symbol_original_calls_and_report(self):
        self.assertEqual(self.raw, self.rom[0x1332F8:0x133386])
        self.assertEqual(self.manifest['bindings'], effect.equipment.bindings(effect.CALLS))
        targets = {f'func_{a:08X}': (a, False) for a in effect.CALLS.values()}
        effect.equipment.check_original(self.image, effect.OWNER, self.manifest['bindings'], targets)
        for ordinal in range(len(effect.CALLS)):
            forged = copy.deepcopy(self.manifest['bindings'])
            forged['calls'][ordinal][0] += 2
            with self.assertRaises(ValueError):
                effect.equipment.check_original(self.image, effect.OWNER, forged, targets)
        report = (self.root/'docs/match/081332F8.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, effect.OWNER))
        self.assertIn('at most two nonzero items', report)
        self.assertFalse(match_evidence.report_matches(
            report.replace('at most two nonzero items', 'any number of nonzero items'), self.root, effect.OWNER))

    def test_source_binding(self):
        dest = Path('src/081332F8.c')
        source = (self.root/dest).read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            for old, new in (('entries[2]', 'entries[3]'), ('slot < 5', 'slot < 4'),
                             ('i < count', 'i <= count'), ('state->flags & 0x10', 'state->flags & 0x20')):
                self.assertIn(old, source)
                (root/dest).write_text(source.replace(old, new))
                with self.subTest(change=new), self.assertRaises(ValueError):
                    effect.equipment.check_source(root, effect.OWNER)

    def test_guard_bound_and_caller_changes(self):
        for site in (0x08133308, 0x08133312, 0x08133340, 0x08133348, 0x08133362, 0x08133364,
                     0x0813336C, 0x08133376):
            bad = bytearray(self.raw)
            bad[site-effect.OWNER] ^= 1
            md = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                effect.owner_frame({i.address:i for i in md.disasm(bytes(bad), effect.OWNER)})
        for addr in (0x081338B2, effect.TABLE+12*67, effect.RECORDS+4*156+1, effect.THUNK):
            bad = bytearray(self.rom)
            bad[addr-effect.equipment.BASE] ^= 8 if addr == effect.THUNK else 1
            with self.subTest(site=hex(addr)), self.assertRaises(ValueError):
                effect.dispatch(bad, self.objects)

    def native(self):
        from test_battle_action_value import battle_environment
        cpu, call, write, _ = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        rows = {}
        for group, row, slots, selected in effect.equipment.scene_rows(self.rom):
            rows.setdefault(len(selected), (effect.equipment.GROUPS[group][1]+48*row, slots, selected))
        self.assertEqual(set(rows), {0, 1, 2})
        def prepare(count, flags):
            record, slots, selected = rows[count]
            call(0x080C9644, source, record, 0)
            call(0x080C9644, target, record, 0)
            call(0x0812F2A4, 95, 0, 0)
            call(0x0812F328, 0)
            self.assertEqual(struct.unpack('<I', cpu.mem_read(effect.STATE+0x30, 4))[0], effect.RECORDS+4*156)
            write(effect.STATE, 'I', source)
            write(effect.STATE+8, 'I', target)
            write(effect.STATE+0x26, 'H', flags)
            return slots, selected
        return cpu, call, write, target, prepare

    def test_actual_action_dispatch_and_mutations(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, target, prepare = self.native()
        log = []
        entry_sp = 0x03007F00-12
        def trace(machine, pc, size, user):
            link = machine.reg_read(reg.UC_ARM_REG_LR) & ~1
            r = [machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4)]
            if pc == effect.OWNER:
                self.assertEqual((r[0], link, machine.reg_read(reg.UC_ARM_REG_SP)),
                                 (effect.STATE, 0x081338BE, entry_sp))
                log.append(('owner',))
            elif pc == 0x0812E540:
                log.append(('write', machine.reg_read(reg.UC_ARM_REG_R6)-(entry_sp-36)))
            elif pc == 0x08133348:
                log.append(('read', machine.reg_read(reg.UC_ARM_REG_R5)-(entry_sp-36)))
            elif effect.OWNER <= link < effect.END:
                count = {effect.WRAPPER: 2, effect.equipment.SLOT: 2, effect.CLEAR: 3,
                         effect.VALIDATE: 2, effect.REFRESH: 1}[pc]
                log.append((pc, *r[:count]))
        for pc in (effect.OWNER, 0x0812E540, 0x08133348, *effect.CALLS.values()):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        for count, flags, duplicate in ((0, 0, False), (1, 0, False), (2, 0, False), (2, 0x10, False),
                                        (2, 0, True)):
            with self.subTest(count=count, flags=flags, duplicate=duplicate):
                slots, selected = prepare(count, flags)
                if duplicate:
                    selected = [106, 106]
                    slots = [106, 106, 0, 0, 0]
                    write(target+42, '5H', *slots)
                log.clear()
                call(effect.DISPATCH)
                self.assertEqual(log[0], ('owner',))
                if flags:
                    self.assertEqual(log, [('owner',)])
                    self.assertEqual(list(struct.unpack('<5H', cpu.mem_read(target+42, 10))), slots)
                    continue
                self.assertIn((effect.WRAPPER, target, entry_sp-36), log)
                self.assertEqual([x[1] for x in log if x[0]=='write'], [0, 2][:count])
                if not count:
                    self.assertEqual(log, [('owner',), (effect.WRAPPER, target, entry_sp-36)])
                    continue
                self.assertEqual([x[2] for x in log if x[0]==effect.equipment.SLOT], list(range(29,34)))
                reads = [x[1] for x in log if x[0]=='read']
                self.assertTrue(reads)
                self.assertEqual(reads, [0, 2][:count]*(len(reads)//count))
                clears = [x for x in log if x[0]==effect.CLEAR]
                self.assertEqual([x[1:3] for x in clears], [(target,0)]*len(clears))
                self.assertEqual([x for x in log if x[0]==effect.VALIDATE],
                                 [(effect.VALIDATE, target, 1)]*len(clears))
                self.assertTrue(clears)
                self.assertEqual(log[-1], (effect.REFRESH, target))
                after = struct.unpack('<5H', cpu.mem_read(target+42, 10))
                self.assertFalse(set(selected).intersection(after))
                if duplicate:
                    self.assertEqual([x[3] for x in clears], [0, 0, 1, 1])

    def test_third_entry_reaches_first_saved_word(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, _, write, target, prepare = self.native()
        prepare(2, 0)
        write(target+42, '5H', 106, 107, 162, 0, 0)
        # Run from the actual dispatcher up to the third append, before the saved register is overwritten.
        offsets = []
        def observe(machine, pc, size, user):
            offsets.append(machine.reg_read(reg.UC_ARM_REG_R6) - (0x03007F00-12-36))
        cpu.hook_add(UC_HOOK_CODE, observe, begin=0x0812E540, end=0x0812E540)
        def stop(machine, pc, size, user):
            if len(offsets) == 3:
                machine.emu_stop()
        cpu.hook_add(UC_HOOK_CODE, stop, begin=0x0812E540, end=0x0812E540)
        cpu.reg_write(reg.UC_ARM_REG_SP, 0x03007F00)
        cpu.reg_write(reg.UC_ARM_REG_LR, 0x03007001)
        cpu.emu_start(effect.DISPATCH|1, 0x03007000, count=100000)
        self.assertEqual(offsets, [0, 2, 4])
        self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_PC), 0x0812E540)


if __name__ == '__main__':
    unittest.main()
