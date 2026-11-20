"""Native action 95, slot 18, and the live equipment bound of 081311DC."""
import copy
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import target_equipment_chance as gate
import unit_equipment_attribute as equipment


@unittest.skipUnless(os.getenv('FFTA_TARGET_EQUIPMENT_ROOT'), 'requires original ROM and recovered handler')
class TargetEquipmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_TARGET_EQUIPMENT_ROOT']).resolve()
        built = owner.build(cls.root, gate.OWNER, selector=equipment.named.EQUIPMENT_SELECTOR)
        cls.raw, cls.manifest, _, _, _, _, cls.rom, _, elf = built
        cls.image = match.elf_image(elf)

    def test_exact_bytes_bindings_and_report(self):
        self.assertEqual(self.raw, self.rom[0x1311DC:0x131204])
        bindings = self.manifest['bindings']
        targets = {f'func_{address:08X}': (address, False) for address in gate.CALLS.values()}
        equipment.check_original(self.image, gate.OWNER, bindings, targets)
        for index in range(2):
            bad = copy.deepcopy(bindings)
            bad['calls'][index][0] += 2
            with self.assertRaises(ValueError):
                equipment.check_original(self.image, gate.OWNER, bad, targets)
        report = (self.root/'docs/match/081311DC.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, gate.OWNER))
        marker = '"local":[-12,-8]'
        self.assertIn(marker, report)
        self.assertFalse(match_evidence.report_matches(report.replace(marker, '"local":[-12,-6]'),
                                                      self.root, gate.OWNER))

    def test_source_frame_and_dispatch_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/'src').mkdir()
            (root/'include').mkdir()
            (root/'include/ffta.h').write_bytes((self.root/'include/ffta.h').read_bytes())
            src = Path('src/081311DC.c')
            source = (self.root/src).read_text()
            for before, after in [('selected[2]', 'selected[3]'), ('context->target', 'context->source'),
                                  ('if (!func_', 'if (func_')]:
                self.assertIn(before, source)
                (root/src).write_text(source.replace(before, after))
                with self.subTest(before=before), self.assertRaises(ValueError):
                    equipment.check_source(root, gate.OWNER)
        for offset in (2, 6, 8, 16, 18, 24, 30, 32, 34):
            bad = bytearray(self.raw)
            bad[offset] ^= 1
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            ins = {i.address: i for i in decoder.disasm(bytes(bad), gate.OWNER)}
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                gate.frame(ins)
        for address in (gate.TABLE+4*gate.SLOT, gate.SITE, gate.THUNK, 0x08131470):
            bad = bytearray(self.rom)
            bad[address-equipment.BASE] ^= 8 if address == gate.THUNK else 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                gate.callback_route(bad)

    def test_original_dispatch_and_collectors(self):
        from test_battle_action_value import battle_environment
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg

        cpu, call, write, _ = battle_environment(self)
        source, target = 0x02002FC4, 0x020030CC
        choices = {}
        for group, row, _, items in equipment.scene_rows(self.rom):
            choices.setdefault(len(items), (equipment.GROUPS[group][1]+48*row, items))
        self.assertEqual(set(choices), {0, 1, 2})
        call(0x080C9644, source, choices[1][0], 0)
        write(source+0xF6, 'bbb', 2, 3, 1)
        seen = {}

        def observe(machine, pc, width, context):
            r0, r1 = [machine.reg_read(reg.UC_ARM_REG_R0+i) for i in (0, 1)]
            sp = machine.reg_read(reg.UC_ARM_REG_SP)
            if pc == gate.QUERY:
                seen['local'] = r1
                seen['target'] = r0
            elif pc == 0x0812E540:
                dest = machine.reg_read(reg.UC_ARM_REG_R6)
                if seen['local'] <= dest < seen['local']+4:
                    seen.setdefault('appends', []).append(dest-seen['local'])
            elif pc == 0x081311EA:
                seen['count'] = r0
                seen['items'] = struct.unpack('<2H', machine.mem_read(sp, 4))
            elif pc == gate.SITE:
                seen['dispatch'] = (r0, r1, sp)
            elif pc == gate.EVALUATE:
                seen['evaluate'] = r0
            elif pc == 0x0812F05E:
                seen['chance'] = r0
            elif pc == 0x081311FC:
                seen['result'] = r0

        for pc in (gate.SITE, gate.QUERY, 0x0812E540, 0x081311EA, gate.EVALUATE,
                   0x0812F05E, 0x081311FC):
            cpu.hook_add(UC_HOOK_CODE, observe, begin=pc, end=pc)
        for count, (definition, selected) in choices.items():
            call(0x080C9644, target, definition, 0)
            write(target+0xF6, 'bbb', 3, 3, 2)
            call(0x0812F2A4, 95, 0, 0)
            write(gate.STATE, 'II', source, target)
            record = struct.unpack('<I', cpu.mem_read(gate.STATE+0x30, 4))[0]
            self.assertEqual((record, bytes(cpu.mem_read(record, 4))), (0x085540E0, bytes([15,67,18,0])))
            for flagged in (False, True):
                write(target+0xEA, 'B', 2 if flagged else 0)
                seen.clear()
                result = call(gate.DISPATCH)
                context, callback, entry_sp = seen['dispatch']
                self.assertEqual((context, callback, seen['target'], seen['local']),
                                 (gate.STATE, gate.OWNER | 1, target, entry_sp-12))
                self.assertEqual((seen['count'], list(seen['items'])), (count, selected+[0]*(2-count)))
                self.assertEqual(seen.get('appends', []), [0, 2][:count])
                self.assertEqual(seen.get('evaluate'), gate.STATE if count else None)
                base = seen.get('chance', 0)
                expected = ((base >> 1) if base < 100 else base) & 255
                self.assertEqual((seen['result'], result), (expected, expected))
                self.assertEqual(result, ([0,100,100] if flagged else [0,37,34])[count])

    def test_third_item_exceeds_four_bytes(self):
        from test_battle_action_value import battle_environment

        cpu, call, write, allocate = battle_environment(self)
        target = 0x020030CC
        out = allocate(12)
        item = next(items[0] for _, _, _, items in equipment.scene_rows(self.rom) if items)
        # Call the unchanged native producer with enough room to observe all its writes.
        write(target+42, '5H', item, 0, item, 0, item)
        write(out, '6H', *([0xFFFF]*6))
        self.assertEqual(call(gate.QUERY, target, out), 3)
        self.assertEqual(struct.unpack('<6H', cpu.mem_read(out, 12)), (item, item, item, 0xFFFF, 0xFFFF, 0xFFFF))


if __name__ == '__main__':
    unittest.main()
