"""Original AI action records and all five native evaluator results."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import battle_action_dispatch as dispatch
import match
import match_evidence
import owner_admission_profile as owner
import unit_equipment_attribute as equip
from test_battle_action_value import battle_environment


@unittest.skipUnless(os.environ.get('FFTA_BATTLE_DISPATCH_ROOT'), 'requires original USA ROM and battle dispatch C')
class DispatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_BATTLE_DISPATCH_ROOT']).resolve()
        cls.built = owner.build(cls.root, dispatch.OWNER, selector=equip.named.EQUIPMENT_SELECTOR)
        cls.rom = cls.built[6]

    def test_exact_symbol_and_receipt(self):
        raw, manifest, _, mapping, index, objects, rom, _, elf = self.built
        self.assertEqual(raw, rom[0xC01D0:0xC034C])
        self.assertEqual(manifest['bindings'], dispatch.BINDINGS)
        image = match.elf_image(elf)
        for name in ('func_080BF5A4', '_call_via_r2', dispatch.TABLE):
            changed = copy.deepcopy(image)
            next(s for s in changed['symbols'] if s['name'] == name)['size'] = 4
            with self.subTest(name=name), self.assertRaises(ValueError):
                owner.original_bindings(changed, dispatch.OWNER, rom, mapping, objects,
                                        selector=equip.named.EQUIPMENT_SELECTOR, index=index)
        report = (self.root/'docs/match/080C01D0.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, dispatch.OWNER))
        for old, new in (('"aligned_zero_words":135','"aligned_zero_words":134'),
                         ('at most two qualifying','at most five qualifying')):
            altered = report.replace(old, new)
            self.assertNotEqual(altered, report)
            self.assertFalse(match_evidence.report_matches(altered, self.root, dispatch.OWNER))

    def test_receipt_binds_dispatch_producer(self):
        report = (self.root/'docs/match/080C01D0.md').read_text()
        self.assertIn('* control flow: ' + equip.named.BATTLE_DISPATCH_CONTROL_FLOW, report.splitlines())
        environment = self.built[1]['proof']['environment']
        self.assertEqual(environment, equip.environment_fingerprint())
        producer = 'battle_action_dispatch.py'
        digest = environment['sources'][producer]
        self.assertFalse(match_evidence.report_matches(
            report.replace(f'"{producer}":"{digest}"', f'"{producer}":"' + '0'*64 + '"'), self.root, dispatch.OWNER))
        changed = copy.deepcopy(environment)
        changed['sources'][producer] = '0' * 64
        with patch.object(equip, 'environment_fingerprint', return_value=changed):
            self.assertFalse(match_evidence.report_matches(report, self.root, dispatch.OWNER))

    def setup_scene(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as reg
        cpu, call, write, allocate = battle_environment(self)
        self.cpu, self.call, self.write, self.allocate = cpu, call, write, allocate
        self.source, self.target = 0x02002FC4, 0x020030CC
        self.left, self.right = allocate(0x84), allocate(0x84)
        collection, self.queue, self.nodes = allocate(0x100), allocate(0x100), allocate(32)
        write(self.left, 'I', self.source)
        write(self.right, 'I', self.target)
        write(self.left+128, 'I', collection)
        write(self.right+128, 'I', collection)
        write(collection+16, 'I', self.queue)
        write(self.queue+4, 'I', self.nodes)
        write(self.nodes, 'III', self.left, 0, self.nodes+16)
        write(self.nodes+16, 'III', self.right, self.nodes, 0)
        write(0x0200F4B0, 'I', collection)
        self.selection = allocate(20)
        self.state = allocate(dispatch.SIZE+8)+4
        self.group, self.other, self.positions = allocate(0x290C), allocate(0x290C), allocate(1024)
        call(0x080C9644, self.target, equip.GROUPS[2][1]+48, 0)
        self.trace = {}

        def enter(machine, pc, size, context):
            values = tuple(machine.reg_read(reg.UC_ARM_REG_R0+i) for i in range(4))
            self.trace.setdefault(pc, []).append(values)

        for pc in (dispatch.OWNER, dispatch.boot.DESTINATION, dispatch.ALLOC, dispatch.QUERY, dispatch.UNIT_FLAG,
                   dispatch.ABILITY, equip.WRAPPER, dispatch.KIND, 0x080C02DE, 0x080C09B4):
            cpu.hook_add(UC_HOOK_CODE, enter, begin=pc, end=pc)
        cpu.ctl_flush_tb()

    def read(self, pointer, fmt):
        return struct.unpack('<'+fmt, self.cpu.mem_read(pointer, struct.calcsize('<'+fmt)))

    def test_initialized_units_and_native_callbacks(self):
        self.setup_scene()
        seen, counts, kinds, flags = set(), set(), set(), set()
        for group, row, slots, selected in equip.scene_rows(self.rom):
            self.call(0x080C9644, self.source, equip.GROUPS[group][1]+48*row, 0)
            self.assertEqual(self.read(self.source+42,'5H'), tuple(slots))
            items = [] if self.read(self.source+0xE9,'B')[0] & 1 else sorted(selected, reverse=True,
                key=lambda item: struct.unpack_from('<b', self.rom, equip.ITEMS-equip.BASE+32*item+16)[0])
            counts.add(len(items))
            first = items[0] if items else 0
            equipment_kind = 19 if self.call(0x080C92F0, self.source, 40) & 4 else (
                self.rom[equip.ITEMS-equip.BASE+32*first+8] if first else 17)
            for action in (0, 1, 22, 103, 110, 146, 231, 265):
                attr = 0x55187C + 28*action
                mode, kind = self.rom[attr+6], self.rom[attr+8]
                for side, target in enumerate((self.right, self.left)):
                    self.write(self.selection, 'HH', action, 7)
                    self.cpu.mem_write(self.state-4, bytes([0xA5])*(dispatch.SIZE+8))
                    self.trace.clear()
                    callback = self.call(dispatch.OWNER, self.state, self.left, target, self.group, self.other,
                                         self.selection, side, self.positions, side)
                    small, large = self.read(self.state+0x200, 'II')
                    self.assertTrue(0x02000000 <= small <= 0x02040000-256)
                    self.assertTrue(0x02000000 <= large <= 0x02040000-1024)
                    self.assertTrue(small+256 <= large or large+1024 <= small)
                    self.assertEqual(self.trace[dispatch.boot.DESTINATION][0][:2], (self.state, 540))
                    self.assertEqual([v[0] for v in self.trace[dispatch.ALLOC]], [1024,256])
                    target_flags = side*4
                    if action == 265:
                        expected = 0x080BF5A4
                    elif not action or mode & 128:
                        target_flags |= 1
                        self.assertEqual(self.trace[equip.WRAPPER][0][:2], (self.source,0x03007F00-36))
                        self.assertEqual(self.trace[dispatch.KIND][0][:2], (self.source,first))
                        self.assertEqual(self.trace[0x080C02DE][0][0]&255, equipment_kind)
                        kinds.add(equipment_kind)
                        expected = 0x080BF7C4 if equipment_kind in (13,14,19) else 0x080BFDB0
                    elif kind in (4,6,7) or mode & 64:
                        expected = 0x080BFDB0
                    else:
                        expected = 0x080BEAC8 if target == self.left else 0x080BEF28
                    image = bytearray(dispatch.SIZE)
                    struct.pack_into('<IIHHIII', image, 0, self.left, target, action, 7, self.group,
                                     self.other, self.selection)
                    image[40] = side
                    struct.pack_into('<II', image, 0x200, small, large)
                    struct.pack_into('<I', image, 0x214, self.positions)
                    image[0x218] = target_flags
                    self.assertEqual(self.cpu.mem_read(self.state-4, dispatch.SIZE+8),
                                     bytes([0xA5])*4 + image + bytes([0xA5])*4)
                    self.assertEqual(callback, expected|1)
                    seen.add(callback & ~1)
                    flags.add(target_flags)
                    self.call(0x08022854, small)
                    self.call(0x08022854, large)
        self.assertEqual(seen, set(dispatch.EVALUATORS.values()))
        self.assertEqual(counts, {0,1,2})
        self.assertEqual(flags, {0,1,4,5})
        self.assertTrue({13,14,17,19} <= kinds)

    def test_native_scene_list_flag(self):
        self.setup_scene()
        # Scene 29 starts with unit kind 20. Its actual initializer sets bit 12,
        # the same bit tested by the placed list's 0809AB3C callback.
        scene = struct.unpack_from('<H2xI', self.rom, equip.SCENES-equip.BASE+29*40)
        self.assertEqual(scene, (4, 0x0852CF00))
        self.call(0x080C9644, self.target, scene[1], 0)
        self.assertEqual(self.call(0x080C8298, self.target), 1)
        self.call(0x080C9644, self.source, equip.GROUPS[37][1]+3*48, 0)
        self.write(self.selection, 'HH', 265, 0)
        for populated in (False, True):
            self.write(self.queue+4, 'I', self.nodes if populated else 0)
            for marked in (0, 1):
                self.call(0x080CDDF4, self.source, marked)
                self.trace.clear()
                self.assertEqual(self.call(dispatch.OWNER, self.state, self.left, self.right, self.group,
                                           self.other, self.selection, 0, self.positions, 1), 0x080BF5A5)
                self.assertEqual(dispatch.UNIT_FLAG in self.trace, populated)
                self.assertEqual(self.read(self.state+0x218,'B'), (4 + 2*(populated and not marked),))
                for ptr in self.read(self.state+0x200, 'II'):
                    self.call(0x08022854, ptr)

    def test_uniform_callback_arguments_and_narrow_result(self):
        from unicorn import arm_const as reg

        self.setup_scene()
        workspace = self.allocate(0x4504)
        self.write(self.state + 0x1B8, 'H', 0xFFFF)
        for target in dispatch.EVALUATORS.values():
            with self.subTest(callback=hex(target)):
                self.assertEqual(self.call(target, self.state, workspace), 1)

        # Execute the original caller's shifts, compare and conditional branch.
        for full, expected, destination in ((0, 0, 0x080C0A08), (1, 1, 0x080C0A04),
                                            (0x100, 0, 0x080C0A08), (0x807FFF01, 1, 0x080C0A04),
                                            (0xFFFFFFFE, 254, 0x080C0A04)):
            with self.subTest(result=hex(full)):
                self.cpu.reg_write(reg.UC_ARM_REG_R0, full)
                self.cpu.emu_start(0x080C09FC | 1, 0x080C0A08, count=4)
                self.assertEqual(self.cpu.reg_read(reg.UC_ARM_REG_R4), expected)
                self.assertEqual(self.cpu.reg_read(reg.UC_ARM_REG_PC), destination)

    def test_action_record_producer_and_complete_ai_caller(self):
        self.setup_scene()
        parent, workspace = self.allocate(0x553C), self.allocate(0x4504)
        self.write(parent, 'II', workspace, self.left)
        self.write(parent+0x54EC, 'I', self.positions)
        self.call(0x080C9644, self.source, equip.GROUPS[37][1]+3*48, 0)
        self.write(self.source+0xF6, 'BB', 6, 6)
        self.write(self.target+0xF6, 'BB', 7, 6)
        # Native producer selects one action for the target in the second group.
        target_group = parent+0x74+0x290C
        self.write(target_group, 'I', self.right)
        self.write(target_group+0x2908, 'H', 1)
        selection = self.allocate(0x58)
        self.write(selection, 'IH', self.left, 55)
        self.assertEqual(self.call(0x080C26EC, target_group, selection, 0, 1, 0, 0), 1)
        self.assertEqual(self.read(target_group+0x324, 'H'), (1,))
        record = target_group+4
        self.assertEqual(self.read(record, 'HH'), (55,0))
        self.assertGreater(self.read(record+12,'h')[0], 0)
        self.write(parent+0x54AC, 'BBB', 1, 0, 0)
        self.write(parent+0x54F4, 'H', 3)
        self.trace.clear()
        self.call(0x080C045C, parent)
        state = parent+0x5290
        self.assertEqual(self.trace[dispatch.OWNER], [(state,self.left,self.right,target_group)])
        self.assertEqual(self.read(state+12, 'III'), (target_group,parent+0x74,record))
        self.assertEqual(self.read(parent+0x54F4, 'H'), (4,))
        self.assertEqual(self.trace[0x080C09B4][0][0], 0x080BEF29)
        self.assertEqual(self.read(parent+0x528C,'I'), (0x080BEF29,))
