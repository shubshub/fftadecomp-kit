import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import movement_overlay as overlay
import test_packed_transfer_task as native


@unittest.skipUnless(os.getenv('FFTA_MOVEMENT_OVERLAY_ROOT'), 'requires USA ROM, agbcc and movement overlay C')
class MovementOverlayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MOVEMENT_OVERLAY_ROOT']).resolve()
        cls.result = owner.build(cls.root, overlay.OWNER, selector=overlay.named.MOVEMENT_OVERLAY_SELECTOR)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_complete_symbol_callback_and_quotient(self):
        import match
        from match_evidence import report_matches

        self.assertEqual(len(self.body), 294)
        self.assertEqual(self.body, self.rom[0x98A88:0x98BAE])
        report = owner.render(overlay.OWNER, self.result)
        self.assertTrue(report_matches(report, self.root, overlay.OWNER))
        self.assertFalse(report_matches(report.replace('"divisor":10', '"divisor":11'), self.root, overlay.OWNER))
        image = match.elf_image(self.elf)
        roles, targets = owner.original_bindings(image, overlay.OWNER, self.rom, self.mapping, self.objects,
                                                selector=overlay.named.MOVEMENT_OVERLAY_SELECTOR, index=self.index)
        self.assertEqual(roles, overlay.bindings())
        for kind, offset, name in (('functions', 272, 'func_08097504'), ('calls', 106, 'func_08142AB0')):
            bad = copy.deepcopy(roles)
            next(entry for entry in bad[kind] if entry[0] == offset)[1] = name
            with self.assertRaises(ValueError):
                overlay.check_original(image, overlay.OWNER, bad, targets)

    def test_full_word_eligibility_return(self):
        bound = overlay.eligibility_result(self.rom, self.mapping)
        self.assertEqual(bound['definitions'], [[0x080975C8, 1], [0x080975CC, 0]])
        # A false value of two or a branch bypassing the assignments invalidates the proof.
        for site, replacement in ((0x080975CC, 0x2002), (0x0809753E, 0xE046)):
            with self.subTest(site=hex(site)):
                changed = bytearray(self.rom)
                struct.pack_into('<H', changed, site-overlay.path.BASE, replacement)
                with self.assertRaises(ValueError):
                    overlay.eligibility_result(bytes(changed), self.mapping)

    def test_ready_state_and_board_scan(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_LR, UC_ARM_REG_PC

        machine = native.TransferTaskTests()
        machine.rom = self.rom
        cpu = machine.cpu()
        cpu.mem_write(overlay.OWNER, self.body)
        cpu.ctl_flush_tb()
        actor, other, unit, other_unit = 0x02010000, 0x02010200, 0x02010400, 0x02010600
        scene, objects, node, next_node = 0x02010800, 0x02010900, 0x02010A00, 0x02010A20
        grid, board, tiles = 0x02011000, 0x02013000, 0x02019000
        display, cells = 0x02008168, 0x02008190
        for address, value in ((actor, unit), (other, other_unit), (actor+0x3C, grid), (actor+0x80, scene),
                               (scene+16, objects), (objects+4, node), (node, actor), (node+8, next_node),
                               (next_node, other), (0x02007F14, board), (display+16, tiles)):
            cpu.mem_write(address, struct.pack('<I', value))
        cpu.mem_write(unit+0x3D, bytes([1]))
        cpu.mem_write(unit+0xF6, bytes([1, 3]))
        cpu.mem_write(other_unit+0xF6, bytes([2, 3]))
        for address in (0x02007F18, 0x02007F1D, 0x02007F1F):
            cpu.mem_write(address, bytes([16]))
        cpu.mem_write(board, bytes([1, 0])*256)
        for x in (1, 2, 3):
            cpu.mem_write(grid+(3*16+x)*7+2, bytes([0x80]))
        cpu.mem_write(display+8, b'\x34\x12')
        cpu.mem_write(cells-1, b'\xA5'*514)
        events = []

        def observe(uc, pc, width, _):
            a, b, c, d = (uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3))
            if pc == 0x08141868:
                self.assertEqual((b, c), (tiles, 0x01001000))
                uc.mem_write(b, bytes(uc.mem_read(a, 4))*(c & 0x1FFFFF))
                uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))
            elif pc == overlay.MARK:
                # The renderer is outside this owner; record its actual dispatched coordinates.
                events.append((pc, a, b, c))
                uc.reg_write(UC_ARM_REG_PC, uc.reg_read(UC_ARM_REG_LR))
            elif pc == overlay.path.ITERATOR:
                self.assertEqual((a, b), (objects, overlay.path.CALLBACK | 1))
                events.append((pc, *bytes(uc.mem_read(c+4, 2))))
            elif pc == overlay.path.ELIGIBLE:
                events.append((pc, b, c, d))
            else:
                events.append((pc,))

        for pc in (overlay.READY, overlay.DISPLAY, overlay.SETUP, overlay.MOVEMENT, overlay.DIV,
                   overlay.path.ELIGIBLE, overlay.path.ITERATOR, overlay.MARK, overlay.SHOW, 0x08141868):
            cpu.hook_add(UC_HOOK_CODE, observe, begin=pc, end=pc)

        def update():
            events.clear()
            return machine.call(cpu, overlay.OWNER, actor)

        self.assertEqual(update(), 0)
        self.assertEqual(events, [(overlay.READY,)])
        cpu.mem_write(grid+0x980, b'\x04')
        self.assertEqual(update(), 0)
        self.assertEqual(events, [(overlay.READY,), (overlay.DISPLAY,)])
        cpu.mem_write(0x02008168, b'\x01\x03')
        self.assertEqual(update(), 0)
        self.assertEqual(events, [(overlay.READY,), (overlay.DISPLAY,), (overlay.DISPLAY,), (overlay.SETUP,)])
        self.assertEqual(bytes(cpu.mem_read(cells-1, 514)), b'\xA5'+bytes(512)+b'\xA5')
        self.assertEqual(bytes(cpu.mem_read(tiles, 0x4000)), b'\x34\x12\x00\x00'*0x1000)
        self.assertEqual(bytes(cpu.mem_read(actor+0x1A, 1)), b'\x01')

        self.assertEqual(update(), 0)
        checked = [event[1:] for event in events if event[0] == overlay.path.ELIGIBLE]
        movement_range = cpu.mem_read(actor+0x1B, 1)[0]
        self.assertGreater(movement_range, 0)
        self.assertEqual(checked, [(x, y, movement_range) for y in range(16) for x in range(16)])
        self.assertEqual(events.count((overlay.MOVEMENT,)), 257)
        self.assertEqual(events.count((overlay.DIV,)), 257)
        self.assertEqual([event[1:] for event in events if event[0] == overlay.path.ITERATOR],
                         [(1, 3), (1, 3), (2, 3), (3, 3), (3, 3)])
        self.assertEqual([event[1:] for event in events if event[0] == overlay.MARK], [(3, 3, 1)])
        self.assertEqual(events[-1], (overlay.SHOW,))
        self.assertEqual(bytes(cpu.mem_read(actor+0x1A, 1)), b'\x02')
        self.assertEqual(update(), 1)
        self.assertEqual(events, [(overlay.READY,), (overlay.DISPLAY,)])
