import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import movement_path_prefix as path
import test_packed_transfer_task as native


@unittest.skipUnless(os.getenv('FFTA_MOVEMENT_PATH_ROOT'), 'requires USA ROM, agbcc and movement path source')
class MovementPathTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MOVEMENT_PATH_ROOT']).resolve()
        cls.result = owner.build(cls.root, path.OWNER, selector=path.named.MOVEMENT_PATH_SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result
        cls.report = owner.render(path.OWNER, cls.result)

    def test_canonical_report_and_closed_bindings(self):
        import match
        from match_evidence import report_matches
        self.assertEqual(self.body, self.rom[0x989AC:0x98A88])
        self.assertTrue(report_matches(self.report, self.root, path.OWNER))
        self.assertIn('"path_argument":5', self.report)
        self.assertFalse(report_matches(self.report.replace('"path_argument":5', '"path_argument":4'),
                                        self.root, path.OWNER))
        image = match.elf_image(self.elf)
        roles, targets = owner.original_bindings(image, path.OWNER, self.rom, self.mapping, self.objects,
                                                 selector=path.named.MOVEMENT_PATH_SELECTOR, index=self.index)
        self.assertEqual(roles, path.bindings())
        for kind, position, replacement in (('functions', 0, [104, 'func_08097504']),
                                             ('calls', 2, [90, 'func_08149384'])):
            bad = copy.deepcopy(roles)
            bad[kind][position] = replacement
            with self.assertRaises(ValueError):
                path.check_original(image, path.OWNER, bad, targets)

    def test_original_copy_and_caller(self):
        record = path.original_path(self.rom, self.mapping, self.index)
        self.assertEqual(record['copies'][0], [1, 92, 4])
        self.assertEqual(record['copies'][-1], [24, 0, 96])
        self.assertEqual(self.manifest['proof']['action_state_path'], [0x124, 0x1A4])
        for site in (0x0814933C, 0x08148A32, path.COPY_SLOT):
            bad = bytearray(self.rom)
            bad[site-path.BASE] ^= 1
            with self.assertRaises(ValueError):
                path.original_path(bytes(bad), self.mapping, self.index)

    def test_original_caller_grid_and_tile_search(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2

        machine = native.TransferTaskTests()
        machine.rom = self.rom
        actor, other, first_unit, other_unit = 0x02010000, 0x02010200, 0x02010400, 0x02010600
        scene, objects, node, second_node = 0x02010800, 0x02010900, 0x02010A00, 0x02010A20
        grid, board, action_state = 0x02011000, 0x02013000, 0x02015000
        destination = action_state + 0x124
        # Exercise the full caller-owned allocation and the adjacent count field.
        untouched = bytes([0xEE]) * 132
        output = bytes([1, 3, 1, 0, 2, 3, 2, 0, 3, 3, 3, 0])
        for body in (self.rom[0x989AC:0x98A88], self.body):
            cpu = machine.cpu()
            cpu.mem_write(path.OWNER, body)
            cpu.ctl_flush_tb()
            for address, value in ((actor, first_unit), (other, other_unit), (actor+0x3C, grid),
                                   (actor+0x80, scene), (scene+16, objects), (objects+4, node),
                                   (node, actor), (node+8, second_node), (second_node, other),
                                   (second_node+8, 0), (0x02007F14, board)):
                cpu.mem_write(address, struct.pack('<I', value))
            cpu.mem_write(first_unit+0xF6, bytes([1, 3]))
            for address in (0x02007F18, 0x02007F1D, 0x02007F1F):
                cpu.mem_write(address, bytes([16]))
            cpu.mem_write(board, bytes([1, 0])*256)
            for x in (1, 2, 3):
                cpu.mem_write(grid+(3*16+x)*7, bytes([x, 0, 0x8F if x == 1 else 0x80, 0, x-1, 0, 0]))
            events = []

            def trace(uc, site, size, _):
                events.append((site, *(uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2))))

            for site in (path.OWNER, path.PATH, path.TRACE, path.ITERATOR, path.CALLBACK,
                         path.ELIGIBLE, path.COPY_ENTRY):
                cpu.hook_add(UC_HOOK_CODE, trace, begin=site, end=site)
            for x, movement, occupied, result, scans in (
                    (4, 0, (8, 8), -1, []), (3, 2, (3, 3), -1, []),
                    (3, 0, (8, 8), 1, [3, 2, 1]), (3, 1, (8, 8), 2, [3, 2]),
                    (3, 1, (2, 3), 1, [3, 2, 1]), (3, 2, (8, 8), 3, [3])):
                with self.subTest(x=x, movement=movement, occupied=occupied, result=result):
                    events.clear()
                    cpu.mem_write(other_unit+0xF6, bytes(occupied))
                    cpu.mem_write(destination, untouched)
                    got = machine.call(cpu, path.WRAPPER, actor, x, 3, movement, destination)
                    self.assertEqual(got, result & 0xFFFFFFFF)
                    self.assertEqual([a[2] for a in events if a[0] == path.ELIGIBLE], scans)
                    self.assertIn((path.OWNER, actor, x, 3), events)
                    copies = [a for a in events if a[0] == path.COPY_ENTRY]
                    if result < 0:
                        self.assertEqual(copies, [])
                        self.assertEqual(bytes(cpu.mem_read(destination, 132)), untouched)
                    else:
                        self.assertIn((path.PATH, grid, destination, x), events)
                        self.assertIn((path.TRACE, grid, path.LAST, x), events)
                        self.assertEqual(copies, [(path.COPY_ENTRY, destination, path.LAST-8, len(output))])
                        self.assertEqual(bytes(cpu.mem_read(destination, 132)), output+untouched[len(output):])
                    for lookup in [a for a in events if a[0] == path.ITERATOR]:
                        self.assertEqual(lookup[1:3], (objects, path.CALLBACK | 1))
                        self.assertIn((path.CALLBACK, node, lookup[3]), [a[:3] for a in events])


if __name__ == '__main__':
    unittest.main()
