import copy
import os
import shutil
import tempfile
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import movement_tile_stop as tile
import test_packed_transfer_task as native


@unittest.skipUnless(os.getenv('FFTA_MOVEMENT_TILE_ROOT'), 'requires original USA ROM and movement tile source')
class TileStopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MOVEMENT_TILE_ROOT']).resolve()
        cls.result = owner.build(cls.root, tile.OWNER, selector=tile.overlay.named.MOVEMENT_TILE_SELECTOR)
        cls.body, _, _, cls.mapping, cls.index, cls.objects, cls.rom, _, cls.elf = cls.result

    def test_exact_symbol_and_provenance(self):
        import match
        from match_evidence import report_matches

        self.assertEqual(self.body, self.rom[0x99FB0:0x9A018])
        report = owner.render(tile.OWNER, self.result)
        self.assertTrue(report_matches(report, self.root, tile.OWNER))
        self.assertFalse(report_matches(report.replace('"divisor":10', '"divisor":11'), self.root, tile.OWNER))
        image = match.elf_image(self.elf)
        roles, targets = owner.original_bindings(image, tile.OWNER, self.rom, self.mapping, self.objects,
                                                selector=tile.overlay.named.MOVEMENT_TILE_SELECTOR, index=self.index)
        for kind, site, substitute in (('functions', 100, 'func_08097504'), ('calls', 26, 'func_08142AB0')):
            bad = copy.deepcopy(roles)
            next(row for row in bad[kind] if row[0] == site)[1] = substitute
            with self.assertRaises(ValueError):
                tile.check_original(image, tile.OWNER, bad, targets)

    def test_changed_proof_environment(self):
        from unittest.mock import patch

        with patch.object(tile.overlay, 'environment_fingerprint', return_value={'stale': True}):
            with self.assertRaisesRegex(ValueError, 'movement tile verifier environment changed'):
                owner.build(self.root, tile.OWNER, selector=tile.overlay.named.MOVEMENT_TILE_SELECTOR)

    def test_shared_callback_declarations(self):
        with tempfile.TemporaryDirectory(dir=self.root / 'build') as directory:
            root = Path(directory)
            (root / 'src').mkdir()
            shutil.copytree(self.root / 'include', root / 'include')
            shutil.copy2(self.root / tile.SOURCE, root / tile.SOURCE)
            for header, before, after in (
                    ('object_list.h', 'typedef u32 (*ListCallback)', 'typedef s32 (*ListCallback)'),
                    ('movement_tile.h', 'u8 unknown_00[4];', 'u8 unknown_00[5];'),
                    ('movement_tile.h', 'void *payload', 'TileSearch *payload')):
                with self.subTest(header=header, mutation=after):
                    path = root / 'include' / header
                    original = path.read_text()
                    self.assertIn(before, original)
                    path.write_text(original.replace(before, after))
                    with self.assertRaisesRegex(ValueError, 'shared tile declarations differ'):
                        tile.check_source(root, tile.OWNER)
                    path.write_text(original)

    def test_range_and_occupants(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3

        runner = native.TransferTaskTests()
        runner.rom = self.rom
        cpu = runner.cpu()
        actor, other, unit, other_unit = 0x02010000, 0x02010200, 0x02010400, 0x02010600
        scene, objects, node, next_node = 0x02010800, 0x02010900, 0x02010A00, 0x02010A20
        grid, board = 0x02011000, 0x02013000
        for addr, value in ((actor,unit), (other,other_unit), (actor+0x3C,grid), (actor+0x80,scene),
                            (scene+16,objects), (objects+4,node), (node,actor), (node+8,next_node),
                            (next_node,other), (0x02007F14,board)):
            cpu.mem_write(addr, struct.pack('<I',value))
        cpu.mem_write(unit+0xF6, bytes([1,3]))
        cpu.mem_write(other_unit+0xF6, bytes([2,3]))
        for address in (0x02007F18, 0x02007F1D, 0x02007F1F):
            cpu.mem_write(address, bytes([16]))
        cpu.mem_write(board, bytes([1,0])*256)
        for x in (1,2,3):
            cpu.mem_write(grid+(3*16+x)*7+2, bytes([0x80]))
        events = []

        def trace(uc, pc, width, context):
            args = [uc.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)]
            if pc == tile.overlay.DIV:
                events.append((pc, *args[:2]))
            elif pc == tile.path.CALLBACK:
                events.append((pc, args[0], *bytes(uc.mem_read(args[1]+4, 2))))
            else:
                events.append((pc, *args))

        for pc in (tile.overlay.DIV, tile.path.ELIGIBLE, tile.path.CALLBACK):
            cpu.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        for movement, x, y, result, visits in ((0,1,3,1,[node]), (0,3,3,0,[]), (1,1,3,1,[node]),
                (1,2,3,0,[node,next_node]), (1,3,3,1,[node,next_node]), (1,4,3,0,[]),
                (1,257,259,1,[node]), (1,255,3,0,[]), (1,3,-1,0,[])):
            with self.subTest(movement=movement, x=x, y=y):
                cpu.mem_write(unit+0x3D, bytes([movement]))
                events.clear()
                self.assertEqual(runner.call(cpu, tile.OWNER, actor, x, y), result)
                signed_x = ((x+128)%256-128) & 0xFFFFFFFF
                signed_y = ((y+128)%256-128) & 0xFFFFFFFF
                self.assertEqual(events[:2], [(tile.overlay.DIV,movement*10,10),
                    (tile.path.ELIGIBLE,actor,signed_x,signed_y,movement)])
                self.assertEqual(events[2:], [(tile.path.CALLBACK,item,x&255,y&255) for item in visits])
