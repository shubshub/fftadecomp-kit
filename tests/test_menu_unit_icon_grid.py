"""Exercise both original caller loops, including the native decoder and tile writes."""
from copy import deepcopy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match_evidence
import menu_unit_icon_grid as grid
import owner_admission_profile as owner


def icon_bytes(rom, number):
    archive = grid.unit.ARCHIVE-grid.menu.BASE
    dictionary = struct.unpack_from('>I', rom, archive+4)[0]
    position = struct.unpack_from('>I', rom, archive+8+4*number)[0]
    end = dictionary if number == 43 else struct.unpack_from('>I', rom, archive+12+4*number)[0]
    output = bytearray()
    while position < end:
        token = rom[archive+position]
        position += 1
        if token & 0x80:
            count = (token & 0x7F)+1
            output.extend(rom[archive+position:archive+position+count])
            position += count
        else:
            index = ((token << 8) | rom[archive+position]) & 1023
            first = archive+dictionary+4+index
            output.extend(rom[first:first+(token >> 2)+3])
            position += 1
    return bytes(output)


def eligible(rom, graphic, ability):
    record = 0x521A14+52*graphic
    while rom[record+5]:
        redirect = rom[record+5]
        record = 0x521A14+52*(graphic if redirect == 255 else redirect)
    kind = rom[0x51D180+32*ability+8]
    if kind == 22:
        return int(rom[record+4] == 4)
    mask = struct.unpack_from('<I',rom,0x51D0F4+4*rom[record+0x2D])[0]
    if kind in (23,25) and ability in (0x11F,0x137,0x13C) and rom[record+4] != 4:
        return 0
    return int(bool(mask & (1 << (kind-1))))


@unittest.skipUnless(os.environ.get('FFTA_UNIT_ICON_GRID_ROOT'), 'requires the original ROM, source and agbcc')
class UnitIconGridTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_UNIT_ICON_GRID_ROOT'])
        result = owner.build(cls.root, grid.OWNER, selector=grid.named.DATAFREE_SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, cls.instructions, _ = result

    def test_replay(self):
        report = (self.root/'docs/match/080701BC.md').read_text()
        self.assertEqual((len(self.body), self.instructions), (164,75))
        self.assertTrue(match_evidence.report_matches(report,self.root,grid.OWNER))
        self.assertFalse(match_evidence.report_matches(report.replace('"last_id":43','"last_id":44'),
                                                       self.root,grid.OWNER))

    def test_rejects_changed_callers_streams_and_bindings(self):
        def bind(rom, bindings):
            proof = grid.UnitIconGridProof(rom,self.mapping,self.index,self.objects)
            proof.bind_row(self.body,grid.OWNER,{grid.OWNER+s:t for s,t in grid.CALLS.items()},bindings)
            return proof
        bindings = self.manifest['bindings']
        for offset in (0x6AEE0,0x6CF9C,0x701FE,0x2ACA0,0xCBA10,0x53C8,0x541C,0x3B9110,0x3B8F54,0x14186C):
            with self.subTest(offset=hex(offset)), self.assertRaises(ValueError):
                bind(self.rom[:offset]+bytes([self.rom[offset]^1])+self.rom[offset+1:],bindings)
        wrong = deepcopy(bindings)
        wrong['calls'][1][1] = 'func_080CB980'
        with self.assertRaises(ValueError):
            bind(self.rom,wrong)
        with self.assertRaisesRegex(ValueError,'both local buffer calls'):
            bind(self.rom,bindings).row_manifest()

    def execute(self, *, caller=None, ability=1, graphic=None, flag=1):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn.arm_const import (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,
                                     UC_ARM_REG_PC,UC_ARM_REG_SP,UC_ARM_REG_LR)
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for base, size in ((grid.menu.BASE,len(self.rom)),(0x02000000,0x40000),
                           (0x03000000,0x8000),(0x06000000,0x18000)):
            cpu.mem_map(base,size)
        cpu.mem_write(grid.menu.BASE,self.rom)
        cpu.mem_write(grid.OWNER,self.body)
        regs = [UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3]
        sp, menu, tile_map = 0x03007B00,0x02018000,0x030008B0
        tiles, pixels = 0x0600E800,0x0600AE00
        stride = 32 if caller else 35
        fill = 0xA5
        expected_map = bytearray([fill])*(2*32*stride)
        expected_graphics = bytearray([fill])*0x2C00
        cpu.mem_write(tiles-4,bytes([fill])*(len(expected_map)+8))
        cpu.mem_write(pixels-4,bytes([fill])*(len(expected_graphics)+8))
        cpu.mem_write(sp-600,bytes([0x6D])*640)
        initial_globals = struct.pack('<III',17,3,0x02009000)
        cpu.mem_write(0x03002BB0,initial_globals)
        cpu.mem_write(0x0200F428,struct.pack('<I',menu))
        cpu.mem_write(menu+0x44EC,struct.pack('<H',ability))
        cpu.mem_write(tile_map+12,bytes([stride]))
        cpu.mem_write(tile_map+20,struct.pack('<I',tiles))
        cpu.reg_write(UC_ARM_REG_SP,sp)
        if caller:
            start, end = caller-0x60,caller
            cases = [(i,4*((i-2)%7)+1,3*((i-2)//7)+2,eligible(self.rom,i,ability),pixels+256*i)
                     for i in range(2,44)]
        else:
            start, end = grid.OWNER,0x08012000
            cases = [(graphic & 255,8,5,flag & 255,pixels+0x240)]
            for register,value in zip(regs,(tile_map,pixels+0x240,graphic,flag)):
                cpu.reg_write(register,value)
            cpu.mem_write(sp,struct.pack('<II',0x108,0x105))
        cpu.reg_write(UC_ARM_REG_LR,end|1)
        calls, copies = [], []

        def observe_root(c, pc, size, context):
            tile, dest, idx, keep = [c.reg_read(r) for r in regs]
            x,y = struct.unpack('<II',c.mem_read(sp,8))
            actual = (idx & 255,x & 255,y & 255,keep & 255,dest)
            self.assertEqual(tile,tile_map)
            self.assertEqual(actual,cases[len(calls)])
            calls.append(actual)

        def cpu_set(c, interrupt, context):
            self.assertEqual(c.reg_read(UC_ARM_REG_PC),grid.item.COPY+2)
            src,dest,control = [c.reg_read(r) for r in regs[:3]]
            idx,x,y,keep,expected_dest = cases[len(copies)]
            self.assertEqual((src,dest,control),(sp-288,expected_dest,128))
            selected = 45 if idx==77 or idx>82 else min(idx,44)
            expected = icon_bytes(self.rom,selected-2) if idx>=2 else bytes([0x6D])*256
            self.assertEqual(len(expected),256)
            self.assertEqual(c.mem_read(src,256),expected)
            c.mem_write(dest,bytes(c.mem_read(src,256)))
            expected_graphics[dest-pixels:dest-pixels+256] = expected
            palette_index = 45 if idx>82 else min(idx,44)
            palette = self.rom[0x3B8F50+4*(palette_index-1)] >> 4
            if not keep:
                palette = (palette-6)&255
            first = ((dest-0x06008000) >> 5)&0xFFFF
            for line in range(2):
                offset = 2*((y+line)*stride+x)
                for col in range(4):
                    struct.pack_into('<H',expected_map,offset+2*col,((palette << 12)|(first+4*line+col))&0xFFFF)
            copies.append(idx)

        cpu.hook_add(UC_HOOK_CODE,observe_root,begin=grid.OWNER,end=grid.OWNER)
        cpu.hook_add(UC_HOOK_INTR,cpu_set)
        cpu.emu_start(start|1,end,count=2000000)
        self.assertEqual((cpu.reg_read(UC_ARM_REG_PC),cpu.reg_read(UC_ARM_REG_SP)),(end,sp))
        self.assertEqual(copies,[case[0] for case in cases])
        self.assertEqual(calls,cases)
        self.assertEqual(cpu.mem_read(pixels-4,len(expected_graphics)+8),bytes([fill])*4+expected_graphics+bytes([fill])*4)
        self.assertEqual(cpu.mem_read(tiles-4,len(expected_map)+8),bytes([fill])*4+expected_map+bytes([fill])*4)
        expected_globals = struct.pack('<III',256,0xFFFFFFFF,sp-288) if cases[-1][0]>=2 else initial_globals
        self.assertEqual(cpu.mem_read(0x03002BB0,12),expected_globals)
        return {case[3] for case in cases}

    def test_both_original_grid_callers(self):
        for after,ability in ((0x0806AF3E,1),(0x0806CFBA,0x11F)):
            with self.subTest(after=hex(after)):
                self.assertEqual(self.execute(caller=after,ability=ability),{0,1})

    def test_palette_and_graphic_remaps_and_uninitialized_inputs(self):
        for graphic,flag in ((0,1),(1,0),(44,0),(77,1),(82,1),(0x153,0x100)):
            with self.subTest(graphic=graphic):
                self.execute(graphic=graphic,flag=flag)


if __name__ == '__main__':
    unittest.main()
