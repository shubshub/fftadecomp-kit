"""Original menu callers, decoder boundaries, invalid graphics and report replay."""
from copy import deepcopy
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match_evidence
import menu_unit_tile_row as row
import owner_admission_profile as owner


def replace(data, offset, value):
    return data[:offset] + value + data[offset+len(value):]


@unittest.skipUnless(os.environ.get('FFTA_UNIT_TILE_ROW_ROOT'), 'requires the original ROM, row and agbcc')
class UnitTileRowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_UNIT_TILE_ROW_ROOT'])
        cls.result = owner.build(cls.root,row.OWNER,selector=row.named.SELECTOR)
        cls.body,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,_ = cls.result

    def bind(self, *, rom=None, bindings=None, address=row.OWNER):
        proof = row.UnitTileRowProof(self.rom if rom is None else rom,self.mapping,self.index,self.objects)
        proof.bind_row(self.body,address,{row.OWNER+s:t for s,t in row.CALLS.items()},
                       self.manifest['bindings'] if bindings is None else bindings)
        return proof

    def test_saved_native_proof_and_environment(self):
        self.assertEqual(self.body,self.rom[0x57cdc:0x57e24])
        self.assertEqual(self.result[7],141)
        report = (self.root/'docs/match/08057CDC.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,row.OWNER))
        self.assertFalse(match_evidence.report_matches(report.replace('"entries":44','"entries":43'),
                                                       self.root,row.OWNER))
        original = self.manifest['proof']['buffers']['unit_tile_row']['environment']
        drift = dict(original, toolchain=[])
        for samples in ((original,drift,original),(original,original,drift)):
            with patch.object(row,'environment_fingerprint',side_effect=samples):
                with self.assertRaisesRegex(ValueError,'changed during compilation'):
                    owner.build(self.root,row.OWNER,selector=row.named.SELECTOR)

    def test_original_calls_objects_conditions_and_consumer(self):
        self.assertIsNone(owner.tile_row_profile(0x08057C88,row.named.SELECTOR))
        self.assertIsNone(owner.tile_row_profile(row.OWNER,row.named.ROOT_SCRATCH_SELECTOR))
        with self.assertRaises(ValueError):
            self.bind(address=row.OWNER+2)
        for role,idx,value in (('calls',5,[0xD2,'func_080CB980']),('data',0,[0x70,'g_state_02000080',0])):
            bindings = deepcopy(self.manifest['bindings'])
            bindings[role][idx] = value
            with self.subTest(role=role), self.assertRaises(ValueError):
                self.bind(bindings=bindings)
        for at in (0x55ce4,0x55e8c,0x5718c,0x572ea,0x57d40,0x57d68,0x57db6,0x57e0a,
                   0xcb9ea,0xcba10,0x53c8,0x52de,0x14186c,0x5412):
            with self.subTest(addr=hex(at)), self.assertRaises(ValueError):
                self.bind(rom=replace(self.rom,at,bytes([self.rom[at]^1])))
        with self.assertRaisesRegex(ValueError,'both live'):
            self.bind().row_manifest()

    def test_stream_bounds_and_remap(self):
        archive = self.rom[row.ARCHIVE-row.menu.BASE:row.END-row.menu.BASE]
        def check(data):
            return row.item.check_mode0_archive(data,row.END-row.ARCHIVE,44,256)
        self.assertEqual(check(archive)['entries'],44)
        dictionary,first = struct.unpack_from('>II',archive,4)
        last, = struct.unpack_from('>I',archive,8+43*4)
        for offset,val in ((dictionary+2,b'\x00\x80'),(first,b'\xff'),
                           (8+43*4,struct.pack('>I',dictionary-1)),(last,b'\xff')):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                check(replace(archive,offset,val))
        indices = [row.graphic_index(i) for i in (0,1,2,43,44,76,77,78,82,83,255)]
        self.assertEqual(indices,[65534,65535,0,41,42,42,43,42,42,43,43])

    def execute(self, mode, graphic, flags, *, caller=False):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,
            UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_PC,UC_ARM_REG_SP,UC_ARM_REG_LR)
        cpu=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for base,size in ((row.menu.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),
                          (0x06000000,0x18000)):
            cpu.mem_map(base,size)
        cpu.mem_write(row.menu.BASE,self.rom)
        cpu.mem_write(row.OWNER,self.body)
        menu,unit,sp,tiles,returned=0x02018000,0x02000080+23*264,0x03007B00,0x06001000,0x08012000
        window,context,name=menu+0x14BC,menu+0x19C8,0x02002000
        cpu.mem_write(0x0200F428,struct.pack('<I',menu))
        cpu.mem_write(0x030008C0,struct.pack('<I',tiles))
        cpu.mem_write(unit,struct.pack('<I',name))
        cpu.mem_write(unit+7,bytes([graphic]))
        cpu.mem_write(unit+40,struct.pack('<H',flags))
        cpu.mem_write(menu+0x2d3a+3,b'\x17')
        cpu.mem_write(window+0x15,b'\x06')
        cpu.mem_write(window+0x1a,struct.pack('<HH',2,7))
        cpu.mem_write(0x03002BB0,struct.pack('<III',17,3,0x02009000))
        cpu.mem_write(sp-400,b'\x6D'*420)
        cpu.mem_write(tiles,b'\x7E'*8192)
        regs=(UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3)
        cpu.reg_write(UC_ARM_REG_SP,sp)
        cpu.reg_write(UC_ARM_REG_LR,returned|1)
        if caller:
            # These native callers load the unit ID from menu+0x2D3A and store mode on SP.
            entry = (0x08055CD4,0x08057178)[mode]
            returned = (0x08055CEC,0x08057190)[mode]
            for reg,v in ((UC_ARM_REG_R0,menu),(UC_ARM_REG_R2,0x19c8),(UC_ARM_REG_R4,1),
                          (UC_ARM_REG_R5,3),(UC_ARM_REG_R6,window)):
                cpu.reg_write(reg,v)
        else:
            entry=row.OWNER
            for reg,v in zip(regs,(window,context,23,1)):
                cpu.reg_write(reg,v)
            cpu.mem_write(sp,struct.pack('<I',mode))
        first=tiles+(7+3*5*6)*32
        second=first+12*32
        events=[]
        def hook(c,pc,size,context_data):
            a,b,count,d=[c.reg_read(reg) for reg in regs]
            if pc==0x08005318:
                self.assertEqual((a,b,count,d),(row.ARCHIVE,sp-292,row.graphic_index(graphic),1))
                events.append('decode')
                return
            if pc==row.item.COPY:
                self.assertEqual((a,b,count),(sp-292,second,128))
                c.mem_write(b,bytes(c.mem_read(a,256)))
                events.append('copy')
            elif pc==0x08141868:
                self.assertEqual((b,count),(second if events else first,0x01000060))
                self.assertEqual(c.mem_read(a,4),bytes(4))
                c.mem_write(b,bytes(384))
                events.append('clear')
            else:
                self.assertEqual((a,b,count,d),(context,first,name,4 if mode==0 and flags&16 else 0))
                self.assertEqual(c.mem_read(c.reg_read(UC_ARM_REG_SP),4),struct.pack('<I',1))
                events.append('text')
            c.reg_write(UC_ARM_REG_PC,c.reg_read(UC_ARM_REG_LR))
        for address in (row.item.COPY,0x08141868,row.item.TEXT,0x08005318):
            cpu.hook_add(UC_HOOK_CODE,hook,begin=address,end=address)
        cpu.emu_start(entry|1,returned,count=150000)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),returned)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
        self.assertEqual(cpu.mem_read(first-1,1),b'\x7E')
        self.assertEqual(cpu.mem_read(second+384,1),b'\x7E')
        if mode<=1:
            self.assertEqual(events,['clear','text','clear','decode','copy'])
            self.assertEqual(cpu.mem_read(sp-292,256),cpu.mem_read(second,256))
        else:
            self.assertEqual(events,[])
        if graphic<2 or mode>1:
            self.assertEqual(cpu.mem_read(0x03002BB0,12),struct.pack('<III',17,3,0x02009000))
            self.assertEqual(cpu.mem_read(second,256),bytes([0x6D if mode<=1 else 0x7E])*256)
        else:
            self.assertEqual(cpu.mem_read(0x03002BB0,12),struct.pack('<III',256,0xffffffff,sp-292))
            self.assertNotEqual(cpu.mem_read(second,256),b'\x6D'*256)

    def test_native_menu_setup_and_category_boundaries(self):
        self.execute(0,2,16,caller=True)
        self.execute(1,255,16,caller=True)
        for graphic in (43,44,76,77,78,82,83):
            self.execute(0,graphic,0)

    def test_native_invalid_graphic_observation_and_default(self):
        self.execute(0,0,0)
        self.execute(1,1,16)
        self.execute(2,1,16)


if __name__ == '__main__':
    unittest.main()
