"""Native item row, all archive streams, actual menu callers and fail-closed replay."""
from copy import deepcopy
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match_evidence
import menu_item_tile_row as row
import owner_admission_profile as owner

def changed(data, offset, value):
    return data[:offset] + value + data[offset+len(value):]


@unittest.skipUnless(os.getenv('FFTA_ITEM_TILE_ROW_ROOT'), 'requires the USA ROM, genuine row and agbcc')
class ItemTileRowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ITEM_TILE_ROW_ROOT'])
        cls.result = owner.build(cls.root, row.OWNER, selector=row.named.SELECTOR)
        cls.body, cls.manifest, _, cls.mapping, cls.index, cls.objects, cls.rom, _, _ = cls.result

    def bind(self, *, rom=None, bindings=None, address=row.OWNER):
        proof = row.ItemTileRowProof(self.rom if rom is None else rom,
                                     self.mapping, self.index, self.objects)
        proof.bind_row(self.body, address, {row.OWNER+s:t for s,t in row.CALLS.items()},
                       self.manifest['bindings'] if bindings is None else bindings)
        return proof

    def test_original_and_saved_report(self):
        self.assertEqual(self.body, self.rom[0x702e8:0x70414])
        self.assertEqual(self.result[7], 131)
        saved = (self.root / 'docs/match/080702E8.md').read_text()
        self.assertTrue(match_evidence.report_matches(saved, self.root, row.OWNER))
        self.assertFalse(match_evidence.report_matches(saved.replace('"entries":522', '"entries":521'),
                                                      self.root, row.OWNER))

    def test_original_roles_and_runtime_sites(self):
        with self.assertRaises(ValueError):
            self.bind(address=row.OWNER+2)
        for role, index, value in [('calls', 1, [0x34,'func_08005318']),
                                   ('data', 2, [0x120,'g_table_08526680',0])]:
            bindings = deepcopy(self.manifest['bindings'])
            bindings[role][index] = value
            with self.subTest(role=role), self.assertRaises(ValueError):
                self.bind(bindings=bindings)
        for at in (0x702FA,0x70318,0x70324,0x7034A,0x703B4,0x703E6,0xCB998,0x531E,
                   0x526C,0x52DA,0x13AA0,0x14186C,0x6AF44,0x6AF78,0x6D030,0x5412):
            with self.subTest(at=hex(at)), self.assertRaises(ValueError):
                self.bind(rom=changed(self.rom, at, bytes([self.rom[at]^1])))
        with self.assertRaisesRegex(ValueError, 'incomplete live'):
            self.bind().row_manifest()

    def test_all_streams_and_final_stream_boundary(self):
        archive = self.rom[row.menu.ARCHIVE-row.menu.BASE:row.ARCHIVE_END-row.menu.BASE]
        self.assertEqual(row.check_archive(archive)['entries'],522)
        first, = struct.unpack_from('>I', archive, 8)
        dictionary, = struct.unpack_from('>I', archive, 4)
        last, = struct.unpack_from('>I', archive, 8+4*521)
        for offset, data in ((2,b'\x00\x02'), (dictionary+2,b'\x00\x81'),
                            (first,b'\xff'), (last,b'\xff'),
                            (8+4*521,struct.pack('>I',dictionary-1))):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                row.check_archive(changed(archive, offset, data))

    def test_environment_drift(self):
        saved = self.manifest['proof']['buffers']['item_tile_row']['environment']
        drift = dict(saved, toolchain=[])
        for values in ((saved, drift, saved), (saved, saved, drift)):
            with patch.object(row, 'environment_fingerprint', side_effect=values):
                with self.assertRaisesRegex(ValueError, 'changed during compilation'):
                    owner.build(self.root,row.OWNER,selector=row.named.SELECTOR)

    def test_two_original_menu_callers_and_native_decoder(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR,
            UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R7)
        registers = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        renderer, menu_state, tiles, tilemap, cells, sp = 0x080161BC,0x02008000,0x0600AC00,0x030008B0,0x02016000,0x03007B00
        for (_, _, block, _), item in zip(row.CALLERS, (0,375)):
            cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
            for base,size in ((row.menu.BASE,len(self.rom)),(0x02000000,0x40000),
                              (0x03000000,0x8000),(0x06000000,0x18000)):
                cpu.mem_map(base, size)
            cpu.mem_write(row.menu.BASE, self.rom)
            cpu.mem_write(row.OWNER, self.body)
            cpu.mem_write(0x0200F428, struct.pack('<I',menu_state))
            cpu.mem_write(menu_state+0x44EC,struct.pack('<H',item))
            cpu.mem_write(tilemap+12,bytes([32]))
            cpu.mem_write(tilemap+20,struct.pack('<I',cells))
            cpu.mem_write(cells,b'\xA5'*256)
            cpu.mem_write(tiles-4,b'\x5A'*(832+8))
            cpu.mem_write(sp-192,b'\x67'*220)
            cpu.reg_write(UC_ARM_REG_SP,sp)
            cpu.reg_write(UC_ARM_REG_R7,0x0200F428)
            seen = []
            def hook(c, pc, size, context):
                first,second,third,fourth = [c.reg_read(reg) for reg in registers]
                if pc == renderer:
                    c.reg_write(UC_ARM_REG_R0,6)
                elif pc == 0x08141868:
                    self.assertEqual((second,third),(tiles,0x010000D0))
                    self.assertEqual(c.mem_read(first,4),bytes(4))
                    c.mem_write(second,bytes(832))
                elif pc == row.COPY:
                    self.assertEqual((first,second,third),(sp-160,tiles,64))
                    c.mem_write(second,bytes(c.mem_read(first,128)))
                else:
                    name, = struct.unpack_from('<H',self.rom,row.ITEMS-row.menu.BASE+item*32)
                    string, = struct.unpack_from('<I',self.rom,row.menu.NAMES-row.menu.BASE+4*name)
                    self.assertEqual((first,second,third,fourth),(menu_state+0x39F4,tiles+128,string,0))
                    self.assertEqual(c.mem_read(c.reg_read(UC_ARM_REG_SP),4),b'\x01\x00\x00\x00')
                seen.append(pc)
                c.reg_write(UC_ARM_REG_PC,c.reg_read(UC_ARM_REG_LR))
            for target in (renderer,0x08141868,row.COPY,row.TEXT):
                cpu.hook_add(UC_HOOK_CODE,hook,begin=target,end=target)
            cpu.emu_start(block|1,block+0x42,count=100000)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),block+0x42)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
            self.assertEqual(seen,[renderer,0x08141868,row.COPY,row.TEXT])
            self.assertEqual(cpu.mem_read(tiles-4,4),b'\x5A'*4)
            self.assertEqual(cpu.mem_read(tiles+832,4),b'\x5A'*4)
            self.assertEqual(cpu.mem_read(0x03002BB0,12),struct.pack('<III',128,0xFFFFFFFF,sp-160))
            self.assertEqual(cpu.mem_read(tiles,128),cpu.mem_read(sp-160,128))
            expected=bytearray(b'\xA5'*256)
            first=(tiles-0x06008000)//32
            palette=(13+(self.rom[0x3c7fe4+4+2*item]>>4))<<12
            for i in range(13):
                top=(first+i)|palette if i<2 else (first+2*i)|0xC000
                bottom=(first+i+2)|palette if i<2 else (first+2*i+1)|0xC000
                struct.pack_into('<H',expected,2*(11+i),top&0xffff)
                struct.pack_into('<H',expected,2*(43+i),bottom&0xffff)
            self.assertEqual(cpu.mem_read(cells,256),expected)


if __name__ == '__main__':
    unittest.main()
