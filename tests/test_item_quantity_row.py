"""Original filtered inventory row, font modes, BIOS operands and authentic callers."""
import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import item_quantity_row as row
import match
import match_evidence as evidence
import menu_icon_row as menu
from test_menu_icon_row import NativeRowFixture, replaced


@unittest.skipUnless(os.environ.get('FFTA_ITEM_QUANTITY_ROW_ROOT'), 'requires original ROM and item row source')
class ItemRowTests(NativeRowFixture, unittest.TestCase):
    fixture = 'FFTA_ITEM_QUANTITY_ROW_ROOT'
    address = row.ADDRESS

    def verify(self, **overrides):
        inputs = dict(raw=self.original, linked_file=self.linked, address=self.address, rom=self.rom,
                      mapping=self.mapping, index=self.index, bindings=self.bindings, objects=self.objects)
        return row.verify_original(**dict(inputs, **overrides))

    def test_bound_objects_receipt_and_mutations(self):
        proof, count = self.verify()
        self.assertEqual(count, 124)
        self.assertEqual(self.body, self.rom[0x5c220:0x5c340])
        self.assertEqual(proof['callers'], list(row.CALLERS))
        self.assertTrue(evidence.report_matches((self.root/'docs/match/0805C220.md').read_text(),
                                                str(self.root), self.address))
        for field in ('font_mode', 'frame', 'callers', 'items', 'environment'):
            altered = copy.deepcopy(proof)
            if field == 'environment':
                altered[field]['producers']['item_quantity_row.py'] = '0'*64
            else:
                altered[field] = None
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'cached'):
                self.verify(manifest=altered)
        image = match.elf_image(self.original)
        text = image['sections'][image['text_index']][4]
        for offset in (0x30, 0x4e, 0x6c, 0x96, 0xd6, 0xf8, 0x10c, 0x118, 0x11c):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(raw=replaced(self.original, text+offset, b'\x02'))
        for addr in (0x0805BF44, 0x0805C178, 0x0805C1F4, 0x080CBDB4, 0x08014944,
                     0x0801479C, 0x08013BCE, 0x08005318, 0x080051C4, 0x08013AA0):
            off = addr-menu.BASE
            with self.subTest(addr=addr), self.assertRaises(ValueError):
                self.verify(rom=replaced(self.rom, off, bytes([self.rom[off]^1])))
        dictionary = struct.unpack_from('>I', self.rom, menu.ARCHIVE-menu.BASE+4)[0]
        with self.assertRaises(ValueError):
            self.verify(rom=replaced(self.rom, menu.ARCHIVE-menu.BASE+dictionary, b'\x01'))
        first_icon = struct.unpack_from('>I', self.rom, menu.ARCHIVE-menu.BASE+8+4*row.FIRST)[0]
        with self.assertRaises(ValueError):
            self.verify(rom=replaced(self.rom, menu.ARCHIVE-menu.BASE+first_icon, b'\xff'))
        for item in (row.FIRST-1, row.LAST+1):
            with self.assertRaises(ValueError):
                row.name_widths(self.rom, item)
        pointer = row.name_widths(self.rom, row.FIRST)[0] - menu.BASE
        with self.assertRaisesRegex(ValueError, 'control'):
            self.verify(rom=replaced(self.rom, pointer, b'\x43'))
        with self.assertRaisesRegex(ValueError, 'name index'):
            self.verify(rom=replaced(self.rom, row.ITEM_TABLE-menu.BASE+32*row.FIRST,b'\xff\xff'))

    def test_every_font_mode_on_original_width_code(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_SP, UC_ARM_REG_R0, UC_ARM_REG_PC
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for address, size in ((menu.BASE, len(self.rom)), (0x02000000, 0x40000), (0x03000000, 0x8000)):
            cpu.mem_map(address, size)
        cpu.mem_write(menu.BASE, self.rom)
        sp, ret = 0x03007b00, 0x02002000
        reads = set()
        def ram_read(cpu, kind, address, size, value, opaque):
            if address < sp-256 or address >= sp:
                reads.add((address,size))
        cpu.hook_add(UC_HOOK_MEM_READ, ram_read, begin=0x02000000, end=0x03007fff)
        for item in range(row.FIRST, row.LAST+1):
            pointer, narrow, fixed = row.name_widths(self.rom, item)
            for mode in range(256):
                cpu.mem_write(row.MODE, bytes([mode]))
                cpu.reg_write(UC_ARM_REG_SP, sp)
                cpu.reg_write(UC_ARM_REG_R0, pointer)
                cpu.reg_write(UC_ARM_REG_LR, ret|1)
                cpu.emu_start(0x080161bd, ret, count=5000)
                self.assertEqual((cpu.reg_read(UC_ARM_REG_PC),cpu.reg_read(UC_ARM_REG_SP),cpu.reg_read(UC_ARM_REG_R0)),
                                 (ret,sp,fixed if mode else narrow))
        self.assertEqual(reads, {(row.MODE,1)})

    def run_item(self, body, item, mode=0, caller=None, row_arg=1, style_arg=0xc0ffee03):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_SP, UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_R0,
            UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6,
            UC_ARM_REG_R7, UC_ARM_REG_R8, UC_ARM_REG_R9, UC_ARM_REG_R10)
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for addr, size in ((menu.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),(0x06000000,0x18000)):
            cpu.mem_map(addr,size)
        cpu.mem_write(menu.BASE,self.rom)
        cpu.mem_write(self.address,body)
        sp, tiles, state, tilemap = 0x03007b00, 0x06001000, 0x02010000, 0x02020000
        run, icon, quantity = state+0xd20, sp-172+4, 0x2a
        def put(a, value): cpu.mem_write(a,struct.pack('<I',value))
        def word(a): return struct.unpack('<I',cpu.mem_read(a,4))[0]
        put(0x0200f428,state)
        put(menu.GRAPHICS+16,tiles)
        put(run+12,tilemap)
        cpu.mem_write(run+0x15,b'\x10\x03')
        cpu.mem_write(run+0x18,struct.pack('<HHH',14,2,7))
        cpu.mem_write(state+0x2ca4+4,struct.pack('<HBB',item,quantity,0))
        cpu.mem_write(tiles,bytes([0xa5])*0x8000)
        cpu.mem_write(row.MODE,bytes([mode]))
        cpu.reg_write(UC_ARM_REG_SP,sp)
        regs = (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3)
        saved = (UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,UC_ARM_REG_R8,UC_ARM_REG_R9,UC_ARM_REG_R10)
        for i, reg in enumerate(saved): cpu.reg_write(reg,0x123400+i)
        if caller is None:
            start, ret = self.address, 0x02002000
            put(sp,style_arg)
            for reg, value in zip(regs, (run,item,quantity,row_arg)): cpu.reg_write(reg,value)
        elif caller == row.CALLERS[0]:
            start, ret = 0x0805bf20, caller+4
            row_arg, style_arg = 2, 0
            cpu.reg_write(UC_ARM_REG_R5,1)
            cpu.reg_write(UC_ARM_REG_R7,run)
            cpu.reg_write(UC_ARM_REG_R3,row_arg)
        else:
            start, ret = (0x0805c160 if caller==row.CALLERS[1] else 0x0805c1dc), caller+4
            row_arg, style_arg = (0 if caller==row.CALLERS[1] else 3), 0
            cpu.reg_write(UC_ARM_REG_R7,0x0200f428)
            cpu.reg_write(UC_ARM_REG_R4,0xd20)
            cpu.reg_write(UC_ARM_REG_R5,0)
            cpu.reg_write(UC_ARM_REG_R6,1)
        cpu.reg_write(UC_ARM_REG_LR,ret|1)
        selected = max(0,min(13,2+((row_arg & 255)^128)-128))
        dest = tiles+(7+32*(selected % 4))*32
        name,narrow,fixed = row.name_widths(self.rom,item)
        width = fixed if mode else narrow
        words = (((12-width)*2)&65535)*8
        clear = dest+(2+width)*64
        writes, calls, services, incoming = [], [], [], {}
        def code(uc,a,size,opaque):
            values = [uc.reg_read(reg) for reg in regs]
            if a==self.address:
                self.assertEqual(values,[run,item,quantity,row_arg]); self.assertEqual(word(sp),style_arg)
                incoming.update({reg:uc.reg_read(reg) for reg in saved})
            elif a==menu.DECODE:
                self.assertEqual(values[:2],[icon,item]); calls.append(a)
            elif a==0x08015110:
                self.assertEqual(values,[state+0x1184,dest+128,name,style_arg&255]); self.assertEqual(word(uc.reg_read(UC_ARM_REG_SP)),1)
                calls.append(a); uc.reg_write(UC_ARM_REG_PC,uc.reg_read(UC_ARM_REG_LR))
            elif a==0x0802979C:
                self.assertEqual(values,[state+0x1184,dest+14*64,quantity,2]); self.assertEqual(word(uc.reg_read(UC_ARM_REG_SP)),style_arg&255)
                calls.append(a); uc.reg_write(UC_ARM_REG_PC,uc.reg_read(UC_ARM_REG_LR))
            elif a==0x0805C340:
                tag = self.rom[0x3c7fe4+2*(item+2)] >> 4
                self.assertEqual(values,[run,row_arg&255,selected,tag+13]); calls.append(a)
        def write(uc,kind,a,size,value,opaque):
            pc = uc.reg_read(UC_ARM_REG_PC)
            if 0x080051c4<=pc<0x080053d4 and sp-172<=a<sp:
                self.assertTrue(icon <= a < icon+128 and size==1)
                writes.append(a)
        def bios(uc,number,opaque):
            command = uc.mem_read(uc.reg_read(UC_ARM_REG_PC)-2,1)[0]
            src,dst,control = [uc.reg_read(reg) for reg in regs[:3]]
            services.append(command)
            if command==11:
                self.assertEqual((src,dst,control),(icon,dest,64))
                uc.mem_write(dst,bytes(uc.mem_read(src,128)))
            else:
                self.assertEqual((command, word(src), dst, control),(12,0,clear,0x01000000|words))
                if width>=12:
                    uc.emu_stop()
                else:
                    uc.mem_write(dst,bytes(4*words))
        cpu.hook_add(UC_HOOK_CODE,code)
        cpu.hook_add(UC_HOOK_MEM_WRITE,write)
        cpu.hook_add(UC_HOOK_INTR,bios)
        cpu.emu_start(start|1,ret,count=50000)
        self.assertEqual(services,[11,12])
        self.assertEqual(writes,[icon]+list(range(icon,icon+128)))
        self.assertEqual((word(0x03002bb8),word(0x03002bb0)),(icon,128))
        self.assertEqual(bytes(cpu.mem_read(dest,128)),menu._decode_icon(self.rom,item))
        if width<12:
            self.assertEqual((cpu.reg_read(UC_ARM_REG_PC),cpu.reg_read(UC_ARM_REG_SP)),(ret,sp))
            self.assertEqual(incoming,{reg:cpu.reg_read(reg) for reg in saved})
            self.assertEqual(calls,[menu.DECODE,0x08015110,0x0802979C,0x0805C340])
            self.assertEqual(bytes(cpu.mem_read(clear,4*words)),bytes(4*words))
            self.assertEqual(cpu.mem_read(clear-1,1),b'\xa5')
            self.assertEqual(cpu.mem_read(dest+14*64,1),b'\xa5')
        else:
            self.assertEqual(calls,[menu.DECODE,0x08015110])
            self.assertEqual(cpu.mem_read(clear,1),b'\xa5')

    def test_native_rows_and_all_three_real_call_sites(self):
        for body in (self.body,self.rom[0x5c220:0x5c340]):
            for item in range(row.FIRST,row.LAST+1):
                for mode in (0,255):
                    with self.subTest(item=item,mode=mode): self.run_item(body,item,mode)
            for site in row.CALLERS:
                self.run_item(body,367,caller=site)
            self.run_item(body,365,row_arg=0x8bad00ff)
