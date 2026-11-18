"""Fixed original decoder inputs, real ARMv4T calls and BIOS service contracts."""
import copy
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

TOOLS = Path(__file__).resolve().parents[1] / 'tools'
sys.path.insert(0, str(TOOLS))
import match
import match_evidence as evidence
import menu_icon_row as menu
import owner_admission_profile as owner
import runtime_summary_profile as runtime


def replaced(raw, at, value):
    return raw[:at] + value + raw[at+len(value):]


@unittest.skipUnless(os.environ.get('FFTA_MENU_ICON_ROOT'), 'requires the original USA ROM and indexed source')
class MenuIconTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_MENU_ICON_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        args = SimpleNamespace(cpp=match.DEFAULT_CPP, cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS,
            assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(cls.root))
        with runner.workspace() as workspace:
            raw, _, image = match.compile_object(runner,workspace,args,cls.root,menu.OWNER,'src/08053E4C.c')
            cls.original = raw
            cls.body, cls.bindings = owner.object_bytes(runner,workspace,args,image,menu.OWNER,cls.rom,
                cls.mapping,cls.objects,selector=runtime.SELECTOR,index=cls.index)
            cls.linked = runner.read_binary(workspace+'/f.elf')

    def verify(self, **changed):
        inputs = dict(raw=self.original, linked_file=self.linked, address=menu.OWNER, rom=self.rom,
            mapping=self.mapping, index=self.index, bindings=self.bindings, objects=self.objects)
        return menu.verify_original(**dict(inputs, **changed))

    def test_canonical_replay_and_bound_original(self):
        proof, count = self.verify()
        self.assertEqual(count,78)
        report = (self.root/'docs/match/08053E4C.md').read_text()
        self.assertTrue(evidence.report_matches(report,str(self.root),menu.OWNER))
        self.assertEqual(self.body,self.rom[0x53e4c:0x53f08])
        for token in ('188/188','retained_output_word','outgoing_word','128 in 03002BB0'):
            self.assertIn(token,report)
            self.assertFalse(evidence.report_matches(report.replace(token,'altered',1),str(self.root),menu.OWNER))
        altered = copy.deepcopy(proof)
        altered['frame']['icon_offset'] = 0
        with self.assertRaisesRegex(ValueError,'cached evidence'):
            self.verify(manifest=altered)
        image = match.elf_image(self.original)
        text_offset = image['sections'][image['text_index']][4]
        for offset in (0x24, 0x40, 0x74, 0xb0, 0xb4):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.verify(raw=replaced(self.original,text_offset+offset,b'\x01'))
        for blob, role in ((self.original, 'raw'), (self.linked, 'linked_file')):
            image = match.elf_image(blob)
            for table, rows in image['symbol_tables'].items():
                for i, row in enumerate(rows):
                    if row['name'] in ('__umodsi3','data_030008B0','func_080CB980'):
                        pos = image['sections'][table][4] + 16*i + 8
                        with self.subTest(role=role,name=row['name']), self.assertRaises(ValueError):
                            self.verify(**{role:replaced(blob,pos,b'\x04')})

    def test_native_mutations_and_stream_bounds(self):
        for a in (0x08053e52,0x08053e58,0x08053e6e,0x08053e8c,0x08053eb6,0x08053ebe,0x08053ede,
                  0x08053efc,0x08053f00,0x080cb998,0x080051e6,0x080053c8,0x08013a94,0x08141868,0x0814186c,
                  0x0805341e,0x08015120,0x08005412):
            at = a-menu.BASE
            with self.subTest(a=hex(a)), self.assertRaises(ValueError):
                self.verify(rom=replaced(self.rom,at,bytes([self.rom[at]^1])))
        head = menu.ARCHIVE-menu.BASE
        offset, = struct.unpack_from('>I',self.rom,head+4)
        start, end = struct.unpack_from('>II',self.rom,head+8+393*4)
        for at,value in ((head+offset, b'\x03'), (head+offset+2, b'\x01'),
                         (head+start,b'\xff'), (head+end-1,b'\xff'),
                         (head+8+394*4,struct.pack('>I',end-1))):
            changed = replaced(self.rom,at,value)
            if at == head+end-1:
                # A changed literal can still be a valid bounded stream.
                self.assertNotEqual(menu.decode_icon(changed,393),menu.decode_icon(self.rom,393))
            else:
                with self.subTest(at=at), self.assertRaises(ValueError):
                    menu.decode_icon(changed,393)

    def run_row(self, body, entry, row, position, width, style, *, stale=False, capture_zero=False):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_R0,
            UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6,
            UC_ARM_REG_R7, UC_ARM_REG_R8)
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for start,size in ((menu.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),(0x06000000,0x18000)):
            cpu.mem_map(start,size)
        cpu.mem_write(menu.BASE,self.rom)
        cpu.mem_write(menu.OWNER,body)
        run, ctx, tiles, sp, returned = 0x02001000,0x02003000,0x06001000,0x03007b00,0x08053500
        cpu.mem_write(run+0x15,bytes([width]))
        cpu.mem_write(run+0x1a,bytes([position]))
        tile = 16
        cpu.mem_write(run+0x1c,struct.pack('<H',tile))
        cpu.mem_write(menu.GRAPHICS+16,struct.pack('<I',tiles))
        cpu.mem_write(tiles,bytes([0x91])*0x10000)
        cpu.mem_write(sp,struct.pack('<I',style))
        cpu.reg_write(UC_ARM_REG_SP,sp)
        cpu.reg_write(UC_ARM_REG_LR,returned|1)
        for reg,value in ((UC_ARM_REG_R0,run),(UC_ARM_REG_R1,ctx),(UC_ARM_REG_R2,entry),(UC_ARM_REG_R3,row)):
            cpu.reg_write(reg,value)
        saved = {reg:0x110000+i for i,reg in enumerate((UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,UC_ARM_REG_R8))}
        for reg,value in saved.items():cpu.reg_write(reg,value)
        icon = sp-152
        graphic = 394 if entry>85 else 393
        destination = tiles+(tile+((row+position)&255)%5*(width*2))*32
        # All normal witnesses have a representable destination.
        fill_words = (((width-2)*2)&65535)*8
        observed, services, writes, renderer = [],[],[],[]
        def word(a):
            return struct.unpack('<I',cpu.mem_read(a,4))[0]
        def hook_code(uc,a,size,opaque):
            if a in (menu.DECODE,0x08005318,0x080051c4,0x080543cc,menu.SCALAR,0x08013a88,0x08141868,0x0814186c):
                observed.append(a)
            if a == menu.DECODE:
                self.assertEqual((uc.reg_read(UC_ARM_REG_R0),uc.reg_read(UC_ARM_REG_R1)),(icon,graphic))
            if a == 0x08015110:
                name = menu.NAMES+4*(625+entry-(85 if entry>85 else 0))
                renderer.append([uc.reg_read(reg) for reg in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3)])
                self.assertEqual(renderer[-1],[ctx,destination+128,word(name),style])
                if entry == 313:
                    self.assertEqual(word(name),0x2800c000)
                self.assertEqual(word(uc.reg_read(UC_ARM_REG_SP)),1)
                # This proof stops at the text ABI. Assume only an ordinary
                # returning call for the separate exit/frame witness.
                uc.reg_write(UC_ARM_REG_PC,uc.reg_read(UC_ARM_REG_LR))
        def on_write(uc,kind,a,size,value,opaque):
            if icon <= a < icon+128:
                writes.append((a,size,value))
            if a in range(icon+128,sp) and uc.reg_read(UC_ARM_REG_PC) in range(0x080051c4,0x080053d4):
                self.fail('decoder wrote into owner saved registers')
        def bios(uc,num,opaque):
            pc = uc.reg_read(UC_ARM_REG_PC)
            command = uc.mem_read(pc-2,1)[0]
            src,dst,control = [uc.reg_read(reg) for reg in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2)]
            services.append((command,src,dst,control))
            if command==12:
                self.assertEqual((word(src),dst,control),(0,destination+128,0x01000000|fill_words))
                if capture_zero:
                    uc.emu_stop()
                    return
                self.assertGreater(fill_words,0)
                uc.mem_write(dst,bytes(4*fill_words))
            else:
                self.assertEqual((command,src,dst,control),(11,icon,destination,64))
                uc.mem_write(dst,bytes(uc.mem_read(src,128)))
        cpu.hook_add(UC_HOOK_INTR,bios)
        cpu.hook_add(UC_HOOK_CODE,hook_code)
        cpu.hook_add(UC_HOOK_MEM_WRITE,on_write)
        cpu.emu_start(menu.OWNER|1,returned,count=50000)
        self.assertEqual([a for a,_,_ in writes],[icon]+list(range(icon,icon+128)))
        self.assertTrue(all(size==1 for _,size,_ in writes))
        self.assertEqual((word(0x03002bb8),word(0x03002bb0)),(icon,128))
        if capture_zero:
            self.assertEqual(services[0][3],0x01000000|fill_words)
            self.assertEqual(len(services),1)
            return
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),returned)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
        self.assertEqual({reg:cpu.reg_read(reg) for reg in saved},saved)
        self.assertEqual(observed,[menu.DECODE,0x08005318,0x080051c4,0x080543cc,menu.SCALAR,
                                  0x08013a88,0x08141868,0x0814186c])
        self.assertEqual(len(renderer),1)
        self.assertEqual(bytes(cpu.mem_read(destination,128)),menu.decode_icon(self.rom,graphic))
        self.assertEqual(bytes(cpu.mem_read(destination+128,4*fill_words)),bytes(4*fill_words))
        self.assertEqual(cpu.mem_read(destination-1,1),b'\x91')
        self.assertEqual(cpu.mem_read(destination+128+4*fill_words,1),b'\x91')
        if stale:
            cpu.reg_write(UC_ARM_REG_R0,0x7c)
            cpu.reg_write(UC_ARM_REG_LR,returned|1)
            old = word(icon+128)
            cpu.emu_start(0x08005409,returned,count=16)
            self.assertEqual(word(0x03002bb0),129)
            self.assertEqual(word(icon+128), (old & ~255)|0x7c)

    def test_original_cpu_and_compiled_body(self):
        for body in (self.rom[0x53e4c:0x53f08],self.body):
            for entry,row,position,width,style in ((0,0,0,8,0),(85,1,3,8,1),(86,3,254,6,5),
                                                    (170,255,254,3,1),(313,2,2,3,0)):
                self.run_row(body,entry,row,position,width,style,stale=entry==86)
            for width in (0,1,2):
                # Observe the descriptor; these counts do not justify a normal clear.
                self.run_row(body,1,0,0,width,1,capture_zero=True)


if __name__ == '__main__':
    unittest.main()
