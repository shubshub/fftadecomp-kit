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


class NativeRowFixture:
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ[cls.fixture]).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = owner.index_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        args = SimpleNamespace(cpp=match.DEFAULT_CPP, cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS,
            assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(cls.root))
        with runner.workspace() as workspace:
            raw, _, image = match.compile_object(runner,workspace,args,cls.root,cls.address,f'src/{cls.address:08X}.c')
            cls.original = raw
            cls.body, cls.bindings = owner.object_bytes(runner,workspace,args,image,cls.address,cls.rom,
                cls.mapping,cls.objects,selector=runtime.SELECTOR,index=cls.index)
            cls.linked = runner.read_binary(workspace+'/f.elf')

    def verify(self, **changed):
        inputs = dict(raw=self.original, linked_file=self.linked, address=self.address, rom=self.rom,
            mapping=self.mapping, index=self.index, bindings=self.bindings, objects=self.objects)
        return menu.verify_original(**dict(inputs, **changed))

    def run_row(self, body, entry, row, position, width, style, *, stale=False, capture_control=False, count=0, height=0, caller=False):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_R0,
            UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_R4, UC_ARM_REG_R5, UC_ARM_REG_R6,
            UC_ARM_REG_R7, UC_ARM_REG_R8, UC_ARM_REG_R9)
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for start,size in ((menu.BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),(0x06000000,0x18000)):
            cpu.mem_map(start,size)
        cpu.mem_write(menu.BASE,self.rom)
        cpu.mem_write(self.address,body)
        clamped = self.address == menu.CLAMPED
        getter = 0x08017b68 if clamped else 0x080543cc
        modulus = 0x08142950 if clamped else menu.SCALAR
        run, ctx, tiles, sp, returned = 0x02001000,0x02003000,0x06001000,0x03007b00,0x08053500
        cpu.mem_write(run+0x15,bytes([width]))
        cpu.mem_write(run+0x16,bytes([height]))
        cpu.mem_write(run+0x18,struct.pack('<HH',count,position))
        tile = 16
        cpu.mem_write(run+0x1c,struct.pack('<H',tile))
        cpu.mem_write(menu.GRAPHICS+16,struct.pack('<I',tiles))
        cpu.mem_write(tiles,bytes([0x91])*0x10000)
        cpu.mem_write(sp,struct.pack('<I',0xdeadbeef if caller else style))
        cpu.reg_write(UC_ARM_REG_SP,sp)
        if caller:
            self.assertTrue(clamped and row == 0 and style == 5)
            returned = 0x080539f4
        cpu.reg_write(UC_ARM_REG_LR,returned|1)
        third, fourth = (row, entry) if clamped else (entry, row)
        for reg,value in ((UC_ARM_REG_R0,run),(UC_ARM_REG_R1,ctx),(UC_ARM_REG_R2,third),(UC_ARM_REG_R3,fourth)):
            cpu.reg_write(reg,0xdeadbeef if caller else value)
        saved = {reg:0x110000+i for i,reg in enumerate((UC_ARM_REG_R4,UC_ARM_REG_R5,UC_ARM_REG_R6,UC_ARM_REG_R7,UC_ARM_REG_R8))}
        if caller:
            saved.update({UC_ARM_REG_R4:run, UC_ARM_REG_R5:ctx, UC_ARM_REG_R6:run-0x2c, UC_ARM_REG_R9:entry})
        for reg,value in saved.items():
            cpu.reg_write(reg,value)
        if caller:
            cpu.reg_write(UC_ARM_REG_R4,0xdeadbeef)
        icon = sp-152
        graphic = 394 if entry>85 else 393
        if clamped:
            signed_row = ((row & 255) ^ 128) - 128
            candidate = (((signed_row + position) & 65535) ^ 32768) - 32768
            last = ((count ^ 32768) - 32768) - 1
            numerator = 0 if candidate < 0 else min(candidate, last) & 65535
            divisor = height + 1
        else:
            numerator, divisor = (row + position) & 255, 5
        offset = ((numerator % divisor) * width * 2) & 65535
        destination = tiles + (tile + offset) * 32
        # All normal witnesses have a representable destination.
        fill_words = (((width-2)*2)&65535)*8
        observed, services, writes, renderer = [],[],[],[]
        def word(a):
            return struct.unpack('<I',cpu.mem_read(a,4))[0]
        def hook_code(uc,a,size,opaque):
            if a in (menu.DECODE,0x08005318,0x080051c4,getter,modulus,0x08013a88,0x08141868,0x0814186c):
                observed.append(a)
            if a == self.address and caller:
                incoming = [uc.reg_read(reg) for reg in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3)]
                self.assertEqual(incoming,[run,ctx,0,entry])
                self.assertEqual(word(uc.reg_read(UC_ARM_REG_SP)),5)
            if a == modulus:
                self.assertEqual((uc.reg_read(UC_ARM_REG_R0),uc.reg_read(UC_ARM_REG_R1)), (numerator,divisor))
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
                if capture_control:
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
        cpu.emu_start((0x080539e0 if caller else self.address)|1,returned,count=50000)
        self.assertEqual([a for a,_,_ in writes],[icon]+list(range(icon,icon+128)))
        self.assertTrue(all(size==1 for _,size,_ in writes))
        self.assertEqual((word(0x03002bb8),word(0x03002bb0)),(icon,128))
        if capture_control:
            self.assertEqual(services[0][3],0x01000000|fill_words)
            self.assertEqual(len(services),1)
            return
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC),returned)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
        self.assertEqual({reg:cpu.reg_read(reg) for reg in saved},saved)
        self.assertEqual(observed,[menu.DECODE,0x08005318,0x080051c4,getter,modulus,
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


@unittest.skipUnless(os.environ.get('FFTA_MENU_ICON_ROOT'), 'requires the original USA ROM and indexed source')
class MenuIconTests(NativeRowFixture, unittest.TestCase):
    fixture = 'FFTA_MENU_ICON_ROOT'
    address = menu.OWNER

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

    def test_original_cpu_and_compiled_body(self):
        for body in (self.rom[0x53e4c:0x53f08],self.body):
            for entry,row,position,width,style in ((0,0,0,8,0),(85,1,3,8,1),(86,3,254,6,5),
                                                    (170,255,254,3,1),(313,2,2,3,0)):
                self.run_row(body,entry,row,position,width,style,stale=entry==86)
            for width in (0,1,2):
                # Observe the descriptor; these counts do not justify a normal clear.
                self.run_row(body,1,0,0,width,1,capture_control=True)



@unittest.skipUnless(os.environ.get('FFTA_CLAMPED_MENU_ICON_ROOT'), 'requires the original clamped menu row fixture')
class ClampedMenuIconTests(NativeRowFixture, unittest.TestCase):
    fixture = 'FFTA_CLAMPED_MENU_ICON_ROOT'
    address = menu.CLAMPED

    def test_native_clamp_and_indexed_call(self):
        for body in (self.rom[0x54314:0x543cc],self.body):
            # Real menu caller at 080539E0 sets up the fifth word and all four registers.
            self.run_row(body,86,0,3,4,5,height=2,count=5,caller=True)
            for row,position,count,height in ((0x1ff,1,3,2), (127,0,6,2), (0x180,20,200,4),
                                              (0,0,0,4), (0,0,0x8001,255), (1,0x7fff,4,255)):
                self.run_row(body,85,row,position,4,1,height=height,count=count)
            # A wrapped offset and an external destination beyond VRAM: observe only the descriptor.
            self.run_row(body,170,0,240,200,5,height=255,count=400,capture_control=True)
            for width in (0,1,2):
                self.run_row(body,0,1,0,width,1,height=1,count=4,capture_control=True)

    def test_clamp_and_caller_mutations(self):
        for a in (0x08054322,0x08054346,0x0805434c,0x08054354,0x08054356,0x08054358,
                  0x08054360,0x08054364,0x08054380,0x08017b6e,0x08017b74,0x08017b82,
                  0x08017b84,0x08017b88,0x08017b90,0x080539e2,0x080539e6,0x080539ec,0x080539ee):
            pos = a-menu.BASE
            with self.subTest(a=hex(a)), self.assertRaises(ValueError):
                self.verify(rom=replaced(self.rom,pos,bytes([self.rom[pos]^1])))

    def test_clamped_replay_and_original_relocations(self):
        proof,count = self.verify()
        self.assertEqual(count,77)
        self.assertEqual(self.body,self.rom[0x54314:0x543cc])
        report = (self.root/'docs/match/08054314.md').read_text()
        self.assertTrue(evidence.report_matches(report,str(self.root),self.address))
        self.assertFalse(evidence.report_matches(report.replace('184/184','182/182',1),str(self.root),self.address))
        altered = copy.deepcopy(proof)
        altered['clamped_row']['divisor_max'] = 255
        with self.assertRaisesRegex(ValueError,'cached evidence'):
            self.verify(manifest=altered)
        image = match.elf_image(self.original)
        offset = image['sections'][image['text_index']][4]
        for pos in (0x38,0x44,0xac,0xb0):
            with self.subTest(pos=pos), self.assertRaises(ValueError):
                self.verify(raw=replaced(self.original,offset+pos,b'\x01'))


if __name__ == '__main__':
    unittest.main()
