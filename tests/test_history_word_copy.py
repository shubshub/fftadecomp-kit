"""Original USA callers, installed image, native qualifiers and the unchecked forwarding edge."""
import argparse
import copy
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import history_word_copy as history


class Bounds(unittest.TestCase):
    def test_stack_input_and_forwarded_field_bounds(self):
        state,sp = 0x020159E4,0x03007D00
        for count in range(13):
            history.placement(state,sp,count,sp,from_builder=True)
        for count in range(25):
            history.placement(state,0x02015000,count,sp,from_builder=False)
        history.placement(state,None,-0x80000000,sp,from_builder=False)
        for source,count,filtering in ((sp,13,True),(sp+4,12,True),(state-4,2,False),
                (0x02015000,25,False),(sp-4,1,False),(sp,1,False),(history.SHADOW+72,1,False),
                (history.PALETTE-4,2,False),(history.ANIMATION+140,1,False),(0x03005EE8,1,False),
                (0x0203FFFC,2,False),(0x02015002,1,False)):
            with self.subTest(source=source,count=count),self.assertRaises(ValueError):
                history.placement(state,source,count,sp,from_builder=filtering)


class NativeHistory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import match
        import volatile_semantics as vs
        import function_thunk_profile as thunk
        from rompath import rom_path
        from inert_spin_profile import index_snapshot
        root = os.environ.get('FFTA_HISTORY_FIXTURE')
        if not root:
            raise unittest.SkipTest('FFTA_HISTORY_FIXTURE must name the reviewed checkout with ROM')
        cls.root = Path(root)
        cls.rom = Path(rom_path(root)).read_bytes()
        cls.mapping = match.mapping_snapshot(cls.root)
        cls.index = index_snapshot(cls.root)
        cls.objects = match.parse_data_symbols(match.data_snapshot(cls.root))
        entry = json.loads((Path(match.__file__).parent/'volatile_allow.json').read_text())['entries'][0]
        args = argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                                  flags=match.DEFAULT_FLAGS,objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD)
        runner = match.Runner(args.cc,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        cls.images, cls.assemblies = [], []
        with runner.workspace() as ws:
            for method in (None,vs.strip_pinned_volatile,vs.perturb_pinned):
                rewrite = None if method is None else lambda text: method(text,entry['declaration'])
                _,_,image = match.compile_object(runner,ws,args,root,history.OWNER,'src/080C62CC.c',rewrite=rewrite)
                cls.images.append(image)
                cls.assemblies.append(runner.read_binary(f'{ws}/f.s').decode())
                bindings = {name:thunk.ALIASES[name] if name.startswith('_call') else int(name[5:],16)
                            for site,name in history.CALLS}
                bindings.update({name:address for site,name,address in history.DATA})
                linked = match.link_typed_targets(runner,ws,args,'func_080C62CC',history.OWNER,bindings,set(cls.objects))
                digest = history.sha256(linked['text']).hexdigest()
                expected = (history.BODY,'0d00d2ec2599a34035bf3c30a6a03ee0a709ca7fe662109b006442aa9ca77e7a',
                            '685c3b2902fe4db555526fed0ab7b68d1ec8a3dbf0fc4675420e81e2e481d8c7')
                if digest != expected[len(cls.images)-1]:
                    raise ValueError('unexpected linked compiler variant')

    def test_variants_relocations_and_conditional_backedge(self):
        for i,(image,asm) in enumerate(zip(self.images,self.assemblies)):
            history.check_object(image,i,self.rom,self.objects)
            self.assertNotEqual(history.bounded_copy(asm),asm)
            changed = copy.deepcopy(image)
            rel = changed['relocations'][0]
            raw = bytearray(changed['section_data'][rel])
            struct.pack_into('<I',raw,0,22)
            changed['section_data'][rel] = bytes(raw)
            with self.assertRaises(ValueError):
                history.check_object(changed,i,self.rom,self.objects)
            for offset in (40,42,44,0x184,0x18A,0x19A):
                changed = dict(image)
                text = bytearray(image['text'])
                text[offset] ^= 1
                changed['text'] = bytes(text)
                with self.assertRaises(ValueError):
                    history.check_object(changed,i,self.rom,self.objects)
            for before,after in (('stmia\tr3!', 'stmia\tr1!'),('bne\t.L13','bne\t.L11'),
                                 ('mov\tr1, #180','mov\tr1, #184')):
                self.assertIn(before,asm)
                with self.assertRaises(ValueError):
                    history.bounded_copy(asm.replace(before,after))
        with self.assertRaises(ValueError):
            history.check_object(self.images[0],0,self.rom,dict(self.objects, data_03003A60=history.SHADOW))

    def test_providers_and_current_report(self):
        from match_evidence import report_matches
        history.provider(self.rom,self.mapping,self.index)
        for pc in (0x080C687C,0x080C6882,0x080C68B2,0x080C68BE,0x080C74A0,0x08124CC2,0x08125742,
                   0x080227EA,0x08007164,0x080CBA4E,0x080C95B4,0x08002796,0x0836D4BC,
                   0x08A38A42,0x08A38ABA,0x08142250,0x080C646C):
            changed = bytearray(self.rom)
            changed[pc-history.BASE] ^= 1
            with self.subTest(pc=pc),self.assertRaises(ValueError):
                history.provider(bytes(changed),self.mapping,self.index)
        report = (self.root/'docs/match/080C62CC.md').read_text()
        self.assertTrue(report_matches(report,self.root,history.OWNER))
        for prefix in ('* ROM bytes:','* compiled :','* verification:','**MATCH'):
            row = next(line for line in report.splitlines() if line.startswith(prefix))
            for replacement in (row+'\n'+row,row[:-2]):
                self.assertFalse(history.report_body(report.replace(row,replacement),self.root))

    def test_original_boot_heap_both_callers_boundaries_and_field_accesses(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE,UC_HOOK_MEM_READ,UC_HOOK_MEM_WRITE,UC_MEM_READ,UC_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3,UC_ARM_REG_SP,UC_ARM_REG_LR,UC_ARM_REG_PC
        machine = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        machine.mem_map(history.BASE,(len(self.rom)+4095)&~4095)
        machine.mem_write(history.BASE,self.rom)
        machine.mem_map(0x02000000,0x40000)
        machine.mem_map(0x03000000,0x8000)
        regs = (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2,UC_ARM_REG_R3)
        def run(pc,*args,end=0x03007FF0):
            for reg,value in zip(regs,args):
                machine.reg_write(reg,value&0xFFFFFFFF)
            machine.reg_write(UC_ARM_REG_SP,0x03007E00)
            machine.reg_write(UC_ARM_REG_LR,0x03007FF1)
            machine.emu_start(pc|1,end,count=2000000)
            self.assertEqual(machine.reg_read(UC_ARM_REG_PC),end)
            return machine.reg_read(UC_ARM_REG_R0)
        plans = []
        def cpu_set(uc,pc,size,data):
            source,dest,control = (uc.reg_read(reg) for reg in regs[:3])
            plans.append((source,dest,control))
            width = 4 if control & (1<<26) else 2
            count = control&0x1FFFFF
            fill = bool(control&(1<<24))
            payload = bytes(uc.mem_read(source,width if fill else width*count))
            uc.mem_write(dest,payload*count if fill else payload)
            uc.reg_write(UC_ARM_REG_PC,uc.reg_read(UC_ARM_REG_LR))
        machine.hook_add(UC_HOOK_CODE,cpu_set,begin=0x0814186C,end=0x0814186C)
        run(0x08002768)
        self.assertEqual(plans[-1],(0x08A38A2C,0x03005E78,88))
        run(0x080227E8)
        def put(addr,fmt,*values):
            machine.mem_write(addr,struct.pack('<'+fmt,*values))
        def read(addr,fmt):
            return struct.unpack('<'+fmt,machine.mem_read(addr,struct.calcsize('<'+fmt)))
        entries,control_events,iterations = [],[],[]
        def capture(uc,pc,size,data):
            entries.append(tuple(uc.reg_read(reg) for reg in (*regs,UC_ARM_REG_SP)))
        def copy_site(uc,pc,size,data):
            iterations.append((uc.reg_read(UC_ARM_REG_R1)-4,uc.reg_read(UC_ARM_REG_R3)))
        def shadow(uc,kind,address,width,value,data):
            pc = uc.reg_read(UC_ARM_REG_PC)
            if history.OWNER <= pc < history.END:
                control_events.append((pc,kind,address-history.SHADOW,width))
        machine.hook_add(UC_HOOK_CODE,capture,begin=history.OWNER,end=history.OWNER)
        machine.hook_add(UC_HOOK_CODE,copy_site,begin=0x080C62F6,end=0x080C62F6)
        machine.hook_add(UC_HOOK_MEM_READ|UC_HOOK_MEM_WRITE,shadow,begin=history.SHADOW,end=history.SHADOW+79)
        def setup(flag,index,palette_mode):
            put(0x030028A0,'B',flag)
            put(0x0200203D,'B',1)
            put(history.ANIMATION+2,'B',index)
            put(0x02002FC2,'B',palette_mode)
            put(history.SHADOW,'H',0x0135)
            put(history.SHADOW+74,'B',0xB7)
            entries.clear()
            iterations.clear()
            control_events.clear()
        def verify(expected,mode,filtered,palette_mode):
            state,items,n,m,sp = entries[-1]
            self.assertEqual((n,m),(len(expected),mode))
            history.placement(state,items,n,sp,from_builder=filtered)
            self.assertEqual(iterations,[(items+4*i,state+4*i) for i in range(n)])
            self.assertEqual(read(state,'I'*n),tuple(expected))
            self.assertEqual(read(state+98,'B'),(n,))
            pushed = (15,11,9,8,5,7) if mode else (15,11,9,12,7)
            self.assertEqual(read(state+108,'HH'),(14,len(pushed)))
            self.assertEqual(read(state+112,'H'*len(pushed)),pushed)
            self.assertEqual(read(state+102,'HH'),(0x0135,0xB7))
            self.assertEqual(read(history.SHADOW,'H'),(0x1135,))
            self.assertEqual(read(history.SHADOW+74,'B'),(0xA7,))
            self.assertEqual(control_events,[(0x080C644A,UC_MEM_READ,0,2),(0x080C6456,UC_MEM_READ,74,1),
                (0x080C6464,UC_MEM_WRITE,0,2),(0x080C6466,UC_MEM_READ,74,1),
                (0x080C646C,UC_MEM_READ,74,1),(0x080C646E,UC_MEM_WRITE,74,1)])
            base = (0x08419D60,0x0841B340,0x0841A860,0x08419D60)[palette_mode]
            self.assertEqual(machine.mem_read(history.PALETTE,32),machine.mem_read(base,32))
        records = [0x02002FC4+0x108*i for i in range(12)]
        # At either real script decision, the nonzero manager gate and both
        # constant arguments execute on the guest. Stop just before publishing
        # the constructed handle back to the script.
        for start,end,flag,active,index,palette_mode in (
                (0x08124CB2,0x08124CC8,0,0,0,0),(0x08124CB2,0x08124CC8,8,0,1,1),
                (0x08125732,0x08125748,8,0x925,2,2),(0x08125732,0x08125748,8,0xFFF,0,3)):
            setup(flag,index,palette_mode)
            machine.mem_write(records[0]-1,b'\xac'+b'\x5a'*(12*0x108)+b'\xb4')
            for i,address in enumerate(records):
                put(address+4,'B',(active>>i)&1)
            run(start,end=end)
            verify([v for i,v in enumerate(records) if not flag or active&(1<<i)],int(bool(flag)),True,palette_mode)
            if not flag:
                self.assertEqual(machine.mem_read(records[0]-1,12*0x108+2),b'\xac'+bytes(12*0x108)+b'\xb4')
            if index == 0:
                self.assertEqual(read(history.ANIMATION+2,'BBHH'),(1,0,216,152))
                self.assertEqual(read(history.ANIMATION+72,'H'),(1,))
            elif index == 2:
                self.assertEqual(read(history.ANIMATION+3,'B'),(1,))
                self.assertTrue(read(history.ANIMATION+1,'B')[0]&4)
        incoming = 0x02015000
        values = [records[i%12] for i in range(25)]
        put(incoming,'25I',*values)
        for count in (0,1,24):
            setup(0,1,0)
            state = run(0x080C7484,incoming,count)
            verify(values[:count],0,False,0)
            self.assertEqual(state,entries[-1][0])
        setup(0,1,0)
        run(0x080C7484,incoming,-1)
        self.assertFalse(iterations)
        self.assertEqual(read(entries[-1][0]+98,'B'),(255,))
        setup(0,1,0)
        run(0x080C7484,history.SHADOW+72,1)
        state,items,n,m,sp = entries[-1]
        self.assertEqual(iterations,[(history.SHADOW+72,state)])
        self.assertEqual(control_events[0],(0x080C62F4,UC_MEM_READ,72,4))
        with self.assertRaises(ValueError):
            history.placement(state,items,n,sp,from_builder=False)
        # Stop at the real 25th STM before executing its first out-of-field
        # access. The forwarding entry transfers the original count unchanged.
        setup(0,1,0)
        def limit(uc,pc,size,data):
            if len(iterations) == 25:
                uc.emu_stop()
        machine.hook_add(UC_HOOK_CODE,limit,begin=0x080C62F6,end=0x080C62F6)
        machine.reg_write(UC_ARM_REG_R0,incoming)
        machine.reg_write(UC_ARM_REG_R1,25)
        machine.reg_write(UC_ARM_REG_SP,0x03007E00)
        machine.reg_write(UC_ARM_REG_LR,0x03007FF1)
        machine.emu_start(0x080C7485,0x03007FF0,count=200000)
        state,items,n,m,sp = entries[-1]
        self.assertEqual((machine.reg_read(UC_ARM_REG_PC),n,iterations[-1]),(0x080C62F6,25,(incoming+96,state+96)))
        with self.assertRaises(ValueError):
            history.placement(state,items,n,sp,from_builder=False)
