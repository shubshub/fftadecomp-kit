"""Machine registration, coordinate bounds, private lifetimes and real particle teardown."""
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import rising_particle_callback as particle


@unittest.skipUnless(os.environ.get('FFTA_RISING_PARTICLE_ROOT'),'requires the USA ROM and rising particle source')
class RisingParticle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_RISING_PARTICLE_ROOT'])
        cls.built = owner.build(cls.root,particle.OWNER,selector=buffers.SELECTOR)
        cls.raw,cls.manifest,_,cls.mapping,cls.index,cls.objects,cls.rom,_,cls.elf = cls.built

    def test_full_report_and_typed_relocations(self):
        self.assertEqual(self.raw,self.rom[0x11D73C:0x11D8A4])
        self.assertEqual(self.manifest['bindings'],particle.BINDINGS)
        report = (self.root/'docs/match/0811D73C.md').read_text()
        self.assertTrue(match_evidence.report_matches(report,self.root,particle.OWNER))
        changed = report.replace('"terminal_state":2','"terminal_state":3')
        self.assertNotEqual(report,changed)
        self.assertFalse(match_evidence.report_matches(changed,self.root,particle.OWNER))
        image = match.elf_image(self.elf)
        for symbol in ('func_080DC224','func_080D6134','data_083A6F2C','data_083A70B4'):
            t,i = next((t,i) for t,rows in image['symbol_tables'].items() for i,s in enumerate(rows)
                       if s['name'] == symbol)
            for offset in (8,12,13):
                changed = bytearray(self.elf)
                changed[image['sections'][t][4]+16*i+offset] ^= 1
                with self.subTest(symbol=symbol,offset=offset), self.assertRaises(ValueError):
                    owner.original_bindings(match.elf_image(bytes(changed)),particle.OWNER,self.rom,
                                            self.mapping,self.objects,selector=buffers.SELECTOR,index=self.index)

    def test_registration_and_cleanup_mutations(self):
        for address in (0x0811DB5A,0x0811DB78,0x080059FE,0x08005A68):
            wrong = bytearray(self.rom)
            wrong[address-particle.BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                particle.registration(wrong,self.mapping,self.index)
        for address in (0x0811D7EA,0x080D6110,0x080D4E38,0x080D4E42,0x080D5F82,0x080058DA,0x080DFDD4):
            wrong = bytearray(self.rom)
            wrong[address-particle.BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                particle.child_task(wrong)

    def test_private_halfword_alias_cannot_use_the_saved_frame(self):
        from owner_graph_profile import graph
        for offset in (0x0811D7B8,0x0811D85A):
            altered = bytearray(self.raw)
            # The high output pointer was SP+18 or SP+22. SP+24 is the
            # first saved word and cannot receive an output halfword.
            altered[offset-particle.OWNER] = 24
            ref = owner.refine(altered,particle.OWNER,self.mapping)
            ins,edges,_,_,_ = graph(altered,particle.OWNER,ref)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                particle.owner_frame(ins,edges,self.rom,self.mapping)

    def test_actual_scheduler_coordinate_phases_and_cleanup(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0 as r0,UC_ARM_REG_SP as sr,UC_ARM_REG_LR as lr,UC_ARM_REG_PC as pc
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        cpu.mem_map(particle.BASE,len(self.rom))
        cpu.mem_write(particle.BASE,self.rom)
        cpu.mem_map(0x02000000,0x40000)
        cpu.mem_map(0x03000000,0x8000)
        parent,model,actor,manager,gate,desc = (0x02015000,0x02009000,0x02009100,0x02012000,0x02009700,0x02011900)
        sp,end = 0x03007400,particle.BASE
        palette = 0x0201D000
        def read(addr,fmt='I'):
            return struct.unpack('<'+fmt,cpu.mem_read(addr,struct.calcsize(fmt)))[0]
        def put(addr,value,fmt='I'):
            cpu.mem_write(addr,struct.pack('<'+fmt,value))
        allocated,freed,phases,screen_writes,destruction = [],[],[],[],[]
        palette_done = False
        put(0x02008FF0,manager)
        put(model,actor)
        put(parent+24+8,model)
        put(parent+24+12,gate)
        put(model+8,7,'h')
        put(model+10,10,'h')
        put(model+12,-9,'h')
        def stub(m,addr,size,user):
            args = [m.reg_read(r0+i) for i in range(4)]
            if addr == 0x08007138:
                result = 0x02018000+256*len(allocated)
                allocated.append((result,args[1]))
            elif addr == 0x03005E78:
                m.mem_write(args[0],bytes(args[1]))
                result = args[0]
            elif addr == 0x08147EC8:
                self.assertEqual(args,[112,16,150,8])
                result = palette
            elif addr == 0x081485D4:
                result = int(palette_done)
            elif addr == 0x08148738:
                result = 0
            elif addr == 0x08007170:
                freed.append(args[1])
                result = 0
            else:
                destruction.append(args[0])
                result = 0
            m.reg_write(r0,result)
            m.reg_write(pc,m.reg_read(lr))
        for addr in (0x08007138,0x03005E78,0x08147EC8,0x081485D4,0x08148738,0x08007170,0x08011428):
            cpu.hook_add(UC_HOOK_CODE,stub,begin=addr,end=addr)
        def enter(m,addr,size,user):
            event=m.reg_read(r0+1)
            phases.append((addr,m.reg_read(r0),read(event,'H'),m.reg_read(r0+2)))
        for addr in (particle.OWNER,0x080D4DEC,0x080DFB0C):
            cpu.hook_add(UC_HOOK_CODE,enter,begin=addr,end=addr)
        def bg_write(m,access,addr,size,value,user):
            screen_writes.append((addr,value & 0xFFFF))
        cpu.hook_add(UC_HOOK_MEM_WRITE,bg_write,begin=0x03000956,end=0x03000959)
        cpu.reg_write(sr,sp)
        cpu.reg_write(r0+4,parent+24)
        cpu.reg_write(r0+6,parent)
        cpu.emu_start(0x0811DB4D,0x0811DB64,count=3000)
        node=read(parent+24+24)
        state=node+24
        self.assertEqual(allocated,[(node,68+28)])
        self.assertEqual(phases,[(particle.OWNER,node,0,state)])
        self.assertEqual((read(state+8),read(state+12)),(model,parent+24+12))
        self.assertEqual((read(state+2,'h'),read(state+4,'h')),(8,-6))
        self.assertEqual(read(node+20,'H'),0x100)
        def invoke(phase):
            put(desc,phase,'H')
            cpu.reg_write(r0,node)
            cpu.reg_write(r0+1,desc)
            cpu.reg_write(r0+2,state)
            regs = [0x124000+i for i in range(8)]
            for i,value in enumerate(regs):
                cpu.reg_write(r0+4+i,value)
            cpu.reg_write(sr,sp)
            cpu.reg_write(lr,end|1)
            cpu.emu_start(particle.OWNER|1,end,count=9000)
            self.assertEqual((cpu.reg_read(pc),cpu.reg_read(sr),cpu.reg_read(r0)),(end,sp,0))
            self.assertEqual([cpu.reg_read(r0+4+i) for i in range(8)],regs)
            return read(desc,'H')
        self.assertEqual(invoke(0x100),0x101)
        for n in range(24,0,-1):
            self.assertEqual(invoke(0x101),0x101)
            self.assertEqual(read(state,'H'),n)
        self.assertEqual(invoke(0x101),0x101)
        self.assertEqual(read(state,'H'),0)
        put(gate+24+6,0x8000,'H')
        put(actor+4,0x51,'B')
        self.assertEqual(invoke(0x101),0x102)
        self.assertEqual(screen_writes[-2:],[(0x03000956,8),(0x03000958,50)])
        child,sequence=read(state+16),read(state+64)
        self.assertEqual(allocated[1:],[(child,28+28),(sequence,16+28)])
        self.assertEqual(read(state+48),palette)
        self.assertEqual((read(child+24+20),read(child+24+6,'H')),(state+20,7))
        self.assertEqual(read(child+24+24),particle.ASSET)
        self.assertEqual(read(sequence+24+12),particle.SEQUENCE)
        self.assertEqual(invoke(0x102),0x102)
        self.assertEqual(read(state+54,'H'),149)
        for remaining in range(148,-1,-1):
            self.assertEqual(invoke(0x102),0x102)
            self.assertEqual(read(state+54,'H'),remaining)
        self.assertEqual(read(state+52,'h'),-22)
        # The two halfword outputs wrap independently at both signed endpoints.
        for x,y,kind in ((-32768,32767,0x51),(32767,-32768,0x52),(37,-21,0x51)):
            put(state+2,x,'h')
            put(state+52,y,'h')
            put(state+54,0,'H')
            put(actor+4,kind,'B')
            self.assertEqual(invoke(0x102),0x102)
            self.assertEqual(screen_writes[-2:],[(0x03000956,(16-x)&65535),
                                              (0x03000958,(48-y-4*(kind==0x51))&65535)])
        palette_done = True
        self.assertEqual(invoke(0x102),0x102)
        self.assertEqual(read(state+48),0)
        self.assertEqual(read(state+16),child)
        put(child+20,2,'H')
        for i in range(7):
            put(state+20+4*i,0x02020000+i*64)
        self.assertEqual(invoke(0x102),0x103)
        self.assertIn((0x080D4DEC,child,1,child+24),phases)
        self.assertEqual(destruction,[0x02020000+i*64 for i in range(7)])
        self.assertEqual(cpu.mem_read(state+20,28),bytes(28))
        self.assertEqual(freed,[child])
        self.assertEqual(invoke(0x103),2)
        for phase in (1,2,0xFF,0x104,0xFFFF):
            self.assertEqual(invoke(phase),phase)
