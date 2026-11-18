"""Original FLASH512 chip command, synchronous wait/timeout, and local reader lifetime."""
import os
from types import SimpleNamespace
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import flash_chip_erase as erase
import library_units as units
import match
import match_evidence as evidence
import plausible
import test_flash_program_byte as flash


@unittest.skipUnless(os.getenv('FFTA_FLASH_CHIP_ROOT'), 'requires the retail ROM, maps and recovered FLASH512 C')
class ChipEraseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_CHIP_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.original = cls.rom[erase.OWNER-erase.bank.BASE:erase.END-erase.bank.BASE]
        cls.report = (cls.root/'docs/match/08141EB8.md').read_text()
        cls.linked = bytes.fromhex(next(line.split('`')[1] for line in cls.report.splitlines() if line.startswith('* compiled : ')))
        cls.stripped = erase.stripped_build(cls.root)

    def test_exact_original_elf_and_fresh_replay(self):
        self.assertEqual(self.original, self.linked)
        self.assertEqual((len(self.linked),len(self.stripped)), (116,104))
        self.assertTrue(evidence.report_matches(self.report,self.root,erase.OWNER))
        for before,after in (('"local_bytes":64','"local_bytes":80'), ('"phase":3','"phase":2'),
                             ('"installed":135','"installed":134'), ('the six qualifiers','zero qualifiers')):
            self.assertIn(before,self.report)
            self.assertFalse(evidence.report_matches(self.report.replace(before,after),self.root,erase.OWNER))
        self.assertFalse(evidence.report_matches(self.report,self.root,erase.sector.OWNER))

    def test_original_object_relocations_and_target_scope(self):
        tool = units.resolve(erase.sector.TOOL)
        args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                               linker=match.DEFAULT_LD,objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc,root=self.root,timeout=90)
        with runner.workspace() as work:
            _,_,original = match.compile_object(runner,work,args,self.root,erase.OWNER,erase.SOURCE)
        self.assertEqual(original['type'],1)
        body, relocations, offset, state, extent = units.signature(original,erase.OWNER)
        self.assertEqual((len(body),offset,state,extent),(116,0,1,116))
        self.assertEqual(relocations,((48,10,'func_08141AB0'),(64,10,'_call_via_r3'),
                                     (100,2,'data_0200F370'),(112,2,'data_0200F368')))
        unit = units.containing(units.load(self.root),erase.OWNER)
        context = dict(unit=unit,tool=tool)
        index = (self.root/'symbols/functions.txt').read_bytes()
        mapping, objects = evidence.mapping_snapshot(self.root), evidence.data_snapshot(self.root)
        for calls,literals in ((erase.CALLS,{}),
                ({0x08141EE8:erase.sector.INSTALL,0x08141EF8:0x08142248},erase.OBJECTS),
                (erase.CALLS,{0x64:erase.OBJECTS[0x70],0x70:erase.OBJECTS[0x64]})):
            with self.assertRaises(ValueError):
                erase.native_proof(self.linked,self.rom,mapping,index,objects,calls,literals,context,{'unit':1})

    def test_no_other_source_command_provider_or_frame(self):
        path = self.root/erase.SOURCE
        text = path.read_text()
        closure = plausible.include_closure(self.root,path)
        self.assertEqual(len(erase.qualifier_offsets(text,self.root,self.root,closure)),6)
        for before,after in (('= 0x10;', '= 0x30;'), ('0x0E002AAA','0x0E002AAB'),
                             ('data_0200F368(3','data_0200F368(2'), ('readBuffer[32]','readBuffer[31]'),
                             ('func_08141AB0(readBuffer)', 'func_08141AB0(readBuffer+1)')):
            self.assertIn(before,text)
            self.assertFalse(erase.qualifier_offsets(text.replace(before,after),self.root,self.root,closure))
        u = units.containing(units.load(self.root),erase.OWNER)
        self.assertNotIn(erase.SCHEMA,units.schemas(u,erase.OWNER,None))
        self.assertNotIn(erase.SCHEMA,units.schemas(u,erase.sector.OWNER,{'other':1}))
        for site in (0x141ee4,0x141ee8,0x141ef4,0x141ef8,0x141e1c,0x36ceb8,0x36cf68,0x36ce82,0x36cf32):
            changed = bytearray(self.rom)
            changed[site] ^= 1
            with self.subTest(at=hex(site)),self.assertRaises(ValueError):
                erase.provider(bytes(changed))
        proof = erase.ChipReaderFrame(self.rom,evidence.mapping_snapshot(self.root))
        stack = [(False,False,True)]*16+[(False,True,False)]*3+[(True,True,False)]
        for reg,off,site in ((match.ARM_REG_R0,-76,0x08141ee8), (match.ARM_REG_R1,-80,0x08141ee8),
                             (match.ARM_REG_R0,-80,0x08141eec)):
            with self.assertRaises(ValueError):
                proof.check_call(erase.sector.INSTALL,{reg:off},stack,{},site=site)

    def test_original_and_linked_chip_erase_and_stripped_timeout(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        helper = flash.NativeTests()
        helper.rom = self.rom
        bus = flash.BUS
        initial = bytes(range(256))*256
        def read_word(cpu, address):
            return struct.unpack('<I',cpu.mem_read(address,4))[0]
        for kind,body in (('original',self.original),('linked',self.linked),
                          ('busy',self.original),('stripped',self.stripped)):
            for ident,ticks,speed in ((0xd4bf,200,1),(0x1b32,500,0),(0x1cc2,2000,3),(0x6bad,200,3)):
                with self.subTest(kind=kind,ident=hex(ident)):
                    cpu,chip,writes,reads = helper.machine(self.rom[0x141fc8:0x142000],ident)
                    self.assertEqual(read_word(cpu,0x0200f378), erase.OWNER|1)
                    cpu.mem_write(erase.OWNER,body)
                    entry_sp = cpu.reg_read(arm.UC_ARM_REG_SP)
                    local = entry_sp - (76 if kind == 'stripped' else 80)
                    cpu.mem_write(local,b'WAIT')
                    cpu.mem_write(0x04000204,struct.pack('<H',0x431a))
                    chip.storage[:] = initial
                    # Hold DQ/readback busy throughout the real interrupt countdown.
                    # The timer and timeout behavior still execute as original ROM code.
                    if kind == 'busy':
                        chip.read = lambda offset: 0xcc
                    pending,waits,fetches,waitcnt = [],[],[],[]
                    def publication(uc,access,addr,size,value,data):
                        pending.append((uc.reg_read(arm.UC_ARM_REG_PC),size,value,bytes(uc.mem_read(local,4))))
                    def wait(uc,addr,size,data):
                        waits.append(tuple(uc.reg_read(r) for r in (arm.UC_ARM_REG_R0,arm.UC_ARM_REG_R1,
                            arm.UC_ARM_REG_R2,arm.UC_ARM_REG_SP))+(read_word(uc,0x0200f364),))
                    def control(uc,access,addr,size,value,data):
                        waitcnt.append((size,value))
                    def fetched(uc,addr,size,data):
                        fetches.append(addr)
                    cpu.hook_add(UC_HOOK_MEM_WRITE,publication,begin=0x0200f364,end=0x0200f367)
                    cpu.hook_add(UC_HOOK_CODE,wait,begin=erase.sector.WAIT,end=erase.sector.WAIT)
                    cpu.hook_add(UC_HOOK_CODE,fetched,begin=local,end=local+3)
                    cpu.hook_add(UC_HOOK_MEM_WRITE,control,begin=0x04000204,end=0x04000205)
                    regs = {r:0xab1c0000+r for r in range(arm.UC_ARM_REG_R4,arm.UC_ARM_REG_R11+1)}
                    for r,v in regs.items():
                        cpu.reg_write(r,v)
                    if kind in ('stripped','busy'):
                        helper.invoke(cpu,erase.OWNER,(),0x08141e8c)
                        interrupted = cpu.context_save()
                        self.assertEqual(struct.unpack('<H',cpu.mem_read(0x03005e42,2))[0],ticks)
                        for _ in range(ticks):
                            helper.invoke(cpu,read_word(cpu,helper.handler_slot))
                        self.assertEqual(cpu.mem_read(0x0200f360,1),bytes([1]))
                        cpu.context_restore(interrupted)
                        helper.run_to(cpu,0x08141e8c,helper.sentinel)
                    else:
                        helper.invoke(cpu,erase.OWNER)
                    self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),entry_sp)
                    self.assertEqual({r:cpu.reg_read(r) for r in regs},regs)
                    self.assertEqual(waits,[(3,bus,255,local,local|1)])
                    self.assertEqual(pending,[(0x08141ab8,4,local|1,b'WAIT')])
                    self.assertEqual(read_word(cpu,0x0200f364),local|1)
                    self.assertEqual(waitcnt,[(2,0x4318|speed),(2,0x431b)])
                    command = flash.PREFIX[:2]+[(0x5555,0x80)]+flash.PREFIX[:2]+[(0x5555,0x10)]
                    expected = command if kind != 'stripped' else [(0x2aaa,0x55),(0x5555,0x10)]
                    timeout = kind in ('busy','stripped')
                    if timeout and ident == 0x1cc2:
                        expected += [(0x5555,0xf0)]
                    self.assertEqual(writes,expected)
                    self.assertEqual(chip.storage,initial if kind == 'stripped' else bytes([255])*65536)
                    self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R0),0xc003 if timeout else 0)
                    polls = 2 if timeout else 1
                    self.assertEqual(reads,[0]*polls)
                    self.assertEqual(fetches,[local,local+2]*polls)
