"""The identified FLASH512 callback, both reader frames, counter and first error."""
import os
from pathlib import Path
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import flash_sector_programmer as flash
import library_units as units
import match
import match_evidence as evidence
import test_flash_program_byte as hardware


@unittest.skipUnless(os.getenv('FFTA_FLASH_PROGRAM_SECTOR_ROOT'),'needs the original ROM, maps and O1 sector source')
class ProgramSectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_PROGRAM_SECTOR_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.source = cls.root/flash.SOURCE
        cls.report = (cls.root/'docs/match/08142160.md').read_text()
        cls.body = bytes.fromhex(next(line.split('`')[1] for line in cls.report.splitlines() if line.startswith('* compiled : ')))
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()

    def test_real_elf_report_replay_and_object_scope(self):
        self.assertEqual(self.body,self.rom[0x142160:0x14220C])
        self.assertEqual(len(self.body),172)
        self.assertTrue(evidence.report_matches(self.report,self.root,flash.OWNER))
        self.assertFalse(evidence.report_matches(self.report,self.root,flash.byte.OWNER))
        for before,after in (('"initial":4096','"initial":4095'),('"phase":2','"phase":3'),
                ('"nested_reader_from_entry_sp":-167','"nested_reader_from_entry_sp":-83')):
            self.assertIn(before,self.report)
            self.assertFalse(evidence.report_matches(self.report.replace(before,after),self.root,flash.OWNER))
        tool = units.resolve(flash.erase.TOOL)
        args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                               objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(tool['cc'],root=self.root,timeout=90)
        with runner.workspace() as work:
            _,_,obj = match.compile_object(runner,work,args,self.root,flash.OWNER,flash.SOURCE)
        text,relocs,offset,state,size = units.signature(obj,flash.OWNER)
        self.assertEqual((obj['type'],len(text),offset,state,size),(1,172,0,1,172))
        self.assertEqual(relocs,((24,2,'data_0200F370'),(34,10,'func_08141F2C'),(48,10,'func_08141AB0'),
                               (100,2,'data_0200F370'),(104,2,'data_0200F374'),(128,10,'func_08141FC8')))
        unit = units.containing(units.load(self.root),flash.OWNER)
        self.assertNotIn(flash.SCHEMA,units.schemas(unit,flash.OWNER,None))
        self.assertNotIn(flash.SCHEMA,units.schemas(unit,flash.erase.OWNER,{'other':1}))
        context = dict(unit=unit,tool=tool)
        objects = evidence.data_snapshot(self.root)
        wrong_objects = objects.replace(b'0x0200F374',b'0x0200F376')
        self.assertNotEqual(objects,wrong_objects)
        for calls,refs,names in (({**flash.CALLS,0x08142182:flash.byte.OWNER},flash.OBJECTS,objects),
                                (flash.CALLS,{**flash.OBJECTS,104:flash.OBJECTS[24]},objects),
                                (flash.CALLS,flash.OBJECTS,wrong_objects)):
            with self.assertRaises(ValueError):
                flash.native_proof(self.body,self.rom,self.mapping,self.index,names,calls,refs,context,{'unit':1})

    def test_changed_source_raw_counter_geometry_reader_or_bus(self):
        with tempfile.TemporaryDirectory(dir=self.root/'build') as work:
            dest = Path(work)
            (dest/'src').mkdir()
            (dest/'include').mkdir()
            (dest/flash.bank.HEADER).write_bytes((self.root/flash.bank.HEADER).read_bytes())
            text = self.source.read_text()
            for before,after in (('void *source','const void *source'),('data_0200F374--','data_0200F374++'),
                                 ('readBuffer[32]','readBuffer[31]'),('destination++','destination += 2'),
                                 ('if (result)','if (!result)')):
                self.assertIn(before,text)
                (dest/flash.SOURCE).write_text(text.replace(before,after,1))
                with self.assertRaises(ValueError):
                    flash.check_source(dest)
        for site in (0x36cf64,0x36cf38,0x36cf64+24,0x36cf38+28,0x141de4,0x141e18,0x141f76,
                     0x14196a,0x141e80,0x141fdc,0x141fe0,0x141fe6,0x142190,0x1421c8):
            rom = bytearray(self.rom)
            rom[site] ^= 1
            with self.subTest(site=hex(site)),self.assertRaises(ValueError):
                flash.erase.provider(rom)
        # Exercise the loop induction independently of the pinned complete ROM digest.
        for offset in (0x6,0x10,0x48,0x4e,0x68,0x6e,0x72,0x74,0x8a,0x94):
            altered = bytearray(self.body)
            altered[offset] ^= 1
            with self.subTest(relative=hex(offset)),self.assertRaises(ValueError):
                flash.loop(flash.erase.closure(bytes(altered),flash.OWNER,self.mapping,count=66))

    def test_timer_writes_cannot_alias_progress_halfword(self):
        # Exercise the memory effect proof independently of the original ROM hash.
        start, end = flash.TIMER_START, flash.TIMER_STOP
        change = bytearray(self.rom)
        change[0x141A60:0x141A64] = struct.pack('<I',flash.REMAINING)
        self.assertNotEqual(self.rom[0x141A60:0x141A64],change[0x141A60:0x141A64])
        graph = flash.erase.closure(bytes(change[start-flash.bank.BASE:end-flash.bank.BASE]),
                                    start,self.mapping,count=65)
        allowed = {(0x04000100,2),(0x04000102,2),(0x03005E44,4),(0x04000200,2),(0x04000208,2),
                   (0x03005E48,2),(0x0200F360,1),(0x03005E42,2),(0x04000202,2)}
        with self.assertRaises(ValueError):
            flash.timer_stores(change,graph,0x04000100,allowed)

    def run_sector(self, ident, sector, *, fail=None, wrapper=False):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_HOOK_CODE
        from unicorn import arm_const as arm
        helper = hardware.NativeTests()
        helper.rom = self.rom
        cpu,chip,writes,reads = helper.machine(self.rom[0x141FC8:0x142000],ident)
        cpu.mem_write(flash.OWNER,self.body)
        def value(addr,size):
            return int.from_bytes(cpu.mem_read(addr,size),'little')
        self.assertEqual(value(0x0200F36C,4),flash.OWNER|1)
        slot = sector & 0xffff
        start = slot*4096
        source = helper.source if slot < 16 else 0x11111111
        payload = bytes((39*i+7)%251 for i in range(4096))
        initial = bytes((0x44,))*65536
        chip.storage[:] = initial
        if slot < 16:
            cpu.mem_write(source,payload)
        cpu.mem_write(flash.REMAINING,b'\xcd\xab')
        cpu.mem_write(0x04000204,struct.pack('<H',0x431a))
        sp = cpu.reg_read(arm.UC_ARM_REG_SP)
        owner_sp = sp-20 if wrapper else sp
        regs = {r:0x5aa50000+r for r in range(arm.UC_ARM_REG_R4,arm.UC_ARM_REG_R11+1)}
        for r,v in regs.items():
            cpu.reg_write(r,v)
        counters,publications,loads,controls = [],[],[],[]
        def remember(uc,access,addr,size,v,target):
            target.append((uc.reg_read(arm.UC_ARM_REG_PC),size,v))
        cpu.hook_add(UC_HOOK_MEM_WRITE,remember,counters,flash.REMAINING,flash.REMAINING+1)
        cpu.hook_add(UC_HOOK_MEM_WRITE,remember,publications,0x0200F364,0x0200F367)
        cpu.hook_add(UC_HOOK_MEM_WRITE,remember,controls,0x04000204,0x04000205)
        def track_source(uc,access,addr,size,v,data):
            pc = uc.reg_read(arm.UC_ARM_REG_PC)
            if pc in (0x08141FDA,0x08141FE0):
                loads.append((pc,size,addr-source))
        if slot < 16:
            cpu.hook_add(UC_HOOK_MEM_READ,track_source,begin=source,end=source+4095)
        function = flash.WRAPPER if wrapper else value(0x0200F36C,4)
        args = (sector,source,4096) if wrapper else (sector,source)
        if fail is not None:
            poll = []
            def phase(uc,address,size,data):
                poll[:] = [uc.reg_read(arm.UC_ARM_REG_R0),uc.reg_read(arm.UC_ARM_REG_R1)-hardware.BUS]
            cpu.hook_add(UC_HOOK_CODE,phase,begin=flash.erase.WAIT,end=flash.erase.WAIT)
            original_read = chip.read
            bad = [2,start] if fail == 'erase' else [1,start+fail]
            chip.read = lambda off: original_read(off) ^ (0x80 if poll == bad else 0)
            helper.invoke(cpu,function,args,0x08141e8c,limit=2000000)
            self.assertEqual(poll,bad)
            interrupted = cpu.context_save()
            ticks = 10 if fail != 'erase' else {0x1b32:500,0x1cc2:2000}[ident]
            self.assertEqual(value(0x03005E42,2),ticks)
            for _ in range(ticks):
                helper.invoke(cpu,value(helper.handler_slot,4))
            self.assertEqual(value(0x0200F360,1),1)
            cpu.context_restore(interrupted)
            helper.run_to(cpu,0x08141e8c,helper.sentinel,limit=2000000)
        else:
            helper.invoke(cpu,function,args,limit=2000000)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),sp)
        self.assertEqual({r:cpu.reg_read(r) for r in regs},regs)
        received = cpu.reg_read(arm.UC_ARM_REG_R0)
        if slot >= 16:
            self.assertEqual((received,writes,reads,counters,controls,publications),(0x80ff,[],[],[],[],[]))
            self.assertEqual(value(flash.REMAINING,2),0xabcd)
            self.assertEqual(chip.storage,initial)
            return
        erase_command = [(0x5555,0xaa),(0x2aaa,0x55),(0x5555,0x80),(0x5555,0xaa),(0x2aaa,0x55),(start,0x30)]
        byte_loop = fail != 'erase'
        succeeded = (4096 if fail is None else fail) if byte_loop else 0
        attempts = succeeded+int(isinstance(fail,int))
        expected_status = 0 if fail is None else (0xc001 if byte_loop else 0xc002)
        self.assertEqual(received,expected_status)
        counters_expected = ([(0x081421AA,2,4096)]+[(0x081421D0,2,4096-i) for i in range(1,succeeded+1)]
                             if byte_loop else [])
        self.assertEqual(counters,counters_expected)
        self.assertEqual(value(flash.REMAINING,2),4096-succeeded if byte_loop else 0xabcd)
        self.assertEqual(loads,[(pc,1,i) for i in range(attempts) for pc in (0x08141FDA,0x08141FE0)])
        self.assertEqual(writes,erase_command+[w for i in range(attempts) for w in (*hardware.PREFIX,(start+i,payload[i]))]
                         + ([(0x5555,0xf0)] if fail is not None and ident == 0x1cc2 else []))
        self.assertEqual(reads,([start]+[start+i for i in range(attempts)]+([start+attempts-1] if byte_loop else [start])
                               if fail is not None else [start]+[start+i for i in range(attempts)])
                         + (list(range(start,start+4096)) if wrapper else []))
        expected_storage = bytearray(initial)
        expected_storage[start:start+4096] = bytes([255])*4096
        expected_storage[start:start+attempts] = payload[:attempts]
        self.assertEqual(chip.storage,expected_storage)
        expected_readers = [owner_sp-167]+([owner_sp-83] if byte_loop else [])
        self.assertEqual([v for _,_,v in publications[:len(expected_readers)]],expected_readers)
        if not wrapper:
            self.assertEqual([v for _,_,v in publications],expected_readers)
            self.assertEqual(value(0x0200F364,4),expected_readers[-1])
        self.assertEqual(value(0x04000204,2),0x431b)
        self.assertTrue(all(size == 2 for _,size,_ in controls))
        speed = {0x1b32:0,0x1cc2:3}[ident]
        self.assertEqual([v for _,_,v in controls[:(4 if byte_loop else 2)]],([0x4318|speed,0x431b]*(2 if byte_loop else 1)))

    def test_original_caller_and_boundary_sectors(self):
        self.run_sector(0x1b32,0,wrapper=True)
        self.run_sector(0x1cc2,0x1000f)
        self.run_sector(0x1b32,16)
        self.run_sector(0x1cc2,65535)

    def test_nested_erase_and_byte_failures(self):
        self.run_sector(0x1b32,8,fail='erase')
        self.run_sector(0x1cc2,15,fail=0)
        self.run_sector(0x1b32,2,fail=193)
        self.run_sector(0x1cc2,0,fail=4095)


if __name__ == '__main__':
    unittest.main()
