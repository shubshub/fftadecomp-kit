"""Actual D4BF and fallback erase retries, copied RAM scan and sector writes."""
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import flash_retry_programmer as flash
import library_units as units
import match
import match_evidence as evidence
import test_flash_program_byte as hardware


@unittest.skipUnless(os.getenv('FFTA_FLASH_RETRY_ROOT'),'needs original FLASH512 input and matching C')
class RetryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_RETRY_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.report = (cls.root/'docs/match/08142000.md').read_text()
        cls.body = bytes.fromhex(next(l.split('`')[1] for l in cls.report.splitlines() if l.startswith('* compiled : ')))
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()

    def test_exact_member_replay_and_existing_callee_schemas(self):
        self.assertEqual((len(self.body),self.body),(292,self.rom[0x142000:0x142124]))
        self.assertTrue(evidence.report_matches(self.report,self.root,flash.OWNER))
        self.assertFalse(evidence.report_matches(self.report,self.root,flash.simple.OWNER))
        for old,new in (('"halfword_writes":18','"halfword_writes":16'),('"extra_on_retry":6','"extra_on_retry":5'),
                        ('"max_attempts":81','"max_attempts":80')):
            self.assertIn(old,self.report)
            self.assertFalse(evidence.report_matches(self.report.replace(old,new),self.root,flash.OWNER))
        for a,schema in ((flash.SCAN,'elf-symbol-thumb-data-v1'),(flash.CHECK,'elf-symbol-thumb-function-address-thunks-v1')):
            report = (self.root/f'docs/match/{a:08X}.md').read_text()
            self.assertIn(f'* verification: `{schema}`',report)
            self.assertTrue(evidence.report_matches(report,self.root,a))
        tool = units.resolve(flash.erase.TOOL)
        args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                               objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(tool['cc'],root=self.root,timeout=90)
        with runner.workspace() as work:
            _,_,original = match.compile_object(runner,work,args,self.root,flash.OWNER,flash.SOURCE)
        _,relocs,offset,state,size = units.signature(original,flash.OWNER)
        self.assertEqual((original['type'],offset,state,size),(1,0,1,292))
        self.assertEqual(relocs,tuple(sorted([(off,2,n) for off,(n,_) in {**flash.OBJECTS,**flash.FUNCTIONS}.items()]
                           + [(site-flash.OWNER,10,f'func_{a:08X}') for site,a in flash.CALLS.items()])))
        u = units.containing(units.load(self.root),flash.OWNER)
        self.assertNotIn(flash.SCHEMA,units.schemas(u,flash.OWNER,None))
        self.assertNotIn(flash.SCHEMA,units.schemas(u,flash.simple.OWNER,{'other':1}))
        context = dict(unit=u,tool=tool)
        for calls,literals,functions in ((flash.CALLS,flash.OBJECTS,{68:flash.FUNCTIONS[72],72:flash.FUNCTIONS[68]}),
            ({**flash.CALLS,0x0814209C:flash.byte.OWNER},flash.OBJECTS,flash.FUNCTIONS),
            (flash.CALLS,{**flash.OBJECTS,216:flash.OBJECTS[64]},flash.FUNCTIONS)):
            with self.assertRaises(ValueError):
                flash.native_proof(self.body,self.rom,self.mapping,self.index,evidence.data_snapshot(self.root),
                                   calls,literals,functions,context,{'unit':1})

    def test_copy_frame_retry_and_scan_fail_closed(self):
        graphs = flash.simple.sdk_graphs(self.rom,self.mapping,self.index,{flash.SCAN:(flash.CHECK,16),flash.CHECK:(flash.END,9)})
        def mutate(site,replacement,fun):
            altered = bytearray(self.rom)
            old = altered[site-flash.BASE:site-flash.BASE+len(replacement)]
            self.assertNotEqual(old,replacement)
            altered[site-flash.BASE:site-flash.BASE+len(replacement)] = replacement
            a,b,n = next((a,b,n) for a,b,n in ((flash.OWNER,flash.SCAN,120),(flash.SCAN,flash.CHECK,16),
                                                (flash.CHECK,flash.END,9)) if a <= site < b)
            with self.subTest(site=hex(site)),self.assertRaises(ValueError):
                graph = flash.erase.closure(bytes(altered[a-flash.BASE:b-flash.BASE]),a,self.mapping,count=n)
                if fun == flash.copy_and_scan:
                    fun(bytes(altered),{**graphs,a:graph})
                else:
                    fun(graph)
        for site,half,fun in ((0x08142008,'97b0',flash.owner_frame),(0x08142036,'0340',flash.copy_and_scan),
                (0x08142052,'0432',flash.copy_and_scan),(0x08142054,'c81e',flash.copy_and_scan),
                (0x0814207E,'0231',flash.copy_and_scan),(0x08142068,'502c',flash.retry_and_program),
                (0x08142092,'0526',flash.retry_and_program),(0x081420E2,'0220',flash.retry_and_program),
                (0x08142140,'f8d1',flash.copy_and_scan),(0x0814215C,'0580',flash.copy_and_scan)):
            mutate(site,bytes.fromhex(half),fun)
        for site in (0x36ceb4,0x36ce88,0x36ceb4+24,0x141dfc,0x141fe0):
            rom = bytearray(self.rom); rom[site] ^= 1
            with self.assertRaises(ValueError):
                flash.erase.provider(rom)

    def run_original(self,ident,sector,*,erase_errors=(),scan_errors=None,byte_error=None):
        from unicorn import UC_HOOK_CODE,UC_HOOK_MEM_READ,UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        helper = hardware.NativeTests()
        helper.rom = self.rom
        cpu,chip,writes,reads = helper.machine(self.rom[0x141FC8:0x142000],ident)
        cpu.mem_write(flash.OWNER,self.body)
        scan_errors = scan_errors or {}
        def value(addr,size):
            return int.from_bytes(cpu.mem_read(addr,size),'little')
        self.assertEqual(value(0x0200F36C,4),flash.OWNER|1)
        slot = sector & 65535
        start = slot*4096
        source = helper.source if slot < 16 else 0x11111111
        payload = bytes((17*i+3)%253 for i in range(4096))
        if slot < 16:
            cpu.mem_write(source,payload)
        initial = bytes((0x35,))*65536
        chip.storage[:] = initial
        cpu.mem_write(flash.simple.REMAINING,b'\xcd\xab')
        cpu.mem_write(0x04000204,struct.pack('<H',0x431a))
        sp = cpu.reg_read(arm.UC_ARM_REG_SP)
        local = sp-124
        cpu.mem_write(local,b'\xA7'*96)
        regs = {r:0x82a60000+r for r in range(arm.UC_ARM_REG_R4,arm.UC_ARM_REG_R11+1)}
        for r,v in regs.items():
            cpu.reg_write(r,v)
        erases,scans,source_reads,counters,publications = [],[],[],[],[]
        phase = [None,None]
        def entered_erase(uc,address,size,data):
            self.assertEqual(uc.reg_read(arm.UC_ARM_REG_R0),slot)
            erases.append(uc.reg_read(arm.UC_ARM_REG_LR)&~1)
        def entered_scan(uc,address,size,data):
            self.assertEqual(value(local+12,4),flash.simple.SETUP)
            self.assertEqual(uc.mem_read(local,36),self.rom[0x142124:0x142148])
            self.assertEqual(uc.reg_read(arm.UC_ARM_REG_R0),hardware.BUS+start)
            scans.append([])
        def remember(uc,access,address,size,v,target):
            target.append((uc.reg_read(arm.UC_ARM_REG_PC),size,v))
        def read_source(uc,access,address,size,v,data):
            if uc.reg_read(arm.UC_ARM_REG_PC) in (0x08141FDA,0x08141FE0):
                source_reads.append(address-source)
        def wait(uc,address,size,data):
            phase[:] = [uc.reg_read(arm.UC_ARM_REG_R0),uc.reg_read(arm.UC_ARM_REG_R1)-hardware.BUS]
        cpu.hook_add(UC_HOOK_CODE,entered_erase,begin=flash.erase.OWNER,end=flash.erase.OWNER)
        # The later byte reader reuses the first four bytes of this very same local.
        cpu.hook_add(UC_HOOK_CODE,entered_scan,begin=local+4,end=local+4)
        cpu.hook_add(UC_HOOK_CODE,wait,begin=flash.erase.WAIT,end=flash.erase.WAIT)
        cpu.hook_add(UC_HOOK_MEM_WRITE,remember,publications,0x0200F364,0x0200F367)
        cpu.hook_add(UC_HOOK_MEM_WRITE,remember,counters,flash.simple.REMAINING,flash.simple.REMAINING+1)
        if slot < 16:
            cpu.hook_add(UC_HOOK_MEM_READ,read_source,begin=source,end=source+4095)
        read = chip.read
        def bus_read(addr):
            if cpu.reg_read(arm.UC_ARM_REG_PC) == local+0x16:
                scans[-1].append(addr-start)
                if scan_errors.get(len(erases)) == addr-start:
                    return 0x0c
            if ((phase[0] == 2 and len(erases) in erase_errors) or
                    (byte_error is not None and phase == [1,start+byte_error])):
                return read(addr)^0x80
            return read(addr)
        chip.read = bus_read
        # Stop at the first mismatch in each wait. Service actual timer IRQs,
        # then resume the interrupted original poll with its register context.
        def pause(uc,addr,size,data):
            if value(0x0200F360,1) == 0:
                uc.emu_stop()
        stop_pc = 0x08141E8C
        cpu.hook_add(UC_HOOK_CODE,pause,begin=stop_pc,end=stop_pc)
        cpu.reg_write(arm.UC_ARM_REG_R0,sector)
        cpu.reg_write(arm.UC_ARM_REG_R1,source)
        cpu.reg_write(arm.UC_ARM_REG_LR,helper.sentinel|1)
        pc = flash.OWNER
        interrupts = []
        while True:
            cpu.emu_start(pc|1,helper.sentinel,count=4000000)
            pc = cpu.reg_read(arm.UC_ARM_REG_PC)
            if pc == helper.sentinel:
                break
            self.assertEqual(pc,stop_pc)
            ticks = 10 if phase[0] == 1 else 40
            self.assertEqual(value(0x03005E42,2),ticks)
            interrupts.append(tuple(phase))
            self.assertLessEqual(len(interrupts),87)
            saved = cpu.context_save()
            for _ in range(ticks):
                helper.invoke(cpu,value(helper.handler_slot,4))
            self.assertEqual(value(0x0200F360,1),1)
            cpu.context_restore(saved)
        self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),sp)
        self.assertEqual({r:cpu.reg_read(r) for r in regs},regs)
        status = cpu.reg_read(arm.UC_ARM_REG_R0)
        if slot >= 16:
            self.assertEqual((status,scans,erases,reads,writes,counters,publications),(0x80ff,[],[],[],[],[],[]))
            self.assertEqual((value(flash.simple.REMAINING,2),chip.storage),(0xabcd,initial))
            return
        first = next((n for n in range(1,82) if n not in erase_errors and n not in scan_errors),None)
        tries = first or 81
        extra = 0 if first is None else (1 if first == 1 else 6)
        self.assertEqual(erases,[0x08142072]*tries+[0x081420A0]*extra)
        self.assertEqual(scans,[list(range(scan_errors.get(n,4095)+1)) for n in range(1,tries+1) if n not in erase_errors])
        reader_values = [local-83]*(tries+extra)+([] if first is None else [local+1])
        self.assertEqual([v for _,_,v in publications],reader_values)
        self.assertEqual(value(0x0200F364,4),reader_values[-1])
        self.assertEqual(bytes(cpu.mem_read(local+(0 if first is None else 4),36 if first is None else 32)),
                         self.rom[0x142124+(0 if first is None else 4):0x142148])
        commands = [(0x5555,0xaa),(0x2aaa,0x55),(0x5555,0x80),(0x5555,0xaa),(0x2aaa,0x55),(start,0x30)]
        expected_bus = commands*(tries+extra)
        expected_flash = bytearray(initial)
        expected_flash[start:start+4096] = bytes([255])*4096
        if first is None:
            self.assertEqual(status,0xc002 if tries in erase_errors else 0x8004)
            self.assertEqual((counters,source_reads,value(flash.simple.REMAINING,2)),([],[],0xabcd))
        else:
            good = 4096 if byte_error is None else byte_error
            attempts = good+int(byte_error is not None)
            self.assertEqual(status,0 if byte_error is None else 0xc001)
            self.assertEqual(source_reads,[i for i in range(attempts) for _ in range(2)])
            self.assertEqual(counters,[(0x081420C6,2,4096)]+[(0x081420E0,2,4096-i) for i in range(1,good+1)])
            self.assertEqual(value(flash.simple.REMAINING,2),4096-good)
            self.assertEqual(value(local,4),int.from_bytes(self.rom[0x141aac:0x141ab0],'little'))
            expected_bus.extend(w for i in range(attempts) for w in (*hardware.PREFIX,(start+i,payload[i])))
            expected_flash[start:start+attempts] = payload[:attempts]
        self.assertEqual(interrupts,[(2,start)]*len(set(range(1,tries+extra+1))&set(erase_errors))
                         + ([(1,start+byte_error)] if first is not None and byte_error is not None else []))
        self.assertEqual(writes,expected_bus)
        self.assertEqual(chip.storage,expected_flash)
        self.assertEqual(value(0x04000204,2),0x431b)

    def test_original_successful_retries_and_ignored_extra_status(self):
        self.run_original(0xd4bf,0)
        self.run_original(0x6bad,0x1000f,scan_errors={1:18},erase_errors={3})
        self.run_original(0xd4bf,10,erase_errors={1},byte_error=4095)
        self.run_original(0x6bad,3,scan_errors={n:0 for n in range(1,81)},byte_error=0)

    def test_original_retry_exhaustion_and_guard(self):
        self.run_original(0x6bad,2,erase_errors=set(range(1,82)))
        self.run_original(0xd4bf,11,scan_errors={n:0 for n in range(1,82)})
        self.run_original(0x6bad,16)
        self.run_original(0xd4bf,65535)


if __name__ == '__main__':
    unittest.main()
