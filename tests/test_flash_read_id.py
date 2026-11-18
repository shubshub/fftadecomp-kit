"""Original FLASH512 ID bus sequence, exact local delays, RAM execution and native controls."""
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import flash_read_id as flash
import match
import match_evidence as evidence
import library_units as units
import plausible
import test_flash_program_byte as hardware


@unittest.skipUnless(os.getenv('FFTA_FLASH_ID_ROOT'),'needs the original ROM and FLASH512 ID source')
class FlashIdTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_ID_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.report = (cls.root/'docs/match/081418C0.md').read_text()
        cls.body = bytes.fromhex(next(line.split('`')[1] for line in cls.report.splitlines() if line.startswith('* compiled : ')))
        cls.mapping = evidence.mapping_snapshot(cls.root)

    def test_original_elf_extent_and_receipt(self):
        self.assertEqual((len(self.body),self.body),(154,self.rom[0x1418C0:0x14195A]))
        self.assertTrue(evidence.report_matches(self.report,self.root,flash.OWNER))
        self.assertFalse(evidence.report_matches(self.report,self.root,flash.IDENTIFY))
        for a,b in (('"writes_per_loop":20001','"writes_per_loop":20000'),('AA/55/F0/F0','AA/55/F0'),
                    ('"reader_from_entry_sp":-79','"reader_from_entry_sp":-75')):
            self.assertIn(a,self.report)
            self.assertFalse(evidence.report_matches(self.report.replace(a,b),self.root,flash.OWNER))
        tool = units.resolve(flash.erase.TOOL)
        args = SimpleNamespace(cc=tool['cc'],flags=tool['flags'],cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
                               objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(tool['cc'],root=self.root,timeout=90)
        with runner.workspace() as work:
            _,_,original = match.compile_object(runner,work,args,self.root,flash.OWNER,flash.SOURCE)
        match.allocated_text_only(original)
        text,relocs,offset,thumb,size = units.signature(original,flash.OWNER)
        self.assertEqual((original['type'],len(text),offset,thumb,size,original['text'][size:]),(1,156,0,1,154,b'\xc0\x46'))
        self.assertEqual(relocs,((6,10,'func_08141AB0'),(66,10,'_call_via_r5'),(78,10,'_call_via_r5')))
        unit = units.containing(units.load(self.root),flash.OWNER)
        self.assertIn(flash.SCHEMA,units.schemas(unit,flash.OWNER,None))
        self.assertNotIn(flash.SCHEMA,units.schemas(unit,flash.OWNER,{'other':1}))
        self.assertNotIn(flash.SCHEMA,units.schemas(unit,flash.erase.OWNER,None))
        with self.assertRaises(ValueError):
            flash.native_proof(self.body,self.rom,self.mapping,(self.root/'symbols/functions.txt').read_bytes(),
                evidence.data_snapshot(self.root),{**flash.CALLS,flash.OWNER+78:0x08142254},{},dict(unit=unit,tool=tool),None)

    def test_mutations_refuse_source_bus_delays_and_thunk(self):
        path = self.root/flash.SOURCE
        text = path.read_text()
        closure = plausible.include_closure(self.root,path)
        self.assertEqual(len(flash.qualifier_offsets(text,self.root,self.root,closure)),8)
        for old,new in (('volatile u16 delay','u16 delay'),('volatile u8','volatile u16'),('20000','19999'),
                ('0x0E000001','0x0E000002'),('0x0E002AAA','0x0E005555'),('readBuffer + 1','readBuffer + 3'),
                ('0xF0','0xFF'),('return id','return id >> 8')):
            self.assertIn(old,text)
            self.assertFalse(flash.qualifier_offsets(text.replace(old,new,1),self.root,self.root,closure))
        for site in (0x1418dc,0x141928,0x141948,0x141ab6,0x141dac,0x142258):
            rom = bytearray(self.rom)
            rom[site] ^= 1
            with self.assertRaises(ValueError):
                flash.provider(rom)
        # Run the per-operand/effect checks without relying on the original digest.
        for addr,half in ((0x081418CC,'0335'),(0x081418DC,'0870'),(0x081418F6,'0238'),
                (0x081418F8,'0870'),(0x08141908,'040e'),(0x08141928,'0878'),(0x08141940,'214e')):
            data = bytearray(self.body)
            index = addr-flash.OWNER
            self.assertNotEqual(data[index:index+2],bytes.fromhex(half))
            data[index:index+2] = bytes.fromhex(half)
            with self.subTest(site=hex(addr)),self.assertRaises(ValueError):
                flash.effects(flash.erase.closure(bytes(data),flash.OWNER,self.mapping,count=58))

    def test_real_ports_local_delay_and_stripped_controls(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        helper = hardware.NativeTests()
        helper.rom = self.rom
        controls = flash.controls(self.root)
        full = [(0x5555,0xaa),(0x2aaa,0x55),(0x5555,0x90),(0x5555,0xaa),(0x2aaa,0x55),
                (0x5555,0xf0),(0x5555,0xf0)]
        stripped = [full[i] for i in (1,2,4,5)]
        image = bytes(range(256))*256
        for kind,body in (('retail',self.rom[0x1418C0:0x14195A]),('qualified',self.body),*controls.items()):
            with self.subTest(build=kind):
                cpu,chip,writes,reads = helper.machine(self.rom[0x141FC8:0x142000],0x1b32)
                chip.storage[:] = image
                # Use different device/maker bytes from the bytes in backing storage.
                chip.ident = 0x80fe
                cpu.mem_write(flash.OWNER,body)
                full_ports = kind in ('retail','qualified','ports')
                local_delay = kind in ('retail','qualified','counter')
                sp = cpu.reg_read(arm.UC_ARM_REG_SP)
                local = sp-(80 if local_delay else 76)
                delay = local+64
                cpu.mem_write(local,b'\xcc'*64)
                cpu.mem_write(0x04000204,b'\x57\x43')
                regs = {n:0xabc40000+n for n in range(arm.UC_ARM_REG_R4,arm.UC_ARM_REG_R11+1)}
                for n,v in regs.items():
                    cpu.reg_write(n,v)
                initialized,read_delay,written,fetches = [],[],[],[]
                def pub(uc,access,addr,size,v,data):
                    initialized.append((uc.reg_read(arm.UC_ARM_REG_PC),size,v,bytes(uc.mem_read(local,4))))
                def access(uc,access,addr,size,v,target):
                    self.assertEqual((addr,size),(delay,2))
                    if target is read_delay:
                        v = int.from_bytes(uc.mem_read(addr,size),'little')
                    target.append(v)
                def fetch(uc,pc,size,data):
                    if pc == local:
                        fetches.append((uc.reg_read(arm.UC_ARM_REG_R0),uc.reg_read(arm.UC_ARM_REG_R5),
                                       len(written),len(read_delay),bytes(uc.mem_read(local,4))))
                cpu.hook_add(UC_HOOK_MEM_WRITE,pub,begin=0x0200F364,end=0x0200F367)
                cpu.hook_add(UC_HOOK_CODE,fetch,begin=local,end=local+3)
                if local_delay:
                    cpu.hook_add(UC_HOOK_MEM_READ,access,read_delay,delay,delay+1)
                    cpu.hook_add(UC_HOOK_MEM_WRITE,access,written,delay,delay+1)
                else:
                    # The save slots start at local+64 in the register-countdown controls.
                    # Hook only owner halfword accesses and exclude prologue/epilogue word saves.
                    def nonlocal_access(uc,kind,addr,size,v,target):
                        if size == 2:
                            target.append(v)
                    cpu.hook_add(UC_HOOK_MEM_READ,nonlocal_access,read_delay,delay,delay+1)
                    cpu.hook_add(UC_HOOK_MEM_WRITE,nonlocal_access,written,delay,delay+1)
                cpu.ctl_flush_tb()
                self.assertEqual(helper.invoke(cpu,flash.OWNER,limit=400000),chip.ident if full_ports else 0x0100)
                self.assertEqual((writes,reads),(full if full_ports else stripped,[1,0]))
                self.assertEqual(initialized,[(0x08141AB8,4,local|1,b'\xcc'*4)])
                before = (20001,40001) if local_delay else (0,0)
                self.assertEqual(fetches,[(hardware.BUS+x,local|1,*before,self.rom[0x141aac:0x141ab0]) for x in (1,0)])
                stores = list(range(20000,-1,-1))
                read_values = [v for v in range(20000,0,-1) for _ in range(2)]+[0]
                self.assertEqual(written,stores*2 if local_delay else [])
                self.assertEqual(read_delay,read_values*2 if local_delay else [])
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),sp)
                self.assertEqual({n:cpu.reg_read(n) for n in regs},regs)
                self.assertEqual(cpu.mem_read(0x0200F364,4),struct.pack('<I',local|1))
                self.assertEqual(cpu.mem_read(0x04000204,2),b'\x57\x43')
                self.assertFalse(chip.id_mode)
                self.assertEqual(chip.storage,image)

    def test_identify_caller_reads_device_and_maker_and_installs_descriptor(self):
        from unicorn import UC_HOOK_CODE
        from unicorn import arm_const as arm
        helper = hardware.NativeTests()
        helper.rom = self.rom
        for ident,setup in zip((0xd4bf,0x1b32,0x1cc2,0x6bad),flash.bank.SETUPS):
            cpu,chip,writes,reads = helper.machine(self.rom[0x141FC8:0x142000],ident)
            cpu.mem_write(flash.OWNER,self.body)
            result = []
            cpu.hook_add(UC_HOOK_CODE,lambda uc,*args:result.append(uc.reg_read(arm.UC_ARM_REG_R0)),
                         begin=0x08141DB0,end=0x08141DB0)
            cpu.ctl_flush_tb()
            self.assertEqual(helper.invoke(cpu,flash.IDENTIFY,limit=400000),int(ident==0x6bad))
            self.assertEqual(result,[ident])
            self.assertEqual(reads,[1,0])
            self.assertEqual(struct.unpack('<I',cpu.mem_read(0x0200F370,4))[0],setup+20)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),0x03007000)


if __name__ == '__main__':
    unittest.main()
