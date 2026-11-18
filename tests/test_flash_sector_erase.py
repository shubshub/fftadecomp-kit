"""Native evidence for the stack-installed FLASH512 sector reader and the retained pointer."""
from pathlib import Path
import os
import struct
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
import flash_sector_erase as erase
import match
import match_evidence as evidence
import plausible
import test_flash_program_byte as program_tests


class GraphTests(unittest.TestCase):
    def test_reinstall_must_dominate_including_loops(self):
        edges = {0:(1,2),1:(1,0),2:(3,),3:(4,),4:(3,5),5:()}
        self.assertFalse(erase.reaches(edges,0,5,{2}))
        edges[1] = (1,4)
        self.assertTrue(erase.reaches(edges,0,5,{2}))


@unittest.skipUnless(os.environ.get('FFTA_FLASH_ERASE_ROOT'),'needs the indexed original game and sector erase C')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_ERASE_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.original = cls.rom[erase.OWNER-erase.BASE:erase.END-erase.BASE]
        cls.stripped = erase.stripped_build(cls.root)
        cls.report = (cls.root/'docs/match/08141F2C.md').read_text()
        cls.linked = bytes.fromhex(next(l.split('`')[1] for l in cls.report.splitlines() if l.startswith('* compiled : ')))

    def test_complete_fresh_report_and_false_claims(self):
        self.assertEqual(len(self.linked),156)
        self.assertEqual(self.linked,self.original)
        self.assertTrue(evidence.report_matches(self.report,str(self.root),erase.OWNER))
        for a,b in [('expired reader pointer remains','reader pointer cleared'),('five flash qualifiers','two qualifiers'),
                    ('elf-symbol-thumb-flash-sector-reader-v1','elf-symbol-thumb-framed-data-v1'),
                    ('"local_bytes":64','"local_bytes":4'),('"excluded_ROM_credit":0','"excluded_ROM_credit":4')]:
            altered = self.report.replace(a,b)
            self.assertNotEqual(altered,self.report)
            self.assertFalse(evidence.report_matches(altered,str(self.root),erase.OWNER))
        self.assertFalse(evidence.report_matches(self.report,str(self.root),erase.INSTALL))

    def test_source_scope_and_cartridge_mutations(self):
        path = self.root/erase.SOURCE
        text = path.read_text()
        closure = plausible.include_closure(self.root,path)
        check = lambda body: erase.qualifier_offsets(body,self.root,self.root,closure)
        self.assertEqual(len(check(text)),5)
        for a,b in [('data_0200F368(2','data_0200F368(1'), ('0x80;','0xA0;'), ('32]','2]'),
                    ('sector >= 16','sector > 16'), ('sector.shift','sector.count'), ('*address = 0x30','*address = 0x10'),
                    ('readBuffer);','readBuffer+1);'), ('volatile u8','volatile u16')]:
            edited = text.replace(a,b)
            self.assertNotEqual(edited,text)
            self.assertFalse(check(edited))
        for site in (0x141f3a,0x141f60,0x141f72,0x141f76,0x141f84,0x141f96,0x141acc,0x141e58,
                     0x141e84,0x1420ac,0x142190,0x36cf14,*(p-erase.BASE+8 for p in erase.bank.SETUPS)):
            rom=bytearray(self.rom)
            rom[site]^=1
            with self.subTest(site=site),self.assertRaises(ValueError):
                erase.provider(rom)

    def test_symbolic_installer_and_reinstallation_mutations(self):
        graphs = {a:erase.closure(self.rom[a-erase.BASE:b-erase.BASE],a,self.mapping)
                  for a,(b,_) in erase.SPANS.items()}
        self.assertEqual(erase.reader_installer(self.rom,graphs[erase.INSTALL])['local_writes'],[[0,2],[2,2]])
        # Bypass the outer ROM identity deliberately; exercise the symbolic
        # loop itself with an extra count, a bad Thumb tag, and wrong copy stride.
        for site in (0x141ad4,0x141ab6,0x141adc,0x141ade):
            rom=bytearray(self.rom)
            rom[site]^=2 if site in (0x141adc,0x141ade) else 1
            graph=erase.closure(rom[0x141ab0:0x141aee],erase.INSTALL,self.mapping)
            with self.subTest(site=site),self.assertRaises(ValueError):
                erase.reader_installer(rom,graph)
        for caller,site,program_site in ((0x08142000,0x0814206e,0x081420f2),(0x08142160,0x08142182,0x081421e0)):
            ins,edges,calls,part=graphs[caller]
            # A new incoming path from the erase continuation to ProgramByte
            # would allow consumption before the parent installs its own reader.
            altered=dict(graphs)
            altered[caller]=ins,dict(edges),calls,part
            altered[caller][1][site+4]=(program_site,)
            with self.assertRaisesRegex(ValueError,'without replacing'):
                erase.reader_lifetime(self.rom,altered,graphs[erase.OWNER][3])
        proof=erase.LocalReaderFrame(self.rom,self.mapping)
        stack=[(False,False,True)]*16+[(False,True,False)]*4+[(True,True,False)]
        for bad,slots in (({match.ARM_REG_R0:-80},{}),({match.ARM_REG_R0:-84,match.ARM_REG_R1:-84},{}),
                          ({match.ARM_REG_R0:-84},{-4:-84})):
            with self.assertRaises(ValueError):
                proof.check_call(erase.INSTALL,bad,stack,slots,site=0x08141f76)

    def test_true_sector_program_unlock_and_reader_lifetime(self):
        from unicorn import UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_PC,UC_ARM_REG_SP,UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2
        helper=program_tests.NativeTests()
        helper.rom=self.rom
        bus=program_tests.BUS
        read_word=lambda cpu,addr:struct.unpack('<I',cpu.mem_read(addr,4))[0]
        for kind,body in (('retail',self.original),('linked',self.linked),('stripped',self.stripped)):
            for ident,ticks in ((0xd4bf,40),(0x1b32,500),(0x1cc2,2000),(0x6bad,40)):
                cpu,chip,writes,reads=helper.machine(self.rom[0x141fc8:0x142000],ident)
                cpu.mem_write(erase.OWNER,body)
                entry_sp=cpu.reg_read(UC_ARM_REG_SP)
                local=entry_sp-(80 if kind=='stripped' else 84)
                published,fetched,waits,waitcnt=[],[],[],[]
                def publication(uc,access,addr,size,value,data):
                    published.append((uc.reg_read(UC_ARM_REG_PC),size,value,bytes(uc.mem_read(local,4))))
                def entering_wait(uc,addr,size,data):
                    waits.append((uc.reg_read(UC_ARM_REG_R0),uc.reg_read(UC_ARM_REG_R1),
                                  uc.reg_read(UC_ARM_REG_R2),uc.reg_read(UC_ARM_REG_SP),read_word(uc,0x0200f364)))
                def fetch(uc,addr,size,data):
                    fetched.append(addr)
                def wait_control(uc,access,addr,size,value,data):
                    waitcnt.append((size,value))
                cpu.hook_add(UC_HOOK_MEM_WRITE,wait_control,begin=0x04000204,end=0x04000205)
                cpu.hook_add(UC_HOOK_MEM_WRITE,publication,begin=0x0200f364,end=0x0200f367)
                cpu.hook_add(UC_HOOK_CODE,entering_wait,begin=erase.WAIT,end=erase.WAIT)
                cpu.hook_add(UC_HOOK_CODE,fetch,begin=local,end=local+3)
                sectors = (0,15,16,65535,0x1000f) if kind == 'stripped' else (*range(16),16,65535,0x1000f)
                for raw in sectors:
                    with self.subTest(kind=kind,ident=ident,raw=raw):
                        for log in (writes,reads,published,fetched,waits,waitcnt):
                            log.clear()
                        cpu.mem_write(0x04000204,struct.pack('<H',0x431a))
                        sector=raw&65535
                        dest=sector*4096
                        prior=read_word(cpu,0x0200f364)
                        initial=bytes([0xcc])*65536
                        chip.storage[:]=initial
                        cpu.mem_write(local,b'WAIT')  # observe publication preceding code writes
                        if sector<16 and kind=='stripped':
                            helper.invoke(cpu,erase.OWNER,(raw,),0x08141e8c)
                            held=cpu.context_save()
                            handler=read_word(cpu,helper.handler_slot)
                            self.assertEqual(struct.unpack('<H',cpu.mem_read(0x03005e42,2))[0],ticks)
                            for _ in range(ticks):
                                helper.invoke(cpu,handler)
                            self.assertEqual(cpu.mem_read(0x0200f360,1),bytes((1,)))
                            cpu.context_restore(held)
                            helper.run_to(cpu,0x08141e8c,helper.sentinel)
                        else:
                            helper.invoke(cpu,erase.OWNER,(raw,))
                        result=cpu.reg_read(UC_ARM_REG_R0)
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),entry_sp)
                        if sector>=16:
                            self.assertEqual(result,0x80ff)
                            self.assertFalse(writes or reads or published or fetched or waits or waitcnt)
                            self.assertEqual(read_word(cpu,0x0200f364),prior)
                            self.assertEqual(chip.storage,initial)
                            continue
                        configured={0xd4bf:1,0x1b32:0,0x1cc2:3,0x6bad:3}[ident]
                        self.assertEqual(waitcnt,[(2,0x4318|configured),(2,0x431b)])
                        self.assertEqual(published,[(0x08141ab8,4,local+1,b'WAIT')])
                        self.assertEqual(waits,[(2,bus+dest,255,local,local+1)])
                        self.assertEqual(read_word(cpu,0x0200f364),local+1)
                        expected=program_tests.PREFIX[:2]+[(0x5555,0x80)]+program_tests.PREFIX[:2]+[(dest,0x30)]
                        storage=bytearray(initial)
                        if kind=='stripped':
                            expected=expected[3:]+([(0x5555,0xf0)] if ident==0x1cc2 else [])
                            self.assertEqual(result,0xc002)
                            polls=2
                        else:
                            self.assertEqual(result,0)
                            storage[dest:dest+4096]=bytes([255])*4096
                            polls=1
                        self.assertEqual(chip.storage,storage)
                        self.assertEqual(writes,expected)
                        self.assertEqual(reads,[dest]*polls)
                        self.assertEqual(fetched,[local,local+2]*polls)


if __name__=='__main__':
    unittest.main()
