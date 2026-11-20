from os import environ
from pathlib import Path
from struct import pack, unpack
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import map_record_loader as record
from rompath import rom_path


@unittest.skipUnless(environ.get('FFTA_RECORD_LOADER_ROOT'), 'requires original FFTA USA ROM and record loader')
class NativeRecordLoader(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(environ['FFTA_RECORD_LOADER_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()

    def setUp(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR
        from unicorn.arm_const import (UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1,
                                      UC_ARM_REG_R2, UC_ARM_REG_R3, UC_ARM_REG_SP)
        self.cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.args = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        self.pc, self.lr, self.sp = UC_ARM_REG_PC, UC_ARM_REG_LR, UC_ARM_REG_SP
        self.stack = 0x03007D00
        self.cpu.mem_map(0x08000000, 0x1000000)
        self.cpu.mem_write(0x08000000, self.rom)
        for start, size in ((0x02000000,0x40000), (0x03000000,0x8000), (0x04000000,0x1000),
                            (0x05000000,0x1000), (0x06000000,0x18000)):
            self.cpu.mem_map(start, size)
        # Original boot relocation of the memory-clear callback at 03005E79.
        self.cpu.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
        self.fills = []

        def modeled_swi(cpu, number, _):
            self.assertEqual((number, cpu.reg_read(self.pc)), (2, record.bios.ADDRESS+2))
            src, dest, control = (cpu.reg_read(reg) for reg in self.args[:3])
            self.assertEqual(control & 0xFF000000, 1 << 24)
            self.assertEqual((src | dest) & 1, 0)
            value = bytes(cpu.mem_read(src, 2))
            count = control & 0x1FFFFF
            site = (cpu.reg_read(self.lr)&~1)-4
            self.fills.append((site, src, dest, control, value))
            if count:
                cpu.mem_write(dest, value*count)
            # Exercise an admissible retained source in R0 across the modeled
            # SWI. Nobody may inspect/use this pointer after its lifetime ends.
        self.cpu.hook_add(UC_HOOK_INTR, modeled_swi)

    def call(self, start, *args):
        cpu = self.cpu
        for reg, arg in zip(self.args, args):
            cpu.reg_write(reg, arg)
        cpu.reg_write(self.sp, self.stack)
        cpu.reg_write(self.lr, 0x03007001)
        cpu.emu_start(start|1, 0x03007000, count=150000)
        self.assertEqual((cpu.reg_read(self.pc), cpu.reg_read(self.sp)), (0x03007000, self.stack))

    def test_real_scene_registration_and_both_callback_continuations(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R4
        cpu = self.cpu
        table, words, flags = 0x03002710, 0x03002820, 0x03000E40
        self.call(0x08006A7C, table, words, flags, 9)
        # Run the real case-0xA registration, ending after the store of phase 0xB.
        cpu.reg_write(self.sp, self.stack)
        cpu.emu_start(0x08024299, 0x080245CE, count=64)
        self.assertEqual(cpu.reg_read(self.pc), 0x080245CE)
        self.assertEqual(bytes(cpu.mem_read(words+12,4)), pack('<I',record.OWNER|1))
        self.assertEqual(bytes(cpu.mem_read(flags+3,1)), b'\x00')
        cpu.mem_write(0x02007F10,pack('<H',255))
        values = (0x06000000,0x06007000,0x06006000)
        cpu.mem_write(0x02007F50,pack('<III',*values))

        for mode, kill in ((0,0x08006A20),(4,0x080C95AE)):
            with self.subTest(mode=mode):
                cpu.mem_write(table+5,bytes([mode]))
                cpu.mem_write(flags+3,b'\x03')
                cpu.reg_write(self.sp,self.stack)
                traced = {}

                def trace(uc, pc, size, _):
                    if pc == record.OWNER:
                        traced['entry'] = uc.reg_read(self.sp)
                    if pc == record.RETURN:
                        traced['stale'] = uc.reg_read(self.args[2])
                        self.assertEqual(uc.reg_read(self.sp),traced['entry'])
                        self.assertEqual(traced['stale'],traced['entry']-52)
                        self.assertEqual(unpack('<III',uc.mem_read(traced['stale']-8,12)), values)
                    if 'stale' in traced and pc == kill:
                        self.assertEqual(uc.reg_read(self.args[2]),traced['stale'])
                        if mode == 0:
                            self.assertEqual(uc.reg_read(UC_ARM_REG_R4),4)
                        traced['kill'] = pc
                    if 'kill' in traced and pc == kill+2:
                        traced['after'] = uc.reg_read(self.args[2])
                        uc.emu_stop()

                hook = cpu.hook_add(UC_HOOK_CODE,trace)
                cpu.emu_start(0x08023FA5,0x03007000,count=3000)
                cpu.hook_del(hook)
                self.assertEqual(traced['after'], 0x2030 if mode else 0)
                self.assertEqual(bytes(cpu.mem_read(flags+3,1)),b'\x04')

    def test_phase_initialization_and_exact_cpuset_outputs(self):
        cpu = self.cpu
        state, flags = 0x02007F40, 0x03000E43
        cpu.mem_write(state+0x1c,b'\xa5\xa5')
        self.call(record.OWNER,3,flags)
        self.assertEqual(bytes(cpu.mem_read(state+0x1c,2)),b'\x00\x08')
        self.assertEqual(bytes(cpu.mem_read(flags,1)),b'\x01')
        cpu.mem_write(0x02007F10,pack('<H',255))
        # All possible byte counts, including zero. Reinitialize the real
        # request queue because each independent case starts in state 4.
        for count in range(256):
            dest, extent = 0x03003860, 32*count
            cpu.mem_write(state+0x1d,bytes([count]))
            cpu.mem_write(0x03002BCC,bytes(4))
            cpu.mem_write(dest-1,b'\xa5'*(extent+2))
            cpu.mem_write(flags,b'\x04')
            self.fills.clear()
            self.call(record.OWNER,3,flags)
            self.assertEqual(self.fills,[(record.FILLS[0],self.stack-90,dest,0x01000000|(count<<4),bytes(2))])
            self.assertEqual(bytes(cpu.mem_read(dest-1,extent+2)),b'\xa5'+bytes(extent)+b'\xa5')
            self.assertEqual(bytes(cpu.mem_read(flags,1)),b'\x05')
        cpu.mem_write(flags,b'\x06')
        cpu.mem_write(state+0x1e,b'\x34\x12')
        cpu.mem_write(0x02007CAF,b'\xa5'*514)
        self.fills.clear()
        self.call(record.OWNER,3,flags)
        self.assertEqual([f[2:] for f in self.fills],[
            (0x020091A0,0x01001000,b'\x34\x12'), (0x0200B1A0,0x01001000,b'\x34\x12'),
            (0x0200D1A0,0x01000800,bytes(2)), (0x0200E1A0,0x01000800,bytes(2)),
            (0x02007CB0,0x01000100,bytes(2))])
        self.assertEqual(self.fills[-1][:2],(record.FILLS[1],self.stack-90))
        self.assertEqual(bytes(cpu.mem_read(0x02007CAF,514)),b'\xa5'+bytes(512)+b'\xa5')
        self.assertEqual(bytes(cpu.mem_read(0x02007F14,4)),pack('<I',0x02007CB0))
        self.assertEqual(bytes(cpu.mem_read(flags,1)),b'\x07')

    def test_only_one_root_alias_and_native_provider(self):
        from match_evidence import report_matches
        report = (self.root/'docs/match/0801A518.md').read_text()
        self.assertTrue(report_matches(report,self.root,record.OWNER))
        row = f'"return_r2":[{record.RETURN},-52]'
        self.assertEqual(report.count(row), 1)
        self.assertFalse(report_matches(report.replace(row,row.replace('-52','-48')),self.root,record.OWNER))
        from types import SimpleNamespace
        from match import ARM_REG_R0 as r0
        body = self.rom[record.OWNER-0x08000000:record.END-0x08000000]
        proof = record.MapRecordProof.__new__(record.MapRecordProof)
        proof.fill = SimpleNamespace(data=body)
        proof.active = []
        aliases = {record.R2: -52}
        for owner, site, regs in (
            (record.OWNER,record.RETURN-2,aliases),
            (record.OWNER+4,record.RETURN,aliases),
            (record.OWNER,record.RETURN,{record.R2:-48}),
            (record.OWNER,record.RETURN,{r0:-52}),
            (record.OWNER,record.RETURN,{r0:-52,record.R2:-52}),
        ):
            self.assertEqual(proof.project(body,owner,site,regs),regs)
        self.assertEqual(proof.project(body,record.OWNER,record.RETURN,aliases),{})
        proof.active = [record.OWNER]
        self.assertEqual(proof.project(body,record.OWNER,record.RETURN,aliases),aliases)
        altered = bytearray(self.rom)
        altered[0xC95AE:0xC95B0] = b'\x12\x68'   # an incoming R2 dereference
        with self.assertRaises(ValueError):
            record.scene_and_outputs(bytes(altered))


if __name__ == '__main__':
    unittest.main()
