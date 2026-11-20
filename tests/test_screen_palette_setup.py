"""Run the native phase-one screen setup with real installed clear and GBA DMA/BIOS models."""
import os
from pathlib import Path
import struct
import sys
import unittest

ROOT = 0x08135B40
BASE = 0x08000000
PAL = 0x03003860
VRAM = 0x06000000
MMIO = 0x040000D4
SHADOW = 0x03000940
SP, DONE = 0x03007F00, 0x03007FF0
if os.getenv('FFTA_SCREEN_SETUP_KIT'):
    sys.path.insert(0, str(Path(os.environ['FFTA_SCREEN_SETUP_KIT'])/'tools'))
else:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))


@unittest.skipUnless(os.environ.get('FFTA_SCREEN_SETUP_ROOT'), 'requires USA ROM and recovered screen setup')
class ScreenSetup(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_SCREEN_SETUP_ROOT'])
        cls.rom = Path(rom_path(cls.root)).read_bytes()

    def machine(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR, UC_HOOK_CODE
        from unicorn import UC_HOOK_MEM_WRITE, UC_HOOK_MEM_READ, UC_MEM_WRITE
        import unicorn.arm_const as reg
        cpu = Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        for addr, size in ((BASE,len(self.rom)),(0x02000000,0x40000),(0x03000000,0x8000),
                           (0x04000000,0x1000),(VRAM,0x19000)):
            cpu.mem_map(addr,size)
        cpu.mem_write(BASE,self.rom)
        state = dict(active=False, transfers=[], registers=[], bios=[], clears=[], stores=[], calls=[])
        def get(address, fmt='I'):
            return struct.unpack('<'+fmt,cpu.mem_read(address,struct.calcsize('<'+fmt)))[0]
        def call(pc,*args,end=DONE):
            for i,v in enumerate(args):
                cpu.reg_write(reg.UC_ARM_REG_R0+i,v)
            cpu.reg_write(reg.UC_ARM_REG_SP,SP)
            cpu.reg_write(reg.UC_ARM_REG_LR,DONE|1)
            cpu.emu_start(pc|1,end,count=1500000)
            self.assertEqual(cpu.reg_read(reg.UC_ARM_REG_PC),end)
            return cpu.reg_read(reg.UC_ARM_REG_R0)
        def bios(uc,no,ctx):
            pc=uc.reg_read(reg.UC_ARM_REG_PC)
            code=get(pc-2,'H')
            src,dest,ctl=[uc.reg_read(reg.UC_ARM_REG_R0+i) for i in range(3)]
            self.assertIn(code,(0xdf0b,0xdf0c))
            unit=4 if code==0xdf0c or ctl & (1<<26) else 2
            units=ctl&0x1fffff
            blob=bytes(uc.mem_read(src,unit if ctl&(1<<24) else unit*units))
            if ctl&(1<<24):
                blob*=units
            if state['active']:
                self.assertEqual((code,dest,ctl,src%4,len(blob)),(0xdf0c,VRAM,0x01006000,0,0x18000))
                self.assertEqual(blob,bytes(0x18000))
                state['bios'].append((pc-2,src,uc.reg_read(reg.UC_ARM_REG_SP)))
            uc.mem_write(dest,blob)
        cpu.hook_add(UC_HOOK_INTR,bios)
        def dma(uc,kind,addr,width,value,_):
            if not state['active']:
                return
            self.assertEqual(width,4)
            state['registers'].append((kind==UC_MEM_WRITE,addr-MMIO))
            if addr==MMIO+8 and kind==UC_MEM_WRITE:
                src,dst=get(MMIO),get(MMIO+4)
                self.assertEqual(value,0x81000100)
                self.assertEqual(src%2,0)
                self.assertIn(dst,(PAL,PAL+0x200))
                color=get(src,'H')
                state['transfers'].append((src,dst,color))
                uc.mem_write(dst,struct.pack('<H',color)*256)
        cpu.hook_add(UC_HOOK_MEM_WRITE|UC_HOOK_MEM_READ,dma,begin=MMIO,end=MMIO+11)
        def record_entry(uc,pc,size,_):
            if pc==ROOT:
                state['calls'].append(uc.reg_read(reg.UC_ARM_REG_LR)&~1)
            elif state['active']:
                state['clears'].append((uc.reg_read(reg.UC_ARM_REG_R0),uc.reg_read(reg.UC_ARM_REG_R1)))
        for pc in (ROOT,0x03005E78):
            cpu.hook_add(UC_HOOK_CODE,record_entry,begin=pc,end=pc)
        def native_clear(uc,kind,addr,width,val,_):
            if state['active'] and 0x03005E78 <= uc.reg_read(reg.UC_ARM_REG_PC) < 0x03005EA8:
                state['stores'].append((addr,width,val))
        cpu.hook_add(UC_HOOK_MEM_WRITE,native_clear,begin=VRAM,end=VRAM+0x18fff)
        call(0x08002768)
        self.assertEqual(bytes(cpu.mem_read(0x03005E78,176)),self.rom[0xA38A2C:0xA38ADC])
        return cpu,get,call,state

    def test_both_native_palette_paths_and_persisted_bg3_destinations(self):
        for mode, prior, bg3, color in ((0,0x0813FD78,VRAM+0x8000,0x7fff),
                                         (2,0x0813FEC8,VRAM+0x8800,0)):
            with self.subTest(mode=mode,prior=hex(prior)):
                u,get,call,s=self.machine()
                call(prior)
                self.assertEqual(get(0x030009A4),bg3)
                u.mem_write(PAL-2,bytes([0xed])*0x404)
                u.mem_write(VRAM,bytes([0xab])*0x18004)
                u.mem_write(0x0300284C,bytes([mode]))
                s['active']=True
                phase=0x02000300
                u.mem_write(phase,b'\x01')
                call(0x08136084,0,phase,end=0x08136148)
                self.assertEqual(s['calls'],[0x08136148])
                [(_,src,sp)]=s['bios']
                self.assertEqual(src,sp+4)
                self.assertEqual(s['transfers'],[(sp,PAL,color),(sp,PAL+512,color)])
                self.assertEqual(s['registers'],[(True,0),(True,4),(True,8),(False,8)]*2)
                self.assertEqual(bytes(u.mem_read(PAL-2,0x404)),b'\xed\xed'+struct.pack('<H',color)*512+b'\xed\xed')
                self.assertEqual(bytes(u.mem_read(VRAM,0x18004)),bytes(0x18000)+b'\xab'*4)
                for addr,tiles,dest in ((0x03000E60,VRAM,VRAM+0xE800),(0x03000E80,VRAM+0x8000,VRAM+0xF000),
                                        (0x030008B0,VRAM+0x8000,VRAM+0xF800)):
                    self.assertEqual(struct.unpack('<II2B2xII',u.mem_read(addr+4,20)),(0,0,32,32,tiles,dest))
                self.assertEqual(s['clears'],[(VRAM+0xE800,2048),(VRAM+0xF000,2048),(bg3,2048)])
                self.assertEqual(s['stores'],[(base+i,4,0) for base,n in s['clears'] for i in range(0,n,4)])
                self.assertEqual((get(SHADOW,'H'),get(SHADOW+2,'H'),get(SHADOW+4,'H'),get(SHADOW+6,'H')),
                                 (0x1040,0x3D83,0x3E0A,0x3F09))
                self.assertEqual(bytes(u.mem_read(SHADOW+10,16)),bytes(16))
                self.assertEqual(bytes(u.mem_read(SHADOW+74,5)),bytes([0x42,0x25,0x0b,0x0e,0x10]))
                self.assertEqual(bytes(u.mem_read(SHADOW+60,8)),bytes(8))
                self.assertEqual(bytes(u.mem_read(SHADOW+68,2)),bytes([0x3f,0]))

    def test_reset_bg3_third_clear_argument_is_zero(self):
        import unicorn.arm_const as reg
        u,get,call,s=self.machine()
        call(0x0800323C)
        self.assertEqual(get(0x030009A4),0)
        # Stop at the genuine thunk before an unmapped host BIOS write.
        s['active']=True
        call(ROOT,end=0x08135CA6)
        self.assertEqual((u.reg_read(reg.UC_ARM_REG_R0),u.reg_read(reg.UC_ARM_REG_R1),
                          u.reg_read(reg.UC_ARM_REG_R2)),(0,2048,0x03005E79))
        self.assertEqual(len(s['clears']),2)
