import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import scanline_wave as wave


@unittest.skipUnless(os.getenv('FFTA_SCANLINE_WAVE_ROOT'), 'requires USA ROM and native agbcc with the reviewed game source')
class NativeWave(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_SCANLINE_WAVE_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.qualified, cls.stripped = wave.compile_bodies(cls.root, cls.rom)
        cls.sine = struct.unpack_from('<256h', cls.rom, 0x149568)

    def cpu(self, body):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(wave.BASE, 0x400000)
        uc.mem_write(wave.BASE, self.rom[:0x400000])
        uc.mem_write(wave.OWNER, body)
        for start, size in ((0x02000000, 0x20000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
            uc.mem_map(start, size)
        return uc

    def call(self, uc, address, *args, count=300000):
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_SP
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3
        for reg, arg in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), args):
            uc.reg_write(reg, arg)
        sp, stop = 0x03007F00, 0x03007000
        uc.reg_write(UC_ARM_REG_SP, sp)
        for i, arg in enumerate(args[4:]):
            uc.mem_write(sp+4*i, struct.pack('<I', arg))
        uc.reg_write(UC_ARM_REG_LR, stop | 1)
        uc.emu_start(address | 1, stop, count=count)
        return uc.reg_read(UC_ARM_REG_PC) == stop

    def model(self, base, first, last, phase, amp, frame_step, row_step):
        phase = (phase + frame_step) & 255
        values = []
        for row in range(max(160, first, last+1)):
            offset = self.sine[(phase + row*row_step) & 255] * amp >> 8 if first <= row <= last else 0
            values.append((base+offset) & 0xFFFF)
        return phase, values

    def test_model_and_same_byte_accesses(self):
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ
        state, bank = 0x02001000, 0x02004000
        for body in (self.qualified, self.stripped):
            for first,last,stride,lane,amp in ((0,159,2,0,250),(159,159,4,2,71),(160,159,8,6,200),
                    (0,160,4,0,127),(254,254,2,0,0),(0,254,8,6,255),(10,4,4,2,32)):
                with self.subTest(first=first,last=last,stride=stride,lane=lane,amp=amp,qual=body==self.qualified):
                    uc = self.cpu(body)
                    args = (-32750,first,last,253,amp,7,193)
                    uc.mem_write(state, struct.pack('<h6B', *args))
                    phase, samples = self.model(*args)
                    expected = bytearray([0xA5])*(len(samples)*stride+16)
                    uc.mem_write(bank, bytes(expected))
                    accesses = []
                    uc.hook_add(UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
                                lambda u,kind,a,w,v,d: accesses.append((a-bank, w, kind==UC_MEM_READ)),
                                begin=bank,end=bank+len(expected)-1)
                    self.assertTrue(self.call(uc, wave.OWNER,state,bank+lane,stride))
                    sequence = []
                    for i, value in enumerate(samples):
                        pos = lane+stride*i
                        struct.pack_into('<H', expected, pos, value)
                        for byte in (pos,pos+1):
                            if body == self.qualified:
                                sequence.append((byte,1,True))
                            sequence.append((byte,1,False))
                    self.assertEqual(bytes(uc.mem_read(bank,len(expected))), expected)
                    self.assertEqual(uc.mem_read(state+4,1)[0],phase)
                    self.assertEqual(accesses, sequence)

    def test_last_row_wrap_and_effect_alias_counterexamples(self):
        from unicorn import UC_HOOK_MEM_WRITE
        state, bank = 0x02001000, 0x02004000
        uc = self.cpu(self.qualified)
        uc.mem_write(state, struct.pack('<h6B',100,0,255,0,0,0,0))
        writes = []
        uc.hook_add(UC_HOOK_MEM_WRITE, lambda u,k,a,w,v,d: writes.append(a), begin=bank,end=bank+0x1FFF)
        self.assertFalse(self.call(uc,wave.OWNER,state,bank,2,count=11000))
        self.assertGreater(max(writes),bank+511)
        # The first sample aliases the descriptor's accumulated phase and amplitude.
        uc = self.cpu(self.qualified)
        values = (0x1234,0,3,6,0,0,0)
        uc.mem_write(state,struct.pack('<h6B',*values))
        self.assertTrue(self.call(uc,wave.OWNER,state,state+4,2))
        self.assertNotEqual(uc.mem_read(state+4,1)[0], self.model(*values)[0])

    def test_altered_store_width_and_lane_on_native_cpu(self):
        from unicorn import UC_HOOK_MEM_WRITE
        state, bank = 0x02001000, 0x02004000
        args = (0x1234,1,1,7,0,1,1)
        _, values = self.model(*args)
        original = struct.pack('<160H', *values)
        for instruction, first_store in ((0x8021,(0,2)), (0x7061,(1,1))):
            altered = bytearray(self.qualified)
            struct.pack_into('<H', altered, 0x40, instruction)
            uc = self.cpu(bytes(altered))
            uc.mem_write(state, struct.pack('<h6B', *args))
            uc.mem_write(bank, bytes([0xA5])*320)
            writes = []
            uc.hook_add(UC_HOOK_MEM_WRITE, lambda u,k,a,w,v,d: writes.append((a-bank,w)),
                        begin=bank, end=bank+319)
            self.assertTrue(self.call(uc,wave.OWNER,state,bank,2))
            self.assertEqual(writes[0],first_store)
            self.assertNotEqual(writes[:2],[(0,1),(1,1)])
            if first_store[0] == 1:
                self.assertNotEqual(bytes(uc.mem_read(bank,320)),original)

    def test_original_constructor_wrappers_bank_and_dma(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_PC, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
        obj, destination = 0x02010000, 0x04000010
        for kind,stride in enumerate((2,4,8)):
            with self.subTest(kind=kind):
                uc = self.cpu(self.qualified)
                uc.mem_write(0x03005E78, self.rom[0xA38A2C:0xA38ADC])
                uc.mem_write(0x02009158,b'\xff'*8)
                allocations=[]
                def allocate(u, address, size, data):
                    allocations.append(u.reg_read(UC_ARM_REG_R1))
                    u.mem_write(obj, b'\xa5'*allocations[-1])
                    u.reg_write(UC_ARM_REG_R0,obj)
                    u.reg_write(UC_ARM_REG_PC,u.reg_read(UC_ARM_REG_LR))
                def cpuset(u, irq, data):
                    self.assertEqual(u.mem_read(u.reg_read(UC_ARM_REG_PC)-2,2),b'\x0b\xdf')
                    src,dst,n = [u.reg_read(reg) for reg in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2)]
                    self.assertEqual(n,stride//2)
                    u.mem_write(dst, bytes(u.mem_read(src,n*2)))
                uc.hook_add(UC_HOOK_CODE,allocate,begin=0x08007138,end=0x08007138)
                uc.hook_add(UC_HOOK_INTR,cpuset)
                self.assertTrue(self.call(uc,0x0800CC8C,kind,7,39,53,0x4567,243,destination))
                word = lambda at: int.from_bytes(uc.mem_read(at,4),'little')
                self.assertEqual(word(0x02009148),obj)
                self.assertEqual(word(obj), (0x0800DDB1,0x0800DDBD,0x0800DDDD)[kind])
                self.assertEqual(word(obj+4),destination)
                lanes=stride//2
                bank_size=(161*stride+3)&~3
                self.assertEqual(allocations,[32+28*lanes+2*bank_size])
                payload=word(obj+20)
                self.assertEqual(payload,obj+32)
                buffers=(word(obj+24),word(obj+28))
                self.assertEqual(buffers,(payload+28*lanes,payload+28*lanes+bank_size))
                for lane in range(lanes):
                    self.assertEqual(bytes(uc.mem_read(payload+lane*28,8)),struct.pack('<h6B',0x4567,0,159,243,53,7,39))
                    uc.mem_write(payload+lane*28+4,bytes([(243+lane)&255]))
                for frame,bank in enumerate(reversed(buffers)):
                    self.assertTrue(self.call(uc,0x0800C64C,obj))
                    self.assertTrue(self.call(uc,0x0800C4B4))
                    rows = bytearray(161*stride)
                    for lane in range(lanes):
                        phase,samples = self.model(0x4567,0,159,(243+lane+7*frame)&255,53,7,39)
                        self.assertEqual(uc.mem_read(payload+lane*28+4,1)[0],phase)
                        for i,v in enumerate(samples+[samples[0]]):
                            struct.pack_into('<H',rows,i*stride+lane*2,v)
                    self.assertEqual(uc.mem_read(bank,len(rows)),rows)
                    self.assertTrue(self.call(uc,0x080008E0))
                    self.assertEqual(struct.unpack('<III',uc.mem_read(0x040000B0,12)),
                                     (bank+stride,destination,0xA2600000|lanes))

    def test_original_elf_relocation_and_destination_encoding(self):
        import argparse
        from copy import deepcopy
        import match
        args = argparse.Namespace(cpp=match.DEFAULT_CPP, cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS,
                                  assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY)
        runner = match.Runner(args.cc, root=str(self.root), timeout=match.SIGNED_REPLAY_TIMEOUT)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, args, str(self.root), wave.OWNER, wave.SOURCE)
        wave.object_contract(image, wave.QUALIFIED)
        rel = image['relocations'][0]
        site, info = struct.unpack('<II', image['section_data'][rel])
        for key, value in (('name','func_08007A60'),('bind',2),('type',2),('section',1),('value',1),('size',4)):
            wrong=deepcopy(image)
            wrong['symbol_tables'][image['sections'][rel][6]][info>>8][key]=value
            with self.assertRaises(ValueError):
                wave.object_contract(wrong, wave.QUALIFIED)
        for new_site,new_info in ((site+2,info),(site,info^1)):
            wrong=deepcopy(image)
            wrong['section_data'][rel]=struct.pack('<II',new_site,new_info)
            with self.assertRaises(ValueError):
                wave.object_contract(wrong,wave.QUALIFIED)
        # An alternate byte base R5, or a halfword store, cannot represent the audited sample.
        for replacement in (0x7029,0x8021):
            wrong=bytearray(self.qualified)
            struct.pack_into('<H',wrong,0x40,replacement)
            with self.assertRaises(ValueError):
                wave.check_body(bytes(wrong),wave.QUALIFIED)

    def test_sources_objects_providers_and_replay(self):
        from match_evidence import report_matches
        src=(self.root/wave.SOURCE).read_text()
        header=(self.root/wave.HEADER).read_bytes()
        self.assertIsNotNone(wave.source_offset(src,header))
        for before,after in (('volatile s16 value;', 'volatile u8 value;'),('packed','aligned(2)'),
                             ('(ScanlineValue *)cursor','(ScanlineValue *)(cursor + 1)'),
                             ('row <= effect->last_row','row < effect->last_row'),
                             ('cursor + stride','cursor + 2'),('offset += base','offset -= base')):
            self.assertIn(before,src)
            self.assertIsNone(wave.source_offset(src.replace(before,after),header))
        self.assertIsNone(wave.source_offset(src,header.replace(b'#endif',b'#define cursor hidden\n#endif')))
        for i in (0xC794,0xCCA0,0xCD0C,0xDDB4,0xDDD2,0xDE0A,0x1497F0,0x149808,0xC4FE,
                  0xC580,0x8E0,0x1443FC,0xA38A2C,0x36D470,0x149568):
            rom=bytearray(self.rom);rom[i]^=1
            if i==0xC794:
                with self.assertRaises(ValueError):wave.check_body(bytes(rom[0xC720:0xC802]),wave.QUALIFIED)
            else:
                with self.assertRaises(ValueError):wave.provider(rom)
        wave.provider(self.rom)
        from rompath import rom_path
        self.assertEqual(Path(rom_path(self.root)).read_bytes()[0xC720:0xC802], self.qualified)
        report=(self.root/'docs/match/0800C720.md').read_text()
        self.assertTrue(report_matches(report,str(self.root),wave.OWNER))
        self.assertFalse(report_matches(report.replace('last < 255','last <= 255'),str(self.root),wave.OWNER))
        self.assertFalse(report_matches(report.replace(self.qualified.hex(),self.qualified.hex()+'0000').replace(
            '226 bytes','228 bytes').replace('226/226','228/228'),str(self.root),wave.OWNER))


if __name__ == '__main__':
    unittest.main()
