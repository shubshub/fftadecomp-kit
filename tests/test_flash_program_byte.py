"""Exercise the installed FLASH512_V130 byte programmer and its readback callback."""
from pathlib import Path
import os
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import flash_program_byte as flash
import match_evidence
import plausible

BUS = 0x0E000000
PREFIX = [(0x5555, 0xaa), (0x2aaa, 0x55), (0x5555, 0xa0)]


class FlashChip:
    """Immediate completion for the commands reached by the SDK sector paths."""
    def __init__(self, ident):
        self.ident = ident
        self.id_mode = False
        self.state = 0
        self.storage = bytearray([255])*65536

    def write(self, offset, value):
        step = self.state
        self.state = 0
        if step == 3:
            self.storage[offset] &= value
        elif value == 0xf0 and offset == 0x5555:
            self.id_mode = False
        elif step in (0, 4) and (offset, value) == PREFIX[0]:
            self.state = step+1
        elif step in (1, 5) and (offset, value) == PREFIX[1]:
            self.state = step+1
        elif step == 2 and offset == 0x5555:
            if value == 0xa0:
                self.state = 3
            elif value == 0x90:
                self.id_mode = True
            elif value == 0x80:
                self.state = 4
        elif step == 6 and (offset,value) == (0x5555,0x10):
            self.storage[:] = bytes([255])*len(self.storage)
        elif step == 6 and value == 0x30:
            start = offset & 0xf000
            self.storage[start:start+4096] = bytes([255])*4096

    def read(self, offset):
        if self.id_mode and offset < 2:
            return (self.ident >> (8*offset)) & 255
        return self.storage[offset]


class ProtocolTests(unittest.TestCase):
    def test_missing_swapped_or_misdirected_unlock_preserves_erased_byte(self):
        for prefix in (PREFIX[1:], PREFIX[:2], PREFIX[:1]+PREFIX[2:], PREFIX[1:2]+PREFIX[:1]+PREFIX[2:],
                       [(0x5554, 0xaa)]+PREFIX[1:], PREFIX[:2]+[(0x5555, 0xb0)]):
            chip = FlashChip(0xd4bf)
            for write in [*prefix, (0x735, 0xc4)]:
                chip.write(*write)
            self.assertEqual(chip.read(0x735), 255)
        chip = FlashChip(0xd4bf)
        for write in [*PREFIX, (0x735, 0xc4)]:
            chip.write(*write)
        self.assertEqual(chip.read(0x735), 0xc4)


@unittest.skipUnless(os.environ.get('FFTA_FLASH_PROGRAM_ROOT'), 'needs original game and ProgramByte C')
class NativeTests(unittest.TestCase):
    sentinel = 0x08141898
    source = 0x02008000
    reader = 0x03001000
    handler_slot = 0x02006000

    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_FLASH_PROGRAM_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(cls.root)).read_bytes()
        cls.qualified, cls.ordinary = flash.compile_bodies(cls.root)

    def test_native_report_and_control(self):
        self.assertEqual(self.qualified, self.rom[0x141fc8:0x142000])
        self.assertEqual([len(self.qualified), len(self.ordinary)], [56, 52])
        report = (self.root/'docs/match/08141FC8.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, str(self.root), flash.OWNER))
        for value in ('56/56', 'A0@0E005555', 'phase-1', flash.STRIPPED, 'elf-symbol-thumb-data-v1', 'agbcc-O1-v1'):
            self.assertFalse(match_evidence.report_matches(report.replace(value, 'altered'), str(self.root), flash.OWNER))

    def test_source_and_provider_mutations(self):
        path = self.root/flash.SOURCE
        text = path.read_text()
        closure = plausible.include_closure(self.root, path)
        def offsets(src, c=closure):
            return flash.qualifier_offsets(src, self.root, self.root, c)
        self.assertEqual(len(offsets(text)), 3)
        self.assertFalse(offsets(text, ({'src/0814189C.c', 'include/ffta.h'}, [])))
        for a, b in [('0xAA', '0xAB'), ('0xA0', '0xB0'), ('0x0E002AAA', '0x0E002AAB'), ('volatile u8', 'volatile u16'),
                     ('*destination = *source;', '*source = *destination;'), ('(1, destination', '(2, destination'),
                     ('destination, *source)', 'destination, *destination)'), ('extern u16', 'extern u32'),
                     ('u8 *address', 'u16 *address'), ('u8 *source', 'volatile u8 *source'),
                     ('#include', '#define destination d\n#include')]:
            altered = text.replace(a,b,1)
            self.assertNotEqual(altered, text)
            self.assertFalse(offsets(altered))
        with self.assertRaises(ValueError):
            flash.provider(self.rom[:0x200000])
        rom = bytearray(self.rom)
        for offset in (0x141fce, 0x141fdc, 0x141fe0, 0x141fe6, 0x141ff4, 0x141ffc,
                       0x141dfc, 0x141e6a, 0x141e98, 0x141ad8, 0x14195c, 0x142250, 0x142248, 0x36ce28, 0x36ce38,
                       0x1420f2, 0x1421e0, 0x36cf0e, *(p-flash.BASE+12 for p in flash.SETUPS)):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                rom[offset] ^= 1
                flash.provider(rom)
            rom[offset] ^= 1

    def run_to(self, cpu, start, end, limit=1000):
        from unicorn.arm_const import UC_ARM_REG_PC
        cpu.emu_start(start|1, end, count=limit)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_PC), end)

    def invoke(self, cpu, start, args=(), end=None, limit=1000):
        from unicorn.arm_const import UC_ARM_REG_LR, UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2
        for reg, arg in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2), args):
            cpu.reg_write(reg, arg)
        cpu.reg_write(UC_ARM_REG_LR, self.sentinel|1)
        if end is None:
            self.run_to(cpu, start, self.sentinel, limit)
        else:
            # The previous call may have cached a block spanning this temporary
            # stop address. Rebuild those translations for this invocation.
            cpu.ctl_flush_tb()
            self.run_to(cpu, start, end, limit)
        return cpu.reg_read(UC_ARM_REG_R0)

    def machine(self, body, ident):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_SP
        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for address, size in ((0x08141000,8192), (0x0836c000,8192), (0x02000000,262144),
                              (0x03000000,32768), (0x04000000,4096), (BUS,65536)):
            cpu.mem_map(address,size)
            if flash.BASE <= address < 0x09000000:
                cpu.mem_write(address,self.rom[address-flash.BASE:address-flash.BASE+size])
        cpu.mem_write(flash.OWNER, body)
        cpu.reg_write(UC_ARM_REG_SP,0x03007000)
        chip, writes, reads = FlashChip(ident), [], []
        def write(uc, kind, address, size, value, data):
            self.assertEqual(size, 1)
            writes.append((address-BUS, value))
            chip.write(address-BUS,value)
        def read(uc, kind, address, size, value, data):
            self.assertEqual(size,1)
            reads.append(address-BUS)
            uc.mem_write(address, bytes((chip.read(address-BUS),)))
        cpu.hook_add(UC_HOOK_MEM_WRITE, write, begin=BUS, end=BUS+65535)
        cpu.hook_add(UC_HOOK_MEM_READ, read, begin=BUS, end=BUS+65535)
        # IdentifyFlash calls the actual ID command, delays and stack-RAM reader.
        self.assertEqual(self.invoke(cpu, 0x08141d9c, limit=400000), int(ident == 0x6bad))
        self.assertEqual(reads, [1,0])
        self.assertFalse(chip.id_mode)
        self.assertEqual(struct.unpack('<I',cpu.mem_read(0x0200f368,4))[0], 0x08141e31)
        self.assertEqual(self.invoke(cpu,0x08141984,(1,self.handler_slot)),0)
        self.assertEqual(struct.unpack('<I',cpu.mem_read(self.handler_slot,4))[0],0x0814195d)
        self.invoke(cpu,0x08141ab0,(self.reader,))
        self.assertEqual(cpu.mem_read(self.reader,4),self.rom[0x141aac:0x141ab0])
        self.assertEqual(struct.unpack('<I',cpu.mem_read(0x0200f364,4))[0],self.reader|1)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),0x03007000)
        writes.clear()
        reads.clear()
        return cpu, chip, writes, reads

    def timer_expiry(self, cpu):
        from unicorn.arm_const import UC_ARM_REG_SP
        # Service ten real countdown-handler entries, preserving the interrupted
        # computation's registers. Only the timing of IRQ delivery is supplied here.
        interrupted = cpu.context_save()
        handler = struct.unpack('<I',cpu.mem_read(self.handler_slot,4))[0]
        self.assertEqual(struct.unpack('<H',cpu.mem_read(0x03005e42,2))[0],10)
        sp = cpu.reg_read(UC_ARM_REG_SP)
        for i in range(10):
            self.invoke(cpu,handler)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),sp)
            self.assertEqual(cpu.mem_read(0x0200f360,1),bytes((int(i == 9),)))
        cpu.context_restore(interrupted)

    def test_original_linked_and_stripped_readback_for_each_installed_callback(self):
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_SP
        for name, body in (('retail',self.rom[0x141fc8:0x142000]), ('compiled',self.qualified), ('stripped',self.ordinary)):
            for ident in (0xd4bf,0x1b32,0x1cc2,0x6bad):
                with self.subTest(name=name,ident=ident):
                    cpu,chip,writes,reads = self.machine(body,ident)
                    for offset,value in ((0,0), (65535,0xf0), (0x2aaa,0x55), (0x403,0xff), (0x5555,0xaa)):
                        writes.clear()
                        reads.clear()
                        cpu.mem_write(self.source,bytes((value,)))
                        args = (self.source,BUS+offset)
                        missed = name == 'stripped' and value != 255
                        if missed:
                            self.invoke(cpu,flash.OWNER,args,0x08141e8c)
                            self.timer_expiry(cpu)
                            self.run_to(cpu,0x08141e8c,self.sentinel)
                        else:
                            self.invoke(cpu,flash.OWNER,args)
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_R0),0xc001 if missed else 0)
                        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),0x03007000)
                        expected = (PREFIX[1:] if name == 'stripped' else PREFIX)+[(offset,value)]
                        if missed and ident == 0x1cc2:
                            expected.append((0x5555,0xf0))
                        self.assertEqual(writes,expected)
                        self.assertEqual(reads,[offset]*(2 if missed else 1))
                        self.assertEqual(chip.read(offset),255 if missed else value)
                        self.assertEqual(cpu.mem_read(0x04000104,4),bytes(4))

    def test_timeout_final_read_can_still_succeed(self):
        from unicorn.arm_const import UC_ARM_REG_R0
        cpu, chip, writes, reads = self.machine(self.qualified,0x1cc2)
        destination, value = 0x8321, 0x72
        cpu.mem_write(self.source,bytes((value,)))
        # Present a busy status until the last poll, as a chip with delayed
        # completion may do; the actual program command and timer still run.
        read = chip.read
        chip.read = lambda off: read(off)^0x80
        self.invoke(cpu,flash.OWNER,(self.source,BUS+destination),0x08141e8c)
        self.timer_expiry(cpu)
        chip.read = read
        self.run_to(cpu,0x08141e8c,self.sentinel)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_R0),0)
        self.assertEqual(writes,PREFIX+[(destination,value)])
        self.assertEqual(reads,[destination,destination])

    def test_source_reload_dynamic_callback_and_return_width(self):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R4, UC_ARM_REG_SP
        cpu,chip,writes,_ = self.machine(self.qualified,0x1b32)
        destination, replacement = BUS+0x4321,0x03002000
        cpu.mem_write(self.source,b'\x27')
        cpu.mem_write(replacement,b'\x70\x47')  # BX LR
        cpu.mem_write(0x0200f368,struct.pack('<I',replacement|1))
        def after_store(uc,*args):
            uc.mem_write(self.source,b'\x81')
        def replacement_callback(uc,*args):
            self.assertEqual([uc.reg_read(r) for r in (UC_ARM_REG_R0,UC_ARM_REG_R1,UC_ARM_REG_R2)],
                             [1,destination,0x81])
            uc.reg_write(UC_ARM_REG_R0,0xdeadbeef)
        cpu.hook_add(UC_HOOK_MEM_WRITE,after_store,begin=destination,end=destination)
        cpu.hook_add(UC_HOOK_CODE,replacement_callback,begin=replacement,end=replacement)
        cpu.reg_write(UC_ARM_REG_R4,0x133755aa)
        self.assertEqual(self.invoke(cpu,flash.OWNER,(self.source,destination)),0xbeef)
        self.assertEqual(chip.read(0x4321),0x27)
        self.assertEqual(writes,PREFIX+[(0x4321,0x27)])
        self.assertEqual(cpu.reg_read(UC_ARM_REG_R4),0x133755aa)
        self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),0x03007000)

    def test_installed_sector_programmers_program_complete_sectors(self):
        from unicorn.arm_const import UC_ARM_REG_SP
        # Distinct first and last sectors also exercise destination bounds 0000/FFFF.
        for ident, programmer, sector in ((0xd4bf,0x08142001,0),(0x1b32,0x08142161,15)):
            cpu, chip, writes, _ = self.machine(self.qualified,ident)
            self.assertEqual(struct.unpack('<I',cpu.mem_read(0x0200f36c,4))[0],programmer)
            payload = bytes(range(256))*16
            cpu.mem_write(self.source,payload)
            chip.storage[sector*4096:(sector+1)*4096] = bytes(4096)
            self.assertEqual(self.invoke(cpu,programmer,(sector,self.source),limit=2000000),0)
            self.assertEqual(cpu.reg_read(UC_ARM_REG_SP),0x03007000)
            expected = bytearray([255])*65536
            start = sector*4096
            expected[start:start+4096] = payload
            self.assertEqual(chip.storage,expected)
            self.assertEqual(writes[-4*4096:], [write for i,byte in enumerate(payload) for write in (*PREFIX,(start+i,byte))])


if __name__ == '__main__':
    unittest.main()
