"""Native phase-zero caller and 0813BDD0, with modeled GBA DMA3 and CpuFastSet."""
import os
from pathlib import Path
from struct import pack, pack_into, unpack
import unittest
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

from inert_spin_profile import index_snapshot
import iwram_installation_prerequisite as installation
from match_evidence import mapping_snapshot, report_matches
from positioned_equipment_chance import direct_sites
from rompath import rom_path

OWNER, END, CALLER = 0x0813BDD0, 0x0813BEEC, 0x0813BCF0
BASE, TABLE, IMAGE = 0x08000000, 0x0836D4B8, 0x03005E78
PALETTE, SHADOW, RECORD = 0x03003860, 0x03000940, 0x03000E60
VRAM, MAP = 0x06000000, 0x06008000


@unittest.skipUnless(os.environ.get("FFTA_SCREEN_ROOT"), "requires the USA ROM and recovered screen setup")
class ScreenInit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_SCREEN_ROOT']).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()

    def test_caller_and_stock_report(self):
        from hashlib import sha256
        from unit_equipment_attribute import ops

        rom = self.rom
        self.assertEqual(sha256(rom[OWNER-BASE:END-BASE]).hexdigest(),
                         'fc91ac0d9c28b8c90f0cfffb2fbd88e094bcd6f38af2d24c360ccc0dfb488ca7')
        self.assertEqual(direct_sites(rom, OWNER), [0x0813BD2E])
        self.assertFalse(any(pack('<I', value) in rom for value in (OWNER, OWNER | 1)))
        self.assertEqual(direct_sites(rom, CALLER), [])
        self.assertEqual(rom.count(pack('<I', CALLER | 1)), 1)
        self.assertEqual(rom[0x3704:0x3708], pack('<I', CALLER | 1))
        ops(rom, 0x0813BD2A, 'bl #0x814224c', 'bl #0x813bdd0', 'bl #0x813beec', 'movs r0, #1',
            'strb r0, [r6]')
        report = (self.root / 'docs/match/0813BDD0.md').read_text()
        self.assertTrue(report_matches(report, self.root, OWNER))
        self.assertIn('**MATCH - byte identical** - 284/284 bytes', report)

    def test_native_scene_dma_bios_lcd_shadow_and_tilemap(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_INTR
        from unicorn import UC_HOOK_MEM_READ, UC_HOOK_MEM_WRITE, UC_MEM_READ, UC_MEM_WRITE
        from unicorn.arm_const import (UC_ARM_REG_LR as LR, UC_ARM_REG_PC as PC,
            UC_ARM_REG_R0 as R0, UC_ARM_REG_R1 as R1, UC_ARM_REG_R2 as R2, UC_ARM_REG_SP as SP)

        rom, root = self.rom, self.root
        plan = installation.verify(rom[0x2768:0x27B8], 0x08002768, rom, mapping_snapshot(root), index_snapshot(root),
                                   selector=installation.SELECTOR, call_site=0x08002796, pointer_address=TABLE)
        self.assertEqual(plan['arguments'], dict(source=0x08A38A2C, destination=IMAGE, control=88))
        self.assertEqual((plan['entry']['pointer_word'],plan['copy_plan']['bytes']), (IMAGE | 1,176))

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(BASE, len(rom))
        cpu.mem_write(BASE, rom)
        cpu.mem_map(0x02000000, 0x40000)
        cpu.mem_map(0x03000000, 0x8000)
        cpu.mem_map(VRAM, 0x19000)
        cpu.mem_write(IMAGE, bytes.fromhex(plan['source_image']['bytes']))
        cpu.mem_write(PALETTE-1, b'\xA5'*1026)
        cpu.mem_write(SHADOW-1, b'\xA5'*82)
        cpu.mem_write(RECORD-1, b'\xA5'*26)
        cpu.mem_write(VRAM, b'\xA5'*0x18001)
        issued, fast, shadows, map_stores, init_call, owner_sp = [], [], [], [], [], []
        readbacks = []
        channel = {}

        def mmio_write(uc, offset, size, value, _):
            self.assertIn(offset, (0xD4, 0xD8, 0xDC))
            self.assertEqual(size, 4)
            channel[offset] = value
            issued.append((uc.reg_read(PC), offset, value))
            if offset == 0xDC:
                self.assertEqual(value, 0x81000100)
                count, source, dest = value & 0xffff, channel[0xD4], channel[0xD8]
                self.assertEqual(source, owner_sp[0]-24)
                unit = bytes(uc.mem_read(source, 2))
                self.assertEqual(unit, bytes(2))
                self.assertEqual(bytes(uc.mem_read(dest, 2*count)), b'\xA5'*(2*count))
                uc.mem_write(dest, unit*count)
                # Immediate transfer completes before the CPU executes the control readback.
                channel[0xDC] = value & 0x7FFF0000

        def mmio_read(uc, offset, size, _):
            self.assertEqual((offset, size), (0xDC, 4))
            readbacks.append(uc.reg_read(PC))
            return channel[offset]

        cpu.mmio_map(0x04000000, 0x1000, mmio_read, None, mmio_write, None)

        def swi(uc, irq, _):
            self.assertEqual((irq, uc.reg_read(PC), uc.reg_read(LR)), (2, 0x0814186A, 0x0813BE0F))
            args = tuple(uc.reg_read(reg) for reg in (R0, R1, R2))
            self.assertEqual(args, (owner_sp[0]-20, VRAM, 0x01006000))
            unit = bytes(uc.mem_read(args[0], 4))
            self.assertEqual(unit, bytes(4))
            count = args[2] & 0x1fffff
            self.assertEqual(count % 8, 0)
            self.assertEqual(bytes(uc.mem_read(VRAM, count*4)), b'\xA5'*(count*4))
            uc.mem_write(VRAM, unit*count)
            fast.append(args)
        cpu.hook_add(UC_HOOK_INTR, swi)

        def enter_owner(uc, pc, size, _):
            self.assertEqual(uc.reg_read(LR), 0x0813BD33)
            owner_sp.append(uc.reg_read(SP))

        def callback(uc, pc, size, _):
            if owner_sp:
                init_call.append((uc.reg_read(LR), uc.reg_read(R0), uc.reg_read(R1), uc.reg_read(R2)))

        def shadow(uc, kind, addr, width, value, _):
            if OWNER <= uc.reg_read(PC) < END:
                shadows.append((kind, addr-SHADOW, width))

        def map_write(uc, kind, addr, width, value, _):
            if IMAGE <= uc.reg_read(PC) < IMAGE+176:
                map_stores.append((addr,width,value))

        cpu.hook_add(UC_HOOK_CODE, enter_owner, begin=OWNER, end=OWNER)
        cpu.hook_add(UC_HOOK_CODE, callback, begin=IMAGE, end=IMAGE)
        cpu.hook_add(UC_HOOK_MEM_READ|UC_HOOK_MEM_WRITE, shadow, begin=SHADOW, end=SHADOW+79)
        cpu.hook_add(UC_HOOK_MEM_WRITE, map_write, begin=VRAM, end=VRAM+0x17fff)
        phase = 0x0203F000
        cpu.reg_write(R0, 0)
        cpu.reg_write(R1, phase)
        cpu.reg_write(SP, 0x03007D00)
        cpu.reg_write(LR, 0x03007001)
        # The real containing scene also creates/clears its arena and state using the
        # installed IWRAM routines. Stop at the first instruction after this owner.
        cpu.emu_start(CALLER|1, 0x0813BD32, count=500000)
        self.assertEqual(cpu.reg_read(PC), 0x0813BD32)
        self.assertEqual(cpu.reg_read(SP), owner_sp[0])
        self.assertEqual(len(owner_sp), 1)
        self.assertEqual(issued,[(0x0813BDDE,0xD4,owner_sp[0]-24), (0x0813BDE2,0xD8,PALETTE),
                                 (0x0813BDE6,0xDC,0x81000100), (0x0813BDEE,0xD4,owner_sp[0]-24),
                                 (0x0813BDF6,0xD8,PALETTE+512), (0x0813BDF8,0xDC,0x81000100)])
        self.assertEqual(readbacks, [0x0813BDE8,0x0813BDFA])
        self.assertEqual(len(fast), 1)
        self.assertEqual(bytes(cpu.mem_read(PALETTE-1,1026)), b'\xA5'+bytes(1024)+b'\xA5')
        self.assertEqual(bytes(cpu.mem_read(VRAM,0x18001)), bytes(0x18000)+b'\xA5')
        self.assertEqual(init_call, [(0x0813BEC3,MAP,0x800,IMAGE|1)])
        self.assertEqual(map_stores, [(MAP+i,4,0) for i in range(0,0x800,4)])

        expected = bytearray(b'\xA5'*80)
        pack_into('<H',expected,0,0x140)
        pack_into('<H',expected,2,0x3000)
        pack_into('<HH',expected,10,0,0)
        fields = (0x4A,0x4B,0x44,0x45,0x4C,0x4D,0x4E,0x42,0x43,0x3B,0x3A,0x3F,0x3E,
                  0x3C,0x3D,0x40,0x41)
        for offset in fields:
            expected[offset] = 16 if offset in (0x4C,0x4E) else 0
        self.assertEqual(bytes(cpu.mem_read(SHADOW-1,82)), b'\xA5'+expected+b'\xA5')
        first = [(UC_MEM_READ,10,2),(UC_MEM_WRITE,10,2),(UC_MEM_READ,10,2),(UC_MEM_READ,12,2),
                 (UC_MEM_WRITE,12,2),(UC_MEM_READ,2,2),(UC_MEM_WRITE,2,2)]
        self.assertEqual(shadows, first+[(kind,offset,1) for offset in fields
                                         for kind in (UC_MEM_READ,UC_MEM_WRITE)]+[(UC_MEM_WRITE,0,2)])
        record = bytearray(b'\xA5'*24)
        pack_into('<II',record,4,0,0)
        record[12:14] = b'\x20\x20'
        pack_into('<II',record,16,VRAM,MAP)
        self.assertEqual(bytes(cpu.mem_read(RECORD-1,26)), b'\xA5'+record+b'\xA5')


if __name__ == '__main__':
    unittest.main()
