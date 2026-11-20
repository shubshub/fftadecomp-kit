"""Native original caller, tile conversion, allocation, and sound #0x8D."""
import os
from pathlib import Path
from struct import pack, unpack
import unittest

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))

from inert_spin_profile import index_snapshot
from match_evidence import mapping_snapshot, report_matches
from positioned_equipment_chance import direct_sites
from rompath import rom_path
import tile_effect_sound as sound

CALLER, OWNER, DONE = 0x080D8924, 0x080D8858, 0x03000100
ACTOR, TILE_ENTRIES, MAP = 0x02039000, 0x02010000, 0x02007F10
EFFECTS, TRACKS, CHANNEL, MIXER = 0x0200F9E8, 0x02034000, 0x02035000, 0x02036000
RETURN_STACK = 0x03007300
PLAYERS = (0x0200F2E0, 0x0200F320)


class TileEffect(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = os.environ.get('FFTA_TILE_EFFECT_ROOT')
        if root is None:
            raise unittest.SkipTest('set FFTA_TILE_EFFECT_ROOT to the native FFTA fixture')
        cls.root = Path(root)
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = mapping_snapshot(cls.root)
        cls.index = index_snapshot(cls.root)

    def test_native_caller_and_rejection(self):
        sites = direct_sites(self.rom, OWNER)
        self.assertEqual(len(sites), 181)
        self.assertIn(0x080D8942, sites)
        self.assertFalse(any(pack('<I', x) in self.rom for x in (OWNER, OWNER | 1)))
        sound.ops(self.rom, 0x080D8932, 'lsls r1, r1, #0x10', 'lsrs r1, r1, #0x10',
                  'mov r8, r1', 'lsls r2, r2, #0x10', 'lsrs r2, r2, #0x10', 'adds r7, r2, #0',
                  'cmp r7, #0', 'bne #0x80d8948', 'bl #0x80d8858', 'b #0x80d89be')
        sound.runtime_bindings(self.rom, self.mapping, self.index)
        for offset in (sound.SONG+3, 0x081455FC, 0x08145500, sound.THUNK):
            with self.subTest(mutation=hex(offset)):
                rom = bytearray(self.rom)
                rom[offset-sound.BASE] ^= 0x80
                with self.assertRaises(ValueError):
                    sound.runtime_bindings(rom, self.mapping, self.index)

    def test_compiled_report_and_changed_evidence(self):
        report = (self.root / 'docs/match/080D8858.md').read_text()
        self.assertTrue(report_matches(report, self.root, OWNER))
        self.assertIn('**MATCH - byte identical** - 202/202 bytes', report)
        forged = report.replace('"reverb_byte":0', '"reverb_byte":128')
        self.assertNotEqual(forged, report)
        self.assertFalse(report_matches(forged, self.root, OWNER))

    def execute(self, flags, *, enabled=True, actor_ready=True, full=False,
                callback=0x08145BF4, locked=False):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import (UC_ARM_REG_R0 as R0, UC_ARM_REG_R1 as R1,
            UC_ARM_REG_R2 as R2, UC_ARM_REG_R3 as R3, UC_ARM_REG_R4 as R4,
            UC_ARM_REG_R11 as R11, UC_ARM_REG_LR as LR, UC_ARM_REG_PC as PC, UC_ARM_REG_SP as SP)

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(sound.BASE, len(self.rom))
        cpu.mem_write(sound.BASE, self.rom)
        for base, length in ((0x02000000, 0x40000), (0x03000000, 0x8000), (0x04000000, 0x1000)):
            cpu.mem_map(base, length)
        def u32(addr):
            return unpack('<I', bytes(cpu.mem_read(addr, 4)))[0]
        def put(addr, fmt, *args):
            cpu.mem_write(addr, pack(fmt, *args))
        def args():
            return tuple(cpu.reg_read(r) for r in (R0, R1, R2, R3))
        # Sign-bit coordinates are narrowed to map bytes, then expanded to world halfwords.
        put(ACTOR+4, '<H', 0x20 if actor_ready else 0)
        put(ACTOR+10, '<bb', -2, -3)
        put(ACTOR+0x2c0, 'B', 0xB7)
        put(MAP+4, '<IB', TILE_ENTRIES, 255)
        put(TILE_ENTRIES+2*(255*253+254), 'B', 201)
        if full:
            for slot in range(32):
                put(EFFECTS+0x71+0x2c*slot, 'B', 1)
        put(0x020084D8, 'B', 2 if enabled else 0)
        put(0x03007FF0, '<I', MIXER)
        put(MIXER+0x2c, '<I', callback | 1)
        for player in PLAYERS:
            put(player+0x34, '<I', 0 if locked else 0x68736D53)
            put(player+8, 'B', 3)
            put(player+0x2c, '<I', TRACKS)
        put(TRACKS, 'B', 0x80)
        put(TRACKS+0x20, '<I', CHANNEL)
        put(CHANNEL, 'BB', 1, 1)
        put(0x04000063, 'B', 0xA5)
        saved = {r: 0x23500000 + r for r in range(R4, R11+1)}
        for r, value in saved.items():
            cpu.reg_write(r, value)
        seen, after_effect, frame = [], [], []
        watched = {OWNER, 0x080DD494, 0x0801CC18, 0x0801CA78, 0x080A92E4,
                   0x080A8BC4, 0x08141520, 0x08141570, 0x081458AC, 0x08144D94,
                   sound.THUNK, *sound.CALLBACKS, 0x081456AC}
        def code(uc, pc, size, data):
            if pc == OWNER:
                frame.append(uc.reg_read(SP))
            if pc == 0x080A92E4:
                after_effect.append(True)
            if pc == 0x080D8914:
                after_effect.clear()
            if pc in watched:
                seen.append((pc, args()))
                if pc == 0x0801CA78:
                    self.assertEqual((args()[3], u32(uc.reg_read(SP)), u32(uc.reg_read(SP)+4)),
                                     tuple(frame[0]-n for n in (36,34,32)))
                if pc == 0x080A92E4:
                    self.assertEqual((u32(uc.reg_read(SP)), u32(uc.reg_read(SP)+4)),
                                     (0x15, frame[0]-32))
        def mem_read(uc, access, address, size, value, data):
            if after_effect and address < frame[0]-40 and address+size > frame[0]-44:
                self.fail(f'stale outgoing word read at PC {uc.reg_read(PC):08X}')
        cpu.hook_add(UC_HOOK_CODE, code)
        cpu.hook_add(UC_HOOK_MEM_READ, mem_read, begin=RETURN_STACK-256, end=RETURN_STACK)
        cpu.reg_write(SP, RETURN_STACK)
        cpu.reg_write(LR, DONE | 1)
        cpu.reg_write(R0, ACTOR)
        cpu.reg_write(R1, 0xBEEF0000 | flags)
        cpu.reg_write(R2, 0xFEED0000)
        cpu.reg_write(R3, 0)
        cpu.emu_start(CALLER | 1, DONE, count=100000)
        self.assertEqual((cpu.reg_read(PC), cpu.reg_read(SP)), (DONE, RETURN_STACK))
        self.assertEqual(saved, {r:cpu.reg_read(r) for r in saved})
        self.assertEqual(seen[0][1][:2], (ACTOR, flags))
        at = lambda addr: [args for pc, args in seen if pc == addr]
        self.assertEqual(cpu.reg_read(R0), 0 if actor_ready else 0xB7)
        if not actor_ready:
            self.assertEqual([pc for pc, args in seen], [OWNER, 0x080DD494])
            return
        world = (254*32+16, 201*16, 253*32+16)
        self.assertEqual(at(0x0801CC18)[0][:2], (254,253))
        self.assertEqual(at(0x0801CA78)[0][:3], (254,201,253))
        self.assertEqual(at(0x080A92E4), [(0, *world)])
        self.assertEqual(len(at(0x080A8BC4)), int(not full))
        if not full:
            self.assertEqual(bytes(cpu.mem_read(EFFECTS+0x71, 2)), bytes((1,0x15)))
            self.assertEqual(unpack('<hhh', bytes(cpu.mem_read(EFFECTS+0x74, 6))), world)
        if flags & 1:
            self.assertFalse(at(0x08141520) or at(0x08141570) or at(0x081458AC))
            return
        mode = 1 if flags & 2 else 2 if flags & 4 else 0
        sound_call = 0x08141570 if mode else 0x08141520
        self.assertEqual(at(sound_call)[0][:2 if mode else 1], (mode,0x8d) if mode else (0x8d,))
        if not enabled:
            self.assertFalse(at(0x081458AC))
            return
        player = PLAYERS[0] if mode == 1 else PLAYERS[1]
        self.assertEqual(at(0x081458AC)[0][:2], (player,sound.SONG))
        self.assertFalse(at(0x081456AC))
        if locked:
            self.assertFalse(at(0x08144D94))
            return
        self.assertEqual(u32(player), sound.SONG)
        self.assertEqual(u32(player+0x34), 0x68736D53)
        self.assertEqual([args[:2] for args in at(0x08144D94)],
                         [(player, TRACKS+i*0x50) for i in range(3)])
        self.assertEqual(len(at(sound.THUNK)), 1)
        self.assertEqual(at(callback)[0][0], 1)
        self.assertEqual(bytes(cpu.mem_read(0x04000063, 1)), bytes((8 if callback == 0x08145BF4 else 0xA5,)))
        self.assertEqual([bytes(cpu.mem_read(TRACKS+i*0x50, 1))[0] for i in range(3)], [0xC0,0xC0,0])

    def test_real_caller_effect_and_sound(self):
        for flags in range(8):
            with self.subTest(flags=flags):
                self.execute(flags, full=flags == 4)
        self.execute(0, callback=0x081465E4)
        self.execute(2, enabled=False)
        self.execute(4, locked=True)
        self.execute(0xFFFF, actor_ready=False)
