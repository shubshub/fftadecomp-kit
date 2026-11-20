"""Execute the original menu lifecycle with the published GBA CpuSet and CpuFastSet operations."""

import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match_evidence
from rompath import rom_path


ROM = 0x08000000
SP = 0x03007F00
OUTER_PHASE = 0x02001000
PHASES = 0x03000E40
WORDS = 0x03002820
ACTIVE = 0x03002710
RING = 0x0201F540
PALETTE = 0x03003860
PARENT = 0x0804C888
HANDLERS = (0x0804D86C, 0x0804CAE4, 0x0804E05C)


class Menu:
    def __init__(self, rom):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE, UC_HOOK_MEM_WRITE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_PC

        self.u = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        self.trace = []
        self.transfers = []
        self.clear_writes = []
        self.work = 0
        self.clearing = False
        for start, size in [
            (ROM, len(rom)),
            (0x02000000, 0x40000),
            (0x03000000, 0x8000),
            (0x04000000, 0x1000),
            (0x05000000, 0x1000),
            (0x06000000, 0x20000),
            (0x07000000, 0x1000),
        ]:
            self.u.mem_map(start, size)
        self.u.mem_write(ROM, rom)

        def bios(u, pc, size, _):
            source, dest, control = [u.reg_read(UC_ARM_REG_R0 + i) for i in range(3)]
            fast = pc == 0x08141868
            assert bytes(u.mem_read(pc, 2)) == (b"\x0c\xdf" if fast else b"\x0b\xdf")
            width = 4 if fast or control & 0x04000000 else 2
            units = control & 0x1FFFFF
            length = width * ((units + 7) & ~7 if fast else units)
            fill = bool(control & 0x01000000)
            raw = bytes(u.mem_read(source, width if fill else length))
            u.mem_write(dest, raw * (length // width) if fill else raw)
            self.transfers.append((source, dest, control))
            u.reg_write(UC_ARM_REG_PC, pc + 3)

        def trace(u, pc, size, _):
            args = [u.reg_read(UC_ARM_REG_R0 + i) for i in range(3)]
            self.trace.append((pc, *args))
            if pc == 0x03005E78 and args[1] == 0x394:
                self.work = args[0]
                assert self.word(RING) == self.work
                # The actual heap has already zeroed the full arena. Refill this one
                # returned allocation to distinguish the initializer's own stores.
                u.mem_write(self.work, b"\xa5" * 0x394)
                self.clearing = True
            if pc == 0x0804C8F6:
                self.clearing = False

        def write(u, access, addr, width, value, _):
            if self.clearing:
                self.clear_writes.append((addr, width, value))

        for pc in (0x08141868, 0x0814186C):
            self.u.hook_add(UC_HOOK_CODE, bios, begin=pc, end=pc)
        for pc in (*HANDLERS, 0x03005E78, 0x0804C8F6, 0x0804CA58, 0x0804CA6C):
            self.u.hook_add(UC_HOOK_CODE, trace, begin=pc, end=pc)
        self.u.hook_add(UC_HOOK_MEM_WRITE, write)

    def word(self, addr):
        return int.from_bytes(self.u.mem_read(addr, 4), "little")

    def call(self, pc, *args):
        from unicorn.arm_const import (
            UC_ARM_REG_R0,
            UC_ARM_REG_R4,
            UC_ARM_REG_LR,
            UC_ARM_REG_SP,
            UC_ARM_REG_PC,
        )

        for i in range(4):
            self.u.reg_write(UC_ARM_REG_R0 + i, args[i] if i < len(args) else 0)
        saved = [0x12340000 + i for i in range(8)]
        for i, val in enumerate(saved):
            self.u.reg_write(UC_ARM_REG_R4 + i, val)
        self.u.reg_write(UC_ARM_REG_LR, ROM | 1)
        self.u.reg_write(UC_ARM_REG_SP, SP)
        self.u.emu_start(pc | 1, ROM, count=3000000)
        assert self.u.reg_read(UC_ARM_REG_SP) == SP and self.u.reg_read(UC_ARM_REG_PC) == ROM
        assert [self.u.reg_read(UC_ARM_REG_R4 + i) for i in range(8)] == saved
        return self.u.reg_read(UC_ARM_REG_R0)

    def open(self):
        self.call(0x08002768)
        self.call(0x0800052C)
        for i, cb in enumerate((PARENT | 1, 0x08003661, PARENT | 1, 0x08003661)):
            self.call(0x08006ADC, 0x03000880, i, cb)
        self.u.mem_write(PALETTE - 2, b"\xdd" * 0x404)
        self.call(PARENT, 0, OUTER_PHASE)


@unittest.skipUnless(os.getenv("FFTA_MENU_RING_ROOT"), "requires the original USA game and recovered C")
class MenuRing(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_MENU_RING_ROOT"]).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()

    def test_original_installer_initializer_and_ring_wrap(self):
        m = Menu(self.rom)
        m.open()
        self.assertEqual(m.work, 0x0201F564)
        self.assertEqual(m.word(OUTER_PHASE), 1)
        self.assertEqual(m.u.mem_read(m.work, 916), bytes(916))
        self.assertEqual(m.clear_writes[1:], [(m.work + i, 4, 0) for i in range(0, 916, 4)])
        self.assertEqual(m.clear_writes[0], (SP - 32, 4, 0x0804C8F7))
        self.assertEqual(m.u.mem_read(PALETTE - 2, 0x404), b"\xdd\xdd" + bytes(1024) + b"\xdd\xdd")
        self.assertEqual(
            m.transfers[-2:], [(SP - 28, PALETTE, 0x01000100), (SP - 26, PALETTE + 512, 0x01000100)]
        )
        self.assertEqual(m.u.mem_read(0x03002860, 16), struct.pack("<4I", 0, 0, PARENT | 1, 0x08003661))
        self.assertEqual(m.u.mem_read(WORDS, 20), struct.pack("<5I", *(p | 1 for p in HANDLERS), 0, 0))
        self.assertEqual((m.word(ACTIVE + 8), m.word(ACTIVE + 12)), (WORDS, PHASES))
        self.assertEqual(m.u.mem_read(PHASES, 5), bytes(5))
        for i in range(33):
            self.assertEqual(m.call(0x0804CA8C), m.work + 16 + 28 * (i % 32))
            self.assertEqual(m.word(m.work + 0x390), (i + 1) % 32)

    def test_original_child_dispatch_and_late_cleanup(self):
        m = Menu(self.rom)
        m.open()
        m.call(PARENT, 0, OUTER_PHASE)
        self.assertEqual(m.u.mem_read(PHASES, 5), bytes((1, 3, 2, 0, 0)))
        self.assertEqual(
            [(pc, slot, ptr) for pc, slot, ptr, _ in m.trace if pc in HANDLERS],
            [(pc, i, PHASES + i) for i, pc in enumerate(HANDLERS)],
        )
        for _ in range(18):
            m.call(PARENT, 0, OUTER_PHASE)
        self.assertEqual(m.u.mem_read(PHASES, 3), bytes((9, 2, 2)))
        # Supply the documented late state; input handling in 0804CBB4 is
        # outside the initializer. No callback result or allocator is stubbed.
        child = m.word(0x0201F544)
        m.u.mem_write(PHASES + 1, b"\x04")
        for ready in (1, 2, 3):
            m.call(PARENT, 0, OUTER_PHASE)
            self.assertEqual(m.word(OUTER_PHASE), ready)
        self.assertEqual(m.word(RING), 0)
        self.assertEqual(m.word(0x0201F544), 0)
        self.assertIn(child, [arg for pc, arg, *_ in m.trace if pc == 0x0804CA6C])
        self.assertIn(m.work, [arg for pc, arg, *_ in m.trace if pc == 0x0804CA6C])
        self.assertEqual(
            [e[1:] for e in m.transfers[-2:]], [(PALETTE, 0x01000100), (PALETTE + 512, 0x01000100)]
        )

    def test_altered_slot_layout_and_target_refuse(self):
        import owner_admission_profile  # noqa: F401
        import menu_ring_initializer as menu

        def body(pc, n):
            return self.rom[pc - ROM : pc - ROM + n]

        ring, setter, root = body(0x0804CA8C, 36), body(0x08006ADC, 28), body(menu.OWNER, 184)
        for raw, offset, index in [(ring, 24, 0), (setter, 22, 1), (root, 120, 2)]:
            changed = bytearray(raw)
            changed[offset] ^= 1
            args = [ring, setter, root]
            args[index] = changed
            with self.subTest(index=index), self.assertRaises(ValueError):
                menu.layout(*args)
        installed = body(0x08A38A2C, 176)
        with self.assertRaises(ValueError):
            menu.zero.verify_aligned_menu_ring(installed, menu.IMAGE + 2)
        with self.assertRaises(ValueError):
            menu.zero.verify_aligned_menu_ring(bytes([installed[0] ^ 1]) + installed[1:], menu.IMAGE)
        with self.assertRaises(ValueError):
            menu.callback_site({}, {}, {}, menu.OWNER, [])
        with self.assertRaises(ValueError):
            menu.zero.verify_conditional(installed, menu.IMAGE, menu.IMAGE, 916, selector=menu.zero.SELECTOR)

    def test_native_report_replay(self):
        address = 0x0804C8C4
        report = (self.root / "docs/match/0804C8C4.md").read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, address))
        for original, changed in [
            ('"zero_word_stores":229', '"zero_word_stores":228'),
            ('"slot_count":5', '"slot_count":4'),
        ]:
            self.assertIn(original, report)
            self.assertFalse(
                match_evidence.report_matches(report.replace(original, changed), self.root, address)
            )
