"""Original USA sprite installation, two-slot lifetime, list visitation and receipt."""

import copy
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import scene_sprite_visitor as sprite
from rompath import rom_path

BASE = 0x08000000
SP = 0x03005000
SCENE, LIST, NODE, VALUE = 0x02002000, 0x02003000, 0x02004000, 0x02005000
SPRITES = (0x02006000, 0x02006200)
SLOTS = SCENE + 0x394


@unittest.skipUnless(
    os.getenv("FFTA_SCENE_SPRITE_ROOT"),
    "requires native USA ROM and matched game sources",
)
class SceneSpriteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_SCENE_SPRITE_ROOT"])
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root / "symbols/functions.txt").read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)

    def machine(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB

        uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        uc.mem_map(BASE, len(self.rom))
        uc.mem_write(BASE, self.rom)
        uc.mem_map(0x02000000, 0x40000)
        uc.mem_map(0x03000000, 0x8000)
        return uc

    def run_to(self, uc, start, end):
        from unicorn.arm_const import UC_ARM_REG_PC

        uc.emu_start(start | 1, end, count=30000)
        self.assertEqual(uc.reg_read(UC_ARM_REG_PC), end)

    def call(self, uc, entry, argument):
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_LR, UC_ARM_REG_SP

        uc.reg_write(UC_ARM_REG_LR, BASE | 1)
        uc.reg_write(UC_ARM_REG_SP, SP)
        uc.reg_write(UC_ARM_REG_R0, argument)
        self.run_to(uc, entry, BASE)
        self.assertEqual(uc.reg_read(UC_ARM_REG_SP), SP)

    def install(self, uc):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import (
            UC_ARM_REG_R0,
            UC_ARM_REG_R1,
            UC_ARM_REG_R2,
            UC_ARM_REG_PC,
        )

        # Execute the real installer and wrapper. Only the BIOS CpuSet SWI service is modeled.
        calls = []

        def bios(machine, pc, size, _):
            source, dest, count = [machine.reg_read(r) for r in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2)]
            calls.append((source, dest, count))
            self.assertEqual(machine.mem_read(pc, 2), bytes.fromhex("0bdf"))
            self.assertEqual((source, dest, count), (0x08A38ADC, 0x03005F28, 0x720))
            machine.mem_write(dest, bytes(machine.mem_read(source, 2 * count)))
            machine.reg_write(UC_ARM_REG_PC, pc + 3)

        handle = uc.hook_add(UC_HOOK_CODE, bios, begin=0x0814186C, end=0x0814186C)
        self.call(uc, 0x0808F74C, 0)
        uc.hook_del(handle)
        self.assertEqual(calls, [(0x08A38ADC, 0x03005F28, 0x720)])
        self.assertEqual(uc.mem_read(0x03005F28, 0xE40), uc.mem_read(0x08A38ADC, 0xE40))

    def draw(self, flags, frame, active, list_length):
        from unicorn import UC_HOOK_CODE, UC_HOOK_MEM_READ
        from unicorn.arm_const import (
            UC_ARM_REG_R0,
            UC_ARM_REG_R1,
            UC_ARM_REG_R2,
            UC_ARM_REG_R3,
            UC_ARM_REG_R4,
        )

        uc = self.machine()
        self.install(uc)
        uc.mem_write(SCENE + 0x10, struct.pack("<I", LIST))
        uc.mem_write(SCENE + 0x24, struct.pack("<I", flags))
        uc.mem_write(0x02007F60, struct.pack("<4h", 5, 6, 7, 8))
        for n in range(list_length):
            node = NODE + 32 * n
            uc.mem_write(
                node,
                struct.pack(
                    "<III",
                    VALUE + 0x100 * n,
                    0,
                    node + 32 if n + 1 < list_length else 0,
                ),
            )
            uc.mem_write(VALUE + 0x100 * n + 0x30, struct.pack("<I", 1))
        uc.mem_write(LIST + 4, struct.pack("<I", NODE if list_length else 0))
        coords = [(-67, 32, 17), (52, -86, -17)]
        for n, address in enumerate(SPRITES):
            uc.mem_write(
                SLOTS + 16 * n,
                struct.pack("<I3h3B", address, *coords[n], active[n], 0, frame[n]),
            )
            uc.mem_write(address + 0x150, struct.pack("<II", 0x02007200, 0x12345000 + n))
        registers = [0x12110000 + i for i in range(8)]
        for i, val in enumerate(registers):
            uc.reg_write(UC_ARM_REG_R4 + i, val)
        observed, reads, callbacks = [], [], []

        def trace(machine, pc, size, _):
            if pc in (0x03006B6C, 0x03006BBC, 0x0808EFCC):
                args = [
                    machine.reg_read(r)
                    for r in (
                        UC_ARM_REG_R0,
                        UC_ARM_REG_R1,
                        UC_ARM_REG_R2,
                        UC_ARM_REG_R3,
                    )
                ]
                observed.append((pc, args[: 4 if pc == 0x0808EFCC else 2]))
            elif pc == sprite.ITERATOR:
                desc = machine.reg_read(UC_ARM_REG_R2)
                self.assertEqual(desc, SP - 36)
                self.assertEqual(
                    bytes(machine.mem_read(desc, 8)),
                    struct.pack("<II", SCENE, sprite.CALLBACK | 1),
                )
            elif pc == sprite.CALLBACK:
                callbacks.append((machine.reg_read(UC_ARM_REG_R0), machine.reg_read(UC_ARM_REG_R1)))

        def read(machine, access, address, size, value, _):
            reads.append((address, size))

        uc.hook_add(UC_HOOK_CODE, trace)
        uc.hook_add(UC_HOOK_MEM_READ, read, begin=sprite.TABLE, end=sprite.TABLE + 40)
        self.call(uc, sprite.OWNER, SCENE)
        expected = []
        for n, address in enumerate(SPRITES):
            if active[n] & 1:
                table_word = sprite.TABLE + 8 * frame[n] + 4
                (graphics,) = struct.unpack("<I", uc.mem_read(table_word, 4))
                expected.extend(
                    [
                        (0x03006B6C, [address, graphics]),
                        (0x03006BBC, [address, 1]),
                        (0x0808EFCC, [address] + [v & 0xFFFFFFFF for v in coords[n]]),
                    ]
                )
                self.assertEqual(uc.mem_read(address + 0x158, 4), struct.pack("<I", graphics))
                self.assertEqual(uc.mem_read(address + 22, 1), b"\1")
                x, y, z = coords[n]
                self.assertEqual(
                    struct.unpack("<hh", uc.mem_read(address + 12, 4)),
                    (((x - z) >> 1) + 5 - 7, ((x + z) >> 2) - (y >> 1) + 6 - 8),
                )
        self.assertEqual(observed, expected)
        self.assertEqual(
            reads,
            [(sprite.TABLE + 8 * frame[n] + 4, 4) for n in range(2) if active[n] & 1],
        )
        self.assertEqual(
            callbacks,
            [] if flags & 2 else [(VALUE + 0x100 * n, SCENE) for n in range(list_length)],
        )
        self.assertEqual(
            int.from_bytes(uc.mem_read(SCENE + 0x24, 4), "little"),
            flags if flags & 2 else flags ^ 0x40,
        )
        if not flags & 2 and not list_length:
            self.assertEqual(uc.reg_read(UC_ARM_REG_R2), SP - 36)
        regs_after = [uc.reg_read(UC_ARM_REG_R4 + i) for i in range(8)]
        self.assertEqual(regs_after, registers)

    def test_original_rom_normal_sprites_and_iterator(self):
        for args in [
            (0, [0, 3], [1, 1], 2),
            (0x40, [1, 2], [1, 1], 0),
            (2, [3, 0], [1, 0], 2),
            (0x42, [0, 1], [0, 1], 2),
            (0, [0, 0], [0, 0], 1),
        ]:
            with self.subTest(args=args):
                self.draw(*args)

    def test_caller_reads_scene_global_and_visits_its_list(self):
        from unicorn import UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_R0

        for address in (0, SCENE):
            with self.subTest(address=address):
                uc = self.machine()
                uc.reg_write(UC_ARM_REG_SP, SP)
                uc.mem_write(0x0200F4B0, struct.pack("<I", address))
                uc.mem_write(SCENE + 0x10, struct.pack("<I", LIST))
                calls = []

                def entry(machine, pc, size, _):
                    if pc in (0x08096D7C, sprite.OWNER, sprite.ITERATOR):
                        calls.append(pc)
                    if pc == sprite.OWNER:
                        self.assertEqual(machine.reg_read(UC_ARM_REG_R0), SCENE)

                uc.hook_add(UC_HOOK_CODE, entry)
                self.run_to(uc, 0x080231FC, 0x0802320C)
                self.assertEqual(
                    calls,
                    [0x08096D7C] if not address else [0x08096D7C, 0x08096D7C, sprite.OWNER, sprite.ITERATOR],
                )
                self.assertEqual(uc.mem_read(SCENE + 0x24, 4), struct.pack("<I", 0x40 if address else 0))

    def test_original_activation_and_frame_expiry(self):
        from unicorn.arm_const import (
            UC_ARM_REG_R4,
            UC_ARM_REG_R6,
            UC_ARM_REG_R9,
            UC_ARM_REG_SP,
        )

        for initial in ((0, 0), (1, 0), (1, 1)):
            uc = self.machine()
            uc.reg_write(UC_ARM_REG_SP, SP)
            uc.reg_write(UC_ARM_REG_R6, VALUE)
            uc.reg_write(UC_ARM_REG_R9, SCENE)
            uc.mem_write(0x02007F14, struct.pack("<IB", 0x02007000, 8))
            for n, active in enumerate(initial):
                uc.mem_write(SLOTS + 16 * n + 10, bytes([active, 3, 2]))
            self.run_to(uc, 0x08097EB8, 0x08097ED6)
            chosen = next((i for i, b in enumerate(initial) if not b), None)
            for n, active in enumerate(initial):
                expected = bytes((1, 0, 0)) if n == chosen else bytes((active, 3, 2))
                self.assertEqual(uc.mem_read(SLOTS + 16 * n + 10, 3), expected)
        for index, (duration, _) in enumerate(sprite.FRAMES):
            uc = self.machine()
            uc.reg_write(UC_ARM_REG_R4, SCENE)
            uc.mem_write(SLOTS + 10, bytes((0x81, duration, index)))
            uc.mem_write(SLOTS + 26, bytes((1, duration - 1, index)))
            self.run_to(uc, 0x0809A426, 0x0809A470)
            self.assertEqual(
                uc.mem_read(SLOTS + 10, 3),
                bytes((0x80 if index == 3 else 0x81, 0, index + 1)),
            )
            self.assertEqual(uc.mem_read(SLOTS + 26, 3), bytes((1, duration, index)))

    def test_verified_receipt_and_mutations(self):
        report = (self.root / "docs/match/0809A48C.md").read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, sprite.OWNER))
        for old, new in [
            ('"halfwords":1824', '"halfwords":1823'),
            ('"node_next":8', '"node_next":12'),
        ]:
            self.assertIn(old, report)
            self.assertFalse(match_evidence.report_matches(report.replace(old, new), self.root, sprite.OWNER))
        for site in [
            sprite.OWNER + 126,
            0x0808F758,
            0x08394038,
            0x08A39770,
            0x08097E74,
            0x0809A468,
            sprite.TABLE + 4,
            0x08098008,
            0x0809ABF2,
            0x0814225C,
        ]:
            with self.subTest(site=hex(site)):
                rom = bytearray(self.rom)
                rom[site - BASE] ^= 1
                rom = bytes(rom)
                with self.assertRaises(ValueError):
                    self.verify(rom, sprite.BINDINGS)
        bindings = copy.deepcopy(sprite.BINDINGS)
        bindings["functions"].reverse()
        with self.assertRaises(ValueError):
            self.verify(self.rom, bindings)

    def verify(self, rom, bindings):
        return owner.verify(
            data=sprite.read(rom, sprite.OWNER, 164),
            address=sprite.OWNER,
            rom=rom,
            mapping=self.mapping,
            index=self.index,
            objects=self.objects,
            bindings=bindings,
            selector=buffers.THUNK_ROOT_SCRATCH_SELECTOR,
        )
