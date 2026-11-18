"""Bind the USA scanline manager and exercise the real callbacks, banks and LCD shadows."""

import argparse
from copy import deepcopy
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence
import scanline_dispatch as scan
import volatile_semantics as vs


class ScanlineDispatch(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from rompath import rom_path

        fixture = os.environ.get("FFTA_SCANLINE_DISPATCH_FIXTURE")
        if not fixture:
            raise unittest.SkipTest("FFTA_SCANLINE_DISPATCH_FIXTURE requires a source and USA ROM")
        cls.root = Path(fixture)
        cls.rom = Path(rom_path(fixture)).read_bytes()
        (cls.entry,) = match.plausibility.allowlisted_volatile_used(cls.root, scan.OWNER)
        cls.objects = match.parse_data_symbols(match.data_snapshot(cls.root))
        cls.interfaces = vs.RomInterfaces(cls.rom, json.loads(match.mapping_snapshot(cls.root)))
        args = argparse.Namespace(
            cc=match.DEFAULT_CC,
            cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,
            flags=match.DEFAULT_FLAGS,
            objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD,
        )
        runner = match.Runner(args.cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=fixture)
        cls.images, cls.assemblies = [], []
        with runner.workspace() as ws:
            for rewrite in (None, vs.strip_pinned_volatile, vs.perturb_pinned):
                _, _, image = match.compile_object(
                    runner,
                    ws,
                    args,
                    fixture,
                    scan.OWNER,
                    "src/0800C4B4.c",
                    rewrite=None if rewrite is None else lambda t: rewrite(t, cls.entry["declaration"]),
                )
                if rewrite is None:
                    cls.preprocessed = runner.read_binary(f"{ws}/f.i").decode()
                cls.images.append(image)
                cls.assemblies.append(runner.read_binary(f"{ws}/f.s").decode())

    def test_native_and_independent_per_slot_semantics(self):
        record = scan.record(
            self.assemblies,
            self.images,
            self.preprocessed,
            self.entry,
            self.interfaces,
            self.rom,
            self.objects,
        )
        self.assertIn("14 branch paths separately at each physical slot", record)
        for i in range(4):
            controls = [scan.second_pass(asm, i) for asm in self.assemblies]
            self.assertEqual(
                vs.compare(
                    *controls[:2],
                    self.preprocessed,
                    scan.SYMBOL,
                    self.entry["declaration"],
                    controls[2],
                    self.interfaces,
                ),
                [("func_0800C4B4", 14, [], [], [], [])],
            )

    def test_refuses_changed_compiler_inputs_or_callback_abi(self):
        with self.assertRaisesRegex(ValueError, "signature"):
            scan.record(
                self.assemblies,
                self.images,
                self.preprocessed.replace("u16 *buffer", "u8 *buffer"),
                self.entry,
                self.interfaces,
                self.rom,
                self.objects,
            )
        with self.assertRaisesRegex(ValueError, "control assembly"):
            scan.record(
                [
                    self.assemblies[0],
                    self.assemblies[1].replace("ble\t.L22", "bge\t.L22"),
                    self.assemblies[2],
                ],
                self.images,
                self.preprocessed,
                self.entry,
                self.interfaces,
                self.rom,
                self.objects,
            )
        changed = self.assemblies[0].replace("and\tr0, r0, r1", "orr\tr0, r0, r1", 1)
        with self.assertRaisesRegex(ValueError, "instructions"):
            scan.record(
                [changed] * 3,
                self.images,
                self.preprocessed,
                self.entry,
                self.interfaces,
                self.rom,
                self.objects,
            )
        for i in (0, 1, 2):
            images = list(self.images)
            images[i] = deepcopy(images[i])
            raw = bytearray(images[i]["text"])
            raw[90] ^= 1
            images[i]["text"] = bytes(raw)
            with self.assertRaises(ValueError):
                scan.record(
                    self.assemblies,
                    images,
                    self.preprocessed,
                    self.entry,
                    self.interfaces,
                    self.rom,
                    self.objects,
                )

    def test_refuses_shadow_retarget_and_changed_providers(self):
        for _, name, target in scan.DATA:
            with self.subTest(name=name), self.assertRaises(ValueError):
                scan.check_image(self.images[0], self.rom, {**self.objects, name: target + 2})
        for address in (
            0x0800A646,
            0x0800CC8C,
            0x0800C50E,
            0x0800C568,
            0x0800DE70,
            0x080D9C48,
            0x0800F93C,
            0x080008E0,
            0x08149818,
            0x08149B24,
            0x0836D4B8,
        ):
            rom = bytearray(self.rom)
            rom[address - scan.BASE] ^= 1
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                scan.provider(rom)

    def test_saved_body_and_receipt(self):
        report = (self.root / "docs/match/0800C4B4.md").read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, scan.OWNER))
        for old, new in (
            ("14 branch paths", "13 branch paths"),
            ("320/320", "318/320"),
            ("thumb-data-v1", "thumb-frame-data-v1"),
        ):
            with self.subTest(old=old):
                self.assertFalse(
                    match_evidence.report_matches(report.replace(old, new), self.root, scan.OWNER)
                )

    def test_four_live_producers_and_hblank_dma(self):
        game = Manager(self.rom)
        game.tick()
        self.assertEqual(game.callbacks, [])
        win0 = game.call(0x0800F9C0, 0, 11, 39)
        win1 = game.call(0x0800F9C0, 1, 14, 27)
        command, state, colors = 0x02026000, 0x02026100, 0x02026200
        game.write_word(command + 4, colors)
        game.write_half(command + 20, 23)
        game.cpu.mem_write(colors, struct.pack("<160H", *(23 + i * i for i in range(160))))
        game.call(0x080D9BCC, 0, command, state)
        palette = game.word(state + 4)
        scroll = game.call(0x0800CE08, 0, 123, 0x0400001E)
        tasks = [win0, win1, palette, scroll]
        targets = [0x04000040, 0x04000042, 0x0500002E, 0x0400001E]
        self.assertEqual([game.word(game.slots + 4 * i) for i in range(4)], tasks)
        self.assertEqual(game.call(0x0800C3CC, 0, 0, 2, 0x04000000), 0)
        for generation, bank_field in enumerate((28, 24)):
            if generation:
                for task in tasks:
                    game.call(0x0800C64C, task)
            game.tick()
            game.call(0x080008E0)
            for index, (task, target) in enumerate(zip(tasks, targets)):
                bank = game.word(task + bank_field)
                self.assertEqual(
                    game.callbacks[generation * 4 + index], (game.word(task + 20), bank, game.word(task))
                )
                self.assertEqual(game.half(task + 14), 1 - generation)
                self.assertEqual(game.half(task + 12), 0)
                self.assertEqual(game.half(bank), game.half(bank + 320))
                self.assertEqual(game.half(game.slots + 16 + 2 * index), index)
                for address in (0x03002BD0 + 16 * index, 0x040000B0 + 12 * index):
                    self.assertEqual(
                        [game.word(address + o) for o in (0, 4, 8)], [bank + 2, target, 0xA2600001]
                    )
            self.assertEqual(
                [game.half(a) for a in (0x0300097A, 0x0300097C, 0x03003860, 0x03000958)],
                [11 * 256 + 39, 14 * 256 + 27, 23, 123],
            )
        self.assertEqual(len(game.callbacks), 8)

    def test_destination_edges_and_refused_dma(self):
        # These constructor API witnesses exercise the manager's original guards. The separate
        # integration case above supplies destinations from reached game producer routines.
        endpoints = (
            (0x04000000, 0x03000940),
            (0x04000006, None),
            (0x04000008, 0x03000942),
            (0x04000052, 0x0300098C),
            (0x04000054, None),
            (0x04FFFFFE, None),
            (0x05000000, 0x03003860),
            (0x050003FE, 0x03003860),
            (0x05000400, None),
        )
        for target, shadow in endpoints:
            with self.subTest(target=hex(target)):
                game = Manager(self.rom)
                task = game.call(0x0800C3CC, 0, 0, 2, target)
                game.write_half(game.word(task + 24), 0xABCD)
                game.tick()
                self.assertEqual(
                    (game.half(task + 14), game.half(game.slots + 16), game.callbacks), (0, 0, [])
                )
                physical = bytearray(80)
                if shadow and shadow != 0x03003860:
                    struct.pack_into("<H", physical, shadow - 0x03000940, 0xABCD)
                self.assertEqual(game.read(0x03000940, 80), physical)
                self.assertEqual(game.half(0x03003860), 0xABCD if shadow == 0x03003860 else 0)
        for unavailable in (False, True):
            game = Manager(self.rom)
            task = game.call(0x0800F9C0, 0, 8, 19)
            if unavailable:
                for i in range(4):
                    game.write_half(0x03002BC0 + 2 * i, 1)
            else:
                game.call(0x0800C6C0, task)
            game.tick()
            self.assertEqual(len(game.callbacks), int(unavailable))
            self.assertEqual(game.half(task + 14), int(unavailable))
            self.assertEqual(game.half(game.slots + 16), 0xFFFF)
            self.assertEqual(game.half(0x0300097A), 0)

    def test_register_copy_uses_start_and_not_the_end_of_the_lcd_block(self):
        # The manager's address test only checks the first destination. This out-of-contract
        # constructor request documents the necessary width premise, not a reached scene input.
        game = Manager(self.rom)
        task = game.call(0x0800C3CC, 0, 0, 16, 0x04000052)
        data = bytes(range(1, 17))
        game.cpu.mem_write(game.word(task + 24), data)
        game.tick()
        self.assertEqual(game.read(0x0300098C, 16), data)
        self.assertEqual(game.read(0x03000990, 12), data[4:])

    def test_wave_and_interleaved_plane_callbacks(self):
        waves = (0x0800DDB1, 0x0800DDBD, 0x0800DDDD, 0x0800DE15, 0x0800DE21, 0x0800DE41)
        planes = (0x0800DE65, 0x0800DE71, 0x0800D325)
        for mode, callback in zip((0, 1, 2, 128, 129, 130, 0, 1, 2), waves + planes):
            game = Manager(self.rom)
            if callback in waves:
                task = game.call(0x0800CC8C, mode, 0, 0, 0, 23, 0, 0x04000010)
            else:
                task = game.call(0x0800CE08, mode, 23, 0x04000010)
            stride = 2 << (mode & 127)
            bank = game.word(task + 28)
            game.tick()
            self.assertEqual(game.callbacks, [(game.word(task + 20), bank, callback)])
            self.assertEqual(game.half(task + 18), stride)
            self.assertEqual(game.read(bank, 161 * stride), struct.pack("<H", 23) * (161 * stride // 2))
            self.assertEqual(game.read(0x0300094A, stride), struct.pack("<H", 23) * (stride // 2))

    def test_affine_and_window_script_callbacks(self):
        for bg in (2, 3):
            game = Manager(self.rom)
            command, state, record = 0x02026000, 0x02026100, 0x02026200
            game.write_half(command + 20, bg)
            game.write_word(command + 4, record)
            game.cpu.mem_write(record, struct.pack("<iihhhhHxx", 512, 2560, 1, 2, 256, 512, 0))
            game.call(0x080D963C, 0, command, state)
            task = game.word(state + 4)
            game.tick()
            bank = game.word(task + 28)
            self.assertEqual(game.callbacks, [(game.word(task + 20), bank, 0x080D9BC1)])
            target = 0x04000020 + (bg - 2) * 16
            self.assertEqual(game.word(task + 4), target)
            self.assertEqual(game.half(task + 18), 16)
            for row in range(161):
                self.assertEqual(
                    game.read(bank + row * 16, 16),
                    struct.pack("<hhhhii", 256, 0, 0, 512, 256, 1536 + (row % 160) * 256),
                )
            self.assertEqual(game.read(0x03000942 + target - 0x04000008, 16), game.read(bank, 16))
        game = Manager(self.rom)
        game.write_half(command + 20, 1)
        game.write_half(command + 22, 17)
        game.write_half(command + 24, 35)
        game.call(0x080D9C58, 0, command, state)
        task = game.word(state + 4)
        game.tick()
        bank = game.word(task + 28)
        self.assertEqual(game.callbacks, [(game.word(task + 20), bank, 0x080DAE71)])
        self.assertEqual(game.read(bank, 322), bytes((35, 17)) * 161)
        self.assertEqual(game.read(0x0300097C, 2), bytes((35, 17)))
        game = Manager(self.rom)
        task = game.call(0x0800D61C, 3, 9)
        game.tick()
        self.assertEqual(game.callbacks, [(game.word(task + 20), game.word(task + 28), 0x0800DEC1)])
        self.assertEqual(game.read(0x0300098C, 2), game.read(game.word(task + 28), 2))


class Manager:
    """Execute the original manager, initializer/allocator, task producers, callbacks and DMA code."""

    slots = 0x02009148
    sp, stop = 0x03007B00, 0x080000C0

    def __init__(self, rom):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_INTR, UC_HOOK_CODE
        from unicorn.arm_const import UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3

        self.regs = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
        self.cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        for address, size in (
            (scan.BASE, len(rom)),
            (0x02000000, 0x40000),
            (0x03000000, 0x8000),
            (0x04000000, 0x1000),
            (0x05000000, 0x1000),
        ):
            self.cpu.mem_map(address, size)
        self.cpu.mem_write(scan.BASE, rom)
        self.cpu.mem_write(0x03005E78, rom[0xA38A2C : 0xA38A2C + 176])
        self.callbacks = []
        self.cpu.hook_add(UC_HOOK_CODE, self.callback_site, begin=0x0800C50E, end=0x0800C50E)
        self.cpu.hook_add(UC_HOOK_INTR, self.cpuset)
        heap = self.call(0x080070C8, 0x02018000, 0x6000)
        self.call(0x0800C6CC, heap)
        assert self.read(self.slots, 24) == bytes(16) + b"\xff" * 8

    def callback_site(self, cpu, address, size, user):
        self.callbacks.append(tuple(cpu.reg_read(reg) for reg in self.regs[:3]))

    def cpuset(self, cpu, interrupt, user):
        from unicorn.arm_const import UC_ARM_REG_PC

        swi = self.half(cpu.reg_read(UC_ARM_REG_PC) - 2)
        source, dest, count = (cpu.reg_read(reg) for reg in self.regs[:3])
        if swi == 0xDF0E:
            # Exactly the zero-angle records supplied by the affine script fixture.
            assert count == 160 and source % 4 == dest % 4 == 0
            for i in range(count):
                x, y, px, py, sx, sy, angle = struct.unpack("<iihhhhHxx", self.read(source + i * 20, 20))
                assert angle == 0
                cpu.mem_write(dest + i * 16, struct.pack("<hhhhii", sx, 0, 0, sy, x - sx * px, y - sy * py))
            return
        assert swi == 0xDF0B and 0 < count <= 160 and source % 2 == dest % 2 == 0
        cpu.mem_write(dest, self.read(source, 2 * count))

    def read(self, address, size):
        return bytes(self.cpu.mem_read(address, size))

    def word(self, address):
        return int.from_bytes(self.read(address, 4), "little")

    def half(self, address):
        return int.from_bytes(self.read(address, 2), "little")

    def write_word(self, address, value):
        self.cpu.mem_write(address, struct.pack("<I", value))

    def write_half(self, address, value):
        self.cpu.mem_write(address, struct.pack("<H", value))

    def call(self, entry, *args):
        from unicorn.arm_const import UC_ARM_REG_SP, UC_ARM_REG_LR, UC_ARM_REG_PC

        for register, value in zip(self.regs, args):
            self.cpu.reg_write(register, value)
        for index, value in enumerate(args[4:]):
            self.write_word(self.sp + 4 * index, value)
        self.cpu.reg_write(UC_ARM_REG_LR, self.stop | 1)
        self.cpu.reg_write(UC_ARM_REG_SP, self.sp)
        self.cpu.emu_start(entry | 1, self.stop, count=800000)
        assert self.cpu.reg_read(UC_ARM_REG_PC) == self.stop and self.cpu.reg_read(UC_ARM_REG_SP) == self.sp
        return self.cpu.reg_read(self.regs[0])

    def tick(self):
        self.call(scan.OWNER)
