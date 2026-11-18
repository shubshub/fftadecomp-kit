"""Compiler, stack initialization, original compaction and RNG evidence for 08128E40."""

import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import active_entry_shuffle_profile as shuffle
import match
import match_evidence
import owner_admission_profile as owner
import signed_divmod_profile as driver


@unittest.skipUnless(
    os.environ.get("FFTA_ACTIVE_SHUFFLE_ROOT"),
    "requires recovered USA game tables and source",
)
class ActiveShuffle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        game = Path(os.environ["FFTA_ACTIVE_SHUFFLE_ROOT"]).resolve()
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        cls.game = Path(tmp.name)
        for item in ("include", "config", "symbols", "baserom.bin"):
            (cls.game / item).symlink_to(game / item)
        (cls.game / "src").mkdir()
        cls.src = cls.game / "src/08128E40.c"
        cls.src.write_bytes((game / "src/08128E40.c").read_bytes())
        cls.rom = (game / "baserom.bin").read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(game)
        cls.index = owner.index_snapshot(game)
        cls.objects = match_evidence.data_snapshot(game)
        cls.result = driver.build(cls.game, shuffle.ADDRESS, selector=shuffle.SELECTOR)

    def test_canonical_cli_source_and_report_mutations(self):
        cmd = [
            sys.executable,
            str(TOOLS / "match.py"),
            "--root",
            str(self.game),
            "08128E40",
        ]

        def run(*args):
            return subprocess.run([*cmd, *args], capture_output=True, text=True)

        self.assertNotEqual(run().returncode, 0)
        args = ("--signed-runtime-profile", shuffle.SELECTOR)
        mixed = run(
            *args, "--owner-runtime-profile", "named-data-buffer-stack-index-v2"
        )
        self.assertNotEqual(mixed.returncode, 0)
        self.assertIn("isolated ordinary Thumb selector", mixed.stderr)
        hit = run(*args)
        self.assertEqual(hit.returncode, 0, hit.stderr)
        r = (self.game / "docs/match/08128E40.md").read_text()
        replay = lambda source: match_evidence.report_matches(
            source, str(self.game), shuffle.ADDRESS
        )
        self.assertTrue(replay(r))
        self.assertIn("160/160 bytes", r)
        for old, new in [
            ('"passes":4', '"passes":3'),
            ('"divisors":[1,20]', '"divisors":[0,20]'),
            ('"selection_count":"min', '"selection_count":"max'),
        ]:
            self.assertIn(old, r)
            self.assertFalse(replay(r.replace(old, new)))
        orig = self.src.read_text()
        try:
            self.src.write_text(
                "int __modsi3(int,int);\n"
                + orig.replace(
                    "(s16)func_08002804() % total",
                    "__modsi3((s16)func_08002804(), total)",
                )
            )
            self.assertFalse(replay(r))
            bad = run(*args)
            self.assertNotEqual(bad.returncode, 0)
            self.assertIn("reserved for compiler emission", bad.stderr)
        finally:
            self.src.write_text(orig)

    def test_real_elf_relocations_and_symbol_roles(self):
        orig = match.elf_image(self.result["original_elf"])

        def bindings(image, address=shuffle.ADDRESS):
            return owner.original_bindings(
                image,
                address,
                self.rom,
                self.mapping,
                self.objects,
                selector=shuffle.SELECTOR,
                index=self.index,
            )

        self.assertEqual(bindings(orig), (shuffle.BINDINGS, shuffle.TARGETS))
        with self.assertRaises(ValueError):
            bindings(orig, 0x08128EE0)
        for change in (
            "object",
            "manual-mod",
            "data-addend",
            "wrong-role",
            "call-addend",
            "visibility",
            "size",
        ):
            image = copy.deepcopy(orig)
            table, syms = next(iter(image["symbol_tables"].items()))
            idx = next(i for i, s in enumerate(syms) if s["name"] == "__modsi3")
            if change == "object":
                image["type"] = 2
            elif change == "manual-mod":
                syms[idx]["name"] = "func_08142950"
            elif change == "visibility":
                raw = bytearray(image["section_data"][table])
                raw[16 * idx + 13] = 2
                image["section_data"][table] = bytes(raw)
            elif change == "size":
                syms[idx]["size"] = 2
            elif change == "wrong-role":
                section = image["relocations"][0]
                raw = bytearray(image["section_data"][section])
                raw[4] = 2
                image["section_data"][section] = bytes(raw)
            else:
                raw = bytearray(image["text"])
                raw[0x98 if change == "data-addend" else 0x46] ^= 1
                image["text"] = bytes(raw)
            with self.subTest(change=change), self.assertRaises(ValueError):
                bindings(image)

    def test_scan_swap_count_stack_and_native_dependencies(self):
        for site, word in [
            (0x08128E46, 0xB084),
            (0x08128E5A, 0xD103),
            (0x08128E60, 0x8004),
            (0x08128E62, 0x3502),
            (0x08128E68, 0x2C14),
            (0x08128E6E, 0xD12C),
            (0x08128E82, 0x0C00),
            (0x08128E84, 0x1C21),
            (0x08128E90, 0x194A),
            (0x08128E98, 0x8010),
            (0x08128EA4, 0x2804),
            (0x08128EAA, 0xDD01),
            (0x08128EBA, 0x8800),
            (0x08128ECA, 0xB004),
            (0x08002814, 0x1000),
            (0x08142950, 0x46C0),
            (0x08038686, 0x6001),
            (0x080CC2CA, 0x2A14),
        ]:
            rom = bytearray(self.rom)
            off = site - shuffle.BASE
            self.assertNotEqual(struct.unpack_from("<H", rom, off)[0], word)
            struct.pack_into("<H", rom, off, word)
            body = bytes(
                rom[shuffle.ADDRESS - shuffle.BASE : shuffle.END - shuffle.BASE]
            )
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                shuffle.prove(
                    body,
                    shuffle.ADDRESS,
                    bytes(rom),
                    self.mapping,
                    self.index,
                    self.objects,
                    shuffle.BINDINGS,
                )
        objects = json.loads(self.objects)
        objects["g_state_030034B0"] = "0x030034B4"
        with self.assertRaises(ValueError):
            shuffle.prove(
                self.result["body"],
                shuffle.ADDRESS,
                self.rom,
                self.mapping,
                self.index,
                json.dumps(objects).encode(),
                shuffle.BINDINGS,
            )

    def test_original_cpu_prefix_and_full_table_effects(self):
        from unicorn import (
            Uc,
            UC_MODE_THUMB,
            UC_ARCH_ARM,
            UC_HOOK_CODE,
            UC_HOOK_MEM_READ,
            UC_HOOK_MEM_WRITE,
            UC_MEM_WRITE,
        )
        from unicorn import arm_const as arm

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(shuffle.BASE, len(self.rom))
        cpu.mem_write(shuffle.BASE, self.rom)
        cpu.mem_map(shuffle.STATE, 0x4000)
        cpu.mem_map(0x03000000, 0x8000)
        sp, stop, rng = 0x03007800, 0x03007F00, 0x030034B0
        bottom = sp - 44
        selected, local, entries_access = [], [], []

        def code(uc, pc, size, _):
            selected.append(
                (pc, uc.reg_read(arm.UC_ARM_REG_R0), uc.reg_read(arm.UC_ARM_REG_R1))
            )

        for entry in (shuffle.RNG, shuffle.REMAINDER, shuffle.CLEAR, shuffle.COMPACT):
            cpu.hook_add(UC_HOOK_CODE, code, begin=entry, end=entry)

        def track_local(uc, mode, addr, size, value, _):
            local.append(
                (
                    uc.reg_read(arm.UC_ARM_REG_PC) - shuffle.ADDRESS,
                    mode == UC_MEM_WRITE,
                    addr - bottom,
                    size,
                )
            )

        cpu.hook_add(
            UC_HOOK_MEM_WRITE | UC_HOOK_MEM_READ,
            track_local,
            begin=bottom,
            end=bottom + 19,
        )

        def table(uc, mode, addr, size, value, _):
            entries_access.append((addr - shuffle.ENTRIES, size))

        cpu.hook_add(
            UC_HOOK_MEM_WRITE | UC_HOOK_MEM_READ,
            table,
            begin=shuffle.ENTRIES - 4,
            end=shuffle.ENTRIES + 43,
        )
        preserved = [getattr(arm, f"UC_ARM_REG_R{i}") for i in range(4, 12)]
        saved = [0xBA000004 + i for i in range(8)]
        choices = [(3 + 7 * i) % 20 for i in range(20)]
        for total in range(21):
            for requested in sorted(
                {0, 1, max(0, total - 1), total, min(255, total + 1), 255}
            ):
                active = sorted(choices[:total])
                before = [(0x3100 + i if i in active else 0) for i in range(20)]
                state = (0xFFFFFFFF ^ ((requested + 1) * (total + 7))) & 0xFFFFFFFF
                cpu.mem_write(rng, struct.pack("<I", state))
                cpu.mem_write(
                    shuffle.ENTRIES - 4,
                    b"BEGN" + struct.pack("<20H", *before) + b"END!",
                )
                cpu.mem_write(bottom, b"\xcd" * 20)
                cpu.mem_write(sp, b"protected")
                cpu.reg_write(arm.UC_ARM_REG_SP, sp)
                cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
                cpu.reg_write(arm.UC_ARM_REG_R0, 0xB0000000 | requested)
                for reg, value in zip(preserved, saved):
                    cpu.reg_write(reg, value)
                selected.clear()
                local.clear()
                entries_access.clear()
                cpu.emu_start(shuffle.ADDRESS | 1, stop, count=100000)
                numerators = []
                trace = [(0x20, True, i, 1) for i in range(total)]
                for _ in range(4):
                    for i in range(total):
                        state = (state * 0x41C64E6D + 0x3039) & 0xFFFFFFFF
                        n = (state >> 16) & 0x7FFF
                        numerators.append(n)
                        j = n % total
                        if i != j:
                            trace.extend(
                                (
                                    (0x52, False, i, 1),
                                    (0x56, False, j, 1),
                                    (0x58, True, i, 1),
                                    (0x5A, True, j, 1),
                                )
                            )
                            active[i], active[j] = active[j], active[i]
                removed = active[:requested]
                trace.extend((0x7A, False, i, 1) for i in range(len(removed)))
                self.assertEqual(local, trace)
                self.assertEqual(
                    [item[1:] for item in selected if item[0] == shuffle.REMAINDER],
                    [(n, total) for n in numerators],
                )
                self.assertEqual(
                    sum(item[0] == shuffle.RNG for item in selected), 4 * total
                )
                self.assertEqual(
                    [item[1] for item in selected if item[0] == shuffle.CLEAR], removed
                )
                self.assertEqual(
                    sum(item[0] == shuffle.COMPACT for item in selected), int(total > 0)
                )
                after = [
                    value
                    for i, value in enumerate(before)
                    if value and i not in removed
                ]
                self.assertEqual(
                    cpu.mem_read(shuffle.ENTRIES - 4, 48),
                    b"BEGN"
                    + struct.pack("<20H", *(after + [0] * (20 - len(after))))
                    + b"END!",
                )
                self.assertTrue(
                    all(
                        0 <= off < 40 and off % 2 == 0 and wid == 2
                        for off, wid in entries_access
                    )
                )
                self.assertEqual(
                    cpu.mem_read(bottom + total, 20 - total), b"\xcd" * (20 - total)
                )
                self.assertEqual(cpu.mem_read(rng, 4), struct.pack("<I", state))
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
                self.assertEqual([cpu.reg_read(reg) for reg in preserved], saved)
                self.assertEqual(cpu.mem_read(sp, 9), b"protected")
