"""ROM execution, original ELF and adverse replay checks for template selection."""

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
import active_entry_selection_profile as select
import match
import match_evidence
import owner_admission_profile as owner
import signed_divmod_profile as driver


@unittest.skipUnless(
    os.environ.get("FFTA_ACTIVE_SELECTION_ROOT"),
    "requires recovered USA game and source",
)
class ActiveSelection(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(os.environ["FFTA_ACTIVE_SELECTION_ROOT"])
        temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(temporary.cleanup)
        cls.game = Path(temporary.name)
        for directory in ("include", "config", "symbols", "baserom.bin"):
            (cls.game / directory).symlink_to(root / directory)
        (cls.game / "src").mkdir()
        cls.source = cls.game / "src/08128EE0.c"
        cls.source.write_bytes((root / "src/08128EE0.c").read_bytes())
        cls.rom = (root / "baserom.bin").read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(root)
        cls.index = owner.index_snapshot(root)
        cls.objects = match_evidence.data_snapshot(root)
        cls.built = driver.build(cls.game, select.ADDRESS, selector=select.SELECTOR)

    def test_report_source_and_mode_isolation(self):
        def issue(*args):
            return subprocess.run(
                [
                    sys.executable,
                    str(TOOLS / "match.py"),
                    "--root",
                    str(self.game),
                    "08128EE0",
                    *args,
                ],
                text=True,
                capture_output=True,
            )

        self.assertNotEqual(issue().returncode, 0)
        flag = ("--signed-runtime-profile", select.SELECTOR)
        self.assertNotEqual(
            issue(
                *flag, "--owner-runtime-profile", "named-data-buffer-stack-index-v2"
            ).returncode,
            0,
        )
        self.assertNotEqual(
            issue("--signed-runtime-profile", select.prefix.SELECTOR).returncode, 0
        )
        result = issue(*flag)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = (self.game / "docs/match/08128EE0.md").read_text()

        def replay(r):
            return match_evidence.report_matches(r, str(self.game), select.ADDRESS)

        self.assertTrue(replay(report))
        self.assertIn("228/228 bytes", report)
        for old, new in [
            ('"minimum_initial":99', '"minimum_initial":255'),
            ('"tie":"last', '"tie":"first'),
            ('"minimum_no_qualifier_slot":0', '"minimum_no_qualifier_slot":1'),
        ]:
            self.assertIn(old, report)
            self.assertFalse(replay(report.replace(old, new)))
        src = self.source.read_text()
        try:
            self.source.write_text(
                "int __modsi3(int,int);\n"
                + src.replace(
                    "(s16)func_08002804() % count",
                    "__modsi3((s16)func_08002804(),count)",
                )
            )
            self.assertFalse(replay(report))
            self.assertIn("reserved for compiler emission", issue(*flag).stderr)
        finally:
            self.source.write_text(src)

    def test_original_elf_data_addends_symbols_and_calls(self):
        original = match.elf_image(self.built["original_elf"])

        def bind(image, address=select.ADDRESS):
            return owner.original_bindings(
                image,
                address,
                self.rom,
                self.mapping,
                self.objects,
                selector=select.SELECTOR,
                index=self.index,
            )

        self.assertEqual(bind(original), (select.BINDINGS, select.TARGETS))
        for mutation in (
            "wrong-owner",
            "ET_EXEC",
            "bad-addend",
            "zero-addend",
            "call-addend",
            "symbol-type",
            "hidden",
            "nonzero-size",
            "different-base",
            "wrong-kind",
        ):
            image = copy.deepcopy(original)
            table, syms = next(iter(image["symbol_tables"].items()))
            n = next(i for i, s in enumerate(syms) if s["name"] == "g_state_02000000")
            where = select.ADDRESS
            if mutation == "wrong-owner":
                where -= 160
            elif mutation == "ET_EXEC":
                image["type"] = 2
            elif mutation == "symbol-type":
                syms[n]["type"] = 1
            elif mutation == "nonzero-size":
                syms[n]["size"] = 4
            elif mutation == "hidden":
                raw = bytearray(image["section_data"][table])
                raw[n * 16 + 13] = 2
                image["section_data"][table] = bytes(raw)
            elif mutation in ("wrong-kind", "different-base"):
                section = image["relocations"][0]
                raw = bytearray(image["section_data"][section])
                for at in range(0, len(raw), 8):
                    site, info = struct.unpack_from("<II", raw, at)
                    if site == 0xA8:
                        entry = next(
                            i
                            for i, s in enumerate(syms)
                            if s["name"] == "data_02002E78"
                        )
                        info = (
                            (entry << 8 | 2)
                            if mutation == "different-base"
                            else (info & ~255) | 10
                        )
                        struct.pack_into("<I", raw, at + 4, info)
                        break
                image["section_data"][section] = bytes(raw)
            else:
                raw = bytearray(image["text"])
                if mutation == "call-addend":
                    raw[0x76] ^= 1
                else:
                    struct.pack_into(
                        "<I", raw, 0xA8, 0x2E7C if mutation == "bad-addend" else 0
                    )
                image["text"] = bytes(raw)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                bind(image, where)

    def test_changed_owner_callees_and_selected_table_rows(self):
        def prove(rom, objects):
            body = rom[select.ADDRESS - select.BASE : select.END - select.BASE]
            return select.prove(
                body,
                select.ADDRESS,
                rom,
                self.mapping,
                self.index,
                objects,
                select.BINDINGS,
            )

        # Include the count guard, local element size, field offset, unsigned
        # ties, fallback slot, seed, modulo, clear and lookup output.
        for address in (
            select.ADDRESS + 2,
            select.ADDRESS + 8,
            select.ADDRESS + 0x22,
            select.ADDRESS + 0x2C,
            select.ADDRESS + 0x34,
            select.ADDRESS + 0x3A,
            select.ADDRESS + 0x58,
            select.ADDRESS + 0x70,
            select.ADDRESS + 0x7C,
            select.ADDRESS + 0x98,
            select.ADDRESS + 0xA8,
            select.ADDRESS + 0xBE,
            select.ADDRESS + 0xE0,
            select.prefix.RNG + 0xC,
            select.prefix.REMAINDER + 2,
            select.CLEAR + 0x2A,
            select.NAME + 0x10,
            select.stats.LOOKUP + 0x100,
            select.UNIT_IDS + 2,
            select.RECORDS + 52 * 44 + 5,
            select.RECORDS + 52 * 47,
            select.NAMES + 18 * 4,
            select.TEXT + 0xBA0,
        ):
            rom = bytearray(self.rom)
            rom[address - select.BASE] ^= 1
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                prove(bytes(rom), self.objects)
        objects = json.loads(self.objects)
        objects["data_02002E78"] = "0x02002E7C"
        with self.assertRaises(ValueError):
            prove(self.rom, json.dumps(objects).encode())

    def test_native_collector_selection_clears_and_real_return(self):
        from unicorn import (
            Uc,
            UC_ARCH_ARM,
            UC_MODE_THUMB,
            UC_HOOK_CODE,
            UC_HOOK_MEM_READ,
            UC_HOOK_MEM_WRITE,
            UC_MEM_WRITE,
        )
        from unicorn import arm_const as arm

        cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        cpu.mem_map(select.BASE, len(self.rom))
        cpu.mem_write(select.BASE, self.rom)
        cpu.mem_map(0x02000000, 0x5000)
        cpu.mem_map(0x03000000, 0x8000)
        sp, stop, seed_address = 0x03007800, 0x03007F00, 0x030034B0
        local = sp - 40
        calls, local_access, stores = [], [], []

        def call(uc, pc, size, _):
            calls.append(
                (
                    pc,
                    uc.reg_read(arm.UC_ARM_REG_R0),
                    uc.reg_read(arm.UC_ARM_REG_R1),
                    uc.reg_read(arm.UC_ARM_REG_R2),
                )
            )

        for pc in (
            select.prefix.RNG,
            select.prefix.REMAINDER,
            select.CLEAR,
            select.NAME,
            select.stats.LOOKUP,
        ):
            cpu.hook_add(UC_HOOK_CODE, call, begin=pc, end=pc)

        def track_local(uc, operation, address, size, value, _):
            local_access.append(
                (
                    uc.reg_read(arm.UC_ARM_REG_PC) - select.ADDRESS,
                    operation == UC_MEM_WRITE,
                    address - local,
                    size,
                )
            )

        def track_store(uc, operation, address, size, value, _):
            stores.append((address - select.TEMPLATES, size, value))

        cpu.hook_add(
            UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE,
            track_local,
            begin=local,
            end=local + 19,
        )
        cpu.hook_add(
            UC_HOOK_MEM_WRITE,
            track_store,
            begin=select.TEMPLATES - 4,
            end=select.TEMPLATES + 324,
        )
        saved = [getattr(arm, f"UC_ARM_REG_R{n}") for n in range(4, 12)]
        reg_values = list(range(0x23000004, 0x2300000C))

        def execute(active, appearances, mode, seed):
            active = sorted(active)
            before = bytearray()
            for i, appearance in enumerate(appearances):
                # Names exercise presence in each of the four individual packed bytes.
                name = (1 << (8 * (i % 4))) if i in active else 0
                before.extend(
                    struct.pack("<IBB", name, 0xCD, appearance)
                    + bytes([0xF0 + i % 13]) * 10
                )
            cpu.mem_write(select.TEMPLATES - 4, b"BEGN" + before + b"END!")
            cpu.mem_write(local, b"\xcd" * 20)
            cpu.mem_write(sp, b"protected")
            cpu.mem_write(seed_address, struct.pack("<I", seed))
            cpu.reg_write(arm.UC_ARM_REG_R0, 0x90000000 | mode)
            cpu.reg_write(arm.UC_ARM_REG_LR, stop | 1)
            cpu.reg_write(arm.UC_ARM_REG_SP, sp)
            for reg, value in zip(saved, reg_values):
                cpu.reg_write(reg, value)
            calls.clear()
            local_access.clear()
            stores.clear()
            cpu.emu_start(select.ADDRESS | 1, stop, count=8000)
            expected = before.copy()
            trace = [(0x2C, True, i, 1) for i in range(len(active))]
            expected_calls = []
            if active:
                if mode == 2:
                    seed = (seed * 0x41C64E6D + 0x3039) & 0xFFFFFFFF
                    dividend = (seed >> 16) & 0x7FFF
                    ordinal = dividend % len(active)
                    chosen = active[ordinal]
                    trace.append((0x7C, False, ordinal, 1))
                    expected_calls.extend([select.prefix.RNG, select.prefix.REMAINDER])
                    self.assertEqual(calls[1][1:3], (dividend, len(active)))
                else:
                    if mode == 3:
                        bound = max(appearances[i] for i in active)
                        chosen = max(i for i in active if appearances[i] == bound)
                    else:
                        qualifying = [i for i in active if appearances[i] <= 99]
                        chosen = max(
                            (
                                i
                                for i in qualifying
                                if appearances[i]
                                == min(appearances[j] for j in qualifying)
                            ),
                            default=0,
                        )
                    trace.extend(
                        (0x8E if mode == 3 else 0xB0, False, i, 1)
                        for i in range(len(active))
                    )
                offsets = [0, 1, 2, 3, *range(5, 16)]
                for offset in offsets:
                    expected[chosen * 16 + offset] = 0
                self.assertEqual(stores, [(chosen * 16 + off, 1, 0) for off in offsets])
                expected_calls.extend([select.CLEAR, select.NAME, select.stats.LOOKUP])
                self.assertEqual(
                    [row[1] for row in calls if row[0] in (select.CLEAR, select.NAME)],
                    [chosen, chosen],
                )
                unit = self.rom[select.UNIT_IDS - select.BASE + chosen]
                self.assertEqual(calls[-1][1:], (unit, unit, 0))
                record = select.RECORDS - select.BASE + 52 * unit
                self.assertEqual(self.rom[record + 5], 0)
                key = struct.unpack_from("<H", self.rom, record)[0]
                value = struct.unpack_from(
                    "<I", self.rom, select.NAMES - select.BASE + 4 * key
                )[0]
            else:
                self.assertEqual(stores, [])
                value = 0x085566C4
            self.assertEqual([row[0] for row in calls], expected_calls)
            self.assertEqual(local_access, trace)
            self.assertEqual(
                cpu.mem_read(local + len(active), 20 - len(active)),
                b"\xcd" * (20 - len(active)),
            )
            self.assertEqual(
                cpu.mem_read(select.TEMPLATES - 4, 328), b"BEGN" + expected + b"END!"
            )
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R0), value)
            self.assertEqual(cpu.mem_read(seed_address, 4), struct.pack("<I", seed))
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), stop)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), sp)
            self.assertEqual(cpu.mem_read(sp, 9), b"protected")
            self.assertEqual([cpu.reg_read(reg) for reg in saved], reg_values)

        slots = [(3 + 7 * i) % 20 for i in range(20)]
        for length in range(21):
            active = slots[:length]
            for mode in (0, 2, 3, 255):
                execute(active, [0, 8, 99, 100, 255] * 4, mode, 0x43350000 + length)
        for i in range(20):
            execute([i], [0] * 20, 3, 0)
        execute([3, 8, 18], [255] * 20, 1, 0)
        execute([3, 8, 18], [99] * 20, 1, 0)
        execute([3, 8, 18], [0] * 20, 3, 0)
