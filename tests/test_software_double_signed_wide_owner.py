"""Signed 64-bit conversion, its original compiler member, and the binary64 ABI."""

import copy
from contextlib import redirect_stdout
import hashlib
import io
import os
from pathlib import Path
import random
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

import test_software_double_profile as fixture
from test_unit_double_add_parts import OriginalCPU

match, profile = fixture.match, fixture.profile
START, END, COUNT, SHA = profile.SIGNED_WIDE_TO_DOUBLE_OWNER
NAMES = profile.SIGNED_WIDE_TO_DOUBLE_BINDINGS
SOURCE = """double func_081428E4(long long value)
{
    double result = (int)(value >> 32);
    result *= 65536;
    result *= 65536;
    result += (unsigned int)value;
    return result;
}
"""


class SignedWideToDoubleTests(unittest.TestCase):
    setUpClass = classmethod(fixture.SoftwareDoubleTests.setUpClass.__func__)
    setUp = fixture.SoftwareDoubleTests.setUp
    indexes = fixture.SoftwareDoubleTests.indexes

    def test_canonical_report_and_generated_calls(self):
        self.indexes(2, 1)
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_bytes(self.index)
        source = self.root / "src/081428E4.c"
        source.write_text(SOURCE)
        body = self.runtime_rom[START-fixture.BASE:END-fixture.BASE]
        self.assertEqual(hashlib.sha256(body).hexdigest(), SHA)
        calls = {site: profile.OPERATIONS[name] for site, name in NAMES.items()}
        instructions = match.verify_leaf_instructions(body, START, True, calls,
            double_context=(self.runtime_rom, self.mapping, self.index, NAMES))
        self.assertEqual(len(instructions), COUNT)
        for lo, hi in ((START+2, END), (START, END-2)):
            with self.assertRaises(ValueError):
                profile.validate_span(self.runtime_rom[lo-fixture.BASE:hi-fixture.BASE], lo,
                                      self.runtime_rom, self.mapping, self.index)
        for names in (dict(list(NAMES.items())[1:]), {**NAMES, START+10: "__adddf3"}):
            with self.assertRaisesRegex(ValueError, "six original"):
                profile.verify_context(body, START, calls, (self.runtime_rom, self.mapping, self.index, names))
        argv = ["match.py", "--root", str(self.root), "--software-double-profile", profile.SELECTOR,
                f"0x{START:08X}"]
        with patch.object(sys, "argv", argv), patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        report = (self.root / "docs/match/081428E4.md").read_text()
        self.assertIn(f"{END-START}/{END-START} bytes", report)
        self.assertTrue(profile.report_matches(report, self.root, START))
        self.assertFalse(profile.report_matches(report.replace("__muldf3", "__adddf3"), self.root, START))
        source.write_text("#define GLUE(a,b) a ## b\nextern double GLUE(__float,sidf)(int);\n" + SOURCE)
        self.assertFalse(profile.report_matches(report, self.root, START))
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as work:
            _, _, original = match.compile_object(runner, work, self.args, self.root, START, "src/081428E4.c")
            with self.assertRaisesRegex(ValueError, "compiler-generated"):
                profile.object_bytes(runner, work, self.args, original, START,
                                     self.mapping, self.runtime_rom, self.index)

    def test_original_elf_symbol_and_relocation_metadata(self):
        (self.root / "src/081428E4.c").write_text(SOURCE)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as work:
            _, _, original = match.compile_object(runner, work, self.args, self.root, START, "src/081428E4.c")
        profile.signed_wide_relocations(original, START)
        for field, value in (("size", 4), ("type", 2), ("bind", 2), ("section", 1), ("value", 1)):
            image = copy.deepcopy(original)
            next(symbol for symbol in image["symbols"] if symbol["name"] == "__muldf3")[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                profile.signed_wide_relocations(image, START)
        image = copy.deepcopy(original)
        table, = image["symbol_tables"]
        idx = next(i for i, symbol in enumerate(image["symbol_tables"][table]) if symbol["name"] == "__adddf3")
        data = bytearray(image["section_data"][table])
        data[16*idx+13] = 2
        image["section_data"][table] = data
        with self.assertRaises(ValueError):
            profile.signed_wide_relocations(image, START)
        table, = original["relocations"]
        entries = list(struct.iter_unpack("<II", original["section_data"][table]))
        site, target = entries[0]
        for first in ((site+2, target), (entries[1][0], target), (site, entries[1][1]), (site, target & ~255 | 2)):
            image = copy.deepcopy(original)
            image["section_data"][table] = b"".join(struct.pack("<II", *pair) for pair in [first, *entries[1:]])
            with self.subTest(relocation=first), self.assertRaises(ValueError):
                profile.signed_wide_relocations(image, START)

    def test_selected_upstream_member(self):
        cc = Path(os.path.expandvars(match.DEFAULT_CC))
        checkout = Path(os.environ.get("FFTA_AGBCC_SOURCE", cc.parents[1]))
        source = checkout / "libgcc/libgcc2.c"
        old_cc = cc.with_name("old_agbcc")
        if not source.is_file() or not old_cc.is_file():
            self.skipTest("FFTA_AGBCC_SOURCE and old_agbcc are required for the upstream build")
        runner = match.Runner(str(old_cc), root=self.root, timeout=120)
        with runner.workspace() as work:
            location = Path(work)
            for command in ((self.args.cpp, "-undef", "-nostdinc", "-I", checkout / "ginclude", "-DL_floatdidf",
                             source, "-o", location / "f.i"),
                            (old_cc, *self.args.flags.split(), location / "f.i", "-o", location / "f.s"),
                            (self.args.assembler, "-mthumb-interwork", location / "f.s", "-o", location / "f.o")):
                subprocess.run(command, check=True, capture_output=True, timeout=120)
            original = match.elf_image((location / "f.o").read_bytes())
            profile.signed_wide_relocations(original, START)
            targets = {name: profile.OPERATIONS[name] for name in NAMES.values()}
            linked = match.link_typed_targets(runner, work, self.args, "__floatdidf", START, targets, set())
        self.assertEqual(linked["text"], self.runtime_rom[START-fixture.BASE:END-fixture.BASE])
        self.assertEqual(hashlib.sha256(linked["text"]).hexdigest(), SHA)

    def test_original_signed_range_rounding_and_call_abi(self):
        from unicorn import UC_HOOK_CODE
        cpu = OriginalCPU(self, self.runtime_rom)
        lower, upper = -(1 << 63), (1 << 63)-1
        values = {0, -1, 1, lower, lower+1, upper}
        for exponent in range(63):
            boundary = 1 << exponent
            values.update(sign * (boundary + change) for sign in (-1, 1) for change in (-1, 0, 1))
            if exponent >= 53:
                step = 1 << (exponent-52)
                # Both parities of the retained low bit, either side of each halfway tie.
                for offset in (0, step):
                    midpoint = boundary + offset + step//2
                    values.update(sign * (midpoint + change) for sign in (-1, 1) for change in (-1, 0, 1))
        rng = random.Random(START)
        values.update(rng.randint(lower, upper) for _ in range(256))
        visit = []
        def observe(machine, pc, size, name):
            visit.append(name)
        for name in set(NAMES.values()):
            target = profile.OPERATIONS[name]
            cpu.uc.hook_add(UC_HOOK_CODE, observe, user_data=name, begin=target, end=target)
        for value in sorted(values):
            with self.subTest(value=value):
                visit.clear()
                hi, lo = cpu.invoke(START, (value & 0xffffffff, (value >> 32) & 0xffffffff))
                bits, = struct.unpack(">Q", struct.pack(">d", float(value)))
                self.assertEqual((hi << 32) | lo, bits)
                adds = 1 + bool(value & 0x80000000)
                self.assertEqual(visit, ["__floatsidf", "__muldf3", "__muldf3", "__floatsidf"] + ["__adddf3"] * adds)


if __name__ == "__main__":
    unittest.main()
