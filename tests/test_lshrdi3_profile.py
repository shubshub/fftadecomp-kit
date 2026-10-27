"""Pinned lshrdi3: native compiler fixtures and fail-closed runtime evidence.

Only the approved runtime span is read into an in-memory synthetic ROM. No
ROM-derived body or disassembly is checked into the toolkit.
"""

import argparse
import builtins
import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lshrdi3_profile as profile
import match
import match_evidence as evidence
import status
import push

BASE = 0x08000000
SOURCE = """typedef unsigned long long Bits;
extern Bits g_flags;
Bits func_08000000(Bits value, unsigned count)
{
    unsigned n = count & 31;
    Bits a = value >> n;
    Bits b = (value + g_flags) >> (n + 1);
    Bits c = (value ^ g_flags) >> (n + 2);
    return a + b + c;
}
"""
# The algorithm from the local agbcc libgcc2.c L_lshrdi3 implementation. Its
# 32-bit shifts are defined for C's 64-bit shift domain (0 <= count < 64).
REFERENCE = 'typedef unsigned SI;\ntypedef unsigned long long DI;\ntypedef union { DI value; struct { SI low, high; } words; } Split;\nDI func_08144378(DI value, int count)\n{\n    Split input, output;\n    int remaining;\n    if (count == 0)\n        return value;\n    input.value = value;\n    remaining = 32 - count;\n    if (remaining <= 0) {\n        output.words.high = 0;\n        output.words.low = input.words.high >> -remaining;\n    } else {\n        SI carry = input.words.high << remaining;\n        output.words.high = input.words.high >> count;\n        output.words.low = (input.words.low >> count) | carry;\n    }\n    return output.value;\n}\n'


class LogicalRightShiftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = bytearray(profile.END - BASE)
        with cls.rom_path.open("rb") as stream:
            stream.seek(profile.ADDRESS - BASE)
            cls.runtime_rom[profile.ADDRESS - BASE:] = stream.read(profile.END - profile.ADDRESS)

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="lshrdi3_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root),
                                               "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                                       assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                                       linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def indexes(self, size, count):
        entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + size:08X}",
                    "mode": "thumb", "instrs": count},
                   {"rom": f"0x{profile.ADDRESS:08X}", "end": f"0x{profile.END:08X}",
                    "mode": "thumb", "instrs": profile.COUNT},
                   {"rom": "0x08000200", "end": "0x08000202", "mode": "thumb", "instrs": 1}]
        self.mapping = json.dumps(entries).encode()
        self.index = "".join(f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} "
                             f"{int(e['end'], 16) - int(e['rom'], 16)} {e['instrs']} return\n"
                             for e in entries).encode()

    def fixture(self, source=SOURCE, assembly=None):
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            if assembly is None:
                _, _, original = match.compile_object(
                    runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            else:
                text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                        ".global func_08000000\n.type func_08000000, %function\n"
                        ".thumb_func\nfunc_08000000:\n" + assembly +
                        "\n.size func_08000000, . - func_08000000\n")
                path = Path(workspace) / "f.s"
                path.write_text(text)
                subprocess.run([self.args.assembler, "-mthumb-interwork", str(path),
                                "-o", str(Path(workspace) / "f.o")],
                               capture_output=True, check=True, timeout=120)
                original = match.elf_image((Path(workspace) / "f.o").read_bytes())
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            self.indexes(symbol["size"], 1)
            self.objects = json.dumps({"g_flags": "0x02000100"}).encode()
            self.bindings = {}
            self.body, self.calls, self.literals = match.link_calls(
                runner, workspace, self.args, original, BASE, self.mapping,
                len(self.runtime_rom), bytes(self.runtime_rom), data_mapping=self.objects,
                ashldi3_bindings=self.bindings, ashldi3_index=self.index)
            self.original = original
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            ashldi3_context=(self.rom, self.mapping, self.index, self.bindings))
        self.indexes(len(self.body), len(self.instructions))
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_bytes(self.index)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)
        self.manifest = profile.make_manifest(self.calls, BASE, self.bindings, self.literals,
                                              self.objects, self.instructions)

    def verify(self, manifest=None):
        return profile.verify(self.body, BASE, self.rom, self.mapping, self.index, self.objects,
                              self.manifest if manifest is None else manifest)

    def patched_rom(self):
        original_open, original_read = builtins.open, Path.read_bytes
        def open_file(path, mode="r", *args, **kwargs):
            if mode == "rb" and Path(path).resolve() == self.rom_path:
                return io.BytesIO(self.rom)
            return original_open(path, mode, *args, **kwargs)
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        return patch.object(builtins, "open", open_file), patch.object(Path, "read_bytes", read)

    def native_report(self):
        opening, reading = self.patched_rom()
        with opening, reading, patch.object(sys, "argv", ["match.py", "--root", str(self.root),
                                                           "0x08000000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08000000.md").read_text()

    def test_native_split_word_reference_is_the_pinned_returning_runtime(self):
        path = self.root / "src/08144378.c"
        path.write_text(REFERENCE)
        runner = match.Runner(match.DEFAULT_CC, root=self.root)
        with runner.workspace() as workspace:
            obj, text, _ = match.compile_object(runner, workspace, self.args, self.root,
                                               profile.ADDRESS, "src/08144378.c")
            body = match.function_bytes(obj, text, "func_08144378", profile.ADDRESS, True)
        self.assertEqual(body, bytes(self.runtime_rom[profile.ADDRESS - BASE:]))
        self.assertEqual(len(match.verify_leaf_instructions(body, profile.ADDRESS, True)), profile.COUNT)

    def test_natural_shifts_data_and_scalar_frame(self):
        self.fixture()
        self.assertEqual(set(self.bindings.values()), {"__lshrdi3"})
        self.assertEqual(len(self.bindings), 3)
        self.assertTrue(self.manifest["frame"])
        self.assertTrue(self.manifest["data"])
        self.assertEqual(len(self.verify()), len(self.instructions))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)
        simple = "unsigned long long func_08000000(unsigned long long v, unsigned n) { return v >> (n & 63); }"
        self.fixture(simple)
        self.assertFalse(self.manifest["frame"])
        self.verify()

    def test_explicit_runtime_source_aliases_are_rejected_by_fresh_replay(self):
        for alias in ("__lshrdi3", "right_shift"):
            prefix = "#define right_shift __lshrdi3\n" if alias == "right_shift" else ""
            source = prefix + "extern unsigned long long " + alias + "(unsigned long long, unsigned);\n" + \
                "unsigned long long func_08000000(unsigned long long v, unsigned n) { return " + \
                alias + "(v, n & 63); }\n"
            self.fixture(source)
            with self.subTest(alias=alias), self.assertRaisesRegex(SystemExit, "compiler-generated"):
                self.native_report()

    def test_body_mode_counts_bounds_and_both_indexes_are_exact(self):
        self.fixture()
        profile.verify_identity(self.rom, self.mapping, self.index)
        changed = bytearray(self.rom); changed[profile.ADDRESS - BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify_identity(bytes(changed), self.mapping, self.index)
        entries = json.loads(self.mapping)
        for change in ("duplicate", "overlap", "short", "arm", "count", "odd"):
            altered = copy.deepcopy(entries)
            if change == "duplicate": altered.append(copy.deepcopy(altered[1]))
            elif change == "overlap": altered.append({"rom": "0x0814437A", "end": "0x0814437C"})
            elif change == "short": altered[1]["end"] = "0x081443AC"
            elif change == "arm": altered[1]["mode"] = "arm"
            elif change == "count": altered[1]["instrs"] -= 1
            else: altered[1]["rom"] = "0x08144379"
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(altered).encode(), self.index)
        with self.assertRaises(ValueError):
            profile.verify_identity(self.rom, self.mapping, self.index.replace(b"54 27", b"54 26"))
        with self.assertRaises(ValueError):
            profile.verify_identity(self.rom, self.mapping, self.index + self.index.splitlines()[1] + b"\n")

    def test_alias_data_and_forged_linked_elf_are_rejected(self):
        self.fixture()
        for target in (profile.ADDRESS, profile.ADDRESS | 1, profile.ADDRESS + 2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                match.parse_data_symbols(json.dumps({"object": f"0x{target:08X}"}).encode())
            with self.subTest(target=target), self.assertRaises(ValueError):
                match.function_address_target(f"func_{target:08X}", json.loads(self.mapping),
                                              BASE, len(self.body), len(self.rom))
        for name in ("__lshrdi3", "func_08144378", "func_0814437A", "func_08144379"):
            altered = copy.deepcopy(self.original)
            for symbol in altered["symbols"]:
                if symbol["name"] == "__lshrdi3": symbol["name"] = name
            # Symbol tables share the original symbol objects in a parsed ELF.
            kwargs = {} if name == "__lshrdi3" else {"ashldi3_bindings": {}, "ashldi3_index": self.index}
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.call_bindings(altered, "func_08000000", BASE, self.mapping, len(self.rom),
                                    self.rom, data_mapping=self.objects, **kwargs)
        for key, value in (("section", 1), ("bind", 2), ("type", 1), ("value", 2)):
            altered = copy.deepcopy(self.original)
            for symbol in altered["symbols"]:
                if symbol["name"] == "__lshrdi3": symbol[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                match.call_bindings(altered, "func_08000000", BASE, self.mapping, len(self.rom),
                                    self.rom, data_mapping=self.objects,
                                    ashldi3_bindings={}, ashldi3_index=self.index)
        linked = copy.deepcopy(self.linked)
        changed = bytearray(linked["text"]); changed[0] ^= 1; linked["text"] = bytes(changed)
        with self.assertRaisesRegex(ValueError, "outside permitted relocations"):
            match.linked_function_bytes(self.original, linked, "func_08000000", BASE, self.calls,
                                        {"__lshrdi3": profile.ADDRESS, "g_flags": 0x02000100},
                                        self.literals, ashldi3_bindings=self.bindings)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, self.linked, "func_08000000", BASE,
                                        self.calls, {"__lshrdi3": profile.ADDRESS,
                                                     "g_flags": 0x02000100}, self.literals)

    def test_caller_frame_return_literal_and_profile_isolation(self):
        self.fixture()
        for key, value in (("frame", False), ("data", []), ("calls", []),
                           ("semantics", "unrestricted-c-shift")):
            altered = copy.deepcopy(self.manifest); altered[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.verify(altered)
        changed = bytearray(self.body); changed[0] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(bytes(changed), BASE, self.rom, self.mapping, self.index,
                           self.objects, self.manifest)
        with self.assertRaisesRegex(ValueError, "isolated ordinary"):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                                           ashldi3_context=(self.rom, self.mapping, self.index, self.bindings),
                                           umodsi3_context=(self.rom, self.mapping, {}, {}))
        changed = copy.copy(self.args); changed.flags = "-mthumb-interwork -O1"
        with self.assertRaises(ValueError): profile.fixed_configuration(changed)
        for body in ("push {lr}\nbl __lshrdi3+2\npop {r1}\nbx r1",
                     "push {lr}\nsub sp, #4\nbl __lshrdi3\npop {r1}\nbx r1",
                     "push {lr}\nbl __lshrdi3\nbl func_08000200\npop {r1}\nbx r1",
                     "push {lr}\nbl __lshrdi3\nbl __umodsi3\npop {r1}\nbx r1"):
            with self.subTest(body=body), self.assertRaises(ValueError): self.fixture(assembly=body)

    def test_native_report_replay_status_and_push_report_gate(self):
        self.fixture()
        report = self.native_report()
        self.assertIn(f"* verification: `{profile.SCHEMA}`", report)
        opening, reading = self.patched_rom()
        with opening, reading, redirect_stdout(io.StringIO()):
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            self.assertTrue(push.check_reports(str(self.root)))
            counts = status.collect(str(self.root), verify=False, quiet=True)
            self.assertEqual((counts[1], counts[4]), (1, []))
            for changed in (report + "\n* signed remainder: forged",
                            report.replace("-O2", "-O1"), report + "\n* lshrdi3: duplicate",
                            report.replace('"frame":true', '"frame":false'),
                            report.replace(profile.SCHEMA, evidence.FRAMED_DATA_SCHEMA)):
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            index = self.root / "symbols/functions.txt"
            original_index = index.read_bytes(); index.write_bytes(original_index + b"# stale\n")
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            index.write_bytes(original_index)
            source = self.root / "src/08000000.c"
            original_digest = evidence.source_fingerprint(self.root, BASE)
            source.write_text(source.read_text().replace("return a + b + c", "return a ^ b ^ c"))
            forged = report.replace(original_digest, evidence.source_fingerprint(self.root, BASE))
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))
            forged = forged.replace(
                profile.fingerprint(BASE, self.body, self.manifest, original_digest,
                                    self.mapping, self.index, self.objects, self.rom),
                profile.fingerprint(BASE, self.body, self.manifest,
                                    evidence.source_fingerprint(self.root, BASE),
                                    self.mapping, self.index, self.objects, self.rom))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))
            self.assertTrue(status.collect(str(self.root), verify=False, quiet=True)[4])


class CountDomainTests(unittest.TestCase):
    setUpClass = LogicalRightShiftTests.__dict__["setUpClass"]
    setUp = LogicalRightShiftTests.setUp
    indexes = LogicalRightShiftTests.indexes
    fixture = LogicalRightShiftTests.fixture
    verify = LogicalRightShiftTests.verify
    def test_invalid_unknown_and_wrapping_counts_are_rejected(self):
        for setup in ("movs r2, #64", "movs r2, #0\nsubs r2, #1", "",
                      "movs r3, #0\ncmp r3, #0\nbne 1f\nmovs r2, #64\n1:",
                      "cmp r2, #63\nble 1f\nmovs r2, #64\n1:"):
            with self.subTest(setup=setup), self.assertRaisesRegex(ValueError, "count 0..63"):
                self.fixture(assembly="push {lr}\n" + setup +
                             "\nbl __lshrdi3\npop {r3}\nbx r3")

    def test_signedness_alias_and_mixed_shift_profiles_are_rejected(self):
        for source in (
            "long long func_08000000(long long v, unsigned n) { return v >> (n & 63); }",
            "unsigned long long func_08000000(unsigned long long v, unsigned n) { "
            "n &= 31; return (v >> n) + (v << n); }"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.fixture(source)

    def test_guarded_count_zero_and_63_are_supported(self):
        for setup in ("movs r2, #0", "movs r2, #63"):
            self.fixture(assembly="push {lr}\n" + setup +
                         "\nbl __lshrdi3\npop {r3}\nbx r3")
            self.verify()
        self.fixture("unsigned long long func_08000000(unsigned long long v, unsigned n) "
                     "{ if (n < 64) return v >> n; return 0; }")
        self.verify()


if __name__ == "__main__":
    unittest.main()
