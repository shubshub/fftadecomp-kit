"""Unsigned remainder profiles: native ELF fixtures and fail-closed evidence.

The approved ROM supplies only the pinned runtime spans. Synthetic callers are
compiled/linked with agbcc and installed into an in-memory ROM fixture; these
tests do not claim a match for any game function.
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
import match
import match_evidence as evidence
import umodsi3_profile as profile

BASE = 0x08000000
NAME = "func_08000000"
CALLEE = 0x08000200
SOURCE = """extern unsigned g_input;
extern unsigned func_08000200(unsigned, unsigned, unsigned, unsigned, unsigned);
unsigned func_08000000(unsigned value)
{
    unsigned a = value % 60U;
    unsigned b = value % 30U;
    unsigned c = value % 56U;
    unsigned d = value % 10U;
    unsigned e = value % 25U;
    unsigned f = value % 20U;
    return func_08000200(a + b + c + d + e + f, g_input, 1, 2, 3);
}
"""


class UnsignedRemainderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM for pinned runtime tests")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = bytearray(profile.IDENTITIES[0][1] - BASE)
        with cls.rom_path.open("rb") as stream:
            for start, end, _ in profile.IDENTITIES:
                stream.seek(start - BASE)
                cls.runtime_rom[start - BASE:end - BASE] = stream.read(end - start)

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="umodsi3_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root),
                                               "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                                       assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                                       linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def fixture(self, source=SOURCE, assembly=None):
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            if assembly is None:
                _, _, original = match.compile_object(
                    runner, workspace, self.args, self.root, BASE, "src/08000000.c")
            else:
                text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                        f".global {NAME}\n.type {NAME}, %function\n.thumb_func\n{NAME}:\n" +
                        assembly + f"\n.size {NAME}, . - {NAME}\n")
                path = Path(workspace) / "f.s"
                path.write_text(text)
                subprocess.run([self.args.assembler, "-mthumb-interwork", str(path),
                                "-o", str(Path(workspace) / "f.o")],
                               capture_output=True, check=True, timeout=120)
                original = match.elf_image((Path(workspace) / "f.o").read_bytes())
            symbol, _ = match.function_record(original, NAME, BASE, True)
            entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}",
                        "mode": "thumb"},
                       {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}",
                        "mode": "thumb"}]
            entries += [{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb"}
                        for start, end, _ in profile.IDENTITIES]
            self.mapping = json.dumps(entries).encode()
            self.objects = json.dumps({"g_input": "0x02000100"}).encode()
            self.bindings = {}
            self.body, self.calls, self.literals = match.link_calls(
                runner, workspace, self.args, original, BASE, self.mapping,
                len(self.runtime_rom), bytes(self.runtime_rom), data_mapping=self.objects,
                umodsi3_bindings=self.bindings)
            self.original = original
            self.linked = match.elf_image((Path(workspace) / "f.elf").read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "config/data_symbols.json").write_bytes(self.objects)

    def manifest(self):
        divisors = {}
        instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            umodsi3_context=(self.rom, self.mapping, self.bindings, divisors))
        self.instructions = instructions
        objects = match.parse_data_symbols(self.objects)
        return {"runtime": profile.RUNTIME,
                "calls": [[site - BASE, self.bindings.get(site, f"func_{target:08X}")]
                          for site, target in sorted(self.calls.items())],
                "divisors": [[site - BASE, value] for site, value in sorted(divisors.items())],
                "data": [[offset, name, value - objects[name]]
                         for offset, (name, value) in sorted(self.literals.items())],
                "frame": match.uses_stack_frame(instructions)}

    def verify(self, manifest):
        return profile.verify(self.body, BASE, self.rom, self.mapping, self.objects, manifest)

    def test_natural_unsigned_remainders_with_scalar_frame_data_and_stack_argument(self):
        self.fixture()
        manifest = self.manifest()
        self.assertEqual([record[1] for record in manifest["divisors"]], [60, 30, 56, 10, 25, 20])
        self.assertTrue(manifest["frame"])
        self.assertEqual(len(manifest["data"]), 1)
        self.assertEqual([(i.address, bytes(i.bytes)) for i in self.verify(manifest)],
                         [(i.address, bytes(i.bytes)) for i in self.instructions])
        self.assertTrue(any(i.mnemonic == "str" and "sp" in i.op_str for i in self.instructions))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls)

    def test_unsigned_high_bit_divisor(self):
        self.fixture(assembly="push {lr}\nmovs r1, #1\nlsls r1, r1, #31\n"
                              "bl __umodsi3\npop {r1}\nbx r1")
        manifest = self.manifest()
        self.assertEqual(manifest["divisors"], [[6, 0x80000000]])
        self.verify(manifest)

    def test_zero_unknown_join_and_call_clobbered_divisors_are_rejected(self):
        bodies = (
            "movs r1, #0\nbl __umodsi3",
            "bl __umodsi3",
            "cmp r2, #0\nbeq 1f\nmovs r1, #30\nb 2f\n1: movs r1, #60\n2: bl __umodsi3",
            "movs r1, #60\nbl func_08000200\nbl __umodsi3",
        )
        for body in bodies:
            with self.subTest(body=body):
                self.fixture(assembly="push {lr}\n" + body + "\npop {r1}\nbx r1")
                with self.assertRaisesRegex(ValueError, "CFG-proven nonzero"):
                    self.manifest()

    def test_runtime_dependency_and_mapping_identity_are_pinned(self):
        self.fixture()
        profile.verify_identity(self.rom, self.mapping)
        for start, _, _ in profile.IDENTITIES:
            changed = bytearray(self.rom)
            changed[start - BASE] ^= 1
            with self.assertRaisesRegex(ValueError, "identity differs"):
                profile.verify_identity(bytes(changed), self.mapping)
        entries = json.loads(self.mapping)
        for change in ("duplicate", "overlap", "short", "arm"):
            altered = copy.deepcopy(entries)
            if change == "duplicate": altered.append(copy.deepcopy(altered[2]))
            elif change == "overlap": altered.append({"rom": "0x08142B2A", "end": "0x08142B2C"})
            elif change == "short": altered[2]["end"] = "0x08142BE6"
            else: altered[2]["mode"] = "arm"
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify_identity(self.rom, json.dumps(altered).encode())

    def test_caller_extent_bytes_frame_and_typed_data_are_exact(self):
        self.fixture()
        manifest = self.manifest()
        for field, value in (("frame", False), ("data", []), ("divisors", [])):
            altered = copy.deepcopy(manifest)
            altered[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.verify(altered)
        altered = copy.deepcopy(manifest)
        altered["data"][0][2] += 4
        with self.assertRaises(ValueError): self.verify(altered)
        altered = copy.deepcopy(manifest)
        altered["divisors"][0][1] = 30
        with self.assertRaises(ValueError): self.verify(altered)
        changed = bytearray(self.body); changed[0] ^= 1
        with self.assertRaisesRegex(ValueError, "exact complete mapped ROM bytes"):
            profile.verify(bytes(changed), BASE, self.rom, self.mapping, self.objects, manifest)
        entries = json.loads(self.mapping); entries[0]["end"] = "0x08000002"
        with self.assertRaisesRegex(ValueError, "exact complete mapped ROM bytes"):
            profile.verify(self.body, BASE, self.rom, json.dumps(entries).encode(), self.objects, manifest)

    def test_runtime_aliases_data_bindings_and_linker_edits_are_rejected(self):
        self.fixture()
        for target in (profile.ADDRESS, profile.ADDRESS + 2, profile.ADDRESS | 1):
            with self.subTest(target=target), self.assertRaises(ValueError):
                match.parse_data_symbols(json.dumps({"object": f"0x{target:08X}"}).encode())
            with self.subTest(target=target), self.assertRaises(ValueError):
                match.function_address_target(f"func_{target:08X}", json.loads(self.mapping),
                                              BASE, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, NAME, BASE, self.mapping, len(self.rom), self.rom,
                                data_mapping=self.objects)
        linked = copy.deepcopy(self.linked)
        changed = bytearray(linked["text"]); changed[0] ^= 1; linked["text"] = bytes(changed)
        with self.assertRaisesRegex(ValueError, "outside permitted relocations"):
            match.linked_function_bytes(self.original, linked, NAME, BASE, self.calls,
                                        {"__umodsi3": profile.ADDRESS, "func_08000200": CALLEE,
                                         "g_input": 0x02000100}, self.literals,
                                        umodsi3_bindings=self.bindings)

    def test_stack_return_provenance_and_profile_isolation_remain_enforced(self):
        self.fixture(assembly="push {lr}\nsub sp, #4\nmovs r1, #60\nbl __umodsi3\n"
                              "pop {r1}\nbx r1")
        with self.assertRaises(ValueError): self.manifest()
        self.fixture()
        with self.assertRaisesRegex(ValueError, "isolated ordinary"):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                                           umodsi3_context=(self.rom, self.mapping, self.bindings, {}),
                                           divsi3_context=(self.rom, self.mapping, {}, {}))
        changed = copy.copy(self.args); changed.flags = "-mthumb-interwork -O1"
        with self.assertRaises(ValueError): profile.fixed_configuration(changed)

    def test_report_replays_source_and_rejects_tampering(self):
        self.fixture()
        manifest = self.manifest()
        lines = [f"* verification: `{profile.SCHEMA}`",
                 f"* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`",
                 f"* mapping SHA-256: `{evidence.mapping_fingerprint(self.mapping)}`",
                 f"* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects)}`",
                 f"* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`",
                 f"* control flow: {evidence.CALL_SUMMARY}",
                 f"* stack frame: {evidence.STACK_SUMMARY}",
                 "* verified extent: complete ELF function symbol, including literal pools",
                 f"* unsigned remainder: {profile.SUMMARY}",
                 f"* unsigned remainder manifest: `{profile.manifest_text(manifest)}`",
                 f"* unsigned remainder proof SHA-256: `{profile.fingerprint(BASE, self.body, manifest)}`",
                 f"* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)",
                 f"* compiled : `{self.body.hex()}`",
                 "* source plausibility: plausible", "* relocations: none",
                 f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]
        # Present the synthetic caller through an in-memory read of the ROM path;
        # the approved ROM file remains untouched and is never copied to disk.
        original_read = Path.read_bytes
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        with patch.object(Path, "read_bytes", read):
            report = "\n".join(lines)
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            for changed in (report + "\n" + lines[0],
                            report.replace("-O2", "-O1"),
                            report.replace('"frame":true', '"frame":false'),
                            report.replace("* stack frame:", "* extra stack frame:"),
                            report + "\n* signed remainder: forged"):
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            source = self.root / "src/08000000.c"
            original_digest = evidence.source_fingerprint(self.root, BASE)
            source.write_text(source.read_text().replace("60U", "61U"))
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            forged = report.replace(original_digest, evidence.source_fingerprint(self.root, BASE))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))

    def test_native_matcher_emits_a_valid_unsigned_remainder_report(self):
        self.fixture()
        (self.root / "symbols").mkdir()
        (self.root / "symbols/functions.txt").write_text(
            f"08000000 {BASE + len(self.body):08X} {len(self.body)} 0 return\n")
        original_open, original_read = builtins.open, Path.read_bytes
        def open_file(path, mode="r", *args, **kwargs):
            if mode == "rb" and Path(path).resolve() == self.rom_path:
                return io.BytesIO(self.rom)
            return original_open(path, mode, *args, **kwargs)
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        output = io.StringIO()
        with patch.object(builtins, "open", open_file), patch.object(Path, "read_bytes", read), \
                patch.object(sys, "argv", ["match.py", "--root", str(self.root), "0x08000000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(output):
            self.assertEqual(match.main(), 0)
            report = (self.root / "docs/match/08000000.md").read_text()
            self.assertIn(f"* verification: `{profile.SCHEMA}`", report)
            self.assertIn("source  plausible", output.getvalue())
            self.assertTrue(evidence.report_matches(report, self.root, BASE))


if __name__ == "__main__":
    unittest.main()
