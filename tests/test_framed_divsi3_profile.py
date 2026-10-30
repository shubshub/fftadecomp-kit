"""Explicit framed positive quotient, using unchanged fixed-O2 native ELF.

Only the pinned helper spans come from the approved ROM. The natural caller
is synthetic and carries no game C, match, or inventory credit.
"""
import argparse
import builtins
import copy
from contextlib import contextmanager, redirect_stdout
import hashlib
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
import divsi3_profile as profile
import status

BASE = 0x08000000
NAME = "func_08000000"
CALLEE = 0x08000200
SOURCE = """extern int func_08000200(int, int, int, int, int);
int func_08000000(int value)
{
    int quotient = value / 7;
    return func_08000200(quotient, 1, 2, 3, 4);
}
"""


class FramedQuotientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get("FFTA_ROM")
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest("FFTA_ROM must reference the approved ROM")
        cls.rom_path = Path(selected).resolve()
        cls.runtime_rom = bytearray(max(end for _, end, _ in profile.IDENTITIES) - BASE)
        with cls.rom_path.open("rb") as stream:
            for start, end, _ in profile.IDENTITIES:
                stream.seek(start - BASE)
                cls.runtime_rom[start - BASE:end - BASE] = stream.read(end - start)

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="framed_divsi3_", dir=scratch)
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

    def fixture(self, assembly=None, source=SOURCE):
        (self.root / "src/08000000.c").write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            workspace = Path(workspace)
            if assembly is None:
                _, _, original = match.compile_object(
                    runner, str(workspace), self.args, self.root, BASE, "src/08000000.c")
            else:
                (workspace / "f.s").write_text(
                    ".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                    f".global {NAME}\n.type {NAME}, %function\n.thumb_func\n{NAME}:\n" +
                    assembly + f"\n.size {NAME}, . - {NAME}\n")
                subprocess.run([self.args.assembler, "-mthumb-interwork", str(workspace / "f.s"),
                                "-o", str(workspace / "f.o")], check=True, capture_output=True)
                original = match.elf_image((workspace / "f.o").read_bytes())
            original_bytes = (workspace / "f.o").read_bytes()
            original_assembly = (workspace / "f.s").read_bytes()
            symbol, _ = match.function_record(original, NAME, BASE, True)
            entries = [{"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}",
                        "mode": "thumb"},
                       {"rom": f"0x{CALLEE:08X}", "end": f"0x{CALLEE + 2:08X}", "mode": "thumb"}]
            entries += [{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb"}
                        for start, end, _ in profile.IDENTITIES]
            self.mapping = json.dumps(entries).encode()
            self.bindings = {}
            self.body, self.calls, literals = match.link_calls(
                runner, str(workspace), self.args, original, BASE, self.mapping,
                len(self.runtime_rom), bytes(self.runtime_rom), divsi3_bindings=self.bindings)
            self.assertFalse(literals)
            self.assertEqual((workspace / "f.o").read_bytes(), original_bytes)
            self.assertEqual((workspace / "f.s").read_bytes(), original_assembly)
            self.assertEqual(int.from_bytes(original_bytes[16:18], "little"), 1)
            self.original = original
            self.linked = match.elf_image((workspace / "f.elf").read_bytes())
            self.original_bytes = original_bytes
            self.assembly = (workspace / "f.s").read_bytes()
            self.linked_bytes = (workspace / "f.elf").read_bytes()
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        (self.root / "config/functions.json").write_bytes(self.mapping)
        (self.root / "symbols/functions.txt").write_text(
            f"08000000 {BASE + len(self.body):08X} {len(self.body)} 0 return\n")

    def native(self, selector=profile.FRAMED_SELECTOR, **kwargs):
        observed = {}
        instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls,
            divsi3_context=(self.rom, self.mapping, self.bindings, observed),
            signed_quotient_profile=selector, **kwargs)
        self.instructions = instructions
        return {"runtime": profile.RUNTIME,
                "calls": [[site - BASE, self.bindings.get(site, f"func_{target:08X}")]
                          for site, target in sorted(self.calls.items())],
                "divisors": [[site - BASE, divisor] for site, divisor in sorted(observed.items())],
                **({"frame": True} if selector else {})}

    @contextmanager
    def rom_reads(self):
        original_open, original_read = builtins.open, Path.read_bytes
        def open_file(path, mode="r", *args, **kwargs):
            if mode == "rb" and Path(path).resolve() == self.rom_path:
                return io.BytesIO(self.rom)
            return original_open(path, mode, *args, **kwargs)
        def read(path):
            return self.rom if path.resolve() == self.rom_path else original_read(path)
        with patch.object(builtins, "open", open_file), patch.object(Path, "read_bytes", read):
            yield

    def cli(self, *options):
        output = io.StringIO()
        with self.rom_reads(), patch.object(sys, "argv", ["match.py", "--root", str(self.root),
                                                         "08000000", *options]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(output):
            code = match.main()
        return code, output.getvalue()

    def test_natural_fixed_o2_retains_original_elf_and_real_sp_frame(self):
        self.fixture()
        manifest = self.native()
        self.assertEqual([value for _, value in manifest["divisors"]], [7])
        self.assertTrue(any((match.thumb_stack_adjustment(i) or 0) < 0 for i in self.instructions))
        self.assertTrue(any(i.mnemonic == "str" and "sp" in i.op_str for i in self.instructions))
        verified = match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest,
                                      selector=profile.FRAMED_SELECTOR)
        self.assertEqual([i.address for i in verified], [i.address for i in self.instructions])
        with self.assertRaisesRegex(ValueError, "frameless caller"):
            self.native(None)
        retained = os.environ.get("FFTA_FRAMED_RETAIN")
        if retained:
            destination = Path(retained)
            destination.mkdir(parents=True, exist_ok=True)
            for name, data in (("caller.c", SOURCE.encode()), ("caller.s", self.assembly),
                               ("caller.o", self.original_bytes), ("caller.elf", self.linked_bytes)):
                (destination / name).write_bytes(data)
            (destination / "manifest.json").write_text(json.dumps({
                "synthetic_only": True, "original_ET_REL_unchanged": True,
                "original_ASM_unchanged": True,
                "compiler": f"{match.DEFAULT_CC} {match.DEFAULT_FLAGS}",
                "profile": profile.FRAMED_SCHEMA, "manifest": manifest,
                "original_object_sha256": hashlib.sha256(self.original_bytes).hexdigest()}, indent=2) + "\n")

    def test_default_standalone_and_selector_boundaries(self):
        self.fixture(assembly="push {lr}\nmovs r1, #7\nbl __divsi3\npop {r1}\nbx r1")
        manifest = self.native(None)
        match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest)
        with self.assertRaisesRegex(ValueError, "allocated caller stack frame"):
            self.native()
        with self.assertRaisesRegex(ValueError, "unsupported signed quotient selector"):
            self.native("ordinary")
        with self.assertRaisesRegex(ValueError, "isolated canonical Thumb"):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                                           signed_quotient_profile=profile.FRAMED_SELECTOR)
        with self.assertRaisesRegex(ValueError, "isolated canonical Thumb"):
            self.native(umodsi3_context=(self.rom, self.mapping, self.bindings, {}))
        with self.assertRaisesRegex(ValueError, "isolated canonical Thumb"):
            match.verify_leaf_instructions(self.body, BASE, False, self.calls,
                divsi3_context=(self.rom, self.mapping, self.bindings, {}),
                signed_quotient_profile=profile.FRAMED_SELECTOR)

    def test_default_natural_standalone_cli_and_report_stay_current(self):
        self.fixture(source="int func_08000000(int value) { return value / 7; }\n")
        code, _ = self.cli()
        self.assertEqual(code, 0)
        report = (self.root / "docs/match/08000000.md").read_text()
        self.assertIn(f"* verification: `{profile.SCHEMA}`", report)
        self.assertNotIn("* stack frame", report)
        with self.rom_reads():
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
        with self.assertRaisesRegex(SystemExit, "allocated caller stack frame"):
            self.cli("--signed-quotient-profile", profile.FRAMED_SELECTOR)
        with self.assertRaisesRegex(SystemExit, "excludes other selectors"):
            self.cli("--signed-quotient-profile", profile.FRAMED_SELECTOR, "--mode", "arm")

    def test_unbalanced_frame_saved_return_and_clobbered_alias_remain_refused(self):
        bodies = (
            "push {lr}\nsub sp, #4\nmovs r1, #7\nbl __divsi3\npop {r1}\nbx r1",
            "push {lr}\nsub sp, #4\nstr r0, [sp, #4]\nmovs r1, #7\nbl __divsi3\nadd sp, #4\npop {r1}\nbx r1",
            "push {r4, lr}\nsub sp, #4\nstr r0, [sp, #4]\nmovs r1, #7\nbl __divsi3\nadd sp, #4\npop {r4}\npop {r1}\nbx r1",
            "push {lr}\nsub sp, #4\nmov r2, sp\nmovs r1, #7\nbl __divsi3\nldr r0, [r2]\nadd sp, #4\npop {r1}\nbx r1",
        )
        for body in bodies:
            with self.subTest(body=body):
                self.fixture(assembly=body)
                with self.assertRaises(ValueError): self.native()

    def test_nonpositive_unknown_join_and_clobbered_divisors_remain_refused(self):
        bodies = ("movs r1, #0\nbl __divsi3", "bl __divsi3",
                  "movs r1, #1\nlsls r1, r1, #31\nbl __divsi3",
                  "cmp r2, #0\nbeq 1f\nmovs r1, #7\nb 2f\n1: movs r1, #8\n2: bl __divsi3",
                  "movs r1, #7\nbl func_08000200\nbl __divsi3")
        for body in bodies:
            with self.subTest(body=body):
                self.fixture(assembly="push {lr}\nsub sp, #4\n" + body +
                             "\nadd sp, #4\npop {r1}\nbx r1")
                with self.assertRaisesRegex(ValueError, "CFG-proven positive signed32"):
                    self.native()

    def test_manifest_identity_runtime_interior_and_original_relocation_gates(self):
        self.fixture()
        manifest = self.native()
        for field, value in (("frame", False), ("frame", 1), ("divisors", []),
                             ("divisors", [[manifest["divisors"][0][0], 8]])):
            changed = copy.deepcopy(manifest); changed[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                match.verify_divsi3(self.body, BASE, self.rom, self.mapping, changed,
                                    selector=profile.FRAMED_SELECTOR)
        with self.assertRaises(ValueError):
            match.verify_divsi3(self.body, BASE, self.rom, self.mapping, manifest)
        self.assertNotEqual(profile.fingerprint(BASE, self.body, manifest),
                            profile.fingerprint(BASE, self.body, manifest, selector=profile.FRAMED_SELECTOR))
        for start, _, _ in profile.IDENTITIES:
            changed = bytearray(self.rom); changed[start - BASE] ^= 1
            with self.assertRaisesRegex(ValueError, "identity differs"):
                match.verify_divsi3(self.body, BASE, bytes(changed), self.mapping, manifest,
                                    selector=profile.FRAMED_SELECTOR)
        with self.assertRaises(ValueError):
            self.fixture(assembly="push {lr}\nsub sp, #4\nmovs r1, #7\nbl __divsi3+2\n"
                                  "add sp, #4\npop {r1}\nbx r1")

    def test_native_cli_report_source_replay_status_and_stale_evidence(self):
        self.fixture()
        with self.assertRaisesRegex(SystemExit, "frameless caller"):
            self.cli()
        code, output = self.cli("--signed-quotient-profile", profile.FRAMED_SELECTOR)
        self.assertEqual(code, 0)
        self.assertIn("source  plausible", output)
        path = self.root / "docs/match/08000000.md"
        report = path.read_text()
        self.assertIn(f"* verification: `{profile.FRAMED_SCHEMA}`", report)
        with self.rom_reads():
            self.assertTrue(evidence.report_matches(report, self.root, BASE))
            collected = status.collect(str(self.root), verify=False, quiet=True)
            self.assertEqual(collected[1], 1)
            # Run the native matcher in-process so the synthetic ROM stays in
            # memory. All compiler, assembler, linker and plausibility processes
            # remain real; the exact status command and exit are checked.
            original_run = subprocess.run
            commands = []
            def run(command, *args, **kwargs):
                if len(command) > 1 and str(command[1]).endswith("/match.py"):
                    commands.append(command)
                    code, stdout = self.cli(*command[5:])
                    return subprocess.CompletedProcess(command, code, stdout, "")
                return original_run(command, *args, **kwargs)
            with patch.object(status.subprocess, "run", run):
                checked = status.collect(str(self.root), verify=True, quiet=True)
            self.assertEqual(checked[1], 1)
            self.assertFalse(checked[4])
            self.assertEqual(len(commands), 1)
            self.assertIn(profile.FRAMED_SELECTOR, commands[0])
            retained = os.environ.get("FFTA_FRAMED_RETAIN")
            if retained:
                destination = Path(retained)
                destination.mkdir(parents=True, exist_ok=True)
                (destination / "native-report.md").write_text(report)
                (destination / "native-match.log").write_text(output)
                (destination / "lifecycle.json").write_text(json.dumps({
                    "synthetic_only": True, "native_match_exit": code,
                    "source_replay_accepted": True, "status_offline": collected,
                    "status_verify": checked, "status_match_command": commands[0],
                    "status_child_in_process_for_in_memory_ROM": True,
                    "compiler_assembler_linker_and_plausibility_are_real": True,
                    "game_C_match_or_inventory_credit": 0}, indent=2) + "\n")
            for changed in (report + "\n* verification: `forged`",
                            report.replace(profile.FRAMED_SCHEMA, profile.SCHEMA),
                            report.replace('"frame":true', '"frame":false'),
                            report.replace("* stack frame:", "* other frame:"),
                            report.replace("-O2", "-O1"),
                            report + "\n* unsigned remainder: forged"):
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(evidence.report_matches(changed, self.root, BASE))
            mapping_path = self.root / "config/functions.json"
            changed_mapping = json.loads(self.mapping)
            changed_mapping[0]["end"] = f"0x{BASE + len(self.body) + 2:08X}"
            mapping_path.write_text(json.dumps(changed_mapping))
            forged_mapping = report.replace(evidence.mapping_fingerprint(self.mapping),
                                              evidence.mapping_fingerprint(mapping_path.read_bytes()))
            self.assertFalse(evidence.report_matches(forged_mapping, self.root, BASE))
            mapping_path.write_bytes(self.mapping)
            source = self.root / "src/08000000.c"
            digest = evidence.source_fingerprint(self.root, BASE)
            source.write_text(source.read_text().replace("/ 7", "/ 8"))
            self.assertFalse(evidence.report_matches(report, self.root, BASE))
            forged = report.replace(digest, evidence.source_fingerprint(self.root, BASE))
            self.assertFalse(evidence.report_matches(forged, self.root, BASE))


if __name__ == "__main__":
    unittest.main()
