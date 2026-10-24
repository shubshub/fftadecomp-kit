import argparse
import contextlib
import copy
import hashlib
import io
import json
import os
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import switch_constants_profile as profile
import match
import match_evidence
import rebuild
import status


ADDRESS = 0x08000000
SOURCE = """unsigned int func_08000000(unsigned int selector, unsigned int left, unsigned int right)
{
    left &= 0xFF00FF00;
    right &= 0x0F0F0F0F;
    switch (selector) {
    case 0: return left + right;
    case 1: return left - right;
    case 2: return left * right;
    case 3: return left ^ right;
    case 4: return left | right;
    case 5: return left & right;
    default: return right;
    }
}
"""


def fixed_args():
    return argparse.Namespace(**dict(zip(("cc", "cpp", "assembler", "objcopy", "linker", "flags"),
                                         profile.configuration())))


def assemble(root, assembly):
    (root / "f.s").write_text(assembly)
    result = subprocess.run(["arm-none-eabi-as", "-mthumb-interwork", str(root / "f.s"), "-o", str(root / "f.o")],
                            capture_output=True, text=True, timeout=120)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return (root / "f.o").read_bytes()


def ordinary_link(root, original, address=ADDRESS):
    (root / "f.o").write_bytes(original)
    undefined = [symbol["name"] for symbol in match.elf_image(original)["symbols"]
                 if symbol["name"] and not symbol["section"]]
    definitions = ".syntax unified\n.thumb\n" + "\n".join(
        f".global {name}\n.type {name}, %function\n.thumb_set {name}, 0x{int(name[5:], 16) | 1:08X}"
        for name in undefined)
    (root / "known.s").write_text(definitions)
    subprocess.run(["arm-none-eabi-as", str(root / "known.s"), "-o", str(root / "known.o")],
                   check=True, capture_output=True)
    subprocess.run(["arm-none-eabi-ld", "--no-undefined", "--no-relax", f"-Ttext=0x{address:08X}",
                    "-e", f"func_{address:08X}", str(root / "f.o"), str(root / "known.o"),
                    "-o", str(root / "f.elf")],
                   check=True, capture_output=True)
    linked = (root / "f.elf").read_bytes()
    image = match.elf_image(linked)
    symbol = next(item for item in image["symbols"] if item["name"] == f"func_{address:08X}")
    return linked, image["text"][:symbol["size"]]


def fixture_assembly(guard="bhi", extra=False, call=False, zero=False, duplicate=False,
                     relocated=None, attack_word=None, prefix="", first="ldr r2, .Lconstant0",
                     second="ldr r3, .Lconstant1", gap="", tail=""):
    guard_code = "bhi .Ldefault" if guard == "bhi" else "bls .Ldispatch\nb .Ldefault"
    constants = ["0" if zero else "0xFF00FF00", "0" if zero else "0x0F0F0F0F"]
    if attack_word is not None:
        constants[attack_word] = "0x08000000 + (.Lcase0 - func_08000000)"
    if relocated is not None:
        constants[relocated] = ".Lcase0"
    prologue = "push {lr}\n" if call else ""
    extra_instruction = "movs r1, #0\n" if extra else ""
    case1 = "" if duplicate else ".Lcase1:\nsubs r0, r2, r3\nb .Ldone\n"
    finish = "bl func_08001000\npop {r1}\nbx r1" if call else "bx lr"
    return f""".syntax unified
.arch armv4t
.thumb
.text
.global func_08000000
.type func_08000000, %function
.thumb_func
func_08000000:
{prologue}{prefix}
{first}
{second}
{extra_instruction}cmp r0, #1
{guard_code}
.Ldispatch:
lsls r0, r0, #2
ldr r1, .Lpointer
adds r0, r0, r1
ldr r0, [r0]
mov pc, r0
.balign 4, 0
{gap}
.Lconstant0:
.word {constants[0]}
.Lconstant1:
.word {constants[1]}
.Lpointer:
.word .Ltable
.Ltable:
.word .Lcase0
.word {'.Lcase0' if duplicate else '.Lcase1'}
.Lcase0:
adds r0, r2, r3
b .Ldone
{case1}.Ldefault:
movs r0, #0
.Ldone:
{finish}
{tail}
.size func_08000000, . - func_08000000
"""


class RealSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.scratch = Path(__file__).resolve().parents[1] / "build"
        cls.scratch.mkdir(exist_ok=True)
        cls.directory = tempfile.TemporaryDirectory(prefix="switch_tests_", dir=cls.scratch)
        cls.fixture = Path(cls.directory.name)
        (cls.fixture / "src").mkdir()
        (cls.fixture / "src/08000000.c").write_text(SOURCE)
        runner = match.Runner(match.DEFAULT_CC, root=cls.fixture, timeout=120)
        with runner.workspace() as workspace:
            cls.original, _, cls.image = match.compile_object(runner, workspace, fixed_args(),
                                                              cls.fixture, ADDRESS, "src/08000000.c")
        cls.linked, cls.body = ordinary_link(cls.fixture, cls.original)
        cls.rom = cls.body + bytes(0x2000 - len(cls.body))
        cls.mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{ADDRESS + len(cls.body):08X}",
                                   "mode": "thumb"}]).encode()
        cls.index = f"08000000 {ADDRESS + len(cls.body):08X} {len(cls.body)}\n".encode()

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="switch_case_", dir=self.scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for relative, contents in {"src/08000000.c": SOURCE.encode(), "include/types.h": b"",
                                   "config/functions.json": self.mapping,
                                   "symbols/functions.txt": self.index, "fixture.rom": self.rom}.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)
        self.enterContext(patch.dict(os.environ, {"FFTA_ROM": str(self.root / "fixture.rom")}))
        self.enterContext(patch.object(profile, "ROM_SIZE", len(self.rom)))
        self.enterContext(patch.object(profile, "ROM_SHA1", hashlib.sha1(self.rom).hexdigest()))

    def test_real_source_cli_and_fresh_report_replay(self):
        arguments = ["match.py", "--root", str(self.root), "--switch-profile", profile.SELECTOR, "08000000"]
        with patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()), \
                patch.object(profile, "_compile_object", wraps=profile._compile_object) as compiled, \
                patch.object(match, "elf_image", wraps=match.elf_image) as parsed, \
                patch.object(profile, "_manifest", wraps=profile._manifest) as manifested:
            self.assertEqual(match.main(), 0)
            report = (self.root / "docs/match/08000000.md").read_text()
            self.assertTrue(match_evidence.report_matches(report, self.root, ADDRESS))
            self.assertEqual(compiled.call_count, 2)
            self.assertGreaterEqual(parsed.call_count, 4)
            self.assertEqual(manifested.call_count, 2)
        self.assertEqual(list((self.root / "build").iterdir()), [])
        destination = os.environ.get("FFTA_SWITCH_NATURAL_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps({"source": SOURCE, "original": self.original.hex(),
                "linked": self.linked.hex(), "body": self.body.hex(), "mapping": self.mapping.decode(),
                "index": self.index.decode(), "report": report, "tools": profile._resolve_tools(),
                "test_only_rom_sha1": hashlib.sha1(self.rom).hexdigest(),
                "fixture_rom_bytes": len(self.rom), "fresh_compile_count": compiled.call_count,
                "fresh_parse_count": parsed.call_count, "fresh_manifest_count": manifested.call_count},
                indent=2) + "\n")

    def build_report(self):
        return profile.render_report(ADDRESS, profile._build_from_source(self.root, ADDRESS))

    def install_fixture(self, original):
        linked, body = ordinary_link(self.root, original)
        rom = body + bytes(0x2000 - len(body))
        (self.root / "fixture.rom").write_bytes(rom)
        entries = [{"rom": "0x08000000", "end": f"0x{ADDRESS + len(body):08X}", "mode": "thumb"},
                   {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]
        (self.root / "config/functions.json").write_text(json.dumps(entries))
        (self.root / "symbols/functions.txt").write_text(f"08000000 {ADDRESS + len(body):08X} {len(body)}\n")
        self.enterContext(patch.object(profile, "ROM_SHA1", hashlib.sha1(rom).hexdigest()))
        return linked, body

    @staticmethod
    def inject_object(original):
        real_compile = profile._compile_object
        def compile_fixture(runner, workspace, args, root, address, source, thumb=True):
            real_compile(runner, workspace, args, root, address, source, thumb)
            (Path(workspace) / "f.o").write_bytes(original)
            image = match.elf_image(original)
            return original, image["text"], image
        return compile_fixture

    def test_same_linked_bytes_cannot_launder_either_relocated_constant(self):
        evidence = []
        for word in (0, 1):
            with self.subTest(word=word):
                good = assemble(self.root, fixture_assembly(attack_word=word))
                bad = assemble(self.root, fixture_assembly(relocated=word))
                good_linked, good_body = self.install_fixture(good)
                bad_linked, bad_body = ordinary_link(self.root, bad)
                self.assertEqual(good_body, bad_body)
                good_image, bad_image = match.elf_image(good), match.elf_image(bad)
                mapping = (self.root / "config/functions.json").read_bytes()
                good_records = profile._original_records(good_image, ADDRESS, mapping, 0x2000)
                bad_records = profile._original_records(bad_image, ADDRESS, mapping, 0x2000)
                self.assertEqual(len(bad_records), len(good_records) + 1)
                with patch.object(profile, "_compile_object", side_effect=self.inject_object(good)):
                    report = self.build_report()
                    self.assertTrue(match_evidence.report_matches(report, self.root, ADDRESS))
                with patch.object(profile, "_compile_object", side_effect=self.inject_object(bad)) as compiled, \
                        patch.object(match_evidence, "switch_report_matches") as legacy:
                    self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
                    compiled.assert_called_once()
                    legacy.assert_not_called()
                evidence.append({"word": word, "good_original": good.hex(), "bad_original": bad.hex(),
                                 "good_linked": good_linked.hex(), "bad_linked": bad_linked.hex(),
                                 "complete_body": good_body.hex(), "good_records": good_records,
                                 "bad_records": bad_records, "accepted_report": report})
        destination = os.environ.get("FFTA_SWITCH_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps(evidence, indent=2) + "\n")

    def test_actual_source_and_input_changes_fail_replay(self):
        report = self.build_report()
        for name, contents in (("src/08000000.c", SOURCE.replace("left + right", "left + right + 1").encode()),
                               ("include/types.h", b"typedef int changed;\n"),
                               ("include/new.h", b""), ("src/new.h", b""),
                               ("config/functions.json", self.mapping + b" "),
                               ("symbols/functions.txt", self.index + b"\n")):
            with self.subTest(name=name):
                path = self.root / name
                previous = path.read_bytes() if path.exists() else None
                path.write_bytes(contents)
                self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
                if previous is None:
                    path.unlink()
                else:
                    path.write_bytes(previous)

    def test_mutations_during_compilation_are_detected(self):
        report = self.build_report()
        real_compile = profile._compile_object
        cases = ("live_source", "captured", "membership", "mapping", "index", "rom", "rom_path", "tools")
        for change in cases:
            with self.subTest(change=change):
                originals = {path: path.read_bytes() for path in self.root.rglob("*") if path.is_file()}
                tool_calls = [0]
                real_tools = profile._resolve_tools

                def changing_tools():
                    result = real_tools()
                    tool_calls[0] += 1
                    return result if tool_calls[0] < 3 else (*result[:-1], ("changed", "changed", "changed"))

                def compile_changed(runner, workspace, args, root, address, source, thumb=True):
                    result = real_compile(runner, workspace, args, root, address, source, thumb)
                    path = {"live_source": self.root / source, "captured": Path(root) / source,
                            "membership": self.root / "include/new.h",
                            "mapping": self.root / "config/functions.json",
                            "index": self.root / "symbols/functions.txt",
                            "rom": self.root / "fixture.rom"}.get(change)
                    if path is not None:
                        path.write_bytes((path.read_bytes() if path.exists() else b"") + b"\n")
                    if change == "rom_path":
                        alternate = self.root / "alternate.rom"
                        alternate.write_bytes(self.rom)
                        os.environ["FFTA_ROM"] = str(alternate)
                    return result

                with patch.object(profile, "_compile_object", side_effect=compile_changed), \
                        patch.object(profile, "_resolve_tools", side_effect=changing_tools if change == "tools" else real_tools):
                    self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
                os.environ["FFTA_ROM"] = str(self.root / "fixture.rom")
                for path in self.root.rglob("*"):
                    if path.is_file() and path not in originals:
                        path.unlink()
                for path, contents in originals.items():
                    path.write_bytes(contents)
                self.assertFalse(profile._active.get())

    def test_capture_membership_drift_and_uncaptured_include(self):
        report = self.build_report()
        real_snapshot = profile._source_snapshot
        calls = [0]

        def snapshot(root, address):
            result = real_snapshot(root, address)
            calls[0] += 1
            if calls[0] == 1:
                (self.root / "include/late.h").write_text("")
            return result

        with patch.object(profile, "_source_snapshot", side_effect=snapshot):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        (self.root / "include/late.h").unlink()
        (self.root / "outside.h").write_text("typedef unsigned int word;\n")
        (self.root / "src/08000000.c").write_text('#include "../outside.h"\n' + SOURCE)
        with self.assertRaises((RuntimeError, ValueError)):
            profile._build_from_source(self.root, ADDRESS)

    def test_missing_duplicate_source_and_overlapping_indexes(self):
        report = self.build_report()
        path = self.root / "src/08000000.c"
        path.unlink()
        self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        path.write_text(SOURCE)
        duplicate = self.root / "src/nested/08000000.c"
        duplicate.parent.mkdir()
        duplicate.write_text(SOURCE)
        self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        duplicate.unlink()
        for name in ("config/functions.json", "symbols/functions.txt"):
            indexed = self.root / name
            saved = indexed.read_bytes()
            if name.endswith("json"):
                entries = json.loads(saved)
                entries.append(dict(entries[0]))
                indexed.write_text(json.dumps(entries))
            else:
                indexed.write_bytes(saved + saved)
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
            indexed.write_bytes(saved)

    def test_failure_paths_reset_context_and_cleanup(self):
        report = self.build_report()
        for error in (OSError("missing"), RuntimeError("tool exit"), subprocess.TimeoutExpired("tool", 120),
                      ValueError("malformed ELF"), struct.error("short ELF")):
            with self.subTest(error=type(error).__name__), \
                    patch.object(profile, "_compile_object", side_effect=error):
                self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
                self.assertFalse(profile._active.get())
                self.assertEqual(list((self.root / "build").iterdir()), [])
        token = profile._active.set(True)
        try:
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        finally:
            profile._active.reset(token)
        with patch.object(shutil, "which", return_value=None):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        self.assertTrue(match_evidence.report_matches(report, self.root, ADDRESS))

    def test_plausibility_allowance_and_captured_checker_fail_closed(self):
        report = self.build_report()
        with patch.object(match, "plausibility_result", return_value=([{"message": "forbidden"}], False)):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        allow = self.root / "allow.json"
        allow.write_text(json.dumps({"entries": [{"address": "0x08000000"}]}))
        with patch.dict(os.environ, {"FFTA_ASM_ALLOW": str(allow)}), \
                patch.object(profile, "_compile_object", wraps=profile._compile_object) as compile_call:
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
            compile_call.assert_not_called()
        source = SOURCE.replace("    switch (selector)", "    if (0) { left++; }\n    switch (selector)")
        (self.root / "src/08000000.c").write_text(source)
        with self.assertRaisesRegex(ValueError, "implausible"):
            profile._build_from_source(self.root, ADDRESS)

    def test_strict_report_routing_and_canonical_serialization(self):
        report = self.build_report()
        altered = []
        for line in report.splitlines():
            if line.startswith("*"):
                altered += [report.replace(line + "\n", "", 1), report + line + "\n",
                            report.replace(line, " " + line, 1)]
        altered += [report.replace(profile.SCHEMA, profile.SCHEMA + "-future"),
                    report.replace(profile.SELECTOR, "two-constants-v1"),
                    report + "* unknown: unbound\n", report + "* buffer calls: mixed\n",
                    report.replace("* switch constants:", "*\tswitch constants:"),
                    report.replace(profile.SCHEMA, match_evidence.SWITCH_SCHEMA)]
        with patch.object(profile, "_build_from_source", wraps=profile._build_from_source), \
                patch.object(match_evidence, "switch_report_matches") as old:
            for changed in altered:
                with self.subTest(changed=changed[-100:]):
                    self.assertFalse(match_evidence.report_matches(changed, self.root, ADDRESS))
            old.assert_not_called()
        manifest_line = next(line for line in report.splitlines() if line.startswith("* switch constants manifest:"))
        encoded = manifest_line.split("`", 2)[1]
        manifest = json.loads(encoded)
        malformed = [encoded.replace('"calls":', '"calls":[],"calls":', 1), json.dumps(manifest),
                     profile.canonical(dict(manifest, extra=[]))]
        for value in (True, -1, 0x100000000):
            changed = copy.deepcopy(manifest)
            changed["constants"][0][1] = value
            malformed.append(profile.canonical(changed))
        changed = copy.deepcopy(manifest)
        changed["constants"][0][2] *= 2
        malformed.append(profile.canonical(changed))
        for encoded_bad in malformed:
            self.assertFalse(match_evidence.report_matches(report.replace(encoded, encoded_bad), self.root, ADDRESS))

    def test_default_cli_and_incompatible_options_reject(self):
        cases = ([], ["--cc", "/home/user/agbcc/gcc/agbcc"], ["--flags=-O1"], ["--mode", "arm"],
                 ["--wsl", "Other"], ["--wsl-path", "/different"],
                 ["--control-flow-profile", "mixed-return-inert-spin-v1"], ["--label", "extra"])
        for options in cases:
            args = ["match.py", "--root", str(self.root), "08000000"]
            if options:
                args += ["--switch-profile", profile.SELECTOR, *options]
            with self.subTest(options=options), patch.object(sys, "argv", args), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(SystemExit):
                    match.main()
            self.assertFalse((self.root / "docs/match/08000000.md").exists())

    def test_timeout_kills_the_owned_child_group(self):
        child_pid_file = self.root / "child.pid"
        script = ("import pathlib,subprocess,sys,time; "
                  "child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']); "
                  f"pathlib.Path({str(child_pid_file)!r}).write_text(str(child.pid)); time.sleep(60)")
        with self.assertRaises(subprocess.TimeoutExpired):
            match._run_replay_process([sys.executable, "-c", script], self.root, 0.3)
        child_pid = int(child_pid_file.read_text())
        for _attempt in range(50):
            state = Path(f"/proc/{child_pid}/stat")
            try:
                running = state.read_text().split()[2] != "Z"
            except FileNotFoundError:
                running = False
            if not running:
                break
            time.sleep(0.01)
        else:
            self.fail("owned timeout child is still executing")

    def test_cleanup_failure_never_produces_a_match(self):
        report = self.build_report()
        real_cleanup = tempfile.TemporaryDirectory.cleanup

        def failing_cleanup(directory):
            real_cleanup(directory)
            raise OSError("injected cleanup failure")

        with patch.object(tempfile.TemporaryDirectory, "cleanup", side_effect=failing_cleanup, autospec=True):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        self.assertFalse(profile._active.get())

    def test_final_comparison_drift_and_tool_path_swap(self):
        report = self.build_report()
        real_checker = match.plausibility_result

        def changed_checker(result, address):
            parsed = real_checker(result, address)
            (self.root / "include/after.h").write_text("")
            return parsed

        with patch.object(match, "plausibility_result", side_effect=changed_checker):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))
        (self.root / "include/after.h").unlink()
        real_resolver = shutil.which
        resolver_calls = [0]

        def swapped_path(spelling):
            resolver_calls[0] += 1
            if resolver_calls[0] > 10 and spelling == "cpp":
                return sys.executable
            return real_resolver(spelling)

        with patch.object(shutil, "which", side_effect=swapped_path):
            self.assertFalse(match_evidence.report_matches(report, self.root, ADDRESS))

    def test_recomputed_manifest_and_digest_do_not_replace_fresh_source(self):
        result = profile._build_from_source(self.root, ADDRESS)
        manifest = json.loads(result.manifest_json)
        manifest["constants"][0][2] = [manifest["constants"][1][2][0]]
        forged = profile.VerifiedSwitch(result.body, profile.canonical(manifest), result.instruction_count,
            result.source_path, result.source_digest, result.mapping_digest, result.index_digest, result.rom_digest)
        self.assertFalse(match_evidence.report_matches(profile.render_report(ADDRESS, forged), self.root, ADDRESS))
        stripped = profile.render_report(ADDRESS, result)
        stripped = "\n".join(line for line in stripped.splitlines()
                             if not line.startswith("* switch constants"))
        stripped = stripped.replace(profile.SCHEMA, match_evidence.SWITCH_SCHEMA)
        stripped += f"\n* switches: {match_evidence.SWITCH_SUMMARY}\n"
        legacy_manifest = {"calls": manifest["calls"], "switch": manifest["switch"]}
        stripped += f"* switch manifest: `{profile.canonical(legacy_manifest)}`\n"
        stripped += f"* switch proof SHA-256: `{match_evidence.switch_fingerprint(ADDRESS, result.body, legacy_manifest)}`\n"
        self.assertFalse(match_evidence.report_matches(stripped, self.root, ADDRESS))

    def test_rebuild_selector_forwarding_is_explicit_and_terminal(self):
        report = self.build_report()
        self.assertEqual(rebuild.saved_profile_arguments(report, self.root, ADDRESS),
                         ["--switch-profile", profile.SELECTOR])
        with patch.object(profile, "report_matches", return_value=False), self.assertRaises(ValueError):
            rebuild.saved_profile_arguments(report, self.root, ADDRESS)
        with self.assertRaises(ValueError):
            rebuild.saved_profile_arguments(report.replace(profile.SELECTOR, "unknown"), self.root, ADDRESS)

    def test_status_forwards_only_explicit_selection(self):
        report = self.build_report()
        destination = self.root / "docs/match/08000000.md"
        destination.parent.mkdir(parents=True)
        destination.write_text(report)
        with patch.object(status.subprocess, "run", return_value=subprocess.CompletedProcess(
                [], 1, "", "deliberate terminal failure")) as invocation:
            result = status.collect(str(self.root), True, quiet=True)
            command = invocation.call_args.args[0]
            self.assertIn("--switch-profile", command)
            self.assertIn(profile.SELECTOR, command)
            self.assertIn("DOES NOT MATCH", str(result))
            invocation.assert_called_once()
        destination.write_text(report.replace(profile.SELECTOR, "unknown"))
        with patch.object(status.subprocess, "run") as invocation:
            status.collect(str(self.root), True, quiet=True)
            invocation.assert_not_called()

    def test_real_late_issuance_status_and_extent_controls(self):
        address = 0x08150000
        source = SOURCE.replace("08000000", f"{address:08X}")
        (self.root / "src/08000000.c").unlink()
        relative = f"src/{address:08X}.c"
        (self.root / relative).write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            original, _, _ = match.compile_object(runner, workspace, fixed_args(),
                                                   self.root, address, relative)
        linked, body = ordinary_link(self.root, original, address)
        rom = bytes(address - ADDRESS) + body
        (self.root / "fixture.rom").write_bytes(rom)
        (self.root / "config/functions.json").write_text(json.dumps([
            {"rom": f"0x{address:08X}", "end": f"0x{address + len(body):08X}", "mode": "thumb"}]))
        (self.root / "symbols/functions.txt").write_text(
            f"{address:08X} {address + len(body):08X} {len(body)}\n")
        rom_sha1 = hashlib.sha1(rom).hexdigest()
        self.enterContext(patch.object(profile, "ROM_SIZE", len(rom)))
        self.enterContext(patch.object(profile, "ROM_SHA1", rom_sha1))
        tools = Path(match.__file__).resolve().parent
        launcher = (
            "import sys\n"
            f"sys.path.insert(0, {str(tools)!r})\n"
            "import match, switch_constants_profile as profile\n"
            f"profile.ROM_SIZE = {len(rom)}\n"
            f"profile.ROM_SHA1 = {rom_sha1!r}\n"
            f"sys.argv[0] = {str(tools / 'match.py')!r}\n"
            "sys.exit(match.main())\n"
        )
        run = subprocess.run
        records = []
        mutation = None

        def invoke_match(command, **kwargs):
            self.assertEqual(command[:2], [sys.executable, str(tools / "match.py")])
            self.assertIn("--switch-profile", command)
            self.assertIn(profile.SELECTOR, command)
            completed = run([sys.executable, "-c", launcher, *command[2:]], timeout=120, **kwargs)
            self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
            records.append({"command": command, "returncode": completed.returncode,
                            "stdout": completed.stdout, "stderr": completed.stderr})
            if mutation is not None:
                completed.stdout = mutation(completed.stdout)
            return completed

        command = [sys.executable, str(tools / "match.py"), "--root", str(self.root),
                   f"{address:08X}", "--switch-profile", profile.SELECTOR]
        issued = invoke_match(command, capture_output=True, text=True)
        report_path = self.root / f"docs/match/{address:08X}.md"
        report = report_path.read_text()
        with patch.object(status.subprocess, "run", side_effect=invoke_match), \
                patch.object(profile, "_build_from_source", wraps=profile._build_from_source) as replayed:
            result = status.collect(str(self.root), True, quiet=True)
            self.assertEqual(result, (0, 0, 0, 0, [], 1, len(body)))
            self.assertEqual(replayed.call_count, 1)
        self.assertEqual(status.matcher_extent(issued.stdout), len(body))
        extent = f"extent    {len(body)} bytes (complete ELF symbol; {profile.CONTROL_FLOW}; no relocations)"
        self.assertEqual(issued.stdout.splitlines().count(extent), 1)
        controls = (
            ("wrong", lambda output: output.replace(extent, extent.replace(str(len(body)), str(len(body) + 2), 1)),
             "disagrees with the late indexed extent"),
            ("missing", lambda output: output.replace(extent + "\n", ""), "missing or duplicate matcher extent"),
            ("duplicate", lambda output: output + extent + "\n", "missing or duplicate matcher extent"),
            ("malformed", lambda output: output.replace("extent    ", "extent   "), "malformed matcher extent"),
        )
        rejected = []
        for name, mutation, expected in controls:
            with self.subTest(control=name), patch.object(status.subprocess, "run", side_effect=invoke_match):
                result = status.collect(str(self.root), True, quiet=True)
                self.assertEqual(result[5:], (0, 0))
                self.assertEqual(len(result[4]), 1)
                self.assertIn(expected, result[4][0])
                rejected.append({"control": name, "result": result})
        self.assertEqual(report_path.read_text(), report)
        self.assertEqual(list((self.root / "build").iterdir()), [])
        destination = os.environ.get("FFTA_SWITCH_LATE_EVIDENCE")
        if destination:
            Path(destination).write_text(json.dumps({"source": source, "original": original.hex(),
                "linked": linked.hex(), "body": body.hex(), "report": report,
                "fixture_rom_bytes": len(rom), "test_only_rom_sha1": rom_sha1,
                "status_positive": [0, 0, 0, 0, [], 1, len(body)],
                "invocations": records, "rejected": rejected}, indent=2) + "\n")

    def test_emit_no_write_and_failure_leave_no_partial_report(self):
        arguments = ["match.py", "--root", str(self.root), "08000000", "--switch-profile",
                     profile.SELECTOR, "--emit", "build/result.bin", "--no-write"]
        with patch.object(sys, "argv", arguments), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        self.assertEqual((self.root / "build/result.bin").read_bytes(), self.body)
        self.assertFalse((self.root / "docs/match/08000000.md").exists())
        (self.root / "build/result.bin").unlink()
        with patch.object(sys, "argv", arguments), patch.object(profile, "_compile_object", side_effect=RuntimeError("failed")), \
                contextlib.redirect_stdout(io.StringIO()) as output, self.assertRaises(SystemExit):
            match.main()
        self.assertNotIn("MATCH", output.getvalue())
        self.assertFalse((self.root / "build/result.bin").exists())
        self.assertFalse((self.root / "docs/match/08000000.md").exists())


class SwitchConstantsTests(unittest.TestCase):
    def test_explicit_schema(self):
        self.assertEqual(profile.SELECTOR, "two-constants-v2")
        self.assertFalse(profile.selected("* verification: `elf-symbol-thumb-v1`"))
        with self.assertRaises(ValueError):
            profile.selected("* switch constants: unknown")


class ObjectAndCFGTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(__file__).resolve().parents[1] / "build"
        scratch.mkdir(exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(prefix="switch_elf_", dir=scratch)
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)

    def fixture(self, **options):
        original = assemble(self.root, fixture_assembly(**options))
        linked, body = ordinary_link(self.root, original)
        mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{ADDRESS + len(body):08X}", "mode": "thumb"},
                              {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]).encode()
        return original, linked, body, mapping

    def admit(self, original, mapping):
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            (Path(workspace) / "f.o").write_bytes(original)
            return profile._object_bytes(runner, workspace, fixed_args(), match.elf_image(original),
                                          ADDRESS, mapping, bytes(0x2000))[:3]

    def descriptor(self, original, body, mapping):
        relocations = {}
        calls, _, _ = match.call_bindings(match.elf_image(original), "func_08000000", ADDRESS,
                                          mapping, 0x2000, switch_relocations=relocations,
                                          allow_switch_constants=True)
        return calls, relocations, profile.layout(body, ADDRESS, relocations)

    def test_guard_alignment_zero_duplicate_and_call_matrix(self):
        dispatch_classes = set()
        for guard in ("bhi", "bls"):
            for extra in (False, True):
                for call in (False, True):
                    for zero in (False, True):
                        with self.subTest(guard=guard, extra=extra, call=call, zero=zero):
                            original, linked, body, mapping = self.fixture(
                                guard=guard, extra=extra, call=call, zero=zero, duplicate=True)
                            accepted, manifest, count = self.admit(original, mapping)
                            self.assertEqual(accepted, body)
                            self.assertFalse(match.elf_image(linked)["relocations"])
                            self.assertGreater(count, 10)
                            self.assertEqual(len(manifest["calls"]), int(call))
                            self.assertEqual([entry[1] for entry in manifest["constants"]],
                                             [0, 0] if zero else [0xFF00FF00, 0x0F0F0F0F])
                            dispatch_classes.add(manifest["switch"]["dispatch"] % 4)
        self.assertEqual(dispatch_classes, {0, 2})

    def test_base_two_remains_rejected_by_unmodified_ownership_gate(self):
        original, _, _, mapping = self.fixture()
        with self.assertRaisesRegex(ValueError, "alignment"):
            match.call_bindings(match.elf_image(original), "func_08000000", ADDRESS + 2,
                                mapping, 0x2000, switch_relocations={}, allow_switch_constants=True)

    def test_each_constant_requires_its_own_reached_load(self):
        original, _, body, mapping = self.fixture(zero=True)
        calls, relocations, descriptor = self.descriptor(original, body, mapping)
        for site in (0, 2):
            for change in ("remove", "unreachable", "redirect"):
                with self.subTest(site=site, change=change):
                    changed = bytearray(body)
                    if change == "remove":
                        changed[site:site + 2] = bytes.fromhex("c046")
                    elif change == "unreachable":
                        if site == 0:
                            changed[0:2] = bytes.fromhex("ffe7")
                        else:
                            changed[0:2] = bytes.fromhex("00e0")
                    else:
                        word = struct.unpack_from("<H", changed, site)[0]
                        struct.pack_into("<H", changed, site, word + (1 if site == 0 else -1))
                    with self.assertRaises(ValueError):
                        profile._manifest(bytes(changed), ADDRESS, calls, relocations)
        repeated = fixture_assembly(prefix="ldr r2, .Lconstant0\n")
        original = assemble(self.root, repeated)
        _, repeated_body = ordinary_link(self.root, original)
        mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{ADDRESS + len(repeated_body):08X}",
                               "mode": "thumb"}]).encode()
        _, manifest, _ = self.admit(original, mapping)
        self.assertEqual(len(manifest["constants"][0][2]), 2)

    def test_code_cannot_enter_reserved_gap_or_bypass_any_dispatch_op(self):
        original, _, body, mapping = self.fixture(extra=True)
        calls, relocations, descriptor = self.descriptor(original, body, mapping)
        targets = list(range(descriptor["dispatch"] + 10, descriptor["table"] + 8, 2))
        targets += list(range(descriptor["dispatch"], descriptor["dispatch"] + 10, 2))
        targets += [descriptor["guard"]]
        for target in targets:
            changed = bytearray(body)
            struct.pack_into("<H", changed, 0, 0xE000 | ((target - 4) // 2 & 0x7FF))
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile._manifest(bytes(changed), ADDRESS, calls, relocations)

    def test_gap_lengths_nonzero_alignment_and_extra_owned_bytes_reject(self):
        for gap in (".word 0", ".word 0x12345678", ".word 0, 0"):
            with self.subTest(gap=gap):
                original, _, _, mapping = self.fixture(gap=gap)
                with self.assertRaises(ValueError):
                    self.admit(original, mapping)
        original, _, body, mapping = self.fixture(extra=False)
        calls, relocations, descriptor = self.descriptor(original, body, mapping)
        if descriptor["literal"] - 8 == descriptor["dispatch"] + 10:
            original, _, body, mapping = self.fixture(extra=True)
            calls, relocations, descriptor = self.descriptor(original, body, mapping)
        changed = bytearray(body)
        changed[descriptor["dispatch"] + 10] = 1
        with self.assertRaises(ValueError):
            profile._manifest(bytes(changed), ADDRESS, calls, relocations)
        for tail in (".hword 0", ".word 0", ".word 0x12345678"):
            original, _, _, mapping = self.fixture(tail=tail)
            with self.assertRaises(ValueError):
                self.admit(original, mapping)

    def test_guard_register_scale_and_pointer_relationships(self):
        original, _, body, mapping = self.fixture()
        calls, relocations, descriptor = self.descriptor(original, body, mapping)
        mutations = [(descriptor["comparison"], 0x2802), (descriptor["guard"], 0xDC10),
                     (descriptor["dispatch"], 0x0040), (descriptor["dispatch"] + 2, 0x4900),
                     (descriptor["dispatch"] + 4, 0x1880), (descriptor["dispatch"] + 6, 0x6840),
                     (descriptor["dispatch"] + 8, 0x4700)]
        for site, instruction in mutations:
            changed = bytearray(body)
            struct.pack_into("<H", changed, site, instruction)
            with self.subTest(site=site), self.assertRaises(ValueError):
                profile._manifest(bytes(changed), ADDRESS, calls, relocations)

    def test_table_targets_count_and_instruction_interiors(self):
        original, _, body, mapping = self.fixture(call=True)
        calls, relocations, descriptor = self.descriptor(original, body, mapping)
        for value in (1, 0, len(body), descriptor["literal"], next(iter(calls)) - ADDRESS + 2):
            changed, bindings = bytearray(body), dict(relocations)
            bindings[descriptor["table"]] = value
            struct.pack_into("<I", changed, descriptor["table"], ADDRESS + value)
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile._manifest(bytes(changed), ADDRESS, calls, bindings)
        for remove in relocations:
            bindings = dict(relocations)
            del bindings[remove]
            with self.subTest(remove=remove), self.assertRaises(ValueError):
                profile._manifest(body, ADDRESS, calls, bindings)

    def test_actual_raw_relocation_mutations_are_not_filtered(self):
        original, _, body, mapping = self.fixture()
        image = match.elf_image(original)
        section_index = image["relocations"][0]
        section = image["sections"][section_index]
        raw_offset, raw_info = struct.unpack_from("<II", original, section[4])
        _, _, descriptor = self.descriptor(original, body, mapping)
        changes = [("unknown-type", raw_offset, raw_info & ~255 | 255),
                   ("before-constant", descriptor["literal"] - 10, raw_info),
                   ("alignment", descriptor["dispatch"] + 10, raw_info),
                   ("duplicate", struct.unpack_from("<I", original, section[4] + 8)[0], raw_info),
                   ("past-symbol", len(body) - 2, raw_info), ("bad-symbol", raw_offset, 0xFFFFFF02)]
        for name, offset, info in changes:
            changed = bytearray(original)
            struct.pack_into("<II", changed, section[4], offset, info)
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.admit(bytes(changed), mapping)
        section_table = struct.unpack_from("<I", original, 32)[0]
        for field, value in ((1, 4), (7, 0), (6, 0), (9, 12), (5, section[5] - 1)):
            changed = bytearray(original)
            struct.pack_into("<I", changed, section_table + section_index * 40 + field * 4, value)
            with self.subTest(field=field), self.assertRaises((ValueError, struct.error)):
                self.admit(bytes(changed), mapping)

    def test_section_symbol_and_call_identity_mutations(self):
        original, _, _, mapping = self.fixture(call=True)
        image = match.elf_image(original)
        text_symbol = next(item for item in image["symbols"]
                           if item["type"] == 3 and item["section"] == image["text_index"])
        call_symbol = next(item for item in image["symbols"] if item["name"] == "func_08001000")
        for selected, field, value in ((text_symbol, "name", "label"), (text_symbol, "type", 0),
                                       (text_symbol, "bind", 1), (text_symbol, "value", 2),
                                       (call_symbol, "name", "runtime"), (call_symbol, "value", 2),
                                       (call_symbol, "bind", 0), (call_symbol, "section", 1)):
            changed = copy.deepcopy(image)
            target = next(item for item in changed["symbols"] if item == selected)
            target[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                profile._original_records(changed, ADDRESS, mapping, 0x2000)
        changed = copy.deepcopy(image)
        changed["symbols"].append(copy.deepcopy(text_symbol))
        with self.assertRaises(ValueError):
            profile._original_records(changed, ADDRESS, mapping, 0x2000)
        for change in ("duplicate", "arm", "missing", "odd"):
            entries = json.loads(mapping)
            if change == "duplicate":
                entries.append(dict(entries[-1]))
            elif change == "arm":
                entries[-1]["mode"] = "arm"
            elif change == "missing":
                entries.pop()
            else:
                entries[-1]["rom"] = "0x08001001"
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile._original_records(image, ADDRESS, json.dumps(entries).encode(), 0x2000)

    def test_linker_cannot_change_any_unrelocated_surface(self):
        original_raw, linked_raw, body, mapping = self.fixture(extra=True)
        original, linked = match.elf_image(original_raw), match.elf_image(linked_raw)
        relocations = {}
        calls, targets, objects = match.call_bindings(original, "func_08000000", ADDRESS, mapping,
            0x2000, switch_relocations=relocations, allow_switch_constants=True)
        descriptor = profile.layout(body, ADDRESS, relocations)
        for site in (0, descriptor["literal"] - 8, descriptor["literal"] - 4,
                     descriptor["dispatch"] + 10):
            changed = copy.deepcopy(linked)
            text = bytearray(changed["text"])
            text[site] ^= 1
            changed["text"] = bytes(text)
            with self.subTest(site=site), self.assertRaises(ValueError):
                profile._linked_bytes(original, changed, ADDRESS,
                    profile._original_records(original, ADDRESS, mapping, 0x2000), calls, targets, relocations)
        for change in ("residual", "veneer", "mode", "address", "size", "allocated"):
            changed = copy.deepcopy(linked)
            symbol = next(item for item in changed["symbols"] if item["name"] == "func_08000000")
            if change == "residual":
                changed["relocations"] = [1]
            elif change == "veneer":
                changed["text"] += b"\0\0\0\0"
            elif change == "mode":
                symbol["value"] &= ~1
            elif change == "address":
                symbol["value"] += 4
            elif change == "size":
                symbol["size"] -= 2
            else:
                changed["sections"].append((0, 1, 2, 0, 0, 4, 0, 0, 4, 0))
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile._linked_bytes(original, changed, ADDRESS,
                    profile._original_records(original, ADDRESS, mapping, 0x2000), calls, targets, relocations)

    def test_no_frame_runtime_indirect_callback_or_extra_function_admission(self):
        variants = (fixture_assembly(prefix="sub sp, #4", tail="add sp, #4"),
                    fixture_assembly(first="ldr r2, [sp, #0]"),
                    fixture_assembly(tail="bx r0"),
                    fixture_assembly().replace("bx lr", "bx r3"),
                    fixture_assembly().replace(".word 0xFF00FF00", ".word func_08001000"),
                    fixture_assembly(call=True).replace("func_08001000", "func_0814274C"))
        for assembly in variants:
            original = assemble(self.root, assembly)
            image = match.elf_image(original)
            size = next(item["size"] for item in image["symbols"] if item["name"] == "func_08000000")
            mapping = json.dumps([{"rom": "0x08000000", "end": f"0x{ADDRESS + size:08X}", "mode": "thumb"},
                                  {"rom": "0x08001000", "end": "0x08001002", "mode": "thumb"}]).encode()
            with self.subTest(assembly=assembly[-100:]), self.assertRaises(ValueError):
                self.admit(original, mapping)
        for extra in (".type helper, %function\n.thumb_func\nhelper:\nbx lr\n.size helper, . - helper\n",
                      ".data\n.word 1\n"):
            original = assemble(self.root, fixture_assembly() + extra)
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                self.admit(original, mapping)

    def test_truncated_and_wrong_architecture_elf_reject_before_binding(self):
        original, _, _, mapping = self.fixture()
        malformed = [original[:10], original[:100], original[:-32]]
        for offset, replacement in ((4, b"\x02"), (5, b"\x02"), (18, b"\x03\x00")):
            changed = bytearray(original)
            changed[offset:offset + len(replacement)] = replacement
            malformed.append(bytes(changed))
        for raw in malformed:
            with self.subTest(size=len(raw)), self.assertRaises((ValueError, IndexError, struct.error)):
                self.admit(raw, mapping)

    def test_lower_optins_are_boolean_isolated_and_default_off(self):
        original, _, body, mapping = self.fixture()
        image = match.elf_image(original)
        for enabled in (False, 0, 1, "true", None):
            with self.subTest(enabled=enabled), self.assertRaises(ValueError):
                match.call_bindings(image, "func_08000000", ADDRESS, mapping, 0x2000,
                                    switch_relocations={}, allow_switch_constants=enabled)
        for option in ("data_mapping", "function_relocations", "udivsi3_bindings", "modsi3_bindings",
                       "divsi3_bindings", "double_bindings", "double_index"):
            with self.subTest(option=option), self.assertRaises(ValueError):
                match.call_bindings(image, "func_08000000", ADDRESS, mapping, 0x2000,
                                    switch_relocations={}, allow_switch_constants=True, **{option: {}})
        for option in ("allow_switch_data", "allow_preloaded_switch", "function_thunks"):
            with self.subTest(option=option), self.assertRaises(ValueError):
                match.call_bindings(image, "func_08000000", ADDRESS, mapping, 0x2000,
                                    switch_relocations={}, allow_switch_constants=True, **{option: True})
        _, relocations, _ = self.descriptor(original, body, mapping)
        for option in ("buffer_proof", "call_resolver", "switch_data_relocations", "udivsi3_context",
                       "modsi3_context", "divsi3_context", "inert_spin_context", "double_context", "function_thunk_context"):
            with self.subTest(option=option), self.assertRaises(ValueError):
                match.verify_leaf_instructions(body, ADDRESS, True, switch_relocations=relocations,
                                               allow_switch_constants=True, **{option: {}})


if __name__ == "__main__":
    unittest.main()
