"""Allowlisted volatile records and the semantic check on every selector path.

match.py checks a source that uses an allowlisted volatile object once, before
any selector runs; selectors that write their own reports get the records
carried into that report, and match_evidence.report_matches compares the
records centrally and hands each profile validator the report without them.
"""
import io
import json
import os
import re
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import standing_premise
import match_evidence
import report_fixtures
import plausible
import addressed_signed_runtime_profile as addressed
import owner_admission_profile as owner
import volatile_semantics
import test_addressed_signed_runtime_profile as addressed_fixtures

A = 0x08010000
ENTRY = plausible.volatile_allow_entries()[0]
SYMBOL = ENTRY["symbol"]
SEMANTICS = volatile_semantics.record(SYMBOL, [(f"func_{A:08X}", 1, [2], [])])
HEADER = ("#ifndef CONTROL_FLAGS_H\n#define CONTROL_FLAGS_H\n"
          "typedef unsigned char u8;\ntypedef unsigned short u16;\n{declaration}\n#endif\n")
# the first two volatile byte members of the entry's declaration, so the
# tests follow the allowlist entry whatever its members are called
PINNED = re.findall(r"\bvolatile u8 (\w+) : 8;", ENTRY["declaration"])[:2]
STORE = f"{SYMBOL}.{PINNED[0]} = 1;"
PLANTED = f"(void){SYMBOL}.{PINNED[0]}; {SYMBOL}.{PINNED[1]} = 1;"
SCRATCH = Path(__file__).resolve().parents[1] / "build/tests"
COMPILER = (Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which("cpp") and
            shutil.which("arm-none-eabi-as") and shutil.which("arm-none-eabi-objcopy"))


def header_user(root, body=STORE):
    """a decomp tree whose addressed source uses the allowlisted object"""
    for name in ("src", "include", "config", "symbols", "docs/match", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    (root / ENTRY["header"]).write_text(
        HEADER.format(declaration=ENTRY["declaration"].replace("; ", ";\n    ")))
    (root / "config/data_symbols.json").write_text(json.dumps({SYMBOL: ENTRY["address"]}) + "\n")
    (root / f"src/{A:08X}.c").write_text(
        f'#include "control_flags.h"\nvoid func_{A:08X}(void)\n{{\n    {body}\n}}\n')


def uses(root):
    return plausible.allowlisted_volatile_uses(root, A)


def run_main(argv):
    output = io.StringIO()
    with patch.object(sys, "argv", ["match.py", *argv]), redirect_stdout(output):
        try:
            status = match.main()
        except SystemExit as stop:
            return stop.code, output.getvalue()
    return status, output.getvalue()


def without(report, prefix):
    return "\n".join(line for line in report.split("\n") if not line.startswith(prefix))


class RecordPlacementTests(unittest.TestCase):
    REPORT = "# 0x08010000\n\n* verification: `x`\n* source plausibility: plausible\n* rest: y\n\n**MATCH**\n"
    RECORDS = ["* allowlisted volatile: `s`", "* allowlisted volatile semantics: `s`"]

    def test_records_follow_the_plausible_source_line(self):
        carried = match_evidence.carry_volatile_records(self.REPORT, self.RECORDS)
        self.assertEqual(carried.split("\n")[3:7], ["* source plausibility: plausible", *self.RECORDS,
                                                    "* rest: y"])
        self.assertEqual(match_evidence.carry_volatile_records(self.REPORT, []), self.REPORT)
        self.assertEqual(match_evidence.strip_volatile_records(carried, self.RECORDS), self.REPORT)

    def test_a_report_that_cannot_carry_them_is_refused(self):
        for report in (self.REPORT.replace("* source plausibility: plausible\n", ""),
                       self.REPORT.replace("plausible\n", "IMPLAUSIBLE\n"),
                       self.REPORT + "* source plausibility: plausible\n",
                       match_evidence.carry_volatile_records(self.REPORT, self.RECORDS)):
            with self.subTest(report=report), self.assertRaises(ValueError):
                match_evidence.carry_volatile_records(report, self.RECORDS)
        with self.assertRaises(ValueError):
            match_evidence.carry_volatile_records(self.REPORT + self.RECORDS[0] + "\n", [])

    def test_stripping_requires_exactly_the_recomputed_records(self):
        carried = match_evidence.carry_volatile_records(self.REPORT, self.RECORDS)
        for report, records in ((carried, self.RECORDS[:1]), (self.REPORT, self.RECORDS),
                                (carried, []), (carried.replace("semantics: `s`", "semantics: `t`"), self.RECORDS),
                                (carried.replace(self.RECORDS[1], "  " + self.RECORDS[1]), self.RECORDS),
                                (self.REPORT + "\n".join(self.RECORDS) + "\n", self.RECORDS),
                                (carried.replace(self.RECORDS[0] + "\n", "* other: z\n" + self.RECORDS[0] + "\n"),
                                 self.RECORDS),
                                (carried.replace(self.RECORDS[1], "* other: z\n" + self.RECORDS[1]), self.RECORDS),
                                (carried + "* source plausibility: plausible\n", self.RECORDS)):
            with self.subTest(report=report, records=records), self.assertRaises(ValueError):
                match_evidence.strip_volatile_records(report, records)


class AddressedRuntimeRecordTests(unittest.TestCase):
    """--addressed-signed-runtime-profile: the report writer is the profile's own"""
    setUp = addressed_fixtures.AddressedSignedRuntimeTests.setUp
    fixture = addressed_fixtures.AddressedSignedRuntimeTests.fixture
    synthetic_result = addressed_fixtures.AddressedSignedRuntimeTests.synthetic_result

    def tree(self):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="volatile_addressed_", dir=SCRATCH)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        header_user(root)
        f = self.fixture()
        (root / "config/functions.json").write_bytes(f["mapping"])
        (root / "symbols/functions.txt").write_bytes(f["index"])
        (root / "baserom.bin").write_bytes(f["rom"])
        environment = patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin"))
        environment.start()
        self.addCleanup(environment.stop)
        return root, f

    def argv(self, root, *extra):
        return ["--root", str(root), "--addressed-signed-runtime-profile", addressed.SELECTOR, *extra, f"{A:08X}"]

    def test_header_user_report_carries_records_and_matches(self):
        root, f = self.tree()
        result = self.synthetic_result(root, f)
        with patch.object(addressed, "build", return_value=result), \
                patch.object(match, "allowlisted_volatile_semantics", return_value=[SEMANTICS]) as semantic:
            status, output = run_main(self.argv(root))
            self.assertEqual(status, 0, output)
            semantic.assert_called()
            records = uses(root) + [SEMANTICS]
            report = (root / f"docs/match/{A:08X}.md").read_text()
            lines = report.split("\n")
            anchor = lines.index("* source plausibility: plausible")
            self.assertEqual(lines[anchor + 1:anchor + 3], records)
            self.assertEqual(standing_premise.strip(report, root, A),
                             match_evidence.carry_volatile_records(addressed.render(result), records))
            printed = output.splitlines()
            self.assertLess(printed.index(f"volatile semantics{SEMANTICS.split('semantics', 1)[1]}"),
                            printed.index("verdict MATCH - byte identical"))
            self.assertTrue(match_evidence.report_matches(report, root, A))
            self.assertFalse(match_evidence.report_matches(without(report, "* allowlisted volatile semantics"),
                                                           root, A))
            self.assertFalse(match_evidence.report_matches(without(report, "* allowlisted volatile"), root, A))
            self.assertFalse(match_evidence.report_matches(report.replace("agrees on", "agrees  on"), root, A))
            self.assertFalse(match_evidence.report_matches(
                report.replace(SEMANTICS, SEMANTICS + "\n" + SEMANTICS), root, A))
            self.assertFalse(report_fixtures.replay(addressed.render(result), root, A))
        with patch.object(match, "allowlisted_volatile_semantics",
                          side_effect=volatile_semantics.SemanticError("dead load")):
            self.assertFalse(match_evidence.report_matches(report, root, A))

    def test_failing_semantic_check_is_implausible_before_the_selector(self):
        root, _ = self.tree()
        with patch.object(addressed, "build", side_effect=AssertionError("selector must not run")), \
                patch.object(match, "allowlisted_volatile_semantics",
                             side_effect=volatile_semantics.SemanticError("planted dead load")):
            status, output = run_main(self.argv(root))
        self.assertIn("source    IMPLAUSIBLE", status)
        self.assertIn("allowlisted volatile semantic check: planted dead load", status)
        self.assertNotIn("MATCH", output + status)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())

    def test_a_writer_that_cannot_carry_records_is_refused(self):
        root, f = self.tree()
        result = self.synthetic_result(root, f)
        plain = addressed.render(result).replace("* source plausibility: plausible\n", "")
        with patch.object(addressed, "build", return_value=result), \
                patch.object(addressed, "render", return_value=plain), \
                patch.object(match, "allowlisted_volatile_semantics", return_value=[SEMANTICS]):
            status, output = run_main(self.argv(root, "--emit", "build/symbol.bin"))
        self.assertIn("allowlisted volatile records not carried", status)
        self.assertNotIn("verdict MATCH", output)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())
        self.assertFalse((root / "build/symbol.bin").exists())

    def test_source_changed_during_the_selector_is_refused(self):
        root, f = self.tree()
        result = self.synthetic_result(root, f)

        def edit(*args, **kwargs):
            source = root / f"src/{A:08X}.c"
            source.write_text(source.read_text() + "/* edited */\n")
            return result
        with patch.object(addressed, "build", side_effect=edit), \
                patch.object(match, "allowlisted_volatile_semantics", return_value=[SEMANTICS]):
            status, output = run_main(self.argv(root))
        self.assertIn("source or headers changed", status)
        self.assertNotIn("verdict MATCH", output)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())

    def test_source_that_becomes_a_user_after_the_check_is_refused(self):
        # review repro (race.py): the check sees a non-user, then the source
        # starts including the header before the selector writes its report
        root, f = self.tree()
        source = root / f"src/{A:08X}.c"
        source.write_text("/* synthetic source token */\n")
        result = self.synthetic_result(root, f)
        check = match.allowlisted_volatile_check

        def raced(*args):
            outcome = check(*args)
            self.assertEqual(outcome[:2], ([], None))
            source.write_text('#include "control_flags.h"\n/* synthetic source token */\n')
            return outcome
        with patch.object(addressed, "build", return_value=result), \
                patch.object(match, "allowlisted_volatile_check", side_effect=raced):
            status, output = run_main(self.argv(root))
        # a non-user's selector output is not held back, but the run exits
        # non-zero with the refusal and its report is removed
        self.assertIn("source or headers changed", status)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())

    def test_non_user_selector_result_passes_through(self):
        root, _ = self.tree()
        (root / f"src/{A:08X}.c").write_text("/* synthetic source token */\n")

        def selector(*args):
            print("selector output")
            return 19
        with patch.object(addressed, "issue", side_effect=selector):
            status, output = run_main(self.argv(root))
        self.assertEqual((status, output), (19, "selector output\n"))

    def test_sources_without_the_object_are_unchanged(self):
        root, f = self.tree()
        (root / f"src/{A:08X}.c").write_text("/* synthetic source token */\n")
        result = self.synthetic_result(root, f)
        with patch.object(addressed, "build", return_value=result), \
                patch.object(match, "allowlisted_volatile_semantics", side_effect=AssertionError("unused")):
            status, output = run_main(self.argv(root))
        self.assertEqual(status, 0, output)
        self.assertEqual(standing_premise.strip((root / f"docs/match/{A:08X}.md").read_text(), root, A),
                         addressed.render(result))


SELECTOR = owner.ACYCLIC_SELECTOR


def owner_report(data):
    """an owner report as owner.render would shape it (build and render are mocked)"""
    return "\n".join([f"# 0x{A:08X}", "", f"* verification: `{owner.ACYCLIC_SCHEMA}`",
                      f"* owner runtime: {SELECTOR}", f"* control flow: {owner.ACYCLIC_CONTROL_FLOW}",
                      "* verified extent: complete ELF function symbol, including literal pools",
                      "* relocations: none", "* source plausibility: plausible", "* hand-asm allow list: not listed",
                      f"* owner runtime evidence: `{owner.text({'manifest': {}})}`", f"* compiled : `{data.hex()}`",
                      f"* ROM bytes: `{data.hex()}` ({len(data)} bytes)", "",
                      f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes", ""])


class OwnerRuntimeRecordTests(unittest.TestCase):
    """--owner-runtime-profile: the owner validator re-renders and compares exactly"""
    DATA = bytes.fromhex("7047")

    def tree(self, body=STORE):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="volatile_owner_", dir=SCRATCH)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        header_user(root, body)
        report_fixtures.rom_holding(self, OwnerRuntimeRecordTests.DATA, A)
        return root

    def profile(self):
        result = (self.DATA,)
        return (patch.object(owner, "build", return_value=result),
                patch.object(owner, "render", return_value=owner_report(self.DATA)))

    def run_owner(self, root):
        return run_main(["--root", str(root), "--owner-runtime-profile", SELECTOR, f"{A:08X}"])

    def check_report(self, root, semantic_records):
        records = uses(root) + semantic_records
        report = (root / f"docs/match/{A:08X}.md").read_text()
        self.assertEqual(report, report_fixtures.carried(
            match_evidence.carry_volatile_records(owner_report(self.DATA), records), root, A))
        self.assertTrue(match_evidence.report_matches(report, root, A))
        self.assertFalse(match_evidence.report_matches(report_fixtures.carried(owner_report(self.DATA), root, A),
                                                       root, A))
        self.assertFalse(match_evidence.report_matches(without(report, "* allowlisted volatile semantics"), root, A))
        self.assertFalse(match_evidence.report_matches(report.replace("agrees on", "agrees  on"), root, A))
        changed = root / ENTRY["header"]
        saved = changed.read_bytes()
        changed.write_bytes(saved + b"/* changed */\n")
        try:
            self.assertFalse(match_evidence.report_matches(report, root, A))
        finally:
            changed.write_bytes(saved)

    def test_header_user_report_carries_records_and_matches(self):
        root = self.tree()
        build, render = self.profile()
        with build, render, patch.object(match, "allowlisted_volatile_semantics", return_value=[SEMANTICS]):
            status, output = self.run_owner(root)
            self.assertEqual(status, 0, output)
            self.check_report(root, [SEMANTICS])

    def test_failing_semantic_check_is_implausible_before_the_selector(self):
        root = self.tree()
        with patch.object(owner, "build", side_effect=AssertionError("selector must not run")), \
                patch.object(match, "allowlisted_volatile_semantics",
                             side_effect=volatile_semantics.SemanticError("planted dead load")):
            status, output = self.run_owner(root)
        self.assertIn("source    IMPLAUSIBLE", status)
        self.assertNotIn("MATCH", output + status)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())

    @unittest.skipUnless(COMPILER, "fixed compiler required")
    def test_compiled_semantic_check_runs_on_the_owner_path(self):
        root = self.tree()
        build, render = self.profile()
        with build, render:
            status, output = self.run_owner(root)
            self.assertEqual(status, 0, output)
            (semantic,) = match.allowlisted_volatile_semantics(root, A)
            self.assertTrue(semantic.startswith("* allowlisted volatile semantics: "))
            self.assertIn(f"volatile semantics{semantic.split('semantics', 1)[1]}", output.splitlines())
            self.check_report(root, [semantic])

    @unittest.skipUnless(COMPILER, "fixed compiler required")
    def test_compiled_planted_read_is_implausible_on_profile_paths(self):
        root = self.tree(PLANTED)
        for module, argv in ((owner, ["--owner-runtime-profile", SELECTOR]),
                             (addressed, ["--addressed-signed-runtime-profile", addressed.SELECTOR])):
            with self.subTest(selector=argv[0]), \
                    patch.object(module, "build", side_effect=AssertionError("selector must not run")):
                status, output = run_main(["--root", str(root), *argv, f"{A:08X}"])
                self.assertIn("source    IMPLAUSIBLE", status)
                self.assertIn("allowlisted volatile semantic check", status)
                self.assertIn("dead load", status)
                self.assertNotIn("MATCH", output)
                self.assertFalse((root / f"docs/match/{A:08X}.md").exists())


@unittest.skipUnless(COMPILER, "fixed compiler required")
class GenericPathRaceTests(unittest.TestCase):
    """the generic writer refuses a source edited after the volatile check"""

    def test_source_edited_after_the_check_is_refused(self):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="volatile_generic_", dir=SCRATCH) as directory:
            root = Path(directory)
            header_user(root)
            source = root / f"src/{A:08X}.c"
            source.write_text(f"int func_{A:08X}(int a)\n{{\n    return a + 1;\n}}\n")
            (root / "symbols/functions.txt").write_text(f"{A:08X} {A + 4:08X} 4 2 return\n")
            (root / "baserom.bin").write_bytes(bytes(A - match.ROM_BASE + 0x100))
            check = match.allowlisted_volatile_check

            def raced(*args):
                outcome = check(*args)
                source.write_text('#include "control_flags.h"\n' + source.read_text())
                return outcome
            with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")), \
                    patch.object(match, "allowlisted_volatile_check", side_effect=raced):
                status, output = run_main(["--root", str(root), f"{A:08X}"])
            self.assertIn("source or headers changed", str(status))
            self.assertNotIn("verdict", output)
            self.assertFalse((root / f"docs/match/{A:08X}.md").exists())


if __name__ == "__main__":
    unittest.main()
