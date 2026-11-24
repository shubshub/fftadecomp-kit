"""Cached replays bind the whole saved report, and status.py and rebuild.py recover the same selectors.

Issue #354. A replay re-verifies a report's evidence and then re-renders the
complete report with match.py's own writer, so an added, removed, indented,
duplicated or reordered line, a changed source path, a forged hand-asm line
and an edited or missing listing all fail.

* EndToEndTests compiles small sources with agbcc, issues each report with
  match.main() and replays it: the plain, frame, call, self-call, data,
  function-address and switch schemas.
* BranchTests covers every other built-in replay branch and the profile
  replays that used to check lines one at a time. Their verifiers are mocked
  (other modules test them); what is under test is that each branch hands its
  evidence to the whole-text comparison.
* SelectorTests holds status.py --verify and rebuild.py --compiled to the same
  match.py arguments for one report of every selector family.
"""

import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.dont_write_bytecode = True
KIT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(KIT / "tools"))
import match
import match_evidence as evidence
import report_fixtures

BASE = 0x08000000
CALLEE = 0x08000400
ROM_SIZE = 0x1000
DATA = json.dumps({"data_02000100": "0x02000100"}).encode()


def tampers(report):
    """name -> an edited copy of a complete saved report; every one must fail replay."""
    lines = report.split("\n")
    index = {line.split(":", 1)[0]: number for number, line in enumerate(lines) if line.startswith("* ")}
    plausible = index["* source plausibility"]
    fence = [number for number, line in enumerate(lines) if line.startswith("```")]
    row = fence[0] + 2

    def insert(at, *added):
        return "\n".join(lines[:at] + list(added) + lines[at:])

    edits = {
        "added claim line": insert(plausible + 1, "* numeric equivalence: proven for every input"),
        "premise line from another schema": insert(plausible + 1, "* canonical thunk callee ABI: forged"),
        "indented claim line": insert(plausible + 1, "  * numeric equivalence: proven"),
        "duplicated line": insert(index["* relocations"], lines[index["* relocations"]]),
        "reordered lines": "\n".join(lines[:index["* verified extent"]] + [
            lines[index["* relocations"]], lines[index["* verified extent"]]] + lines[index["* relocations"] + 1:]),
        "source path": report.replace("* source: `src/", "* source: `src/forged/", 1),
        "hand-asm listed": report.replace("* hand-asm allow list: not listed",
                                          "* hand-asm allow list: listed (forged)", 1),
        "hand-asm removed": report.replace("* hand-asm allow list: not listed\n", "", 1),
        "listing row edited": "\n".join(lines[:row] + [lines[row] + " ; edited"] + lines[row + 1:]),
        "listing row removed": "\n".join(lines[:row] + lines[row + 1:]),
        "listing row added": insert(row, lines[row]),
        "listing removed": "\n".join(lines[:fence[0]] + lines[fence[1] + 1:]),
        "listing header": report.replace("compiled" + " " * 32 + "rom", "compiled rom", 1),
        "header": report.replace("# match report - ", "# match report (forged) - ", 1),
        "blank line removed": report.replace("\n\n**MATCH", "\n**MATCH", 1),
        "trailing text": report + "forged\n",
        "trailing newline removed": report[:-1],
        "CRLF line endings": report.replace("\n", "\r\n"),
    }
    assert all(text != report for text in edits.values()), [name for name, text in edits.items() if text == report]
    return edits


def decode(body, address=BASE):
    return report_fixtures.decode(body, address)


def thumb_bl(site, target):
    offset = (target - (site + 4)) >> 1
    return struct.pack("<HH", 0xF000 | (offset >> 11) & 0x7FF, 0xF800 | offset & 0x7FF)


class Root:
    """A decomp root with one source at BASE, a mapping, data symbols, an index and a ROM holding `body`."""

    def __init__(self, test, body, source="int func_08000000(int a) { return a; }\n"):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="closed_report_", dir=scratch)
        test.addCleanup(directory.cleanup)
        self.path = Path(directory.name)
        for name in ("src", "include", "config", "symbols", "docs/match"):
            (self.path / name).mkdir(parents=True)
        (self.path / "src/08000000.c").write_text(source)
        entries = [(BASE, len(body)), (CALLEE, 2)]
        self.mapping = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{start + size:08X}", "mode": "thumb"}
                                   for start, size in entries]).encode()
        (self.path / "config/functions.json").write_bytes(self.mapping)
        (self.path / "config/data_symbols.json").write_bytes(DATA)
        (self.path / "symbols/functions.txt").write_text(
            "".join(f"{start:08X} {start + size:08X} {size} 1 return\n" for start, size in entries))
        self.index = (self.path / "symbols/functions.txt").read_bytes()
        rom = bytearray(ROM_SIZE)
        rom[:len(body)] = body
        struct.pack_into("<H", rom, CALLEE - BASE, 0x4770)
        self.rom = bytes(rom)
        (self.path / "baserom.bin").write_bytes(self.rom)
        environment = {key: value for key, value in os.environ.items() if key != "FFTA_ROM"}
        environment.update(TMPDIR=str(self.path), PYTHONDONTWRITEBYTECODE="1")
        test.enterContext(mock.patch.dict(os.environ, environment, clear=True))

    def render(self, body, instructions, schema, **parts):
        """The report match.py writes for this evidence: the expected saved report."""
        listing, _, _ = match.report_listing(instructions, bytes(body), BASE, len(body), True)
        parts.setdefault("mapping", self.mapping)
        parts.setdefault("data_mapping", DATA)
        return match.render_report(
            addr=BASE, src_rel="src/08000000.c", schema=schema,
            fingerprint=evidence.source_fingerprint(self.path, BASE),
            compiler=f"{match.DEFAULT_CC} {match.DEFAULT_FLAGS}", want=bytes(body), span=len(body),
            got_body=bytes(body), verdict="MATCH - byte identical", same_bytes=len(body), listing=listing,
            framed_profile=match.uses_stack_frame(instructions), **parts)


class ClosureAssertions:
    def assert_closed(self, report, root):
        self.assertTrue(evidence.report_matches(report, root, BASE), "the untampered report must replay")
        for name, text in tampers(report).items():
            with self.subTest(tamper=name):
                self.assertFalse(evidence.report_matches(text, root, BASE))


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file(), "agbcc required")
class EndToEndTests(ClosureAssertions, unittest.TestCase):
    SOURCES = {
        evidence.SCHEMA: "int func_08000000(int a) { return a * 3 + 1; }\n",
        evidence.FRAMED_SCHEMA: "int func_08000000(int a, int b, int c, int d, int e) { return a + e; }\n",
        evidence.LINKED_SCHEMA: "void func_08000400(void);\nvoid func_08000000(void) { func_08000400(); }\n",
        evidence.FRAMED_LINKED_SCHEMA: (
            "void func_08000400(int);\n"
            "void func_08000000(int a, int b, int c, int d, int e) { func_08000400(e); }\n"),
        evidence.DATA_SCHEMA: "extern int data_02000100;\nint func_08000000(void) { return data_02000100; }\n",
        evidence.FRAMED_DATA_SCHEMA: (
            "extern int data_02000100;\n"
            "int func_08000000(int a, int b, int c, int d, int e) { return data_02000100 + e; }\n"),
        "data with calls": ("extern int data_02000100;\nvoid func_08000400(int);\n"
                            "void func_08000000(void) { func_08000400(data_02000100); }\n"),
        "self call": "int func_08000000(int a) { if (a <= 0) return 0; return func_08000000(a - 1) + 1; }\n",
        evidence.FUNCTION_ADDRESS_SCHEMA: (
            "void func_08000400(void);\nvoid *func_08000000(void) { return (void *)func_08000400; }\n"),
        evidence.SWITCH_SCHEMA: (
            "int func_08000000(int a) {\n    switch (a) {\n    case 0: return 5;\n    case 1: return 9;\n"
            "    case 2: return 13;\n    case 3: return 2;\n    case 4: return 7;\n    default: return 0;\n"
            "    }\n}\n"),
    }

    def issue(self, source):
        """Compile `source`, lay its bytes into the ROM and write its report with match.main()."""
        root = Root(self, b"\x70\x47", source)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=root.path, timeout=120)
        with runner.workspace() as workspace:
            object_data, text_data, original = match.compile_object(
                runner, workspace, args, root.path, BASE, "src/08000000.c")
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            entries = [(BASE, symbol["size"]), (CALLEE, 2)]
            mapping = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{start + size:08X}", "mode": "thumb"}
                                  for start, size in entries]).encode()
            (root.path / "config/functions.json").write_bytes(mapping)
            (root.path / "symbols/functions.txt").write_text(
                "".join(f"{start:08X} {start + size:08X} {size} 1 return\n" for start, size in entries))
            if original["relocations"]:
                body, _, _ = match.link_calls(runner, workspace, args, original, BASE, mapping, ROM_SIZE, root.rom,
                                              DATA, {}, {}, allow_self_call=True)
            else:
                body = match.function_bytes(object_data, text_data, "func_08000000", BASE, True)
        rom = bytearray(root.rom)
        rom[:len(body)] = body
        (root.path / "baserom.bin").write_bytes(rom)
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["match.py", "--root", str(root.path), f"0x{BASE:08X}"]), \
                mock.patch.object(match, "ROOT", match.ROOT), contextlib.redirect_stdout(output):
            self.assertEqual(match.main(), 0, output.getvalue())
        return root.path, (root.path / f"docs/match/{BASE:08X}.md").read_text()

    def test_every_saved_report_line_is_bound(self):
        for family, source in self.SOURCES.items():
            with self.subTest(family=family):
                root, report = self.issue(source)
                schema = re.search(r"^\* verification: `([^`]+)`$", report, re.M)[1]
                if family.startswith("elf-symbol"):
                    self.assertEqual(schema, family)
                if family == "self call":
                    self.assertIn("* self call sites: ", report)
                if family == "data with calls":
                    self.assertIn(f"* control flow: {evidence.CALL_SUMMARY}\n", report)
                # the writer lists every verified instruction, compiled beside ROM
                listing = report.split("```\n")[1].splitlines()
                self.assertEqual(listing[0].split(), ["compiled", "rom"])
                self.assertGreater(len(listing), 2)
                self.assertTrue(all(row[:40].strip() == row[40:].strip() != "" for row in listing[1:]))
                self.assert_closed(report, root)

    def test_schema_choices_are_rederived(self):
        root, report = self.issue(self.SOURCES[evidence.FRAMED_SCHEMA])
        unframed = report.replace(evidence.FRAMED_SCHEMA, evidence.SCHEMA).replace(
            f"* stack frame: {evidence.STACK_SUMMARY}\n", "")
        self.assertFalse(evidence.report_matches(unframed, root, BASE))
        # the schema name alone, with every other line intact
        self.assertFalse(evidence.report_matches(report.replace(evidence.FRAMED_SCHEMA, evidence.SCHEMA), root, BASE))
        root, report = self.issue(self.SOURCES[evidence.FRAMED_LINKED_SCHEMA])
        self.assertFalse(evidence.report_matches(
            report.replace(evidence.FRAMED_LINKED_SCHEMA, evidence.LINKED_SCHEMA), root, BASE))
        root, report = self.issue(self.SOURCES["data with calls"])
        self.assertTrue(evidence.report_matches(report, root, BASE))
        leaf = report.replace(f"* control flow: {evidence.CALL_SUMMARY}", "* control flow: closed leaf CFG")
        self.assertFalse(evidence.report_matches(leaf, root, BASE))
        root, report = self.issue(self.SOURCES[evidence.DATA_SCHEMA])
        called = report.replace("* control flow: closed leaf CFG", f"* control flow: {evidence.CALL_SUMMARY}")
        self.assertFalse(evidence.report_matches(called, root, BASE))
        relabelled = report.replace(evidence.DATA_SCHEMA, evidence.LINKED_SCHEMA).replace(
            re.search(r"^\* data symbols SHA-256: .*\n", report, re.M)[0], "")
        self.assertFalse(evidence.report_matches(relabelled, root, BASE))

    def check_report(self, root):
        """match.py --check-report against the saved report: (exit status, output)."""
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["match.py", "--root", str(root), f"0x{BASE:08X}", "--check-report"]), \
                mock.patch.object(match, "ROOT", match.ROOT), contextlib.redirect_stdout(output):
            status = match.main()
        return status, output.getvalue()

    def verified(self, root):
        """status.py --verify over the root's one source: (functions counted, problems)."""
        import status
        _, matched, _, _, problems, _, _ = status.collect(str(root), True)
        return matched, problems

    def test_verify_requires_the_report_match_writes(self):
        root, report = self.issue(self.SOURCES[evidence.LINKED_SCHEMA])
        path = root / f"docs/match/{BASE:08X}.md"
        status, output = self.check_report(root)
        self.assertEqual(status, 0, output)
        self.assertIn(f"report  identical to the saved docs/match/{BASE:08X}.md", output)
        self.assertEqual(self.verified(root), (1, []))
        self.assertEqual(path.read_text(), report, "--check-report writes nothing")
        # the review's reproducer: a claim line and a listing row that says what the ROM does not
        row = report.split("```\n")[1].splitlines()[2]
        forged = report.replace("* relocations: none\n",
                                "* relocations: none\n* numeric equivalence: proven for every input\n", 1)
        forged = forged.replace(row, row[:40] + "pop {pc}", 1)
        self.assertIn("\n* numeric equivalence: proven for every input\n", forged)
        self.assertIn(row[:40] + "pop {pc}\n", forged)
        for text in [forged, *tampers(report).values()]:
            with self.subTest(text=text[-60:]):
                path.write_bytes(text.encode())
                status, output = self.check_report(root)
                self.assertEqual(status, 1)
                self.assertIn(f"report  DIFFERS from the saved docs/match/{BASE:08X}.md", output)
                self.assertEqual(path.read_bytes(), text.encode())
        path.write_text(forged)
        matched, problems = self.verified(root)
        self.assertEqual(matched, 0)
        self.assertEqual(problems, [f"{BASE:08X}: the saved report differs from the one match.py writes now; "
                                    "re-run match.py"])
        self.assertFalse(evidence.report_matches(forged, root, BASE))

    def test_a_source_that_does_not_match_keeps_its_verdict(self):
        """--verify reports a source whose bytes differ as DOES NOT MATCH: match.py compares a report only for
        a MATCH, so "re-run match.py" (which would write a NOT MATCHING report) is never the advice."""
        root, report = self.issue(self.SOURCES[evidence.SCHEMA])
        source = root / "src/08000000.c"
        source.write_text(source.read_text().replace("a * 3 + 1", "a * 3 + 2"))
        status, output = self.check_report(root)
        self.assertEqual(status, 1)
        self.assertIn("verdict NOT MATCHING - bytes differ", output)
        self.assertFalse(any(line.startswith("report  ") for line in output.splitlines()))
        self.assertEqual((root / f"docs/match/{BASE:08X}.md").read_text(), report)
        self.assertEqual(self.verified(root), (0, [f"{BASE:08X}: DOES NOT MATCH"]))

    def test_compiled_choices_are_held_by_verify(self):
        """Whether the object links a data relocation is the compile's to say.  From the bytes, a data label
        needs a reached literal that points outside the function (plain_report_fields' rule 7), but such a
        literal may be a raw constant, so a consistent relabel across the data boundary still replays in the
        cached replay (closed_report says so).  status.py --verify, which compiles, refuses every one."""
        def to_data(report, schema):
            lines = report.replace(f"`{schema}`", f"`{evidence.DATA_SCHEMA}`").split("\n")
            at = next(index for index, line in enumerate(lines) if line.startswith("* control flow:")) + 1
            return "\n".join(lines[:at] + [f"* data symbols SHA-256: `{evidence.mapping_fingerprint(DATA)}`"] +
                             lines[at:])
        root, report = self.issue(self.SOURCES[evidence.DATA_SCHEMA])
        leaf = "\n".join(line for line in report.replace(f"`{evidence.DATA_SCHEMA}`", f"`{evidence.SCHEMA}`").split("\n")
                         if not line.startswith(("* mapping SHA-256:", "* control flow:", "* data symbols SHA-256:")))
        raw = "void func_08000400(int);\nvoid func_08000000(void) { func_08000400(*(int *)0x02000100); }\n"
        root2, report2 = self.issue(raw)
        self.assertIn(f"`{evidence.LINKED_SCHEMA}`", report2)
        root3, report3 = self.issue(self.SOURCES[evidence.LINKED_SCHEMA])
        self.assertFalse(evidence.report_matches(to_data(report3, evidence.LINKED_SCHEMA), root3, BASE),
                         "a call-only body has no literal a data relocation could be")
        for name, directory, relabelled in (("data -> leaf", root, leaf),
                                            ("raw constant -> data", root2, to_data(report2, evidence.LINKED_SCHEMA))):
            with self.subTest(relabel=name):
                self.assertTrue(evidence.report_matches(relabelled, directory, BASE), "the documented residual")
                (directory / f"docs/match/{BASE:08X}.md").write_text(relabelled)
                self.assertEqual(self.check_report(directory)[0], 1)
                self.assertEqual(self.verified(directory)[0], 0)

    def test_the_source_path_is_the_one_match_names(self):
        root, report = self.issue(self.SOURCES[evidence.SCHEMA])
        self.assertTrue(evidence.report_matches(report, root, BASE))
        (root / "src/folder").mkdir()
        (root / "src/08000000.c").rename(root / "src/folder/08000000.c")
        self.assertEqual(evidence.report_source(root, BASE), "src/folder/08000000.c")
        self.assertFalse(evidence.report_matches(report, root, BASE))
        moved = report.replace("* source: `src/08000000.c`", "* source: `src/folder/08000000.c`")
        self.assertFalse(evidence.report_matches(moved, root, BASE))


WIDE_SCALAR_SOURCE = """extern int data_02000100;
int func_08000000(int a)
{
    switch (a) {
    case 0: return data_02000100;
    case 1: return 0x12345678;
    case 2: return 0x1234;
    case 3: return 9;
    case 4: return 13;
    default: return 0;
    }
}
"""


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file(), "agbcc required")
class PortedWriterTests(unittest.TestCase):
    """The train's writer edits, ported into render_report (#390 wide scalars, #393 thunk store premises,
    #397 owner switches): the report match.py writes is the one the cached replay re-renders, so it replays
    whole, match.py --check-report finds it identical, and the ported line cannot be edited on its own."""

    def issue(self, source, objects, entries, arguments, *, link=(), rom_words=()):
        """Compile `source`, lay it into a ROM beside the `entries` stubs and write its report with
        match.main(); returns (root, report text)."""
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="closed_report_ported_", dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (root / name).mkdir()
        environment = {key: value for key, value in os.environ.items() if key != "FFTA_ROM"}
        environment.update(TMPDIR=str(root), PYTHONDONTWRITEBYTECODE="1")
        self.enterContext(mock.patch.dict(os.environ, environment, clear=True))
        (root / "src/08000000.c").write_text(source)
        (root / "config/data_symbols.json").write_bytes(objects)
        size = max([0x1000] + [address + 4 - BASE for address, _ in rom_words])
        rom = bytearray(size)
        for address, words in rom_words:
            struct.pack_into("<HH", rom, address - BASE, *words)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, root, BASE, "src/08000000.c")
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            spans = [(BASE, symbol["size"]), *entries]
            mapping = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{start + length:08X}", "mode": "thumb"}
                                  for start, length in spans]).encode()
            (root / "config/functions.json").write_bytes(mapping)
            (root / "symbols/functions.txt").write_text(
                "".join(f"{start:08X} {start + length:08X} {length} 1 return\n" for start, length in spans))
            body, _, _ = match.link_calls(runner, workspace, args, original, BASE, mapping, len(rom), bytes(rom),
                                          objects, {}, {}, allow_switch_data=True, **dict(link))
        rom[:len(body)] = body
        (root / "baserom.bin").write_bytes(rom)
        self.assertEqual(self.main(root, arguments), 0)
        return root, (root / f"docs/match/{BASE:08X}.md").read_text()

    def main(self, root, arguments, *extra):
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["match.py", "--root", str(root), f"0x{BASE:08X}", *arguments, *extra]), \
                mock.patch.object(match, "ROOT", match.ROOT), contextlib.redirect_stdout(output):
            status = match.main()
        self.output = output.getvalue()
        return status

    def round_trip(self, root, report, arguments, line):
        """The written report replays, --check-report finds it identical, and the ported `line` is bound."""
        self.assertEqual(report.count(line + "\n"), 1, report)
        # where main() wrote it: after the switch manifest, before the switch proof
        lines = report.splitlines()
        manifest = next(index for index, text in enumerate(lines) if text.startswith("* switch manifest: "))
        proof = next(index for index, text in enumerate(lines) if text.startswith("* switch proof SHA-256: "))
        self.assertTrue(manifest < lines.index(line) < proof, report)
        self.assertTrue(evidence.report_matches(report, root, BASE))
        self.assertEqual(self.main(root, arguments, "--check-report"), 0, self.output)
        self.assertIn(f"report  identical to the saved docs/match/{BASE:08X}.md", self.output)
        for name, edited in (("removed", report.replace(line + "\n", "", 1)),
                             ("duplicated", report.replace(line + "\n", line + "\n" + line + "\n", 1)),
                             ("altered", report.replace(line, line[:-1] + "!", 1))):
            with self.subTest(edit=name):
                self.assertFalse(evidence.report_matches(edited, root, BASE))

    def test_a_wide_scalar_report_round_trips(self):
        import switch_wide_scalars as wide_scalars
        arguments = ["--switch-data-profile", evidence.SWITCH_U16_SCALAR_SELECTOR]
        root, report = self.issue(WIDE_SCALAR_SOURCE, DATA, [(CALLEE, 2)], arguments)
        self.assertIn(f"* verification: `{evidence.SWITCH_U16_SCALAR_SCHEMA}`\n", report)
        self.assertIn('"wide_scalar_policy":', report)
        self.round_trip(root, report, arguments, wide_scalars.report_line())
        # #390's own check in the switch replay, apart from the whole-text comparison report_matches adds
        lines = report.splitlines()
        self.assertTrue(evidence.switch_report_matches(lines, root, BASE, data_profile=True))
        for name, edited in (("missing", [text for text in lines if text != wide_scalars.report_line()]),
                             ("duplicated", lines + [wide_scalars.report_line()])):
            with self.subTest(switch_replay=name):
                self.assertFalse(evidence.switch_report_matches(edited, root, BASE, data_profile=True))

    def test_a_thunk_store_premise_report_round_trips(self):
        # A module, not its classes: importing a TestCase class would make it run here again.
        import test_switch_data_thunks as thunk_tests
        objects = json.dumps({f"data_{value:08X}": f"0x{value:08X}" for value in
                              (0x02000100, 0x02000200, 0x02000300, 0x02000304, 0x02000308)}).encode()
        arguments = ["--switch-data-profile", thunk_tests.PLAIN]
        root, report = self.issue(thunk_tests.PREMISED, objects, [(BASE + 0x400, 2), (BASE + 0x410, 2)], arguments,
                                  link={"switch_thunks": thunk_tests.PLAIN},
                                  rom_words=[(thunk_tests.THUNK_R2, (0x4710, 0x46C0))])
        premises = [line for line in report.splitlines() if line.startswith("* thunk store premise:")]
        self.assertEqual(len(premises), 1, report)
        self.round_trip(root, report, arguments, premises[0])

    def test_an_owner_switch_buffer_report_has_no_switch_lines(self):
        import owner_switch_buffer_profile as owner_switch
        import test_owner_switch_buffers as owner_tests
        data_calls = owner_tests.data_calls
        if not data_calls.tools_present():
            self.skipTest("fixed compiler and ARM tools required")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="closed_report_owner_switch_", dir=scratch)
        self.addCleanup(directory.cleanup)
        root = owner_tests.build_switch(Path(directory.name) / "data", owner_tests.DATA_SWITCH, data_calls.STORES)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        lines = report.splitlines()
        owner, = [line for line in lines if line.startswith(owner_switch.LINE)]
        self.assertFalse(any(line.startswith(("* switches", "* switch manifest", "* switch proof")) for line in lines))
        environment = dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
        self.enterContext(mock.patch.dict(os.environ, environment))
        self.assertTrue(evidence.report_matches(report, root, data_calls.A))
        check = subprocess.run([sys.executable, str(KIT / "tools/match.py"), "--root", str(root),
                                f"0x{data_calls.A:08X}", "--check-report"], capture_output=True, text=True,
                               env=environment, timeout=600)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        self.assertIn(f"report  identical to the saved docs/match/{data_calls.A:08X}.md", check.stdout)
        # the switch lines main() leaves out for an owner switch, written back in: refused
        at = lines.index(owner) + 1
        switched = lines[:at] + ["* switches: forged", "* switch manifest: `{}`",
                                 "* switch proof SHA-256: `" + "0" * 64 + "`"] + lines[at:]
        self.assertFalse(evidence.report_matches("\n".join(switched) + "\n", root, data_calls.A))
        self.assertFalse(evidence.report_matches(report.replace(owner + "\n", ""), root, data_calls.A))


class BranchTests(ClosureAssertions, unittest.TestCase):
    """The built-in and profile replay branches whose verifiers other modules test."""

    LEAF = bytes.fromhex("01207047")                     # movs r0, #1; bx lr
    FRAME = bytes.fromhex("81b001b07047")                # sub sp, #4; add sp, #4; bx lr
    CALL = bytes(bytearray(b"\x00\xb5") + thumb_bl(BASE + 2, CALLEE) + bytes.fromhex("01bc0047"))
    # push {lr}; sub sp, #4; bl; add sp, #4; pop {r0}; bx r0
    FRAMED_CALL = bytes(bytearray(bytes.fromhex("00b581b0")) + thumb_bl(BASE + 4, CALLEE) + bytes.fromhex("01b001bc0047"))

    def setUp(self):
        self.enterContext(mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False))

    def family(self, body, schema, patches, rooted=lambda root: {}, **parts):
        """Patch the branch's verifiers, render its report from `parts` and hold every line of it."""
        root = Root(self, body)
        instructions = decode(body)
        with contextlib.ExitStack() as stack:
            for target, name, value in patches(instructions, root):
                stack.enter_context(mock.patch.object(target, name, value))
            report = root.render(body, instructions, schema, **parts, **rooted(root))
            self.assert_closed(report, root.path)
        return report

    def returns(self, value):
        return lambda *args, **kwargs: value

    def test_unsigned_quotient(self):
        manifest = {"calls": [[2, "__udivsi3"]], "divisors": [[2, 10]], "runtime": evidence.UDIVSI3_RUNTIME}
        for body, selector, verifier in ((self.CALL, None, "verify_udivsi3"),
                                         (self.FRAME, evidence.UDIVSI3_FRAMED_SELECTOR, "verify_udivsi3_source")):
            with self.subTest(selector=selector):
                evidence_manifest = dict(manifest, frame=True) if selector else manifest
                self.family(body, evidence.udivsi3_schema(selector),
                            lambda instructions, _: [(match, verifier, self.returns(instructions))],
                            mapped=True, control_flow=evidence.CALL_SUMMARY, udivsi3_bindings=True,
                            division_evidence=evidence_manifest, unsigned_quotient_profile=selector)

    def test_signed_quotient(self):
        manifest = {"calls": [[2, "__divsi3"]], "divisors": [[2, 10]], "runtime": evidence.divsi3.RUNTIME}
        for body, selector in ((self.CALL, None), (self.FRAME, evidence.divsi3.FRAMED_SELECTOR)):
            for switched in (False, True):
                with self.subTest(selector=selector, switched=switched):
                    quotient = dict(manifest, frame=True) if selector else dict(manifest)
                    if switched:
                        quotient["switch"] = {"bound": 1, "relocations": [[12, 16]]}
                    self.family(body, evidence.divsi3.schema(selector, switched),
                                lambda instructions, _: [(match, "verify_divsi3_source", self.returns(instructions))],
                                mapped=True, control_flow=evidence.CALL_SUMMARY, quotient_evidence=quotient,
                                signed_quotient_profile=selector)

    def test_signed_and_unsigned_remainder(self):
        self.family(self.CALL, evidence.modsi3.SCHEMA,
                    lambda instructions, _: [(match, "verify_modsi3", self.returns(instructions))],
                    mapped=True, control_flow=evidence.CALL_SUMMARY,
                    remainder_evidence={"calls": [[2, "__modsi3"]], "data": [], "operands": [],
                                        "runtime": evidence.modsi3.RUNTIME})
        self.family(self.CALL, evidence.umodsi3.SCHEMA,
                    lambda instructions, _: [(match, "verify_umodsi3_source", self.returns(instructions))],
                    mapped=True, control_flow=evidence.CALL_SUMMARY,
                    unsigned_remainder_evidence={"calls": [[2, "__umodsi3"]], "data": [], "divisors": [],
                                                 "frame": False, "runtime": evidence.umodsi3.RUNTIME})

    def test_switches(self):
        base = {"calls": [], "switch": {"bound": 1}}
        one = [[8, "data_02000100", 0]]
        two = one + [[12, "data_02000100", 4]]
        multiple = dict(base, data=two, data_policy=evidence.SWITCH_MULTIPLE_DATA_POLICY)
        cases = [
            (evidence.SWITCH_SCHEMA, base, False),
            (evidence.SWITCH_DATA_SCHEMA, dict(base, data=one), True),
            (evidence.SWITCH_MULTIPLE_DATA_SCHEMA, multiple, True),
            (evidence.SWITCH_U16_SCALAR_SCHEMA,
             dict(multiple, scalar_policy=evidence.SWITCH_U16_SCALAR_POLICY, scalars=[]), True),
        ]
        for schema, manifest, data in cases:
            with self.subTest(schema=schema):
                self.family(self.LEAF, schema, lambda instructions, _: [
                    (match, "verify_switches", self.returns((instructions, "closed leaf CFG")))],
                    mapped=True, control_flow="closed leaf CFG", data_profile=data, switches=True,
                    switch_evidence=manifest)
        # match.py writes the version-2 data policy exactly when more than one data relocation is linked,
        # so a consistent report for the other version, proof and listing recomputed, is refused
        for schema, manifest in ((evidence.SWITCH_MULTIPLE_DATA_SCHEMA, dict(multiple, data=one)),
                                 (evidence.SWITCH_DATA_SCHEMA, dict(base, data=two))):
            with self.subTest(forged=schema):
                root = Root(self, self.LEAF)
                instructions = decode(self.LEAF)
                with mock.patch.object(match, "verify_switches", self.returns((instructions, "closed leaf CFG"))):
                    forged = root.render(self.LEAF, instructions, schema, mapped=True, control_flow="closed leaf CFG",
                                         data_profile=True, switches=True, switch_evidence=manifest)
                    self.assertFalse(evidence.report_matches(forged, root.path, BASE))
        with self.subTest(schema=evidence.PRELOADED_SWITCH_SCHEMA):
            self.family(self.LEAF, evidence.PRELOADED_SWITCH_SCHEMA, lambda instructions, _: [
                (match, "verify_preloaded_switches",
                 self.returns((instructions, evidence.PRELOADED_SWITCH_CONTROL_FLOW)))],
                mapped=True, control_flow=evidence.PRELOADED_SWITCH_CONTROL_FLOW, data_profile=True,
                switches=True, switch_evidence=dict(base, data=[[8, "data_02000100", 0]]), preloaded_profile=True)

    def proof(self, stack_arguments, body=None):
        return SimpleNamespace(dependencies={CALLEE}, stack_arguments=stack_arguments,
                               stack_index_retry=None, buffer_evidence=lambda: True,
                               fingerprint=lambda: "ab" * 32, loop_replay_lines=lambda: [],
                               bios_summary_lines=lambda: [], span=lambda address: body or self.CALL,
                               target=lambda target: None)

    def test_function_addresses_and_buffers(self):
        manifest = {"calls": [], "data": [], "functions": [[4, f"func_{CALLEE:08X}"]]}
        for addresses, data in ((manifest, False), (dict(manifest, data=[[8, "data_02000100", 0]]), True)):
            with self.subTest(data=data):
                self.family(self.LEAF, evidence.FUNCTION_ADDRESS_SCHEMA, lambda instructions, _: [
                    (match, "verify_function_addresses", self.returns((instructions, "closed leaf CFG")))],
                    mapped=True, control_flow="closed leaf CFG", data_profile=data, address_manifest=addresses)
        proof = self.proof(True)
        self.family(self.CALL, evidence.FUNCTION_BUFFER_SCHEMA, lambda instructions, _: [
            (match, "verify_function_buffers", self.returns((instructions, proof)))],
            buffer_proof=proof, mapped=True, control_flow=evidence.CALL_SUMMARY, address_manifest=manifest)
        for schema, stack_arguments in ((evidence.BUFFER_SCHEMA, False), (evidence.STACK_BUFFER_SCHEMA, True)):
            with self.subTest(schema=schema):
                proof = self.proof(stack_arguments, self.FRAMED_CALL)
                self.family(self.FRAMED_CALL, schema, lambda instructions, _: self.buffer_patches(instructions, proof),
                            buffer_proof=proof, mapped=True, control_flow=evidence.CALL_SUMMARY)
        # match.py tries the version-1 proof first: a version-2 report whose body the version-1 proof admits is
        # one match.py never writes
        with self.subTest(forged=evidence.STACK_BUFFER_SCHEMA):
            proof = self.proof(True, self.FRAMED_CALL)
            root = Root(self, self.FRAMED_CALL)
            instructions = decode(self.FRAMED_CALL)
            with contextlib.ExitStack() as stack:
                for target, name, value in self.buffer_patches(instructions, proof, version_one=True):
                    stack.enter_context(mock.patch.object(target, name, value))
                forged = root.render(self.FRAMED_CALL, instructions, evidence.STACK_BUFFER_SCHEMA, buffer_proof=proof,
                                     mapped=True, control_flow=evidence.CALL_SUMMARY)
                self.assertFalse(evidence.report_matches(forged, root.path, BASE))

    def buffer_patches(self, instructions, proof, version_one=False):
        """BufferCallProof hands out `proof` for the report's version and a version-1 proof otherwise;
        the walk refuses the version-1 proof unless `version_one`."""
        first = self.proof(False, self.FRAMED_CALL)

        def walk(*args, buffer_proof=None, **kwargs):
            if buffer_proof is first and not version_one:
                raise ValueError("fixture: version-1 buffer proof refused")
            return instructions
        return [(match, "BufferCallProof",
                 lambda *args, stack_arguments=False, **kwargs: proof if stack_arguments == proof.stack_arguments
                 else first),
                (match, "verify_leaf_instructions", walk),
                (evidence.function_thunk, "legacy_absence", self.returns(True))]

    def test_profiles(self):
        import ashldi3_profile, data_buffer_profile, function_thunk_profile, inert_spin_profile
        import lshrdi3_profile, software_double_profile, software_float_profile
        thunk = function_thunk_profile.SELECTOR
        with self.subTest(profile="function thunks"):
            self.family(self.CALL, function_thunk_profile.schema_for(thunk), lambda instructions, root: [
                (function_thunk_profile, "verify", self.returns(instructions)),
                (function_thunk_profile, "verify_source", self.returns(None)),
                (function_thunk_profile, "selector_from_manifest", self.returns(thunk))],
                lambda root: dict(function_index=root.index, rom=root.rom),
                mapped=True, control_flow=function_thunk_profile.CONTROL_FLOW, thunk_profile=True,
                function_address_profile=thunk, thunk_evidence={"data": [], "frame": False})
        with self.subTest(profile="software double"):
            self.family(self.CALL, software_double_profile.SCHEMA, lambda instructions, root: [
                (software_double_profile, "verify_source", self.returns(instructions)),
                (software_double_profile, "summary", self.returns("fixture double summary"))],
                lambda root: dict(function_index=root.index, rom=root.rom),
                mapped=True, control_flow=evidence.CALL_SUMMARY, double_profile=True,
                double_evidence={"frame": False}, data_mapping=None)
        with self.subTest(profile="software float"):
            self.family(self.CALL, software_float_profile.SCHEMA, lambda instructions, root: [
                (software_float_profile, "verify_source", self.returns(instructions))],
                lambda root: dict(empty_index=root.index, rom=root.rom),
                mapped=True, control_flow=evidence.CALL_SUMMARY, float_evidence={"frame": False})
        with self.subTest(profile="inert spin"):
            self.family(self.CALL, inert_spin_profile.SCHEMA, lambda instructions, root: [
                (inert_spin_profile, "verify_source", self.returns(instructions)),
                (inert_spin_profile, "control_flow", self.returns("fixture spin control flow")),
                (inert_spin_profile, "summary", self.returns("fixture spin summary"))],
                lambda root: dict(function_index=root.index),
                mapped=True, control_flow="fixture spin control flow", spin_profile=True,
                spin_evidence={"frame": False}, data_mapping=None)
        for module in (ashldi3_profile, lshrdi3_profile):
            with self.subTest(profile=module.NAME):
                self.family(self.CALL, module.SCHEMA, lambda instructions, root: [
                    (module, "verify_source", self.returns(instructions))],
                    lambda root: dict(empty_index=root.index, rom=root.rom),
                    mapped=True, control_flow=evidence.CALL_SUMMARY, shift_evidence={"frame": False},
                    shift_profile=module, shift_options={})
        with self.subTest(profile="data buffer"):
            proof, manifest = self.proof(True), {"fixture": True}
            self.family(self.CALL, data_buffer_profile.SCHEMA, lambda instructions, root: [
                (data_buffer_profile, "verify_source",
                 self.returns((instructions, proof, data_buffer_profile.SCHEMA, manifest)))],
                buffer_proof=proof, mapped=True, control_flow=evidence.CALL_SUMMARY, data_profile=True,
                data_buffer_evidence=manifest)

    def test_an_internal_branch_and_link_is_not_a_call(self):
        """match.py's calls are relocations to other functions: a BL inside the function (a long branch)
        leaves a leaf a leaf, with no mapping or call-summary lines."""
        body = bytes(thumb_bl(BASE, BASE + 4) + bytes.fromhex("70477047"))
        self.family(body, evidence.SCHEMA, lambda instructions, _: [
            (match, "verify_leaf_instructions", self.returns(instructions))])

    def test_empty_body(self):
        import empty_body_profile
        root = Root(self, empty_body_profile.BODY, "void func_08000000(void) {}\n")
        self.enterContext(mock.patch.object(empty_body_profile, "verify_source", self.returns(None)))
        report = root.render(empty_body_profile.BODY, decode(empty_body_profile.BODY), empty_body_profile.SCHEMA,
                             empty_profile=True, empty_index=root.index, control_flow="closed leaf CFG")
        self.assert_closed(report, root.path)


class VerifyVerdictTests(unittest.TestCase):
    """status.py --verify reads the verdict before the comparison."""

    def test_a_difference_without_a_match_is_not_a_report_difference(self):
        import status
        root = Root(self, BranchTests.LEAF)
        (root.path / f"docs/match/{BASE:08X}.md").write_text("saved\n")
        outputs = {
            "verdict NOT MATCHING - bytes differ\nreport  DIFFERS from the saved docs/match/08000000.md\n":
                f"{BASE:08X}: DOES NOT MATCH",
            "extent    4 bytes (complete ELF symbol; closed CFG; no relocations)\n"
            "verdict MATCH - byte identical\nreport  DIFFERS from the saved docs/match/08000000.md\n":
                f"{BASE:08X}: the saved report differs from the one match.py writes now; re-run match.py"}
        for output, problem in outputs.items():
            with self.subTest(output=output.splitlines()[-2]), \
                    mock.patch.object(status.subprocess, "run",
                                      return_value=subprocess.CompletedProcess([], 1, output, "")):
                self.assertEqual(status.collect(str(root.path), True)[4], [problem])


class FreshCheckerTests(unittest.TestCase):
    """A compiling replay refuses an allow entry from its fresh plausibility run.

    Defence in depth: plausibility_result raises on an allow entry without
    findings and the replay refuses any finding, so the real checker cannot
    reach this; the state exists here only with plausibility_result mocked.
    """

    def test_signed_quotient_source_replay_refuses_an_allow_entry(self):
        root = Root(self, BranchTests.CALL)
        manifest = {"calls": [[2, "__divsi3"]], "divisors": [[2, 10]], "runtime": evidence.divsi3.RUNTIME}
        instructions = decode(BranchTests.CALL)

        class Runner:
            def __init__(self, *args, **kwargs):
                pass

            @contextlib.contextmanager
            def workspace(self):
                yield "workspace"

        def link(*args, divsi3_bindings, **kwargs):
            divsi3_bindings[BASE + 2] = "__divsi3"
            return BranchTests.CALL, {BASE + 2: 0x081426B8}, {}

        for name, value in (("Runner", Runner), ("compile_object", lambda *args: (None, None, {})),
                            ("link_calls", link), ("verify_divsi3", lambda *args, **kwargs: instructions),
                            ("_run_replay_process", lambda *args: None)):
            self.enterContext(mock.patch.object(match, name, value))
        digest = evidence.source_fingerprint(root.path, BASE)
        for allowed, accepted in ((None, True), ({"address": f"0x{BASE:08X}", "reason": "forged"}, False)):
            with self.subTest(allowed=allowed), \
                    mock.patch.object(match, "plausibility_result", return_value=([], allowed)):
                replay = lambda: match.verify_divsi3_source(root.path, BASE, BranchTests.CALL, root.rom,
                                                            root.mapping, digest, manifest)
                if accepted:
                    self.assertEqual(replay(), instructions)
                else:
                    with self.assertRaisesRegex(ValueError, "allow-listed"):
                        replay()


class SelectorTests(unittest.TestCase):
    """status.py --verify and rebuild.py --compiled forward the same selectors for every family."""

    def families(self):
        import addressed_signed_runtime_profile as addressed, libgcc_divdi3, library_units
        import palette_source_admission_profile as palette, private_float_pack_admission_profile as private_float
        import signed_divmod_profile as signed, unsigned_divmod_profile as unsigned
        import switch_constants_profile as constants, typed_switch_outgoing_frame as typed, switch_data_thunks
        import function_thunk_profile as thunk, inert_spin_profile as spin, software_double_profile as double
        import switch_pool_outgoing_frame as pool_frame
        import owner_admission_profile as owner, compiler_orphan_constants_native_profile as orphan
        verification = lambda schema: f"* verification: `{schema}`"
        float_selector = private_float.SELECTORS[0]
        signed_selector, signed_schema = next(iter(signed.REPORT_SCHEMAS.items()))
        policy = constants.POLICIES[0]
        families = {
            "ordinary": ([verification(evidence.LINKED_SCHEMA)], []),
            "libgcc owner": ([verification(libgcc_divdi3.SCHEMA)], ["--owner-runtime-profile", libgcc_divdi3.SELECTOR]),
            "restoring owner": ([verification(owner.SCHEMA)], ["--owner-runtime-profile", owner.SELECTOR]),
            "orphan constants owner": ([verification(orphan.SCHEMA)], ["--owner-runtime-profile", orphan.SELECTOR]),
            "palette owner": ([verification(palette.SCHEMA), f"* palette source: `{palette.SELECTOR}`"],
                              ["--owner-runtime-profile", palette.SELECTOR]),
            "private float owner": ([verification(private_float.profile(float_selector)[1]),
                                     f"* private float pack: `{float_selector}`"],
                                    ["--owner-runtime-profile", float_selector]),
            "addressed runtime": ([verification(addressed.SCHEMA), f"* addressed signed runtime: `{addressed.SELECTOR}`"],
                                  ["--addressed-signed-runtime-profile", addressed.SELECTOR]),
            "signed runtime": ([verification(signed_schema), f"* signed runtime: {signed_selector}"],
                               ["--signed-runtime-profile", signed_selector]),
            "unsigned runtime": ([verification(unsigned.SCHEMA), f"* unsigned runtime: {unsigned.SELECTOR}"],
                                 ["--unsigned-runtime-profile", unsigned.SELECTOR]),
            "switch constants": ([verification(policy.schema), f"* switch constants: {policy.selector}",
                                  "* switch constants manifest: `{}`", f"* switch constants proof SHA-256: `{'0' * 64}`"],
                                 ["--switch-profile", policy.selector]),
            "typed outgoing switch": ([verification(typed.SCHEMA), f"* switches: {typed.SUMMARY}",
                                       "* switch manifest: `" + evidence.switch_manifest(
                                           {"frame_policy": typed.SELECTOR}) + "`"],
                                      ["--switch-data-profile", typed.SELECTOR]),
            "function thunks": ([verification(thunk.schema_for(thunk.SELECTOR)),
                                 f"* function-address thunks: {thunk.SELECTOR}"],
                                ["--function-address-profile", thunk.SELECTOR]),
            "software double": ([verification(double.SCHEMA)], ["--software-double-profile", double.SELECTOR]),
            "inert spin": ([verification(spin.SCHEMA)], ["--control-flow-profile", spin.SELECTOR]),
            "framed unsigned quotient": ([verification(evidence.UDIVSI3_FRAMED_SCHEMA)],
                                         ["--unsigned-quotient-profile", evidence.UDIVSI3_FRAMED_SELECTOR]),
            "framed signed quotient": ([verification(evidence.divsi3.FRAMED_SCHEMA)],
                                       ["--signed-quotient-profile", evidence.divsi3.FRAMED_SELECTOR]),
            "fixed-pool frame u16 scalars": ([verification(evidence.pool_switch_frame.FIXED_SCHEMA)],
                                             ["--switch-data-profile", evidence.pool_switch_frame.FIXED_SELECTOR]),
            "framed signed quotient switch": ([verification(evidence.divsi3.FRAMED_SWITCH_SCHEMA)],
                                              ["--signed-quotient-profile", evidence.divsi3.FRAMED_SELECTOR]),
            "signed quotient switch": ([verification(evidence.divsi3.SWITCH_SCHEMA)], []),
            "library unit": ([verification(evidence.LINKED_SCHEMA), f"{library_units.UNIT_LINE}`fixture unit`",
                              f"{library_units.TOOLCHAIN_LINE}`fixture-toolchain`",
                              f"{library_units.COMPILER_LINE}`{'0' * 64}`",
                              f"* compiler: `{match.DEFAULT_CC} -O1`"],
                             ["--unit-toolchain", "fixture-toolchain"]),
            "default flags": ([verification(evidence.LINKED_SCHEMA),
                               f"* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`"], []),
            "other flags": ([verification(evidence.LINKED_SCHEMA), f"* compiler: `{match.DEFAULT_CC} -O1`"],
                            ["--flags", "-O1"]),
            "inert spin with other flags": ([verification(spin.SCHEMA), f"* compiler: `{match.DEFAULT_CC} -O1`"],
                                            ["--control-flow-profile", spin.SELECTOR, "--flags", "-O1"]),
        }
        for schema, selector in ((evidence.SWITCH_U16_SCALAR_SCHEMA, evidence.SWITCH_U16_SCALAR_SELECTOR),
                                 (evidence.SWITCH_POOL_U16_SCALAR_SCHEMA, evidence.SWITCH_POOL_U16_SCALAR_SELECTOR),
                                 (pool_frame.SCHEMA, pool_frame.SELECTOR),
                                 (evidence.SWITCH_FUNCTION_U16_SCALAR_SCHEMA,
                                  evidence.SWITCH_FUNCTION_U16_SCALAR_SELECTOR),
                                 (evidence.SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA,
                                  evidence.SWITCH_FUNCTION_POOL_U16_SCALAR_SELECTOR),
                                 (evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA,
                                  evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SELECTOR),
                                 (evidence.SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA,
                                  evidence.SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SELECTOR),
                                 *((schema, selector) for selector, schema in switch_data_thunks.SCHEMAS.items())):
            families[schema] = ([verification(schema)], ["--switch-data-profile", selector])
        return families

    def test_status_and_rebuild_forward_the_same_arguments(self):
        import rebuild
        import status
        families = self.families()
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="closed_report_selectors_", dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for name in ("config", "src", "docs/match"):
            (root / name).mkdir(parents=True)
        addresses = {BASE + 16 * number: family for number, family in enumerate(families)}
        (root / "config/functions.json").write_text(json.dumps([
            {"rom": f"0x{address:08X}", "end": f"0x{address + 8:08X}", "mode": "thumb"} for address in addresses]))
        for address, family in addresses.items():
            (root / f"src/{address:08X}.c").write_text("void fixture(void) {}\n")
            (root / f"docs/match/{address:08X}.md").write_text("\n".join(families[family][0]) + "\n")
        image = root / "fixture.rom"
        with image.open("wb") as stream:
            stream.truncate(0x10000)
        output = ("extent    8 bytes (complete ELF symbol; closed CFG; no relocations)\n"
                  "verdict MATCH - byte identical\n")
        with mock.patch.object(status, "rom_path", return_value=str(image)), \
                mock.patch.object(status, "report_matches", return_value=True), \
                mock.patch.object(status.subprocess, "run",
                                  return_value=subprocess.CompletedProcess([], 0, output, "")) as run:
            status.collect(str(root), True)
        forwarded = {}
        for call in run.call_args_list:
            command = call.args[0]
            self.assertEqual(command[-2:], ["--check-report", "--no-write"])
            forwarded[int(command[4], 16)] = command[5:-2]
        self.assertEqual(set(forwarded), set(addresses))
        with mock.patch.object(rebuild, "report_matches", return_value=True):
            for address, family in addresses.items():
                with self.subTest(family=family):
                    report = (root / f"docs/match/{address:08X}.md").read_text()
                    self.assertEqual(forwarded[address], families[family][1])
                    self.assertEqual(rebuild.saved_profile_arguments(report, root, address), forwarded[address])
                    self.assertEqual(evidence.saved_selectors(report).arguments, forwarded[address])


class BufferLineTests(BranchTests):
    """Every replay branch refuses, in its own line check, a buffer or DMA fill line its evidence does not write.

    BranchTests' fixtures run again with the whole-text comparison answered True, so the refusal
    is the branch's own.  A branch without buffer evidence refuses every line that starts with
    evidence.BUFFER_LINES; a branch with it holds every such line to its proof, which here writes
    one replay line and one BIOS line: they replay as match.py writes them and not swapped.  The
    DMA fill lines are refused by the guard in report_matches or by the replay that recomputes
    them.  The inserted lines are one of each kind match.py writes, each head line without its
    colon, one of no known kind and the bare prefix with a colon, each as a field and indented,
    after the plausibility line and where match.py writes the buffer proof lines.
    """

    PROOF = "* buffer proof SHA-256: `" + "ab" * 32 + "`"   # the fixture proof's fingerprint line
    OWN = ("* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400 sites 0x08000002",
           "* buffer BIOS summaries: `fixture` written by the proof")
    LINES = (
        f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
        "* buffer calls forged",
        PROOF,
        "* buffer proof SHA-256 forged",
        "* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400 sites none writes sp+0:4; "
        "proved none; trusted none; pruned edges 0",
        "* buffer copy summary: `fixture` 0x08000400 at 0x08000002: forged",
        "* buffer switch callee: `fixture` 0x08000400: dispatch at 0x08000402",
        "* buffer owner switch: `fixture`",
        "* buffer BIOS summaries: `fixture` forged",
        "* buffer BIOS premise: forged",
        "* buffer BIOS manifest: `[]`",
        "* buffer unlisted: forged",
        "* buffer: forged",
        "* DMA fills: forged",
        "* DMA fill premise: forged",
        '* DMA fill manifest: `{"sites":[]}`',
    )

    def proof(self, stack_arguments, body=None):
        proof = super().proof(stack_arguments, body)
        proof.loop_replay_lines, proof.bios_summary_lines = (lambda: [self.OWN[0]]), (lambda: [self.OWN[1]])
        return proof

    def assert_closed(self, report, root):
        lines = report.split("\n")
        places = {"plausibility": lines.index("* source plausibility: plausible") + 1}
        if self.PROOF in lines:
            places["buffer proof"] = lines.index(self.PROOF) + 1
            self.assertEqual(tuple(lines[places["buffer proof"]:][:2]), self.OWN)
        self.assertTrue(evidence.report_matches(report, root, BASE), "the untampered report must replay")
        with mock.patch.object(evidence, "closed_report", self.returns(True)):
            self.assertTrue(evidence.report_matches(report, root, BASE), "the untampered report must replay")
            for place, at in places.items():
                for forged in self.LINES:
                    for line in (forged, "  " + forged):
                        with self.subTest(after=place, line=line):
                            self.assertFalse(evidence.report_matches(
                                "\n".join(lines[:at] + [line] + lines[at:]), root, BASE))
            if self.PROOF in lines:
                at = places["buffer proof"]
                with self.subTest(swapped=self.OWN):
                    self.assertFalse(evidence.report_matches(
                        "\n".join(lines[:at] + [self.OWN[1], self.OWN[0]] + lines[at + 2:]), root, BASE))


if __name__ == "__main__":
    unittest.main()
