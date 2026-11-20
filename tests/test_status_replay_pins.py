"""status.py --verify applies the address-keyed replay pins after a passing report comparison.

match.py --check-report holds a saved report to the text match.py writes now. It does not ask whether the
function at that address may carry that schema. The cached replay asks that with the pins it keys by address
(match_evidence.address_pins), and status.py --verify used to skip the replay, and with it the pins, whenever
the comparison passed.

* ComparedReportTests gives status.collect the output match.py prints for a passing comparison, over complete
  reports rendered by match.py's own writer: a pinned address under its pinned schema and under another one,
  the same reports at an address nothing pins, the pins that depend on the report's volatile records, the same
  pins under threads and worker processes, and a report removed, replaced or never there while match.py ran.
* ModeTests holds each status mode to the one check it runs.
* IssuedReportTests compiles a small source at a pinned address with agbcc, lets match.py issue its report and
  runs the real comparison; a report removed right after that comparison is refused.
"""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
KIT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(KIT / "tools"))
sys.path.insert(0, str(KIT / "tests"))
import match
import match_evidence as evidence
import report_fixtures
import status

BASE = 0x08000000
AFFINE_SLOT = 0x08000FC8        # affine_oam_slot.report_body: elf-symbol-thumb-data-v1 over 148 bytes
KEYFRAMES = 0x08006720          # blend_keyframe_loop.report_scope: the addressed runtime report, given records
DISPATCHER = 0x0800C4B4         # scanline_dispatch.report_body: needs the report's volatile records
WINDOW_CIRCLE = 0x080D9F60      # window_scanline.report_body: elf-symbol-thumb-frame-v1 over 276 bytes
UNPINNED = 0x08001FC8
RECORD = "* allowlisted volatile: `fixture` at `0x03000940` declared in `include/fixture.h` (SHA-256 `00`)"
SCANLINE_RECORD = "* allowlisted volatile scanline: fixture"
REFUSED = "{:08X}: match.py writes this report, but the replay pin for this address refuses it"
CHANGED = "{:08X}: the saved report changed or vanished during the comparison; re-run status.py"


def body(size):
    """`size` bytes of straight-line Thumb: movs r0, #1 ... bx lr."""
    return bytes.fromhex("0120") * (size // 2 - 1) + bytes.fromhex("7047")


def root(test, address, data, source):
    """A decomp root with one source at `address` and a ROM holding `data` there."""
    scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
    scratch.mkdir(parents=True, exist_ok=True)
    directory = tempfile.TemporaryDirectory(prefix="status_replay_pins_", dir=scratch)
    test.addCleanup(directory.cleanup)
    path = Path(directory.name)
    for name in ("src", "include", "config", "symbols", "docs/match"):
        (path / name).mkdir(parents=True)
    (path / f"src/{address:08X}.c").write_text(source)
    (path / "config/functions.json").write_text(json.dumps(
        [{"rom": f"0x{address:08X}", "end": f"0x{address + len(data):08X}", "mode": "thumb"}]))
    (path / "config/data_symbols.json").write_text("{}")
    (path / "symbols/functions.txt").write_text(
        f"{address:08X} {address + len(data):08X} {len(data)} 1 return\n")
    rom = bytearray(address - BASE + 0x1000)
    rom[address - BASE:address - BASE + len(data)] = data
    (path / "baserom.bin").write_bytes(rom)
    environment = {key: value for key, value in os.environ.items() if key != "FFTA_ROM"}
    environment.update(TMPDIR=str(path), PYTHONDONTWRITEBYTECODE="1")
    test.enterContext(mock.patch.dict(os.environ, environment, clear=True))
    return path


def verified(path):
    """status.py --verify over the root's one source: (functions counted, problems)."""
    _, matched, _, _, problems, _, _ = status.collect(str(path), True)
    return matched, problems


class ComparedReportTests(unittest.TestCase):
    def verify_saved(self, address, size, schema, records=(), during=None, **modes):
        """--verify of a complete `schema` report that match.py finds identical to the one it writes.

        `during(path)`, when given, runs inside match.py's run with the report's path; `modes` go to collect.
        """
        data = body(size)
        path = root(self, address, data, "void fixture(void) {}\n")
        report = report_fixtures.legacy_report(path, address, data, schema, volatile_records=list(records))
        self.assertIn(f"* verification: `{schema}`\n", report)
        self.assertEqual(evidence.volatile_record_lines(report), list(records))
        saved = path / f"docs/match/{address:08X}.md"
        saved.write_text(report)
        output = (f"extent    {size} bytes (complete ELF symbol; closed CFG; no relocations)\n"
                  "verdict MATCH - byte identical\n\n"
                  f"report  identical to the saved docs/match/{address:08X}.md\n")

        def run(command, **kwargs):
            self.assertEqual(command[-2:], ["--check-report", "--no-write"])
            if during:
                during(saved)
            return subprocess.CompletedProcess(command, 0, output, "")
        with mock.patch.object(status.subprocess, "run", side_effect=run) as invoked:
            _, matched, _, _, problems, _, _ = status.collect(str(path), True, **modes)
        # a worker process calls its own copy of the mock
        self.assertEqual(invoked.call_count, 0 if modes.get("worker_processes") else 1)
        return matched, problems

    def test_a_pinned_address_keeps_its_schema(self):
        self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.DATA_SCHEMA), (1, []))
        for schema in (evidence.FRAMED_DATA_SCHEMA, evidence.SCHEMA):
            with self.subTest(schema=schema):
                self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, schema), (0, [REFUSED.format(AFFINE_SLOT)]))
        self.assertEqual(self.verify_saved(AFFINE_SLOT, 144, evidence.DATA_SCHEMA),
                         (0, [REFUSED.format(AFFINE_SLOT)]), "the pinned body is 148 bytes")

    def test_an_address_nothing_pins_is_unchanged(self):
        for schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA, evidence.SCHEMA):
            with self.subTest(schema=schema):
                self.assertEqual(self.verify_saved(UNPINNED, 148, schema), (1, []))
        self.assertEqual(self.verify_saved(UNPINNED, 148, evidence.SCHEMA, [RECORD]), (1, []))

    def test_the_pins_read_the_records_the_report_carries(self):
        # the window pin applies to a report that carries the scanline record, and only to that one
        self.assertEqual(self.verify_saved(WINDOW_CIRCLE, 276, evidence.FRAMED_SCHEMA, [SCANLINE_RECORD]), (1, []))
        self.assertEqual(self.verify_saved(WINDOW_CIRCLE, 276, evidence.SCHEMA, [SCANLINE_RECORD]),
                         (0, [REFUSED.format(WINDOW_CIRCLE)]))
        self.assertEqual(self.verify_saved(WINDOW_CIRCLE, 276, evidence.SCHEMA), (1, []))
        # the record names a window function; anywhere else it is refused
        self.assertEqual(self.verify_saved(UNPINNED, 276, evidence.FRAMED_SCHEMA, [SCANLINE_RECORD]),
                         (0, [REFUSED.format(UNPINNED)]))
        # the keyframe loop's record belongs to the addressed runtime report alone
        self.assertEqual(self.verify_saved(KEYFRAMES, 148, evidence.FRAMED_DATA_SCHEMA, [RECORD]),
                         (0, [REFUSED.format(KEYFRAMES)]))
        self.assertEqual(self.verify_saved(KEYFRAMES, 148, evidence.FRAMED_DATA_SCHEMA), (1, []))
        # the dispatcher needs its records as well as its body, and a fixture ROM does not hold that body
        import scanline_dispatch
        with mock.patch.object(scanline_dispatch, "report_body", return_value=True):
            self.assertEqual(self.verify_saved(DISPATCHER, 320, evidence.DATA_SCHEMA),
                             (0, [REFUSED.format(DISPATCHER)]))
            self.assertEqual(self.verify_saved(DISPATCHER, 320, evidence.DATA_SCHEMA, [RECORD]), (1, []))
        self.assertEqual(self.verify_saved(DISPATCHER, 320, evidence.DATA_SCHEMA, [RECORD]),
                         (0, [REFUSED.format(DISPATCHER)]))

    def test_threads_and_worker_processes_run_the_pins(self):
        import scanline_dispatch
        for modes in ({"jobs": 2}, {"worker_processes": 2}):
            with self.subTest(**modes):
                self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.DATA_SCHEMA, **modes), (1, []))
                self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.FRAMED_DATA_SCHEMA, **modes),
                                 (0, [REFUSED.format(AFFINE_SLOT)]))
                with mock.patch.object(scanline_dispatch, "report_body", return_value=True):
                    self.assertEqual(self.verify_saved(DISPATCHER, 320, evidence.DATA_SCHEMA, **modes),
                                     (0, [REFUSED.format(DISPATCHER)]))
                    self.assertEqual(self.verify_saved(DISPATCHER, 320, evidence.DATA_SCHEMA, [RECORD], **modes),
                                     (1, []))

    def test_a_report_removed_after_the_comparison_is_refused(self):
        # the text the pin refuses, and the text it admits: neither is counted once the file is gone
        for schema in (evidence.FRAMED_DATA_SCHEMA, evidence.DATA_SCHEMA):
            with self.subTest(schema=schema):
                self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, schema, during=Path.unlink),
                                 (0, [CHANGED.format(AFFINE_SLOT)]))

    def test_a_report_replaced_after_the_comparison_is_refused(self):
        def admitted(saved):
            """The text the pin admits, written over the one match.py compared."""
            saved.write_text(report_fixtures.legacy_report(saved.parents[2], AFFINE_SLOT, body(148),
                                                           evidence.DATA_SCHEMA))
        self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.FRAMED_DATA_SCHEMA, during=admitted),
                         (0, [CHANGED.format(AFFINE_SLOT)]))
        self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.DATA_SCHEMA, during=admitted),
                         (1, []), "the same text written again is the text status read")
        # a write torn inside a multibyte character leaves bytes that are not UTF-8
        torn = "\N{EM DASH}".encode()[:2]
        self.assertEqual(self.verify_saved(AFFINE_SLOT, 148, evidence.DATA_SCHEMA,
                                           during=lambda saved: saved.write_bytes(saved.read_bytes() + torn)),
                         (0, [CHANGED.format(AFFINE_SLOT)]))

    def test_a_report_status_did_not_read_is_refused(self):
        # no report before match.py ran: none after it either, or one written while it ran
        output = ("verdict MATCH - byte identical\n\n"
                  f"report  identical to the saved docs/match/{AFFINE_SLOT:08X}.md\n")
        for appears in (False, True):
            with self.subTest(appears=appears):
                path = root(self, AFFINE_SLOT, body(148), "void fixture(void) {}\n")

                def run(command, **kwargs):
                    if appears:
                        (path / f"docs/match/{AFFINE_SLOT:08X}.md").write_text(report_fixtures.legacy_report(
                            path, AFFINE_SLOT, body(148), evidence.DATA_SCHEMA))
                    return subprocess.CompletedProcess(command, 0, output, "")
                with mock.patch.object(status.subprocess, "run", side_effect=run):
                    self.assertEqual(verified(path), (0, [CHANGED.format(AFFINE_SLOT)]))


class ModeTests(unittest.TestCase):
    """Which check each status mode runs on a saved report: the whole replay, or the pins after a comparison."""

    MATCH = ("extent    4 bytes (complete ELF symbol; closed CFG; no relocations)\n"
             "verdict MATCH - byte identical\n")
    MODES = {  # mode -> (verify, write_reports, match.py output after the verdict, (replays, pin checks))
        "cached": (False, False, None, (1, 0)),
        "--verify, comparison passed": (True, False, "\nreport  identical to the saved docs/match/08001FC8.md\n",
                                       (0, 1)),
        "--verify, selector wrote no comparison": (True, False, "", (1, 0)),
        "--write --verify": (True, True, "\nwrote docs/match/08001FC8.md\n", (1, 0)),
    }

    def test_each_mode_checks_the_saved_report_once(self):
        for mode, (verify, write, tail, expected) in self.MODES.items():
            with self.subTest(mode=mode):
                path = root(self, UNPINNED, body(4), "void fixture(void) {}\n")
                report = report_fixtures.legacy_report(path, UNPINNED, body(4), evidence.SCHEMA)
                (path / f"docs/match/{UNPINNED:08X}.md").write_text(report)
                with mock.patch.object(status, "report_matches", return_value=True) as replay, \
                        mock.patch.object(status, "issued_report_pins", return_value=True) as pins, \
                        mock.patch.object(status.subprocess, "run", return_value=subprocess.CompletedProcess(
                            [], 0, self.MATCH + (tail or ""), "")) as run:
                    counted = status.collect(str(path), verify, write_reports=write)[1]
                self.assertEqual(counted, 1)
                self.assertEqual(run.call_count, int(verify))
                self.assertEqual((replay.call_count, pins.call_count), expected)
                for check in (replay, pins):
                    if check.call_count:
                        self.assertEqual(check.call_args.args, (report, str(path), UNPINNED))

    def test_a_refusing_check_refuses_in_every_mode(self):
        for mode, (verify, write, tail, _) in self.MODES.items():
            with self.subTest(mode=mode):
                path = root(self, UNPINNED, body(4), "void fixture(void) {}\n")
                (path / f"docs/match/{UNPINNED:08X}.md").write_text(
                    report_fixtures.legacy_report(path, UNPINNED, body(4), evidence.SCHEMA))
                with mock.patch.object(status, "report_matches", return_value=False), \
                        mock.patch.object(status, "issued_report_pins", return_value=False), \
                        mock.patch.object(status.subprocess, "run", return_value=subprocess.CompletedProcess(
                            [], 0, self.MATCH + (tail or ""), "")):
                    self.assertEqual(status.collect(str(path), verify, write_reports=write)[1], 0)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file(), "agbcc required")
class IssuedReportTests(unittest.TestCase):
    """A report match.py itself issues at a pinned address, held by the real comparison."""

    SOURCE = "int func_{:08X}(int a) {{ return a * 3 + 1; }}\n"
    # adds r1, r0, #0; lsls r0, r1, #1; adds r0, r0, r1; adds r0, #1; bx lr
    BODY = bytes.fromhex("011c4800401801307047")

    def issue(self, address):
        path = root(self, address, self.BODY, self.SOURCE.format(address))
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["match.py", "--root", str(path), f"0x{address:08X}"]), \
                mock.patch.object(match, "ROOT", match.ROOT), contextlib.redirect_stdout(output):
            self.assertEqual(match.main(), 0, output.getvalue())
        report = (path / f"docs/match/{address:08X}.md").read_text()
        self.assertIn(f"* verification: `{evidence.SCHEMA}`\n", report)
        self.assertEqual(evidence.volatile_record_lines(report), [])
        return path, report

    def test_the_dispatcher_address_refuses_a_report_without_its_records(self):
        path, report = self.issue(DISPATCHER)
        self.assertFalse(evidence.report_matches(report, path, DISPATCHER), "the cached replay refuses it")
        self.assertEqual(verified(path), (0, [REFUSED.format(DISPATCHER)]))
        self.assertEqual((path / f"docs/match/{DISPATCHER:08X}.md").read_text(), report)

    def test_the_same_source_elsewhere_is_counted(self):
        path, report = self.issue(UNPINNED)
        self.assertTrue(evidence.report_matches(report, path, UNPINNED))
        self.assertEqual(verified(path), (1, []))

    def test_a_report_removed_after_the_real_comparison_is_refused(self):
        path, report = self.issue(UNPINNED)
        compare = subprocess.run

        def run(command, **kwargs):
            result = compare(command, **kwargs)
            self.assertIn(f"report  identical to the saved docs/match/{UNPINNED:08X}.md",
                          result.stdout.splitlines())
            (path / f"docs/match/{UNPINNED:08X}.md").unlink()
            return result
        with mock.patch.object(status.subprocess, "run", side_effect=run):
            self.assertEqual(verified(path), (0, [CHANGED.format(UNPINNED)]))


if __name__ == "__main__":
    unittest.main()
