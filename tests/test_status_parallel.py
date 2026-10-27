"""Ordered, bounded status verification and push CLI forwarding."""

import contextlib
from collections import Counter
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from threading import Barrier, Lock
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import warnings

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import push
import status


def matched_output(size=8):
    return (f"extent    {size} bytes (complete ELF symbol; closed CFG; no relocations)\n"
            "verdict MATCH - byte identical\n")


class StatusParallelTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="status_parallel_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("config", "src", "docs/match"):
            (self.root / name).mkdir(parents=True)

    def fixture(self, addresses):
        entries = [{"rom": f"0x{address:08X}", "end": f"0x{address + 8:08X}",
                    "mode": "thumb"} for address in addresses]
        (self.root / "config/functions.json").write_text(json.dumps(entries))
        for address in addresses:
            (self.root / f"src/{address:08X}.c").write_text("void fixture(void) {}\n")
        rom = self.root / "fixture.rom"
        with rom.open("wb") as stream:
            stream.truncate(0x150100)
        self.enterContext(patch.object(status, "rom_path", return_value=str(rom)))

    def collect(self, jobs=1, **kwargs):
        return status.collect(str(self.root), True, jobs=jobs, **kwargs)

    def test_ordered_counts_and_errors_match_serial_despite_completion_order(self):
        self.fixture([0x08000000 + i * 16 for i in range(8)])
        (self.root / "src/08000100.c").write_text("void unknown(void) {}\n")
        expected = (8, 5, 64, 40, ["08000010: DOES NOT MATCH", "08000030: DOES NOT MATCH",
                                 "08000060: DOES NOT MATCH",
                                 "08000100: src/08000100.c does not match a known function"], 0, 0)
        cwd, environment = os.getcwd(), dict(os.environ)
        for jobs in (1, 2, 6):
            with self.subTest(jobs=jobs):
                lock, barrier = Lock(), Barrier(jobs)
                active, peak, started, completed = 0, 0, [], []

                def invoke(command, **kwargs):
                    nonlocal active, peak
                    address = command[4]
                    self.assertEqual(kwargs, {"capture_output": True, "text": True})
                    self.assertEqual(command[2:4], ["--root", str(self.root)])
                    self.assertEqual(command[-1], "--no-write")
                    with lock:
                        started.append(address)
                        first_batch = len(started) <= jobs
                        active += 1
                        peak = max(peak, active)
                    if first_batch:
                        barrier.wait(timeout=5)
                    if address == "08000000":
                        time.sleep(0.04)
                    with lock:
                        active -= 1
                        completed.append(address)
                    code = 1 if address in ("08000010", "08000060") else 0
                    output = "no verdict\n" if address == "08000030" else matched_output()
                    return subprocess.CompletedProcess(command, code, output, "diagnostic")

                with patch.object(status.subprocess, "run", side_effect=invoke):
                    self.assertEqual(self.collect(jobs), expected)
                self.assertEqual(peak, jobs)
                self.assertEqual(len(started), 8)
                if jobs > 1:
                    self.assertNotEqual(completed, sorted(completed))
        self.assertEqual(os.getcwd(), cwd)
        self.assertEqual(dict(os.environ), environment)

    def test_profiles_replay_and_report_refusals_are_preserved(self):
        addresses = [0x08000000 + i * 16 for i in range(8)]
        self.fixture(addresses)
        reports = ["spin", "double", "thunk", "constants", "malformed", "stale-thunk",
                   "stale-source", "ordinary"]
        for address, report in zip(addresses, reports):
            (self.root / f"docs/match/{address:08X}.md").write_text(report)

        def constants(report):
            if report == "malformed":
                raise ValueError("malformed saved profile")
            return SimpleNamespace(selector="fixture-switch") if report == "constants" else False

        with patch.object(status.switch_constants, "selected_policy", side_effect=constants), \
                patch.object(status.inert_spin, "selected", side_effect=lambda text: text == "spin"), \
                patch.object(status.software_double, "selected", side_effect=lambda text: text == "double"), \
                patch.object(status.function_thunk, "selected", side_effect=lambda text: "thunk" in text):
            for jobs in (1, 6):
                with self.subTest(jobs=jobs), \
                        patch.object(status, "report_matches",
                                     side_effect=lambda text, *_: not text.startswith("stale")) as replay, \
                        patch.object(status.subprocess, "run", return_value=subprocess.CompletedProcess(
                            [], 0, matched_output(), "")) as invocation:
                    result = self.collect(jobs, write_reports=True)
                    self.assertEqual(result, (8, 5, 64, 40, [
                        "08000040: malformed saved profile",
                        "08000050: invalid saved function-thunk report",
                        "08000060: DOES NOT MATCH"], 0, 0))
                    commands = {entry.args[0][4]: entry.args[0] for entry in invocation.call_args_list}
                    self.assertEqual(len(commands), 6)
                    for address, option, selector in (
                            ("08000000", "--control-flow-profile", status.inert_spin.SELECTOR),
                            ("08000010", "--software-double-profile", status.software_double.SELECTOR),
                            ("08000020", "--function-address-profile", status.function_thunk.SELECTOR),
                            ("08000030", "--switch-profile", "fixture-switch")):
                        self.assertEqual(commands[address][-2:], [option, selector])
                    self.assertTrue(all("--no-write" not in command for command in commands.values()))
                    self.assertEqual(Counter(entry.args[0] for entry in replay.call_args_list),
                                     Counter(["spin", "double", "thunk", "thunk", "constants",
                                              "stale-thunk", "stale-source", "ordinary"]))

    def test_late_complete_extent_and_overlap_refusals_keep_order(self):
        self.fixture([0x0814FFF0, 0x08150000, 0x08150010, 0x08150020, 0x08150030])
        responses = {"0814FFF0": matched_output(24), "08150000": matched_output(),
                     "08150010": matched_output(10),
                     "08150020": "verdict MATCH - byte identical\n",
                     "08150030": matched_output() + matched_output().splitlines()[0] + "\n"}
        expected = (1, 1, 8, 8, [
            "08150010: complete verified body disagrees with the late indexed extent",
            "08150020: missing or duplicate matcher extent",
            "08150030: missing or duplicate matcher extent",
            "08150000: late function overlaps another verified body"], 0, 0)
        for jobs in (1, 6):
            with self.subTest(jobs=jobs), patch.object(status.subprocess, "run", side_effect=
                    lambda command, **_: subprocess.CompletedProcess(command, 0, responses[command[4]], "")):
                self.assertEqual(self.collect(jobs), expected)

    def test_missing_written_report_keeps_both_existing_diagnostics(self):
        self.fixture([0x08000000])
        for jobs in (1, 6):
            with self.subTest(jobs=jobs), patch.object(status.subprocess, "run", return_value=
                    subprocess.CompletedProcess([], 0, matched_output(), "")):
                self.assertEqual(self.collect(jobs, write_reports=True)[4], [
                    "08000000: no match report in docs/match/", "08000000: DOES NOT MATCH"])

    def test_duplicate_report_destinations_never_run_concurrently(self):
        self.fixture([0x08000000])
        (self.root / "src/nested").mkdir()
        (self.root / "src/nested/08000000.c").write_text("void duplicate(void) {}\n")
        lock, active, peak = Lock(), 0, 0

        def invoke(command, **_):
            nonlocal active, peak
            with lock:
                active += 1
                peak = max(peak, active)
            time.sleep(0.01)
            with lock:
                active -= 1
            return subprocess.CompletedProcess(command, 1, "", "")

        with patch.object(status.subprocess, "run", side_effect=invoke) as invocation:
            self.assertEqual(self.collect(6, write_reports=True)[4],
                             ["08000000: DOES NOT MATCH"] * 2)
        self.assertEqual(invocation.call_count, 2)
        self.assertEqual(peak, 1)

    def test_default_and_offline_paths_do_not_create_workers(self):
        self.fixture([0x08000000])
        with patch.object(status, "ThreadPoolExecutor") as executor, \
                patch.object(status.subprocess, "run", return_value=
                             subprocess.CompletedProcess([], 0, matched_output(), "")):
            self.assertEqual(status.collect(str(self.root), True)[1], 1)
            self.assertEqual(status.collect(str(self.root), False, jobs=6)[1], 0)
        executor.assert_not_called()

    def test_direct_jobs_bounds(self):
        for jobs in (0, -1, 7):
            with self.subTest(jobs=jobs), self.assertRaisesRegex(ValueError, "between 1 and 6"):
                self.collect(jobs)

    def test_status_cli_passes_jobs_and_preserves_check_no_write(self):
        for suffix, expected in (([], 1), (["--jobs", "6"], 6)):
            with self.subTest(jobs=expected), patch.object(sys, "argv", [
                    "status.py", "--root", str(self.root), "--verify", "--check", "--write", *suffix]), \
                    patch.object(status, "collect", return_value=(0, 0, 0, 0, [], 0, 0)) as collect, \
                    patch.object(status, "badge_base_from_remote", return_value=""), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaisesRegex(SystemExit, "no status markers"):
                status.main()
            collect.assert_called_once_with(str(self.root), True, write_reports=False, jobs=expected)

    def test_both_clis_reject_jobs_outside_bounds_before_io(self):
        for module in (status, push):
            for jobs in ("0", "7", "-1", "many"):
                with self.subTest(module=module.__name__, jobs=jobs), \
                        patch.object(sys, "argv", [module.__name__, "--jobs", jobs]), \
                        patch.object(module.subprocess, "run") as invocation, \
                        contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                    module.main()
                self.assertEqual(error.exception.code, 2)
                invocation.assert_not_called()

    def test_status_cli_preserves_ordered_diagnostics_and_stale_exit(self):
        self.fixture([0x08000000, 0x08000010, 0x08000020])
        (self.root / "README.md").write_text(status.START + "\nstale\n" + status.END)
        self.enterContext(warnings.catch_warnings())
        warnings.simplefilter("ignore", ResourceWarning)
        results = []
        for jobs in (1, 6):
            output, errors = io.StringIO(), io.StringIO()
            with patch.object(sys, "argv", ["status.py", "--root", str(self.root),
                                           "--verify", "--check", "--jobs", str(jobs)]), \
                    patch.object(status, "badge_base_from_remote", return_value=""), \
                    patch.object(status.subprocess, "run", side_effect=lambda command, **_:
                                 subprocess.CompletedProcess(command, 1, "", "failure")), \
                    contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors), \
                    self.assertRaises(SystemExit) as error:
                status.main()
            results.append((output.getvalue(), errors.getvalue(), error.exception.code))
        self.assertEqual(results[0], results[1])
        self.assertIn("3 item(s) need attention:\n  08000000: DOES NOT MATCH\n"
                      "  08000010: DOES NOT MATCH\n  08000020: DOES NOT MATCH\n", results[0][1])
        self.assertIn("Verified status: 0/3 functions; 0/24 indexed bytes; "
                      "0 late functions, 0 late bytes", results[0][1])
        self.assertEqual(results[0][2], "README status is stale - run: python tools/status.py --write")

    def test_push_check_forwards_only_opt_in_jobs_to_status(self):
        for jobs in (1, 6):
            with self.subTest(jobs=jobs), patch.object(push, "run", return_value=(0, "up to date")) as run, \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_matches(str(self.root), "fixture-badges", jobs=jobs))
            command = [sys.executable, str(ROOT / "tools/status.py"), "--root", str(self.root),
                       "--check", "--verify", "--badge-base", "fixture-badges"]
            if jobs != 1:
                command += ["--jobs", str(jobs)]
            run.assert_called_once_with(command, cwd=str(self.root))

    def test_push_cli_keeps_archived_snapshot_gates_with_jobs(self):
        (self.root / ".git").mkdir()
        archive = self.root / "archive"
        archive.mkdir()
        snapshot = ("refs/heads/main", "a" * 40)
        with patch.object(sys, "argv", ["push.py", "--repo", str(self.root), "--check-only", "--jobs", "6"]), \
                patch.object(push, "publish_snapshot", return_value=snapshot) as capture, \
                patch.object(push, "committed_tree", return_value=str(archive)) as archived, \
                patch.object(push, "check_history", return_value=True) as history, \
                patch.object(push, "check_no_rom_data", return_value=True) as no_rom, \
                patch.object(push, "badge_base", return_value="fixture-badges"), \
                patch.object(push, "check_matches", return_value=True) as matches, \
                patch.object(push, "check_plausible", return_value=True) as plausible, \
                patch.object(push, "check_reports", return_value=True) as reports, \
                patch.object(push, "do_push") as publish, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(push.main(), 0)
        capture.assert_called_once_with(str(self.root), "main", require_clean=False)
        archived.assert_called_once_with(str(self.root), snapshot[1])
        history.assert_called_once_with(str(self.root), "origin", "main", force=False)
        no_rom.assert_called_once_with(str(self.root), commit=snapshot[1])
        matches.assert_called_once_with(str(archive), "fixture-badges", jobs=6)
        plausible.assert_called_once_with(str(archive))
        reports.assert_called_once_with(str(archive))
        publish.assert_not_called()
        self.assertFalse(archive.exists())

    def test_push_archive_failure_never_falls_back_to_working_tree(self):
        (self.root / ".git").mkdir()
        with patch.object(sys, "argv", ["push.py", "--repo", str(self.root), "--check-only", "--jobs", "6"]), \
                patch.object(push, "publish_snapshot", return_value=("refs/heads/main", "a" * 40)), \
                patch.object(push, "committed_tree", return_value=None), \
                patch.object(push, "check_history", return_value=True), \
                patch.object(push, "check_no_rom_data", return_value=True), \
                patch.object(push, "check_matches") as matches, \
                patch.object(push, "do_push") as publish, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(push.main(), 1)
        matches.assert_not_called()
        publish.assert_not_called()


if __name__ == "__main__":
    unittest.main()
