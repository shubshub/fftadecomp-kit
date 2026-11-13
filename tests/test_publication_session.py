"""Live native publication reuse, strict bindings and race refusals."""
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import publication_session as publication
import push
import status


class PublicationSessionTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="publication_session_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.repo = self.root / "repo"
        for name in ("src", "include", "config", "symbols", "docs/match"):
            (self.repo / name).mkdir(parents=True, exist_ok=True)
        self.entries = [{"rom": f"0x{address:08X}", "end": f"0x{address+4:08X}",
                         "mode": "thumb"} for address in (0x08000000, 0x08000010, 0x08000020)]
        (self.repo / "config/functions.json").write_text(json.dumps(self.entries))
        (self.repo / "symbols/functions.txt").write_text("".join(
            f"{int(entry['rom'],16):08X} {int(entry['end'],16):08X} 4 2 return\n"
            for entry in self.entries))
        (self.repo / "config/data_symbols.json").write_text("{}\n")
        (self.repo / "include/ffta.h").write_text("typedef unsigned int u32;\n")
        (self.repo / "baserom.bin").write_bytes(b"\0" * 64)
        (self.repo / "README.md").write_text(status.START + "\n" + status.END)
        self.tool = self.root / "tool.py"
        self.tool.write_text("initial tool\n")
        self.head = "a" * 40
        self.calls = []
        self.archive = None
        self.add_source("08000000")
        self.enterContext(contextlib.redirect_stdout(io.StringIO()))
        self.enterContext(patch.dict(os.environ, {"FFTA_ROM": str(self.repo / "baserom.bin")}))
        self.enterContext(patch.object(publication, "runtime_pin", side_effect=lambda: {
            "tool": publication.file_pin(self.tool),
            "environment": publication.object_pin(dict(os.environ))}))
        self.enterContext(patch.object(push, "capture_force_lease", return_value=("destination", "b"*40)))
        self.enterContext(patch.object(push, "publish_snapshot", side_effect=lambda *a, **k:
                                      ("refs/heads/topic", self.head)))
        self.enterContext(patch.object(push, "committed_tree", side_effect=self.make_archive))
        self.enterContext(patch.object(push, "check_history", return_value=True))
        self.enterContext(patch.object(push, "check_no_rom_data", return_value=True))
        self.enterContext(patch.object(push, "badge_base", return_value=""))
        self.enterContext(patch.object(push, "git", side_effect=self.git))
        self.compiler = self.enterContext(patch.object(status.subprocess, "run", side_effect=self.compile))
        self.session = publication.VerificationSession(str(self.repo), "topic", "fork", "origin/main")

    def add_source(self, address):
        (self.repo / f"src/{address}.c").write_text(f"unsigned func_{address}(unsigned x) {{ return x+1; }}\n")
        (self.repo / f"docs/match/{address}.md").write_text("**MATCH - byte identical** - 4/4 bytes\n")

    def make_archive(self, repo, commit):
        self.archive = Path(tempfile.mkdtemp(prefix="archive_", dir=self.root))
        shutil.copytree(self.repo, self.archive, dirs_exist_ok=True)
        return str(self.archive)

    def git(self, *args, **kwargs):
        if args[0] == "rev-parse":
            return 0, "c" * 40 + "\n"
        if args[0] == "ls-remote":
            return 0, "c" * 40 + "\trefs/heads/main\n"
        return 0, ""

    def compile(self, command, **kwargs):
        self.calls.append(command[4])
        return subprocess.CompletedProcess(command, 0,
            "extent    4 bytes (complete ELF symbol; closed CFG; no relocations)\n"
            "verdict MATCH - byte identical\n", "")

    def verify(self):
        return self.session.verify(self.head)

    def accept_progress(self):
        event = self.verify()
        (self.repo / "README.md").write_text(event["status_block"])
        (self.repo / "docs/status.md").write_text(event["status_block"])
        return self.verify()

    def test_fresh_baseline_unchanged_reuse_and_new_source_verification(self):
        self.assertEqual(self.accept_progress()["event"], "verified")
        self.assertEqual(self.calls, ["08000000"])
        self.add_source("08000010")
        self.head = "d" * 40
        event = self.verify()
        self.assertEqual((event["event"], event["fresh"], event["reused"]), ("progress-stale", 1, 1))
        self.assertEqual(self.calls, ["08000000", "08000010"])
        with self.assertRaisesRegex(ValueError, "every gate"):
            self.session.publish(self.head)
        self.assertEqual(self.accept_progress()["event"], "verified")
        self.assertEqual(self.calls, ["08000000", "08000010"])
        with patch.object(push, "do_push", return_value=True) as publish:
            self.session.publish(self.head)
            publish.assert_called_once_with(str(self.repo), "fork", "topic", force=True,
                lease=("destination", "b"*40), commit=self.head)

    def test_modified_source_or_report_invalidates_all_and_recompiles(self):
        self.add_source("08000010")
        self.accept_progress()
        for name in ("src/08000000.c", "docs/match/08000000.md"):
            path = self.repo / name
            path.write_text(path.read_text() + "\n")
            event = self.verify()
            self.assertEqual((event["fresh"], event["reused"]), (2, 0))
        self.assertEqual(len(self.calls), 6)

    def test_changed_source_failure_cannot_reuse_old_success(self):
        self.accept_progress()
        (self.repo / "src/08000000.c").write_text("invalid\n")
        self.compiler.side_effect = lambda command, **kwargs: subprocess.CompletedProcess(command, 1, "", "real error")
        with self.assertRaisesRegex(ValueError, "DOES NOT MATCH"):
            self.verify()
        self.assertFalse(self.session.results)
        self.assertIsNone(self.session.verified)

    def test_shared_dependencies_refuse_reuse(self):
        self.accept_progress()
        for name in ("include/ffta.h", "config/functions.json", "config/data_symbols.json",
                     "symbols/functions.txt", "profile-helper.json"):
            with self.subTest(name=name):
                path = self.repo / name
                old = path.read_bytes() if path.exists() else None
                path.write_bytes((old or b"") + b"\n")
                with self.assertRaisesRegex(ValueError, "shared committed dependency"):
                    self.verify()
                if old is None:
                    path.unlink()
                else:
                    path.write_bytes(old)
        self.assertEqual(self.calls, ["08000000"])

    def test_rom_tool_and_environment_changes_refuse_reuse(self):
        self.accept_progress()
        for path in (self.repo / "baserom.bin", self.tool):
            original = path.read_bytes()
            path.write_bytes(original + b"x")
            with self.assertRaisesRegex(ValueError, "runtime, tool, environment or ROM"):
                self.verify()
            path.write_bytes(original)
        with patch.dict(os.environ, {"PUBLICATION_CHANGED_ENV": "1"}):
            with self.assertRaisesRegex(ValueError, "runtime, tool, environment or ROM"):
                self.verify()
        self.assertFalse(self.session.results)

    def test_duplicate_source_and_duplicate_index_entries_refuse(self):
        self.accept_progress()
        nested = self.repo / "src/nested"
        nested.mkdir()
        shutil.copy2(self.repo / "src/08000000.c", nested / "08000000.c")
        with self.assertRaisesRegex(ValueError, "unique canonical"):
            self.verify()
        shutil.rmtree(nested)
        (self.repo / "config/functions.json").write_text(json.dumps(self.entries + self.entries[:1]))
        with self.assertRaisesRegex(ValueError, "duplicate function-index"):
            self.verify()

    def test_overlap_of_reused_and_fresh_complete_bodies_refuses(self):
        self.entries[1].update(rom="0x08000002", end="0x08000006")
        (self.repo / "config/functions.json").write_text(json.dumps(self.entries))
        (self.repo / "symbols/functions.txt").write_text("".join(
            f"{int(entry['rom'],16):08X} {int(entry['end'],16):08X} 4 2 return\n"
            for entry in self.entries))
        self.accept_progress()
        self.add_source("08000002")
        with self.assertRaisesRegex(ValueError, "overlapping complete verified"):
            self.verify()
        self.assertEqual(self.calls, ["08000000", "08000002"])

    def test_missing_complete_extent_refuses(self):
        self.compiler.side_effect = lambda command, **kwargs: subprocess.CompletedProcess(command, 0,
                                                        "verdict MATCH - byte identical\n", "")
        with self.assertRaisesRegex(ValueError, "missing complete verified"):
            self.verify()

    def test_snapshot_mutation_during_compilation_refuses(self):
        def mutate(command, **kwargs):
            (self.archive / "include/ffta.h").write_text("changed\n")
            return self.compile(command, **kwargs)
        self.compiler.side_effect = mutate
        with self.assertRaisesRegex(ValueError, "snapshot mutated"):
            self.verify()
        self.assertFalse(self.session.results)

    def test_head_change_during_compilation_refuses(self):
        def mutate(command, **kwargs):
            self.head = "d" * 40
            return self.compile(command, **kwargs)
        self.compiler.side_effect = mutate
        with self.assertRaisesRegex(ValueError, "captured current branch HEAD"):
            self.verify()
        self.assertFalse(self.session.results)

    def test_runtime_change_during_compilation_refuses(self):
        def mutate(command, **kwargs):
            self.tool.write_text("changed\n")
            return self.compile(command, **kwargs)
        self.compiler.side_effect = mutate
        with self.assertRaisesRegex(ValueError, "runtime, tool, environment or ROM"):
            self.verify()
        self.assertFalse(self.session.results)

    def test_report_and_plausibility_gates_still_run_on_reuse(self):
        self.accept_progress()
        for name in ("check_reports", "check_plausible"):
            with patch.object(push, name, return_value=False):
                with self.assertRaisesRegex(ValueError, "plausibility/report"):
                    self.verify()
        self.assertEqual(self.calls, ["08000000"])

    def test_removed_source_and_unowned_report_addition_refuse(self):
        self.accept_progress()
        path = self.repo / "src/08000000.c"
        old = path.read_bytes()
        path.unlink()
        with self.assertRaisesRegex(ValueError, "removed or moved"):
            self.verify()
        path.write_bytes(old)
        (self.repo / "docs/match/08000010.md").write_text("unowned\n")
        with self.assertRaisesRegex(ValueError, "unowned report"):
            self.verify()

    def test_archive_failure_never_falls_back_to_working_files(self):
        with patch.object(push, "committed_tree", return_value=None):
            with self.assertRaisesRegex(ValueError, "archive"):
                self.verify()
        self.assertFalse(self.calls)

    def test_remote_destination_race_refuses_without_push(self):
        self.accept_progress()
        with patch.object(push, "capture_force_lease", return_value=("destination", "e"*40)), \
                patch.object(push, "do_push") as publish:
            with self.assertRaisesRegex(ValueError, "destination changed"):
                self.session.publish(self.head)
            publish.assert_not_called()

    def test_upstream_race_refuses_without_push(self):
        self.accept_progress()
        original = self.git
        def raced(*args, **kwargs):
            return (0, "e"*40 + "\trefs/heads/main\n") if args[0] == "ls-remote" else original(*args, **kwargs)
        with patch.object(push, "git", side_effect=raced), patch.object(push, "do_push") as publish:
            with self.assertRaisesRegex(ValueError, "upstream base changed"):
                self.session.publish(self.head)
            publish.assert_not_called()

    def test_changed_head_and_failed_history_never_publish(self):
        self.accept_progress()
        for context in (patch.object(push, "publish_snapshot", return_value=("refs/heads/topic", "e"*40)),
                        patch.object(push, "check_history", return_value=False)):
            with context, patch.object(push, "do_push") as publish:
                with self.assertRaises(ValueError):
                    self.session.publish(self.head)
                publish.assert_not_called()

    def test_duplicate_text_index_and_committed_build_inputs_refuse(self):
        self.accept_progress()
        path = self.repo / "symbols/functions.txt"
        old = path.read_text()
        path.write_text(old + old.splitlines()[0] + "\n")
        with self.assertRaisesRegex(ValueError, "duplicate text function-index"):
            self.verify()
        path.write_text(old)
        (self.repo / "build").mkdir()
        (self.repo / "build/input").write_text("unbound input")
        with self.assertRaisesRegex(ValueError, "committed build inputs"):
            self.verify()

    def test_added_match_may_remove_only_its_standard_parked_files(self):
        parked = self.repo / "Parked/08000010"
        parked.mkdir(parents=True)
        for name in ("README.md", "08000010.c"):
            (parked / name).write_text("previous attempt\n")
        self.accept_progress()
        self.add_source("08000010")
        shutil.rmtree(parked)
        event = self.verify()
        self.assertEqual((event["reused"], event["fresh"]), (1, 1))

    def test_other_parked_removals_edits_or_extra_artifacts_are_refused(self):
        parked = self.repo / "Parked/08000010"
        parked.mkdir(parents=True)
        for name in ("README.md", "extra.json"):
            (parked / name).write_text("previous attempt\n")
        self.accept_progress()
        readme = parked / "README.md"
        readme.unlink()
        with self.assertRaisesRegex(ValueError, "shared committed dependency"):
            self.verify()
        readme.write_text("changed attempt\n")
        self.add_source("08000010")
        with self.assertRaisesRegex(ValueError, "shared committed dependency"):
            self.verify()
        shutil.rmtree(parked)
        with self.assertRaisesRegex(ValueError, "shared committed dependency"):
            self.verify()

    def test_file_presence_and_time_dependent_preprocessing_are_refused(self):
        path = self.repo / "src/08000000.c"
        original = path.read_text()
        for token in ('__has_include("08000010.c")', '__DATE__', '__TIME__', '__TIMESTAMP__',
                      '__has_\\\ninclude("08000010.c")', '#define P(a,b) a ## b\nP(__,TIME__)',
                      '#define P(a,b) a %:%: b', '#define P(a,b) a ??=??= b',
                      '__has_\\u0069nclude("08000010.c")', 'char *s="//"; int x=__TIME__;',
                      '#define P(a,b) a #/**/# b'):
            with self.subTest(token=token):
                path.write_text(token + "\n" + original)
                with self.assertRaisesRegex(ValueError, "context-dependent preprocessing"):
                    self.verify()
        self.assertFalse(self.calls)

    def test_process_boundary_refuses(self):
        with patch.object(publication.os, "getpid", return_value=os.getpid()+1):
            with self.assertRaisesRegex(ValueError, "process boundary"):
                self.verify()

    def test_two_push_protocol_reuses_results_and_advances_exact_lease(self):
        self.accept_progress()
        first = self.head
        second = "d" * 40
        destination = ["destination", "b" * 40]
        pushed = []

        def publish(*args, **kwargs):
            self.assertEqual(kwargs["lease"], tuple(destination))
            destination[1] = kwargs["commit"]
            pushed.append(kwargs["commit"])
            return True

        def commands():
            yield f"push {first}\n"
            self.add_source("08000010")
            self.head = second
            yield f"verify {second}\n"
            event = events[-1]
            self.assertEqual((event["fresh"], event["reused"]), (1, 1))
            (self.repo / "README.md").write_text(event["status_block"])
            (self.repo / "docs/status.md").write_text(event["status_block"])
            yield f"verify {second}\n"
            yield f"push {second}\n"
            yield "quit\n"

        from types import SimpleNamespace
        args = SimpleNamespace(repo=str(self.repo), branch="topic", remote="fork",
                               session_base="origin/main", jobs=1, worker_processes=0)
        events = []
        with patch.object(push, "is_checkout_root", return_value=True), \
                patch.object(push, "capture_force_lease", side_effect=lambda *a: tuple(destination)), \
                patch.object(push, "do_push", side_effect=publish), \
                patch.object(publication, "emit", side_effect=events.append), \
                patch.object(sys, "stdin", commands()):
            self.assertEqual(publication.run_session(args), 0)
        self.assertEqual(pushed, [first, second])
        self.assertEqual([e["commit"] for e in events if e["event"] == "pushed"], [first, second])
        self.assertEqual(self.calls, ["08000000", "08000000", "08000010"])

    def test_after_push_stale_destination_and_atomic_failure_keep_lease(self):
        self.accept_progress()
        with patch.object(push, "do_push", return_value=True):
            self.session.publish(self.head)
        lease = ("destination", self.head)
        self.assertEqual(self.session.lease, lease)
        for remote_tip in ("b" * 40, "e" * 40):
            with patch.object(push, "capture_force_lease", return_value=("destination", remote_tip)), \
                    patch.object(push, "do_push") as publish:
                with self.assertRaisesRegex(ValueError, "destination changed"):
                    self.session.publish(self.head)
                publish.assert_not_called()
            self.assertEqual(self.session.lease, lease)
        self.head = "d" * 40
        self.accept_progress()
        with patch.object(push, "capture_force_lease", return_value=lease), \
                patch.object(push, "do_push", return_value=False):
            with self.assertRaisesRegex(ValueError, "conditional native push failed"):
                self.session.publish(self.head)
        self.assertEqual(self.session.lease, lease)

    def test_dry_push_does_not_advance_destination_lease(self):
        with patch.dict(os.environ, {"FFTA_PUSH_DRY": "1"}):
            self.session = publication.VerificationSession(str(self.repo), "topic", "fork", "origin/main")
            self.accept_progress()
            lease = self.session.lease
            with patch.object(push, "do_push", return_value=True) as publish:
                self.session.publish(self.head)
                self.session.publish(self.head)
                self.assertEqual(publish.call_count, 2)
            self.assertEqual(self.session.lease, lease)

    def test_actual_stdin_protocol_routes_through_live_session(self):
        self.accept_progress()
        from types import SimpleNamespace
        args = SimpleNamespace(repo=str(self.repo), branch="topic", remote="fork", session_base="origin/main",
                               jobs=1, worker_processes=0)
        with patch.object(push, "is_checkout_root", return_value=True), \
                patch.object(sys, "stdin", io.StringIO(f"verify {self.head}\nquit\n")):
            self.assertEqual(publication.run_session(args), 0)
        # A second session starts from fresh verification; no previous JSON receipt is read.
        self.assertEqual(self.calls, ["08000000", "08000000"])


if __name__ == "__main__":
    unittest.main()
