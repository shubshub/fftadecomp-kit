"""Forked verification preserves complete checks, report ownership and errors."""
import contextlib
from concurrent.futures.process import BrokenProcessPool
import io
import json
import multiprocessing
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import push
import status
import test_status_parallel as fixtures


class ProcessVerificationTests(unittest.TestCase):
    setUp = fixtures.StatusParallelTests.setUp
    fixture = fixtures.StatusParallelTests.fixture

    def collect(self, workers=4, **kwargs):
        return status.collect(str(self.root), True, worker_processes=workers, **kwargs)

    def test_actual_processes_check_every_source_once_and_keep_order(self):
        self.fixture([0x08000000 + i * 16 for i in range(32)])
        ctx = multiprocessing.get_context('fork')
        count, active, peak = [ctx.Value('i', 0) for _ in range(3)]
        lock, barrier = ctx.Lock(), ctx.Barrier(8)
        original_cwd, original_env = os.getcwd(), dict(os.environ)
        def invoke(command, **kwargs):
            self.assertEqual(kwargs, dict(capture_output=True, text=True))
            self.assertEqual(command[-1], '--no-write')
            address = command[4]
            with lock:
                count.value += 1
                first = count.value <= 8
                active.value += 1
                peak.value = max(peak.value, active.value)
            if first:
                barrier.wait(timeout=10)
            if address == '08000000':
                time.sleep(.03)
            with (self.root / (address + '.invocation')).open('x') as stream:
                json.dump(dict(pid=os.getpid(), command=command), stream)
            with lock:
                active.value -= 1
            return subprocess.CompletedProcess(command, int(address in ('08000010', '080001F0')),
                                               fixtures.matched_output(), '')
        with patch.object(status.subprocess, 'run', side_effect=invoke):
            self.assertEqual(self.collect(8), (32, 30, 256, 240,
                ['08000010: DOES NOT MATCH', '080001F0: DOES NOT MATCH'], 0, 0))
        records = [json.loads(p.read_text()) for p in self.root.glob('*.invocation')]
        self.assertEqual(len(records), 32)
        self.assertEqual(len({x['pid'] for x in records}), 8)
        self.assertNotIn(os.getpid(), {x['pid'] for x in records})
        self.assertEqual(peak.value, 8)
        self.assertEqual(count.value, 32)
        self.assertEqual((os.getcwd(), dict(os.environ)), (original_cwd, original_env))

    def test_duplicate_destinations_share_one_worker_and_original_result_order(self):
        self.fixture([0x08000000, 0x08000010])
        (self.root / 'src/nested').mkdir()
        (self.root / 'src/nested/08000000.c').write_text('void duplicate(void) {}\n')
        ctx = multiprocessing.get_context('fork')
        active, peak, count = [ctx.Value('i', 0) for _ in range(3)]
        lock = ctx.Lock()
        def invoke(command, **kwargs):
            self.assertNotIn('--no-write', command)
            if command[4] == '08000000':
                with lock:
                    active.value += 1
                    peak.value = max(peak.value, active.value)
                    count.value += 1
                time.sleep(.02)
                with lock:
                    active.value -= 1
            return subprocess.CompletedProcess(command, 1, '', '')
        with patch.object(status.subprocess, 'run', side_effect=invoke):
            self.assertEqual(self.collect(write_reports=True)[4], [
                '08000000: DOES NOT MATCH', '08000010: DOES NOT MATCH',
                '08000000: DOES NOT MATCH'])
        self.assertEqual((count.value, peak.value), (2, 1))

    def test_saved_owner_validation_replay_and_flags_remain_required(self):
        self.fixture([0x08000000, 0x08000010, 0x08000020])
        for address, report in [('08000000', 'valid'), ('08000010', 'stale'), ('08000020', 'changed')]:
            (self.root / f'docs/match/{address}.md').write_text(report)
        import owner_admission_profile as owner
        def replay(report, root, address):
            with (self.root / f'{address:08X}.replays').open('a') as stream:
                stream.write(report + '\n')
            return report != 'stale'
        def invoke(command, **kwargs):
            self.assertEqual(command[-5:], ['--owner-runtime-profile', 'fixture-owner',
                                          '--flags', '-O2', '--no-write'])
            if command[4] == '08000020':
                (self.root / 'docs/match/08000020.md').write_text('stale')
            return subprocess.CompletedProcess(command, 0, fixtures.matched_output(), '')
        with patch.object(owner, 'selected', return_value=True), \
                patch.object(owner, 'selector_for_report', return_value='fixture-owner'), \
                patch.object(status, 'compiler_flags', return_value='-O2'), \
                patch.object(status, 'report_matches', side_effect=replay), \
                patch.object(status.subprocess, 'run', side_effect=invoke):
            self.assertEqual(self.collect(), (3, 1, 24, 8, [
                '08000010: invalid saved complete-owner report',
                '08000020: DOES NOT MATCH'], 0, 0))
        self.assertEqual((self.root / '08000000.replays').read_text(), 'valid\nvalid\n')
        self.assertEqual((self.root / '08000010.replays').read_text(), 'stale\n')
        self.assertEqual((self.root / '08000020.replays').read_text(), 'changed\nstale\n')

    def test_parent_keeps_late_extent_and_cross_worker_overlap_checks(self):
        self.fixture([0x0814FFF0, 0x08150000, 0x08150010, 0x08150020])
        responses = {'0814FFF0': fixtures.matched_output(24),
                     '08150000': fixtures.matched_output(),
                     '08150010': fixtures.matched_output(10),
                     '08150020': 'verdict MATCH - byte identical\n'}
        with patch.object(status.subprocess, 'run', side_effect=lambda command, **kwargs:
                          subprocess.CompletedProcess(command, 0, responses[command[4]], '')):
            self.assertEqual(self.collect(), (1, 1, 8, 8, [
                '08150010: complete verified body disagrees with the late indexed extent',
                '08150020: missing or duplicate matcher extent',
                '08150000: late function overlaps another verified body'], 0, 0))

    def test_worker_exception_propagates_without_partial_success(self):
        self.fixture([0x08000000])
        with patch.object(status.subprocess, 'run', side_effect=ValueError('fixture worker failure')), \
                self.assertRaisesRegex(ValueError, 'fixture worker failure'):
            self.collect(2)

    def test_terminated_worker_is_failure(self):
        self.fixture([0x08000000])
        with patch.object(status.subprocess, 'run', side_effect=lambda *args, **kwargs: os._exit(17)), \
                self.assertRaises(BrokenProcessPool):
            self.collect(2)

    def test_invalid_modes_fail_before_loading_sources(self):
        for options in ({'worker_processes': -1}, {'worker_processes': 65},
                        {'worker_processes': 2, 'jobs': 2}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                status.collect(str(self.root), True, **options)
        with patch.object(status.multiprocessing, 'get_all_start_methods', return_value=['spawn']), \
                self.assertRaisesRegex(ValueError, 'require fork'):
            self.collect(2)
        with patch.object(status, 'active_count', return_value=2), \
                self.assertRaisesRegex(ValueError, 'single-threaded'):
            self.collect(2)

    def test_status_cli_process_check_is_readonly(self):
        with patch.object(sys, 'argv', ['status.py', '--root', str(self.root), '--verify', '--check',
                                      '--write', '--worker-processes', '8']), \
                patch.object(status, 'collect', return_value=(0, 0, 0, 0, [], 0, 0)) as collect, \
                patch.object(status, 'badge_base_from_remote', return_value=''), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaisesRegex(SystemExit, 'no status markers'):
            status.main()
        collect.assert_called_once_with(str(self.root), True, write_reports=False, jobs=1, progress={}, worker_processes=8)

    def test_push_forwards_full_verification_and_reports_process_failure(self):
        with patch.object(push, 'run', return_value=(1, 'worker failed')) as run, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(push.check_matches(str(self.root), worker_processes=8))
        run.assert_called_once_with([sys.executable, str(ROOT / 'tools/status.py'), '--root',
            str(self.root), '--check', '--verify', '--worker-processes', '8'], cwd=str(self.root))

    def test_process_gate_keeps_snapshot_all_checks_and_failed_check_prevents_push(self):
        (self.root / '.git').mkdir()
        for match_ok in (True, False):
            archive = self.root / 'archive'
            archive.mkdir()
            with self.subTest(match_ok=match_ok), \
                    patch.object(sys, 'argv', ['push.py', '--repo', str(self.root), '--worker-processes', '8']), \
                    patch.object(push, 'is_checkout_root', return_value=True), \
                    patch.object(push, 'publish_snapshot', return_value=('refs/heads/main', 'a'*40)) as capture, \
                    patch.object(push, 'committed_tree', return_value=str(archive)) as archived, \
                    patch.object(push, 'check_history', return_value=True) as history, \
                    patch.object(push, 'check_no_rom_data', return_value=True) as no_rom, \
                    patch.object(push, 'badge_base', return_value='fixture-badges'), \
                    patch.object(push, 'check_matches', return_value=match_ok) as matches, \
                    patch.object(push, 'check_plausible', return_value=True) as plausible, \
                    patch.object(push, 'check_reports', return_value=True) as reports, \
                    patch.object(push, 'do_push', return_value=True) as publish, \
                    patch.dict(os.environ, {}, clear=False), contextlib.redirect_stdout(io.StringIO()):
                os.environ.pop('FFTA_PUSH_DRY', None)
                self.assertEqual(push.main(), 0 if match_ok else 1)
            # Publishing rechecks the same snapshot after verification.
            self.assertEqual(capture.call_count, 2 if match_ok else 1)
            for call in capture.call_args_list:
                self.assertEqual(call.args, (str(self.root), 'main'))
                self.assertEqual(call.kwargs, dict(require_clean=False))
            archived.assert_called_once_with(str(self.root), 'a'*40)
            history.assert_called_once_with(str(self.root), 'origin', 'main', force=False)
            no_rom.assert_called_once_with(str(self.root), commit='a'*40)
            matches.assert_called_once_with(str(archive), 'fixture-badges', jobs=1, worker_processes=8)
            plausible.assert_called_once_with(str(archive))
            reports.assert_called_once_with(str(archive))
            self.assertEqual(publish.call_count, int(match_ok))
            self.assertFalse(archive.exists())

    def test_push_rejects_process_thread_mix_and_toolkit_mode(self):
        for extra in (['--jobs', '2'], ['--kit']):
            with self.subTest(extra=extra), \
                    patch.object(sys, 'argv', ['push.py', '--worker-processes', '2', *extra]), \
                    patch.object(push, 'publish_snapshot') as capture, \
                    contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
                push.main()
            self.assertEqual(error.exception.code, 2)
            capture.assert_not_called()


class OfflineProcessReplayTests(unittest.TestCase):
    setUp = fixtures.StatusParallelTests.setUp
    fixture = fixtures.StatusParallelTests.fixture

    def report(self, address, size=8, valid=True):
        text = '* compiled : `' + '00' * size + '`\n'
        if not valid:
            text += 'stale\n'
        (self.root / f'docs/match/{address:08X}.md').write_text(text)

    def test_serial_parallel_replay_equivalence_order_progress_and_no_compile(self):
        addresses = [0x08000000 + i * 16 for i in range(12)]
        self.fixture(addresses)
        for address in addresses[:-1]:
            self.report(address, valid=address != addresses[3])
        snapshot = {p: p.read_bytes() for p in self.root.rglob('*.md')}
        ctx = multiprocessing.get_context('fork')
        count, active, peak = [ctx.Value('i', 0) for _ in range(3)]
        lock, barrier = ctx.Lock(), ctx.Barrier(4)
        workers = 0
        def replay(report, root, address):
            with lock:
                count.value += 1
                first = count.value <= 4
                active.value += 1
                peak.value = max(peak.value, active.value)
            if workers and first:
                barrier.wait(timeout=10)
            if address == addresses[0]:
                time.sleep(.03)
            with (self.root / f'{address:08X}.replay').open('a') as stream:
                stream.write(str(os.getpid()) + '\n')
            with lock:
                active.value -= 1
            return 'stale' not in report
        results, progresses = [], []
        with patch.object(status, 'report_matches', side_effect=replay), \
                patch.object(status.subprocess, 'run', side_effect=AssertionError('offline compiled')):
            for workers in (0, 4):
                count.value = active.value = peak.value = 0
                progress = {}
                results.append(status.collect(str(self.root), False,
                    worker_processes=workers, progress=progress, write_reports=True))
                progresses.append(progress)
                self.assertEqual(count.value, 11)
                self.assertEqual(peak.value, 4 if workers else 1)
        self.assertEqual(results[0], results[1])
        self.assertEqual(results[0][:4], (12, 10, 96, 80))
        self.assertEqual(results[0][4], [
            '08000030: no current, source-bound MATCH report; re-run match.py',
            '080000B0: no match report in docs/match/',
            '080000B0: no current, source-bound MATCH report; re-run match.py'])
        self.assertEqual(progresses[0], progresses[1])
        self.assertEqual(snapshot, {p:p.read_bytes() for p in self.root.rglob('*.md')})
        records = [p.read_text().splitlines() for p in self.root.glob('*.replay')]
        self.assertTrue(all(len(row) == 2 and int(row[0]) == os.getpid()
                            and int(row[1]) != os.getpid() for row in records))

    def test_duplicate_reports_stay_in_one_process(self):
        self.fixture([0x08000000, 0x08000010])
        (self.root / 'src/nested').mkdir()
        (self.root / 'src/nested/08000000.c').write_text('void duplicate(void) {}\n')
        for address in (0x08000000, 0x08000010):
            self.report(address)
        def replay(report, root, address):
            with (self.root / f'{address:08X}.pid').open('a') as stream:
                stream.write(str(os.getpid()) + '\n')
            return True
        with patch.object(status, 'report_matches', side_effect=replay):
            result = status.collect(str(self.root), False, worker_processes=2)
        self.assertEqual(result[1], 3)
        pids = (self.root / '08000000.pid').read_text().splitlines()
        self.assertEqual(len(pids), 2)
        self.assertEqual(len(set(pids)), 1)

    def test_parent_rejects_cross_worker_overlap_and_malformed_late_extent(self):
        self.fixture([0x0814FFF0, 0x08150000, 0x08150010])
        self.report(0x0814FFF0, size=24)
        self.report(0x08150000)
        self.report(0x08150010, size=10)
        with patch.object(status, 'report_matches', return_value=True):
            serial = status.collect(str(self.root), False)
            parallel = status.collect(str(self.root), False, worker_processes=3)
        self.assertEqual(serial, parallel)
        self.assertEqual(parallel[4], [
            '08150010: complete verified body disagrees with the late indexed extent',
            '08150000: late function overlaps another verified body'])
        self.assertEqual(parallel[-2:], (0, 0))

    def test_parent_rejects_unknown_main_extent_and_duplicate_late_source(self):
        self.fixture([0x0814FFF0, 0x08150000])
        (self.root / 'docs/match/0814FFF0.md').write_text('missing extent\n')
        self.report(0x08150000)
        with patch.object(status, 'report_matches', return_value=True):
            expected = status.collect(str(self.root), False)
            self.assertEqual(status.collect(str(self.root), False, worker_processes=2), expected)
        self.assertEqual(expected[4], [
            '08150000: cannot exclude overlap with an unknown complete main-body extent'])
        (self.root / 'src/nested').mkdir()
        (self.root / 'src/nested/08150000.c').write_text('void duplicate(void) {}\n')
        with patch.object(status, 'report_matches', return_value=True):
            serial = status.collect(str(self.root), False)
            self.assertEqual(status.collect(str(self.root), False, worker_processes=2), serial)
        self.assertEqual(serial[-2:], (0, 0))
        self.assertEqual(serial[4], [
            '08150000: late source requires one canonical addressed source',
            '08150000: late source requires one canonical addressed source'])

    def test_offline_worker_exceptions_and_death_are_failures(self):
        self.fixture([0x08000000])
        self.report(0x08000000)
        with patch.object(status, 'report_matches', side_effect=ValueError('replay failed')), \
                self.assertRaisesRegex(ValueError, 'replay failed'):
            status.collect(str(self.root), False, worker_processes=2)
        with patch.object(status, 'report_matches', side_effect=lambda *args: os._exit(17)), \
                self.assertRaises(BrokenProcessPool):
            status.collect(str(self.root), False, worker_processes=2)

    def test_offline_restrictions_and_cli_readonly_check(self):
        for options in ({'jobs': 2}, {'worker_processes': 65}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                status.collect(str(self.root), False, **({'worker_processes':2} | options))
        for target, value in ((status.multiprocessing, ['spawn']), (status, 2)):
            name = 'get_all_start_methods' if target is status.multiprocessing else 'active_count'
            with patch.object(target, name, return_value=value), self.assertRaises(ValueError):
                status.collect(str(self.root), False, worker_processes=2)
        with patch.object(sys, 'argv', ['status.py', '--root', str(self.root), '--check',
                                      '--write', '--worker-processes', '4']), \
                patch.object(status, 'collect', return_value=(0,0,0,0,[],0,0)) as collect, \
                patch.object(status, 'badge_base_from_remote', return_value=''), \
                contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit):
            status.main()
        collect.assert_called_once_with(str(self.root), False, write_reports=False,
                                        jobs=1, progress={}, worker_processes=4)


if __name__ == '__main__':
    unittest.main(verbosity=2)
