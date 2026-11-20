"""Explicit larger verification pools retain ordering, locks and every gate."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
from threading import Barrier, Event, Lock
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from event_waits import arrive, await_set
import push
import status
import test_status_parallel as fixtures

class LargePoolTests(unittest.TestCase):
    setUp=fixtures.StatusParallelTests.setUp
    fixture=fixtures.StatusParallelTests.fixture
    collect=fixtures.StatusParallelTests.collect

    def test_64_workers_keep_every_source_ordered_with_failures(self):
        self.fixture([0x08000000+i*16 for i in range(128)],reports=True)
        lock,barrier,other_done,sizes=Lock(),Barrier(64),Event(),[]
        active=peak=0
        started,completed=[],[]
        cwd,environment=os.getcwd(),dict(os.environ)
        def invoke(command,**kwargs):
            nonlocal active,peak
            self.assertEqual(kwargs,dict(capture_output=True,text=True))
            self.assertEqual(command[-1],'--no-write')
            address=command[4]
            with lock:
                started.append(address);first=len(started)<=64
                active+=1;peak=max(peak,active)
            if first:arrive(barrier,'all 64 first-batch checks running at once')
            # The first failure finishes only after the last one's check has completed,
            # so completion order reverses the two reported failures.
            if address=='08000010':await_set(other_done,"the check of 080007F0 completing before 08000010's")
            with lock:active-=1;completed.append(address)
            return subprocess.CompletedProcess(command,int(address in ('08000010','080007F0')),
                fixtures.matched_output(),'')
        with patch.object(status,'ThreadPoolExecutor',
                          fixtures.signalling_executor(status.ThreadPoolExecutor,sizes,other_done,'080007F0')), \
                patch.object(status.subprocess,'run',side_effect=invoke):
            result=self.collect(64)
        self.assertEqual(result,(128,126,1024,1008,
            ['08000010: DOES NOT MATCH','080007F0: DOES NOT MATCH'],0,0))
        # Counted under the test's lock: Mock.call_count is updated without a lock on
        # Python 3.12 and early 3.13/3.14 releases (fixed by gh-142651).
        self.assertEqual(len(started),128)
        self.assertEqual(sizes,[64])
        self.assertEqual(len(set(started)),128)
        self.assertEqual(peak,64)
        self.assertGreater(completed.index('08000010'),completed.index('080007F0'))
        self.assertEqual(os.getcwd(),cwd)
        self.assertEqual(dict(os.environ),environment)

    def test_64_worker_duplicate_report_paths_still_serialize(self):
        self.fixture([0x08000000]);(self.root/'src/nested').mkdir()
        (self.root/'src/nested/08000000.c').write_text('void duplicate(void) {}\n')
        fixtures.duplicate_checks_wait_for_each_other(self,64)

    def test_status_cli_64_keeps_check_readonly(self):
        with patch.object(sys,'argv',['status.py','--root',str(self.root),'--verify','--check','--write','--jobs','64']), \
                patch.object(status,'collect',return_value=(0,0,0,0,[],0,0)) as collect, \
                patch.object(status,'badge_base_from_remote',return_value=''), \
                contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaisesRegex(SystemExit,'no status markers'):
            status.main()
        collect.assert_called_once_with(str(self.root),True,write_reports=False,jobs=64,progress={})

    def test_native_gate_64_keeps_snapshot_and_all_checks(self):
        (self.root/'.git').mkdir();archive=self.root/'archive';archive.mkdir()
        snapshot=('refs/heads/main','a'*40)
        with patch.object(sys,'argv',['push.py','--repo',str(self.root),'--check-only','--jobs','64']), \
                patch.object(push,'is_checkout_root',return_value=True), \
                patch.object(push,'publish_snapshot',return_value=snapshot) as capture, \
                patch.object(push,'committed_tree',return_value=str(archive)) as archived, \
                patch.object(push,'check_history',return_value=True) as history, \
                patch.object(push,'check_no_rom_data',return_value=True) as no_rom, \
                patch.object(push,'badge_base',return_value='fixture-badges'), \
                patch.object(push,'check_matches',return_value=True) as matches, \
                patch.object(push,'check_plausible',return_value=True) as plausible, \
                patch.object(push,'check_reports',return_value=True) as reports, \
                patch.object(push,'do_push') as publish,contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(push.main(),0)
        capture.assert_called_once_with(str(self.root),'main',require_clean=False)
        archived.assert_called_once_with(str(self.root),snapshot[1])
        history.assert_called_once_with(str(self.root),'origin','main',force=False)
        no_rom.assert_called_once_with(str(self.root),commit=snapshot[1])
        matches.assert_called_once_with(str(archive),'fixture-badges',jobs=64)
        plausible.assert_called_once_with(str(archive));reports.assert_called_once_with(str(archive))
        publish.assert_not_called();self.assertFalse(archive.exists())

    def test_64_forwarding_runs_full_status_verify(self):
        with patch.object(push,'run',return_value=(0,'up to date')) as run, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(push.check_matches(str(self.root),jobs=64))
        run.assert_called_once_with([sys.executable,str(ROOT/'tools/status.py'),'--root',str(self.root),
                                    '--check','--verify','--jobs','64'],cwd=str(self.root))

    def test_failed_source_gate_still_prevents_push_at_64(self):
        (self.root/'.git').mkdir();archive=self.root/'archive';archive.mkdir()
        with patch.object(sys,'argv',['push.py','--repo',str(self.root),'--jobs','64']), \
                patch.object(push,'is_checkout_root',return_value=True), \
                patch.object(push,'publish_snapshot',return_value=('refs/heads/main','a'*40)), \
                patch.object(push,'committed_tree',return_value=str(archive)), \
                patch.object(push,'check_history',return_value=True), \
                patch.object(push,'check_no_rom_data',return_value=True), \
                patch.object(push,'badge_base',return_value=''), \
                patch.object(push,'check_matches',return_value=False), \
                patch.object(push,'check_plausible',return_value=True), \
                patch.object(push,'check_reports',return_value=True), \
                patch.object(push,'do_push') as publish,contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(push.main(),1)
        publish.assert_not_called();self.assertFalse(archive.exists())

if __name__=='__main__':
    unittest.main(verbosity=2)
