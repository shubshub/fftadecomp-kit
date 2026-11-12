"""New contribution branches keep history checks and atomic absent-ref leases."""
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import push


class CreationTests(unittest.TestCase):
    def setUp(self):
        scratch = ROOT / 'build'
        scratch.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='push_creation_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / 'work'
        self.origin = self.root / 'origin.git'
        self.fork = self.root / 'fork.git'
        self.git('init', '--bare', str(self.origin), cwd=self.root)
        self.git('init', '--bare', str(self.fork), cwd=self.root)
        self.git('init', '-b', 'main', str(self.repo), cwd=self.root)
        self.git('config', 'user.name', 'Publication test')
        self.git('config', 'user.email', 'publication@example.invalid')
        self.git('commit', '--allow-empty', '-m', 'base')
        self.base = self.git('rev-parse', 'HEAD')
        self.git('remote', 'add', 'origin', str(self.origin))
        self.git('remote', 'add', 'fork', str(self.fork))
        self.git('push', 'origin', 'main')
        self.git('switch', '-c', 'contribution')
        self.git('commit', '--allow-empty', '-m', 'change')
        self.head = self.git('rev-parse', 'HEAD')
        self.output = contextlib.redirect_stdout(io.StringIO())
        self.output.__enter__()
        self.addCleanup(self.output.__exit__, None, None, None)
        self.env = patch.dict(os.environ, {}, clear=False)
        self.env.__enter__()
        self.addCleanup(self.env.__exit__, None, None, None)
        os.environ.pop('FFTA_PUSH_DRY', None)

    def git(self, *args, cwd=None):
        return subprocess.run(['git', *args], cwd=cwd or self.repo, check=True,
                              capture_output=True, text=True).stdout.strip()

    def capture(self):
        return push.capture_creation(str(self.repo), 'fork', 'contribution', 'origin/main')

    def publish(self, lease):
        return push.do_push(str(self.repo), 'fork', 'contribution', lease=lease,
                            commit=self.head, create=True)

    def test_actual_creation_pins_base_checks_history_and_publishes_exact_commit(self):
        lease, base = self.capture()
        self.assertEqual(lease, (str(self.fork), ''))
        self.assertEqual(base, (self.base, 'origin/main'))
        self.assertEqual(self.git('ls-remote', '--heads', 'fork'), '')
        self.assertTrue(push.check_history(str(self.repo), 'fork', 'contribution', base=base))
        self.assertTrue(self.publish(lease))
        self.assertEqual(self.git('--git-dir', str(self.fork), 'rev-parse',
                                  'refs/heads/contribution'), self.head)

    def test_concurrent_creation_refuses_even_a_fast_forward(self):
        lease, _ = self.capture()
        self.git('push', 'fork', f'{self.base}:refs/heads/contribution')
        self.assertFalse(self.publish(lease))
        self.assertEqual(self.git('--git-dir', str(self.fork), 'rev-parse',
                                  'refs/heads/contribution'), self.base)

    def test_existing_branch_is_not_a_creation(self):
        self.git('push', 'fork', f'{self.base}:refs/heads/contribution')
        self.assertIsNone(self.capture())

    def test_transport_failure_is_not_absence(self):
        self.git('remote', 'set-url', '--push', 'fork', str(self.root / 'missing.git'))
        self.assertIsNone(self.capture())

    def test_multiple_push_destinations_are_refused(self):
        self.git('config', '--add', 'remote.fork.pushurl', str(self.fork))
        self.git('config', '--add', 'remote.fork.pushurl', str(self.origin))
        self.assertIsNone(self.capture())

    def test_missing_or_invalid_base_is_refused(self):
        for base in ('main', 'origin/missing', 'origin/main:other', 'missing/main'):
            with self.subTest(base=base):
                self.assertIsNone(push.capture_creation(str(self.repo), 'fork',
                                                        'contribution', base))

    def test_fresh_base_advance_requires_rebase(self):
        self.git('switch', 'main')
        self.git('commit', '--allow-empty', '-m', 'upstream advance')
        advanced = self.git('rev-parse', 'HEAD')
        self.git('push', 'origin', 'main')
        self.git('switch', 'contribution')
        _, base = self.capture()
        self.assertEqual(base[0], advanced)
        self.assertFalse(push.check_history(str(self.repo), 'fork', 'contribution', base=base))

    def test_authored_merge_is_refused(self):
        self.git('switch', '-c', 'side', self.base)
        self.git('commit', '--allow-empty', '-m', 'side')
        self.git('switch', 'contribution')
        self.git('merge', '--no-ff', 'side', '-m', 'merge')
        _, base = self.capture()
        self.assertFalse(push.check_history(str(self.repo), 'fork', 'contribution', base=base))

    def test_wrong_checked_out_branch_is_refused(self):
        _, base = self.capture()
        self.git('switch', 'main')
        self.assertFalse(push.check_history(str(self.repo), 'fork', 'contribution', base=base))

    def test_force_cannot_relax_creation_contract(self):
        lease, base = self.capture()
        self.assertFalse(push.check_history(str(self.repo), 'fork', 'contribution',
                                            base=base, force=True))
        self.assertFalse(push.do_push(str(self.repo), 'fork', 'contribution',
                                     lease=lease, commit=self.head, force=True, create=True))
        self.assertFalse(self.publish((str(self.fork), self.base)))
        self.assertFalse(self.publish(None))
        with patch.object(sys, 'argv', ['push.py', '--create-from', 'origin/main', '--force']), \
                contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            push.main()
        self.assertEqual(error.exception.code, 2)

    def test_main_keeps_all_game_gates_and_does_not_publish_a_failed_check(self):
        for failed in (None, 'check_matches', 'check_no_rom_data', 'check_plausible', 'check_reports'):
            with self.subTest(failed=failed), contextlib.ExitStack() as stack:
                archive = self.root / 'archive'
                archive.mkdir()
                stack.enter_context(patch.object(sys, 'argv', ['push.py', '--repo', str(self.repo),
                    '--remote', 'fork', '--branch', 'contribution', '--create-from', 'origin/main']))
                snapshot = ('refs/heads/contribution', self.head)
                capture = stack.enter_context(patch.object(push, 'publish_snapshot', return_value=snapshot))
                stack.enter_context(patch.object(push, 'committed_tree', return_value=str(archive)))
                stack.enter_context(patch.object(push, 'badge_base', return_value=''))
                gates = {name: stack.enter_context(patch.object(push, name, return_value=name != failed))
                         for name in ('check_matches', 'check_no_rom_data', 'check_plausible', 'check_reports')}
                publish = stack.enter_context(patch.object(push, 'do_push', return_value=True))
                self.assertEqual(push.main(), int(failed is not None))
                for gate in gates.values():
                    gate.assert_called_once()
                self.assertEqual(capture.call_count, 2 if failed is None else 1)
                self.assertEqual(publish.call_count, int(failed is None))
                if failed is None:
                    self.assertEqual(publish.call_args.kwargs,
                                     dict(force=False, lease=(str(self.fork), ''), commit=self.head, create=True))
                self.assertFalse(archive.exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
