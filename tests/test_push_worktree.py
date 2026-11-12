"""Publication root validation uses Git for ordinary and linked checkouts."""
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
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import push


class WorktreeRootTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='push_worktree_', dir=os.environ['TMPDIR'])
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.repo = self.root / 'ordinary'
        self.linked = self.root / 'linked'
        self.git('init', '-b', 'main', str(self.repo), cwd=self.root)
        self.git('config', 'user.name', 'Publication test')
        self.git('config', 'user.email', 'publication@example.invalid')
        self.git('commit', '--allow-empty', '-m', 'base')
        self.git('worktree', 'add', '-b', 'linked', str(self.linked))

    def git(self, *args, cwd=None):
        return subprocess.run(['git', *args], cwd=cwd or self.repo, check=True,
                              capture_output=True, text=True).stdout.strip()

    @contextlib.contextmanager
    def invocation(self, repo, *, kit=True, executing_root=None):
        with contextlib.ExitStack() as stack:
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            argv = ['push.py', '--repo', str(repo), '--check-only']
            if kit:
                argv.append('--kit')
            else:
                argv.append('--working-tree')
            stack.enter_context(patch.object(sys, 'argv', argv))
            if executing_root is not None:
                stack.enter_context(patch.object(push, 'KIT_ROOT', str(executing_root.resolve())))
            gates = {name: stack.enter_context(patch.object(push, name, return_value=True))
                     for name in ('check_history', 'check_no_rom_data', 'check_kit_tools',
                                  'check_matches', 'check_plausible', 'check_reports')}
            gates['do_push'] = stack.enter_context(patch.object(push, 'do_push'))
            yield gates

    def accepted(self, repo, *, kit=True):
        with self.invocation(repo, kit=kit, executing_root=repo if kit else None) as gates:
            self.assertEqual(push.main(), 0)
            gates['check_history'].assert_called_once()
            gates['check_no_rom_data'].assert_called_once()
            gates['check_kit_tools' if kit else 'check_matches'].assert_called_once()
            gates['do_push'].assert_not_called()

    def rejected(self, repo):
        with self.invocation(repo, executing_root=repo) as gates:
            with self.assertRaisesRegex(SystemExit, 'is not a git repository'):
                push.main()
            for gate in gates.values():
                gate.assert_not_called()

    def test_ordinary_checkout_root_is_accepted(self):
        self.assertTrue((self.repo / '.git').is_dir())
        self.accepted(self.repo)

    def test_linked_checkout_root_is_accepted_in_kit_mode(self):
        self.assertTrue((self.linked / '.git').is_file())
        self.accepted(self.linked)

    def test_linked_checkout_root_is_accepted_in_game_mode(self):
        self.accepted(self.linked, kit=False)

    def test_other_checkout_remains_forbidden_in_kit_mode(self):
        with self.invocation(self.repo) as gates:
            with self.assertRaisesRegex(SystemExit, 'only the toolkit checkout containing this script'):
                push.main()
            for gate in gates.values():
                gate.assert_not_called()

    def test_nested_subdirectory_is_not_a_checkout_root(self):
        for root in (self.repo, self.linked):
            nested = root / 'nested'
            nested.mkdir()
            with self.subTest(root=root):
                self.rejected(nested)

    def test_bare_repository_is_refused(self):
        bare = self.root / 'bare.git'
        self.git('init', '--bare', str(bare), cwd=self.root)
        self.rejected(bare)

    def test_invalid_and_dangling_git_files_are_refused(self):
        for index, contents in enumerate(('invalid git metadata\n', 'gitdir: missing\n')):
            repo = self.root / f'invalid{index}'
            repo.mkdir()
            (repo / '.git').write_text(contents)
            with self.subTest(contents=contents):
                self.rejected(repo)

    def test_fake_git_directory_is_refused(self):
        repo = self.root / 'fake'
        (repo / '.git').mkdir(parents=True)
        self.rejected(repo)

    def test_non_repository_and_missing_directory_are_refused(self):
        plain = self.root / 'plain'
        plain.mkdir()
        for repo in (plain, self.root / 'missing'):
            with self.subTest(repo=repo):
                self.rejected(repo)


if __name__ == '__main__':
    unittest.main()
