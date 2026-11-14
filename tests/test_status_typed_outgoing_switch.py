"""New status lifecycle checks using real typed-switch report replay, never a compiler."""
import copy
import json
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
if os.environ.get('FFTA_TEST_TOOLS_FALLBACK'):
    sys.path.append(os.environ['FFTA_TEST_TOOLS_FALLBACK'])
import status
import match_evidence as evidence
import typed_switch_outgoing_frame as frame
from test_typed_switch_outgoing_frame import combined, BASE, OBJECTS


class StatusTypedOutgoingSwitchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='status_typed_', dir=scratch)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for relative in ('config', 'src', 'docs/match'):
            (self.root / relative).mkdir(parents=True)
        self.fixture = combined()
        self.body = bytes(self.fixture[0])
        self.size = len(self.body)
        self.source = self.root / 'src/08000000.c'
        self.source.write_text('/* synthetic status input; never compiled */\n')
        self.mapping = self.root / 'config/functions.json'
        self.mapping.write_text(json.dumps(self.fixture[5]))
        self.objects = self.root / 'config/data_symbols.json'
        self.objects.write_text(json.dumps(OBJECTS))
        self.rom = self.root / 'synthetic.bin'
        self.rom.write_bytes(self.body.ljust(8192, b'\0'))
        self.enterContext(patch.object(evidence, 'report_rom_path', return_value=str(self.rom)))
        self.report = self.root / 'docs/match/08000000.md'
        self.original = self.render()
        self.report.write_text(self.original)
        self.output = (f'extent    {self.size} bytes (complete ELF symbol; synthetic subprocess)\n'
                       'verdict MATCH - byte identical\n')

    def render(self):
        manifest = self.fixture[4]
        return '\n'.join([
            '# synthetic typed outgoing switch', f'* verification: `{frame.SCHEMA}`',
            f'* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`',
            f'* mapping SHA-256: `{evidence.mapping_fingerprint(self.mapping.read_bytes())}`',
            f'* data symbols SHA-256: `{evidence.mapping_fingerprint(self.objects.read_bytes())}`',
            f'* switches: {frame.SUMMARY}', '* source plausibility: plausible',
            '* relocations: none',
            '* verified extent: complete ELF function symbol, including literal pools',
            f'* stack frame: {evidence.STACK_SUMMARY}',
            f'* compiled : `{self.body.hex()}`',
            f'* switch manifest: `{evidence.switch_manifest(manifest)}`',
            f'* switch proof SHA-256: `{frame.fingerprint(BASE, self.body, manifest)}`',
            f'* control flow: {evidence.CALL_SUMMARY}',
            f'* ROM bytes: `{self.body.hex()}` ({self.size} bytes)',
            f'**MATCH - byte identical** - {self.size}/{self.size} bytes', ''])

    def collect(self, verify=True, write=False):
        return status.collect(str(self.root), verify, write_reports=write)

    def assert_count(self, result, matched):
        total = sum(int(row['end'], 16) - int(row['rom'], 16) for row in self.fixture[5])
        self.assertEqual(result[:4], (2, int(matched), total, self.size if matched else 0))
        self.assertEqual(result[-2:], (0, 0))
        self.assertEqual(bool(result[4]), not matched)

    def test_real_fresh_report_routes_exact_selector_and_replays_no_write(self):
        def invoke(command, **kwargs):
            self.assertEqual(command, [sys.executable, str(ROOT / 'tools/match.py'), '--root',
                str(self.root), '08000000', '--switch-data-profile', frame.SELECTOR, '--no-write'])
            self.assertEqual(kwargs, {'capture_output': True, 'text': True})
            return subprocess.CompletedProcess(command, 0, self.output, '')
        with patch.object(status.subprocess, 'run', side_effect=invoke) as native, \
                patch.object(status, 'report_matches', wraps=evidence.report_matches) as replay:
            self.assert_count(self.collect(), True)
            native.assert_called_once()
            self.assertEqual(replay.call_count, 2)
            self.assertEqual([call.args[0] for call in replay.call_args_list], [self.original] * 2)

    def test_rebuild_forwards_the_exact_selector(self):
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(self.original, self.root, BASE),
                         ['--switch-data-profile', frame.SELECTOR])
        with self.assertRaisesRegex(ValueError, 'invalid saved profile report'):
            rebuild.saved_profile_arguments(self.original.replace('* relocations: none', '* relocations: some'),
                                            self.root, BASE)

    def test_write_verification_revalidates_actual_regenerated_report(self):
        regenerated = self.original.replace('# synthetic', '# regenerated synthetic')
        def invoke(command, **kwargs):
            self.assertEqual(command[-2:], ['--switch-data-profile', frame.SELECTOR])
            self.assertNotIn('--no-write', command)
            self.report.write_text(regenerated)
            return subprocess.CompletedProcess(command, 0, self.output, '')
        with patch.object(status.subprocess, 'run', side_effect=invoke) as native, \
                patch.object(status, 'report_matches', wraps=evidence.report_matches) as replay:
            self.assert_count(self.collect(write=True), True)
            native.assert_called_once()
            self.assertEqual([call.args[0] for call in replay.call_args_list],
                             [self.original, regenerated])

    def test_stale_source_mapping_and_data_never_launch_verification(self):
        for path in (self.source, self.mapping, self.objects):
            previous = path.read_bytes()
            with self.subTest(path=path.name):
                path.write_bytes(previous + b'\n')
                with patch.object(status.subprocess, 'run') as native:
                    result = self.collect()
                    self.assert_count(result, False)
                    self.assertIn('invalid saved typed outgoing switch report', result[4][0])
                    native.assert_not_called()
                path.write_bytes(previous)

    def test_malformed_ambiguous_and_cross_profile_reports_never_launch(self):
        manifest_line = next(line for line in self.original.splitlines()
                             if line.startswith('* switch manifest:'))
        variants = [self.original.replace(frame.SCHEMA, frame.SCHEMA + '-unknown'),
            self.original.replace(frame.SELECTOR, 'typed-outgoing-six-words-v2'),
            self.original + manifest_line + '\n',
            self.original + '* verification: `elf-symbol-cfg-leaf-v2`\n',
            self.original + '* owner runtime: restoring-owner-runtime-v1\n',
            self.original + '* switch constants: two-constants-v1\n',
            self.original.replace('"frame_policy":', '"frame_policy":"duplicate","frame_policy":'),
            self.original.replace('* switch manifest:', ' * switch manifest:')]
        for number, report in enumerate(variants):
            with self.subTest(number=number):
                self.report.write_text(report)
                with patch.object(status.subprocess, 'run') as native:
                    self.assert_count(self.collect(), False)
                    native.assert_not_called()

    def test_native_success_cannot_bypass_changed_or_missing_report(self):
        for mode in ('source', 'manifest', 'missing'):
            previous = self.source.read_bytes()
            self.report.write_text(self.original)
            def invoke(command, **kwargs):
                if mode == 'source': self.source.write_bytes(previous + b'\n')
                elif mode == 'manifest': self.report.write_text(self.original.replace(frame.SELECTOR, 'wrong'))
                else: self.report.unlink()
                return subprocess.CompletedProcess(command, 0, self.output, '')
            with self.subTest(mode=mode), patch.object(status.subprocess, 'run', side_effect=invoke) as native:
                self.assert_count(self.collect(), False)
                native.assert_called_once()
            self.source.write_bytes(previous)

    def test_offline_authentication_failed_native_and_default_routing(self):
        with patch.object(status.subprocess, 'run') as native:
            self.assert_count(self.collect(verify=False), True)
            native.assert_not_called()
        with patch.object(status.subprocess, 'run', return_value=subprocess.CompletedProcess(
                [], 1, self.output, 'synthetic compiler refusal')) as native, \
                patch.object(status, 'report_matches', wraps=evidence.report_matches) as replay:
            self.assert_count(self.collect(), False)
            native.assert_called_once()
            self.assertEqual(replay.call_count, 1)
        self.report.unlink()
        def invoke(command, **kwargs):
            self.assertNotIn('--switch-data-profile', command)
            self.assertEqual(command[-1], '--no-write')
            return subprocess.CompletedProcess(command, 1, '', 'synthetic default refusal')
        with patch.object(status.subprocess, 'run', side_effect=invoke) as native:
            self.assert_count(self.collect(), False)
            native.assert_called_once()
        self.assertIsNone(frame.selector_for_report('* verification: `elf-symbol-cfg-leaf-v2`\n'))


if __name__ == '__main__':
    unittest.main()
