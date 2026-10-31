"""Synthetic status dispatch checks; subprocess and proof boundaries stay mocked."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

STAGED = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get('FFTA_TEST_PRODUCTION_KIT', STAGED))
sys.path[:0] = [str(STAGED / 'tools'), str(PRODUCTION / 'tools')]
import private_float_pack_admission_profile as private_float
import status

ADDRESS = 0x08000000
BODY = '0000000000007047'
REPORT = ('# synthetic status fixture\n'
          f'* verification: `{private_float.SCHEMA}`\n'
          f'* private float pack: `{private_float.SELECTOR}`\n'
          f'* compiled : `{BODY}`\n'
          f'* ROM bytes: `{BODY}` (8 bytes)\n'
          '**MATCH - byte identical** - 8/8 bytes\n')
OUTPUT = ('extent    8 bytes (complete ELF symbol; synthetic mock; no relocations)\n'
          'verdict MATCH - byte identical\n')


class StatusPrivateFloatRoutingTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', STAGED / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='private_float_status_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for relative in ('config', 'src', 'docs/match'):
            (self.root / relative).mkdir(parents=True)
        (self.root / 'config/functions.json').write_text(json.dumps([
            {'rom': f'0x{ADDRESS:08X}', 'end': f'0x{ADDRESS + 8:08X}', 'mode': 'thumb'}]))
        (self.root / f'src/{ADDRESS:08X}.c').write_text('/* synthetic; never compiled */\n')
        self.report_path = self.root / f'docs/match/{ADDRESS:08X}.md'
        self.report_path.write_text(REPORT)

    def collect(self, verify=True, write_reports=False):
        return status.collect(str(self.root), verify, write_reports=write_reports)

    def success(self):
        return (1, 1, 8, 8, [], 0, 0)

    def test_verify_routes_exact_selector_and_revalidates_no_write_report(self):
        def invoke(command, **options):
            self.assertEqual(command, [sys.executable, str(STAGED / 'tools/match.py'),
                '--root', str(self.root), f'{ADDRESS:08X}', '--owner-runtime-profile',
                private_float.SELECTOR, '--no-write'])
            self.assertEqual(options, {'capture_output': True, 'text': True})
            return subprocess.CompletedProcess(command, 0, OUTPUT, '')
        with patch.object(status.subprocess, 'run', side_effect=invoke) as native, \
                patch.object(private_float, 'report_matches', return_value=True) as proof:
            self.assertEqual(self.collect(), self.success())
            native.assert_called_once()
            proof.assert_called_once_with(REPORT, str(self.root), ADDRESS)

    def test_write_verify_checks_regenerated_report_after_native(self):
        old_report = REPORT.replace('# synthetic status fixture', '# previous producer fixture')
        self.report_path.write_text(old_report)
        def invoke(command, **options):
            self.assertEqual(command[-2:], ['--owner-runtime-profile', private_float.SELECTOR])
            self.assertNotIn('--no-write', command)
            self.report_path.write_text(REPORT)
            return subprocess.CompletedProcess(command, 0, OUTPUT, '')
        with patch.object(status.subprocess, 'run', side_effect=invoke) as native, \
                patch.object(private_float, 'report_matches', return_value=True) as proof:
            self.assertEqual(self.collect(write_reports=True), self.success())
            native.assert_called_once()
            proof.assert_called_once_with(REPORT, str(self.root), ADDRESS)

    def test_successful_native_cannot_bypass_report_evidence_refusal(self):
        with patch.object(status.subprocess, 'run', return_value=subprocess.CompletedProcess(
                [], 0, OUTPUT, '')) as native, \
                patch.object(private_float, 'report_matches', return_value=False) as proof:
            self.assertEqual(self.collect(), (1, 0, 8, 0, ['08000000: DOES NOT MATCH'], 0, 0))
            native.assert_called_once()
            proof.assert_called_once_with(REPORT, str(self.root), ADDRESS)

    def test_unknown_duplicate_and_mixed_profiles_never_launch_native(self):
        variants = [REPORT.replace(private_float.SELECTOR, 'private-float-unpack-pack-v2'),
            REPORT.replace(private_float.SCHEMA, 'elf-symbol-thumb-private-float-inventory-v1'),
            REPORT + f'* private float pack: `{private_float.SELECTOR}`\n',
            REPORT + '* verification: `elf-symbol-cfg-leaf-v2`\n',
            REPORT + '* owner runtime: restoring-owner-runtime-v1\n']
        for number, report in enumerate(variants):
            with self.subTest(number=number):
                self.report_path.write_text(report)
                with patch.object(status.subprocess, 'run') as native, \
                        patch.object(private_float, 'report_matches') as proof:
                    result = self.collect()
                    self.assertEqual(result[:4], (1, 0, 8, 0))
                    self.assertEqual(len(result[4]), 1)
                    self.assertIn('mixed or malformed', result[4][0])
                    native.assert_not_called()
                    proof.assert_not_called()

    def test_failed_native_never_counts_or_revalidates_report(self):
        for code, output in ((1, OUTPUT), (0, 'extent only, no verdict\n')):
            with self.subTest(exit=code), patch.object(status.subprocess, 'run',
                    return_value=subprocess.CompletedProcess([], code, output, 'failure')) as native, \
                    patch.object(private_float, 'report_matches') as proof:
                self.assertEqual(self.collect(), (1, 0, 8, 0, ['08000000: DOES NOT MATCH'], 0, 0))
                native.assert_called_once()
                proof.assert_not_called()

    def test_offline_acceptance_still_uses_private_report_validator(self):
        for accepted in (True, False):
            with self.subTest(accepted=accepted), patch.object(status.subprocess, 'run') as native, \
                    patch.object(private_float, 'report_matches', return_value=accepted) as proof:
                result = self.collect(verify=False)
                expected = self.success() if accepted else (1, 0, 8, 0,
                    ['08000000: no current, source-bound MATCH report; re-run match.py'], 0, 0)
                self.assertEqual(result, expected)
                native.assert_not_called()
                proof.assert_called_once_with(REPORT, str(self.root), ADDRESS)

    def test_selector_and_verdict_without_evidence_cannot_count(self):
        # The real report parser rejects this deliberately incomplete synthetic
        # report before any source rebuild, ROM lookup or proof execution.
        with patch.object(status.subprocess, 'run', return_value=subprocess.CompletedProcess(
                [], 0, OUTPUT, '')) as native, \
                patch.object(private_float, 'build', side_effect=AssertionError('must not rebuild')) as build:
            self.assertEqual(self.collect(), (1, 0, 8, 0, ['08000000: DOES NOT MATCH'], 0, 0))
            native.assert_called_once()
            build.assert_not_called()


if __name__ == '__main__':
    unittest.main()
