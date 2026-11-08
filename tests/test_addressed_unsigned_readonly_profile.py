"""One explicit incoming ABI word composed with explicit unsigned runtime calls."""
from contextlib import redirect_stdout
import io
import json
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned

profile, match, A = unsigned.profile, unsigned.match, unsigned.A


class UnsignedReadonlyTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, access=0x9802, calls=('udiv', 'umod')):
        return dict(self.base.fixture((0xB510, access, *calls,
                                      0xBC10, 0xBC02, 0x4708)),
                    selector=profile.UNSIGNED_READONLY_SELECTOR)

    def test_actual_read_is_unknown_and_undeclared_reads_writes_escapes_refuse(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['schema'],
                         'elf-symbol-thumb-addressed-unsigned-runtime-readonly-word0-v1')
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0])
        self.assertEqual(incoming['reads'], [[A+2, 0, 4, '0298']])
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertIn('readonly_entry_stack_profile.py', manifest['producer_source_sha256'])
        self.assertIn('umodsi3_profile.py', manifest['producer_source_sha256'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        # word1 read, entry-word store, entry-word address escape
        for access, reason in ((0x9803, 'leaves the declared incoming word0'),
                               (0x9002, 'stack-frame write is outside the tracked frame'),
                               (0xA802, 'stack aliases cannot cross calls')):
            with self.subTest(access=access), self.assertRaisesRegex(ValueError, reason):
                profile.verify(**self.fixture(access))
        for selector, reason in (
                (profile.UNSIGNED_SELECTOR, 'leaves its established frame'),
                (profile.UNSIGNED_BUFFER_SELECTOR, 'leaves its established frame'),
                (profile.INTEGER_READONLY_SELECTOR, 'requires actual signed and unsigned calls'),
                (profile.READONLY_SELECTOR, 'complete canonical addressed bindings')):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, reason):
                profile.verify(**dict(f, selector=selector))
        signed = self.fixture(calls=('udiv', 'div'))
        with self.assertRaisesRegex(ValueError, 'complete canonical addressed bindings'):
            profile.verify(**signed)
        no_read = self.base.fixture((0xB510, 'udiv', 'umod', 0xBC10, 0xBC02, 0x4708))
        with self.assertRaisesRegex(ValueError, 'actual checked incoming reads'):
            profile.verify(**dict(no_read, selector=profile.UNSIGNED_READONLY_SELECTOR))
        with self.assertRaisesRegex(ValueError, 'separate explicit addressed selector'):
            profile.verify(**dict(f, data_mapping=b'{}', data_bindings=[]))

    def test_cli_report_discloses_premise_and_rejects_stale_runtime_or_policy(self):
        f = self.fixture()
        f.update(data_mapping=b'{}', data_bindings=[])
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI: ', report)
            self.assertEqual(profile.selector_for_report(report), profile.UNSIGNED_READONLY_SELECTOR)
            self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
            with patch.object(profile, 'toolchain_fingerprint', return_value=[['changed', '2'*64]]):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
            changed = report.replace(profile.UNSIGNED_READONLY_SELECTOR, profile.UNSIGNED_SELECTOR)
            self.assertFalse(unsigned.fixtures.evidence.report_matches(changed, root, A))
            path = root/'src/08010000.c'
            original = path.read_bytes()
            path.write_bytes(original+b' ')
            try:
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
            finally:
                path.write_bytes(original)
            premise = next(line for line in report.splitlines()
                           if line.startswith('* incoming stack ABI: '))
            self.assertFalse(unsigned.fixtures.evidence.report_matches(
                report.replace(premise+'\n', ''), root, A))
            relabelled = report.replace(
                profile.SCHEMAS[profile.UNSIGNED_READONLY_SELECTOR],
                profile.SCHEMAS[profile.INTEGER_READONLY_SELECTOR]).replace(
                profile.UNSIGNED_READONLY_SELECTOR, profile.INTEGER_READONLY_SELECTOR)
            self.assertEqual(profile.selector_for_report(relabelled), profile.INTEGER_READONLY_SELECTOR)
            self.assertFalse(unsigned.fixtures.evidence.report_matches(relabelled, root, A))
            prefix = '* addressed signed runtime evidence: `'
            line = next(row for row in report.splitlines() if row.startswith(prefix))
            digest = next(row for row in report.splitlines()
                          if row.startswith('* addressed signed runtime proof SHA-256:'))

            def widen(entry):
                entry['words'] = [0, 1]

            def drop_reads(entry):
                entry['reads'] = []

            def move_read(entry):
                entry['reads'][0][1] = 4

            def weaken(entry):
                entry['loaded_value'] = 'nonzero scalar'

            for mutate in (widen, drop_reads, move_read, weaken):
                payload = json.loads(line[len(prefix):-1])
                mutate(payload['manifest']['frame']['entry_stack'])
                changed = profile.text(payload)
                forged = report.replace(line, prefix+changed+'`').replace(
                    digest, f'* addressed signed runtime proof SHA-256: `{profile.sha(changed.encode())}`')
                with self.subTest(forgery=mutate.__name__):
                    self.assertNotEqual(forged, report)
                    self.assertFalse(unsigned.fixtures.evidence.report_matches(forged, root, A))

    def test_single_unsigned_runtime_calls_and_late_read_are_admitted(self):
        for calls in (('udiv',), ('umod',), ('udiv', 'ordinary', 'umod')):
            with self.subTest(calls=calls):
                manifest, _ = profile.verify(**self.fixture(calls=calls))
                self.assertEqual(manifest['frame']['entry_stack']['reads'],
                                 [[A+2, 0, 4, '0298']])
        late = self.base.fixture((0xB510, 'udiv', 0x9802, 'umod', 0xBC10, 0xBC02, 0x4708))
        manifest, _ = profile.verify(**dict(late, selector=profile.UNSIGNED_READONLY_SELECTOR))
        self.assertEqual(manifest['frame']['entry_stack']['reads'], [[A+6, 0, 4, '0298']])

    def test_base_unsigned_selectors_still_refuse_the_incoming_read(self):
        for selector in (profile.UNSIGNED_SELECTOR, profile.UNSIGNED_BUFFER_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(
                    ValueError, 'leaves its established frame'):
                profile.verify(**dict(self.fixture(), selector=selector))


if __name__ == '__main__':
    unittest.main()
