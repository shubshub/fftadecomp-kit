"""Explicit discarded R2/R3 results retain native bounds and R0/R1 escape guards."""
from contextlib import redirect_stdout
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_addressed_native_buffer_data as composition

profile, match = composition.profile, composition.match
A, B = composition.A, composition.native.B


class AddressedNativeBufferScratchTests(unittest.TestCase):
    def setUp(self):
        self.base = composition.AddressedNativeBufferDataTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, helper=b'\x03\x1c\x07\x21\x19\x70\x00\x20\x70\x47', tokens=None):
        f = (self.base.fixture(True, False) if tokens is None else
             self.base.base.base.fixture(tokens))
        rows = json.loads(f['mapping'])
        row = next(row for row in rows if int(row['rom'], 16) == B)
        row.update(end=f'0x{B+len(helper):08X}', instrs=len(helper)//2)
        f['mapping'], f['index'] = composition.native.unsigned.fixtures.indexes(rows)
        rom = bytearray(f['rom'])
        rom[B-match.ROM_BASE:B-match.ROM_BASE+len(helper)] = helper
        f.update(rom=bytes(rom), selector=profile.BUFFER_SCRATCH_SELECTOR)
        return f

    def test_only_explicit_scratch_selector_accepts_native_discarded_alias(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        proof = manifest['native_buffers']
        self.assertEqual(proof['discarded_exit_scratch']['registers'], [2, 3])
        self.assertEqual(proof['discarded_exit_scratch_sites'], [[B, B+8, 3, -12]])
        self.assertIn('no result values are returned through them', proof['contract'])
        for selector in (profile.BUFFER_SELECTOR, profile.SELECTOR,
                         profile.UNSIGNED_BUFFER_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        old = self.base.fixture(True, False)
        before, _ = profile.verify(**old)
        helper = old['rom'][B-match.ROM_BASE:B-match.ROM_BASE+8]
        self.assertEqual(before['native_buffers']['fingerprint'],
                         profile.sha(struct.pack('<II', B, len(helper))+helper))
        with self.assertRaisesRegex(ValueError, 'actual native scratch'):
            profile.verify(**dict(old, selector=profile.BUFFER_SCRATCH_SELECTOR))

    def test_bounds_returned_results_and_pointer_stores_still_fail(self):
        helpers = (
            (b'\x03\x1c\x07\x21\x19\x70\x70\x47', 'buffer pointer escapes through a return register'),
            (b'\x01\x1c\x07\x23\x0b\x70\x00\x20\x70\x47', 'buffer pointer escapes through a return register'),
            (b'\x03\x1c\x07\x21\x19\x71\x00\x20\x70\x47', 'outside allocated local words'),
            (b'\x03\x1c\x18\x60\x00\x20\x70\x47', 'buffer pointers cannot be stored or spilled'),
        )
        for helper, message in helpers:
            with self.subTest(helper=helper.hex()), self.assertRaisesRegex(ValueError, message):
                profile.verify(**self.fixture(helper))
        f = self.fixture()
        policy = profile.buffer_scratch_policy(f['selector'])
        for bad in ({}, dict(policy, registers=[0, 1]),
                    dict(policy, registers=[True, 3]), dict(policy, extra=True)):
            with self.subTest(policy=bad), self.assertRaises(ValueError):
                match.BufferCallProof(f['rom'], f['mapping'], discarded_exit_scratch=bad)
        with self.assertRaisesRegex(ValueError, 'separate'):
            match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True,
                                  discarded_exit_scratch=policy)

    def test_cli_replay_binds_policy_sites_helpers_sources_and_runtime(self):
        f = self.fixture()
        f.update(data_mapping=b'{}', data_bindings=[])
        boundary = self.base.base.base.build_boundary
        with boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = composition.native.unsigned.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(
                report.replace('"registers":[2,3]', '"registers":[0,1]'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            rom = bytearray((root/'baserom.bin').read_bytes())
            rom[B-match.ROM_BASE+4] ^= 1
            (root/'baserom.bin').write_bytes(rom)
            self.assertFalse(evidence.report_matches(report, root, A))

    def test_signed_local_index_requires_native_all_path_zero(self):
        prefix = (0xB510, 0xB081, 0x4668, 0x1C04, 'ordinary')
        suffix = (0x56A0, 0x2102, 'div', 0xB001, 0xBC10, 0xBC02, 0x4708)
        f = self.fixture(tokens=(*prefix, 0x2200, *suffix))
        manifest, _ = profile.verify(**f)
        self.assertEqual(len(manifest['frame']['zero_index_signed_loads']), 1)
        self.assertIn('zero_index_stack_profile.py', manifest['producer_source_sha256'])
        with self.assertRaisesRegex(ValueError, 'local alias requires an ordinary constant-offset memory access'):
            profile.verify(**self.fixture(tokens=(*prefix, 0x2201, *suffix)))


if __name__ == '__main__':
    unittest.main()
