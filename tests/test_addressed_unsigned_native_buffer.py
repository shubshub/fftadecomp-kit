"""Unsigned ABI composition retains native buffer bounds and source replay."""
import copy
from contextlib import redirect_stdout
import io
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned

profile, match, A, B = unsigned.profile, unsigned.match, unsigned.A, unsigned.B


class AddressedUnsignedNativeBufferTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, helper=b'\x07\x21\x01\x70\x00\x20\x70\x47'):
        f = self.base.fixture((0xB510, 0xB081, 0x4668, 'ordinary',
                               0x2009, 0x2102, 'udiv', 0xB001,
                               0xBC10, 0xBC02, 0x4708))
        rows = unsigned.fixtures.json.loads(f['mapping'])
        row = next(r for r in rows if int(r['rom'], 16) == B)
        row.update(end=f'0x{B+len(helper):08X}', instrs=len(helper)//2)
        f['mapping'], f['index'] = unsigned.fixtures.indexes(rows)
        rom = bytearray(f['rom'])
        rom[B-match.ROM_BASE:B-match.ROM_BASE+len(helper)] = helper
        f.update(rom=bytes(rom), selector=profile.UNSIGNED_BUFFER_SELECTOR)
        return f

    def test_native_bounds_returns_escape_and_selector_separation(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['schema'], profile.SCHEMAS[f['selector']])
        self.assertEqual(manifest['native_buffers']['dependencies'],
                         [[B, 8, profile.sha(f['rom'][B-match.ROM_BASE:B-match.ROM_BASE+8])]])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        for helper, message in (
                (b'\x07\x21\x01\x71\x00\x20\x70\x47', 'outside allocated local words'),
                (b'\x07\x21\x01\x70\x00\x1c\x70\x47', 'buffer pointer escapes through a return register'),
                (b'\x08\x60\x00\x20\x70\x47', 'unsupported buffer pointer use or escape')):
            with self.subTest(helper=helper.hex()), self.assertRaisesRegex(ValueError, message):
                profile.verify(**self.fixture(helper))
        for selector in (profile.UNSIGNED_SELECTOR, profile.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, f['calls'])
        with self.assertRaisesRegex(ValueError, 'actual inspected buffer'):
            profile.verify(**dict(self.base.fixture(), selector=profile.UNSIGNED_BUFFER_SELECTOR))
        bad = copy.deepcopy(manifest)
        bad['native_buffers']['dependencies'][0][2] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=bad)

    def test_full_cli_and_replay_bind_helper_source_runtime_and_maps(self):
        f = self.fixture()
        f['data_bindings'] = []
        f['data_mapping'] = b'{}'
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root / 'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report), f['selector'])
            self.assertIn('local buffer boundary:', report)
            self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
            for relative in ('src/08010000.c', 'config/functions.json',
                             'symbols/functions.txt', 'baserom.bin'):
                path = root / relative
                before = path.read_bytes()
                path.write_bytes(before + b' ')
                try:
                    self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
                finally:
                    path.write_bytes(before)
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
