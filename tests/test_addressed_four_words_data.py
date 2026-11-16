"""Exact four-word incoming ABI premise for mixed integer and compiler signed runtimes."""
from contextlib import redirect_stdout
import io
import struct
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as unsigned
import test_compiler_signed_runtime_numeric_mmio as mmio

profile, match, A = unsigned.profile, unsigned.match, unsigned.A
# Entry SP is two saved words up in the numeric MMIO fixture and one in the integer fixture.
FOUR = (0x9802, 0x9903, 0x9A04, 0x9B05)
INTEGER_FOUR = (0x9801, 0x9902, 0x9A03, 0x9B04)
WRONG_LAST_WORD = ((0x2300, 'cover exactly every declared incoming word'),  # word 3 is never read
                   (0x9B00, 'leaves the declared incoming words'),          # a fifth word is read
                   (0x9300, 'stack-frame write is outside the tracked frame'),
                   (0xAB00, 'stack alias arithmetic leaves the tracked frame'))


def wrong_words(four):
    """Replace word 3's read by each refused access; word 0 is read at SP+4*depth."""
    depth = four[0] & 0xFF
    words = {0x2300: 0, 0x9B00: depth + 4, 0x9300: depth + 3, 0xAB00: depth + 3}
    return [(four[:3] + (encoding | words[encoding],), message) for encoding, message in WRONG_LAST_WORD]


class IntegerFourWordsDataTests(unittest.TestCase):
    def setUp(self):
        self.base = unsigned.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, accesses=INTEGER_FOUR):
        # push {lr} leaves entry SP one word up; the literal follows bx r1 at offset 24.
        tokens = (0xB500, *accesses, 'udiv', 'div', 0x4801, 0xBC02, 0x4708, 0x0020, 0x0300)
        f = self.base.fixture(tokens)
        f.update(selector=profile.INTEGER_FOUR_DATA_SELECTOR,
                 data_mapping=b'{"buffer":"0x03000020"}', data_bindings=[[24, 'buffer', 0]])
        return f

    def test_exact_four_reached_words_stay_unknown_and_boundaries_remain_closed(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['schema'], profile.SCHEMAS[profile.INTEGER_FOUR_DATA_SELECTOR])
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1, 2, 3])
        self.assertEqual([r[1] for r in incoming['reads']], [0, 4, 8, 12])
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual(manifest['data_bindings'], [[24, 'buffer', 0]])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        for accesses, message in wrong_words(INTEGER_FOUR):
            with self.subTest(accesses=accesses), self.assertRaisesRegex(ValueError, message):
                profile.verify(**self.fixture(accesses))
        for selector in (profile.INTEGER_THREE_DATA_SELECTOR, profile.INTEGER_DATA_SELECTOR,
                         profile.READONLY_TWO_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_bindings=[]))
        # The three-word selector's fixture is not widened to four words either.
        three = self.base.fixture((
            0xB510, 0x9802, 0x9903, 0x9A04, 'udiv', 'div', 0x4C01, 0xBC10, 0xBC02, 0x4708, 0x0020, 0x0300))
        three.update(data_mapping=b'{"buffer":"0x03000020"}', data_bindings=[[24, 'buffer', 0]])
        profile.verify(**dict(three, selector=profile.INTEGER_THREE_DATA_SELECTOR))
        with self.assertRaisesRegex(ValueError, 'cover exactly every declared incoming word'):
            profile.verify(**dict(three, selector=profile.INTEGER_FOUR_DATA_SELECTOR))

    def test_mixed_integer_calls_remain_required(self):
        for operations in (('udiv', 'udiv'), ('div', 'div')):
            tokens = (0xB500, *INTEGER_FOUR, *operations, 0x4801,
                      0xBC02, 0x4708, 0x0020, 0x0300)
            f = self.base.fixture(tokens)
            f.update(selector=profile.INTEGER_FOUR_DATA_SELECTOR,
                     data_mapping=b'{"buffer":"0x03000020"}', data_bindings=[[24, 'buffer', 0]])
            with self.subTest(operations=operations), \
                    self.assertRaisesRegex(ValueError, 'actual signed and unsigned calls'):
                profile.verify(**f)

    def test_fresh_cli_report_discloses_premises_and_rejects_stale_inputs(self):
        f = self.fixture()
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn(f'* addressed signed runtime: `{profile.INTEGER_FOUR_DATA_SELECTOR}`', report)
            self.assertIn('* incoming stack ABI: ', report)
            self.assertIn('* named data binding: ', report)
            self.assertTrue(unsigned.fixtures.evidence.report_matches(report, root, A))
            three = report.replace('four-words', 'three-words')
            self.assertFalse(unsigned.fixtures.evidence.report_matches(three, root, A))
            for relative in ('config/data_symbols.json', 'src/08010000.c'):
                path = root/relative
                original = path.read_bytes()
                path.write_bytes(original+b' ')
                try:
                    self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))
                finally:
                    path.write_bytes(original)
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(unsigned.fixtures.evidence.report_matches(report, root, A))


class CompilerFourWordsNumericMmioTests(unittest.TestCase):
    SELECTOR = profile.COMPILER_MMIO_FOUR_DATA_SELECTOR

    def setUp(self):
        self.mmio = mmio.CompilerSignedRuntimeNumericMmioTests('runTest')
        self.mmio.setUp()
        self.addCleanup(self.mmio.doCleanups)

    def fixture(self, reads=FOUR, value=0x04000052):
        # Same shape as the numeric MMIO fixture, with incoming reads before the literal load.
        f = self.mmio.base.base.fixture(reads=reads)
        offset = f['data_bindings'][0][0]
        body = bytearray(f['data'])
        struct.pack_into('<I', body, offset, value)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        f.update(data=bytes(body), rom=bytes(rom), data_bindings=f['data_bindings'][1:])
        return f

    def test_four_words_with_numeric_mmio_and_old_selectors_remain_strict(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f, selector=self.SELECTOR)
        self.assertEqual(manifest['schema'], profile.COMPILER_MMIO_FOUR_DATA_SCHEMA)
        incoming = manifest['frame']['entry_stack']
        self.assertEqual(incoming['words'], [0, 1, 2, 3])
        self.assertEqual([r[1] for r in incoming['reads']], [0, 4, 8, 12])
        self.assertEqual(manifest['numeric_mmio_literals']['words'][0][1], 0x04000052)
        self.assertEqual(manifest['data_bindings'], [])
        self.assertIn('no numeric result', manifest['compiler_runtime']['contract'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        for selector in (profile.COMPILER_MMIO_DATA_SELECTOR, profile.COMPILER_DATA_SELECTOR,
                         profile.READONLY_TWO_DATA_SELECTOR, profile.INTEGER_FOUR_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**f, selector=selector)
        # The existing numeric MMIO selector keeps its frameless incoming boundary.
        profile.verify(**self.mmio.fixture(), selector=profile.COMPILER_MMIO_DATA_SELECTOR)
        with self.assertRaisesRegex(ValueError, 'cover exactly every declared incoming word'):
            profile.verify(**self.mmio.fixture(), selector=self.SELECTOR)

    def test_wrong_incoming_words_and_missing_mmio_refuse(self):
        for reads, message in [(FOUR[:3], 'cover exactly every declared incoming word'), *wrong_words(FOUR)]:
            with self.subTest(reads=reads), self.assertRaisesRegex(ValueError, message):
                profile.verify(**self.fixture(reads), selector=self.SELECTOR)
        # Agbcc's add/ldrb pair for a narrow incoming byte is not admitted on this path.
        with self.assertRaisesRegex(ValueError, 'stack alias arithmetic leaves the tracked frame'):
            profile.verify(**self.fixture(FOUR[:3] + (0xAB05, 0x781B)), selector=self.SELECTOR)
        for value in (0x03000100, 0x04000053, 0x04000400):
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.verify(**self.fixture(value=value), selector=self.SELECTOR)

    def test_native_cli_report_guards_source_runtime_producer_and_premise(self):
        evidence = mmio.fixtures.fixtures.evidence
        with self.mmio.build_boundary(self.fixture()) as (root, _, _):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', self.SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertIn('* incoming stack ABI: ', report)
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'readonly-four-words-numeric', 'numeric'), root, A))
            pins = profile.data_producer_fingerprint(self.SELECTOR)
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'readonly_entry_stack_words_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))

    def test_new_build_rejects_explicit_runtime_source_before_linking(self):
        with self.mmio.build_boundary(self.fixture()) as (root, _, commands):
            read = match.Runner.read_binary

            def explicit_source(runner, path):
                return b'int __divsi3(int, int);' if path.endswith('f.i') else read(runner, path)

            with patch.object(match.Runner, 'read_binary', explicit_source), \
                    self.assertRaisesRegex(ValueError, 'preprocessed C'):
                profile.build(root, A, selector=self.SELECTOR)
            self.assertEqual(commands, [])


if __name__ == '__main__':
    unittest.main()
