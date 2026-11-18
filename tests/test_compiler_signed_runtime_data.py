"""Compiler aliases retain exact ELF identities and conditional runtime limits."""
import copy
from contextlib import redirect_stdout
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_addressed_signed_runtime_two_words_data as fixtures

profile, match, A = fixtures.profile, fixtures.match, fixtures.A
SELECTOR = profile.COMPILER_DATA_SELECTOR


class CompilerSignedRuntimeDataTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.TwoWordsDataTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self):
        return self.base.fixture(reads=())

    def rename(self, image, reverse=False):
        names = profile.COMPILER_ALIASES if reverse else {
            canonical: alias for alias, canonical in profile.COMPILER_ALIASES.items()}
        for symbol in image['symbols']:
            symbol['name'] = names.get(symbol['name'], symbol['name'])
        return image

    def image(self, f):
        return self.rename(self.base.fixtures.data_image(f))

    def linked(self, f, original):
        canonical = self.rename(copy.deepcopy(original), reverse=True)
        return self.rename(self.base.fixtures.linked_data_image(f, canonical))

    def bindings(self, f, image=None, selector=SELECTOR):
        records = {}
        calls, bindings, targets = profile.original_bindings(
            image or self.image(f), A, f['rom'], f['mapping'], selector=selector,
            data_mapping=f['data_mapping'], data_relocations=records)
        return calls, bindings, targets, records

    def test_original_aliases_link_without_renaming_and_old_profiles_stay_strict(self):
        for operation in ('div', 'mod', 'both'):
            f = self.base.fixtures.data_fixture(
                operations=('div', 'mod') if operation == 'both' else (operation,))
            original = self.image(f)
            before = copy.deepcopy(original)
            calls, bindings, targets, records = self.bindings(f, original)
            self.assertEqual(original, before)
            self.assertEqual((calls, bindings), (f['calls'], f['bindings']))
            self.assertTrue(set(targets) & set(profile.COMPILER_ALIASES))
            self.assertFalse(set(targets) & set(profile.OPERATIONS))
            self.assertEqual(profile.linked_bytes(original, self.linked(f, original),
                A, calls, targets, data_relocations=records), f['data'])
            for selector in (profile.DATA_SELECTOR, profile.READONLY_TWO_DATA_SELECTOR):
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    self.bindings(f, original, selector)
            # Canonical addressed calls keep their existing separate route.
            self.bindings(f, self.base.fixtures.data_image(f), profile.DATA_SELECTOR)
            with self.assertRaisesRegex(ValueError, 'compiler-emitted'):
                self.bindings(f, self.base.fixtures.data_image(f))

    def test_original_alias_symbols_relocations_and_addends_remain_guarded(self):
        f = self.fixture()
        for field, value in [('name', '__divsi30'), ('name', '__udivsi3'),
                             ('type', 1), ('value', 2), ('section', 1),
                             ('bind', 0), ('size', 4)]:
            bad = self.image(f)
            bad['symbols'][1][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                self.bindings(f, bad)
        bad = self.image(f)
        bad['symbols'].append(copy.deepcopy(bad['symbols'][1]))
        with self.assertRaises(ValueError):
            self.bindings(f, bad)
        bad = self.image(f)
        body = bytearray(bad['text'])
        site = next(iter(f['bindings'])) - A
        body[site + 2] ^= 1
        bad['text'] = bytes(body)
        with self.assertRaisesRegex(ValueError, 'zero addend'):
            self.bindings(f, bad)
        with self.assertRaises(ValueError):
            profile.original_bindings(self.image(f), A, f['rom'], f['mapping'],
                                      selector=SELECTOR)

    def test_linked_alias_names_addresses_types_and_full_bytes_are_exact(self):
        f = self.fixture()
        original = self.image(f)
        calls, _, targets, records = self.bindings(f, original)
        for reason in ('renamed', 'ARM', 'address', 'object', 'undefined', 'byte'):
            bad = self.linked(f, original)
            if reason == 'renamed':
                bad['symbols'][1]['name'] = 'func_081426B8'
            elif reason == 'ARM':
                bad['symbols'][1]['value'] &= ~1
            elif reason == 'address':
                bad['symbols'][1]['value'] += 2
            elif reason == 'object':
                bad['symbols'][1]['type'] = 1
            elif reason == 'undefined':
                bad['symbols'][1]['section'] = 0
            else:
                body = bytearray(bad['text'])
                body[0] ^= 1
                bad['text'] = bytes(body)
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                profile.linked_bytes(original, bad, A, calls, targets,
                                     data_relocations=records)

    def test_source_namespace_rejects_explicit_runtime_identifiers_before_linking(self):
        profile.compiler_namespace('int f(int a, int b) { return a / b + a % b; }')
        for name in (*profile.COMPILER_ALIASES, *profile.COMPILER_ALIASES.values()):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'preprocessed C'):
                profile.compiler_namespace(f'int {name}(int, int);')
        with self.build_boundary() as (root, _, commands):
            read = match.Runner.read_binary

            def explicit_source(runner, path):
                return b'int __divsi3(int, int);' if path.endswith('f.i') else read(runner, path)

            with patch.object(match.Runner, 'read_binary', explicit_source), \
                    self.assertRaisesRegex(ValueError, 'preprocessed C'):
                profile.build(root, A, selector=SELECTOR)
            self.assertEqual(commands, [])

    def test_canonical_runtime_identities_and_manifest_limits_are_unchanged(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f, selector=SELECTOR)
        self.assertEqual(manifest['schema'], profile.COMPILER_DATA_SCHEMA)
        self.assertEqual(manifest['compiler_runtime']['calls'],
            [[site-A, '__divsi3', 'func_081426B8'] for site in f['bindings']])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertIn('no numeric result', manifest['compiler_runtime']['contract'])
        bad = bytearray(f['rom'])
        bad[profile.quotient.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(bad)), selector=SELECTOR)
        forged = copy.deepcopy(manifest)
        forged['compiler_runtime']['calls'][0][1] = '__udivsi3'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, selector=SELECTOR, manifest=forged)

    def test_compiler_two_words_combines_frame_alias_and_data_proofs(self):
        selector = profile.COMPILER_TWO_DATA_SELECTOR
        f = self.base.fixture()
        manifest, _ = profile.verify(**f, selector=selector)
        self.assertEqual(manifest['schema'], profile.COMPILER_TWO_DATA_SCHEMA)
        self.assertEqual(manifest['frame']['entry_stack']['words'], [0, 1])
        self.assertEqual(manifest['data_bindings'], f['data_bindings'])
        self.assertEqual({call[1] for call in manifest['compiler_runtime']['calls']}, {'__divsi3'})
        self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
        with self.assertRaises(ValueError):
            profile.verify(**f, selector=SELECTOR)
        with self.assertRaises(ValueError):
            self.bindings(f, self.base.fixtures.data_image(f), selector)
        for reads, extra in (((), ()), ((0x9802,), ()), ((0x9802, 0x9903, 0x9A04), ()),
                             ((0x9802, 0x9903), (0x9002,)), ((0x9802, 0x9903), (0xA802,))):
            with self.subTest(reads=reads, extra=extra), self.assertRaises(ValueError):
                profile.verify(**self.base.fixture(reads, extra), selector=selector)
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_bindings=[]), selector=selector)
        with self.build_boundary(f) as (root, _, _):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', selector, f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root / 'docs/match/08010000.md').read_text()
            self.assertIn('incoming stack ABI', report)
            self.assertTrue(fixtures.evidence.report_matches(report, root, A))
            self.assertFalse(fixtures.evidence.report_matches(
                report.replace('incoming stack ABI', 'unchecked stack'), root, A))

    def build_boundary(self, f=None):
        f = self.fixture() if f is None else f
        original_builder = self.base.fixtures.data_image
        linked_builder = self.base.fixtures.linked_data_image

        def original(value):
            return self.rename(original_builder(value))

        def linked(value, image):
            canonical = self.rename(copy.deepcopy(image), reverse=True)
            return self.rename(linked_builder(value, canonical))

        from contextlib import contextmanager

        @contextmanager
        def boundary():
            with patch.object(self.base.fixtures, 'data_image', side_effect=original), \
                    patch.object(self.base.fixtures, 'linked_data_image', side_effect=linked):
                with self.base.build_boundary(f) as result:
                    yield result

        return boundary()

    def test_native_cli_report_binds_source_runtime_producer_and_alias_policy(self):
        with self.build_boundary() as (root, _, _):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertTrue(fixtures.evidence.report_matches(report, root, A))
            self.assertFalse(fixtures.evidence.report_matches(
                report.replace('original and linked ELF names preserved', 'forged policy'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(fixtures.evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(SELECTOR)
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'addressed_signed_runtime_profile.py': '0'*64})):
                self.assertFalse(fixtures.evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(fixtures.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
