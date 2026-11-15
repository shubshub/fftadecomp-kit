"""Typed function points compose with the existing ordinary BIOS ABI only."""
from contextlib import redirect_stdout
import copy
import io
import json
import sys
import unittest
from unittest.mock import patch

import test_bios_function_literals as functions

profile, match, A, B = functions.profile, functions.match, functions.A, functions.B


class OrdinaryBiosFunctionLiteralTests(unittest.TestCase):
    def setUp(self):
        self.base = functions.BiosFunctionLiteralTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, source=0x1C18):
        original = self.base.base.fixture
        with patch.object(self.base.base, 'fixture',
                side_effect=lambda **kw: original(**dict(kw, prefix=(), source=source))):
            f = self.base.fixture()
        f['selector'] = profile.BIOS_ORDINARY_FUNCTION_DATA_SELECTOR
        return f

    def test_genuine_typed_function_and_object_points_keep_ordinary_abi(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['function_literal_bindings'], [f['data_bindings'][-1][:2]])
        self.assertIn('bios_ordinary', manifest)
        self.assertNotIn('native_buffers', manifest)
        self.assertIn('no BIOS memory effects', manifest['bios_ordinary']['contract'])
        self.assertIn('function literals are not objects', manifest['data_contract'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertFalse(manifest['original_formal_type_certainty'])

    def test_old_profiles_and_local_stack_transport_remain_refused(self):
        f = self.fixture()
        for selector in (profile.BIOS_ORDINARY_DATA_SELECTOR, profile.BIOS_FUNCTION_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(source=0x4668))
        # The established bounded-fill selector still accepts actual local fill.
        old = self.base.fixture()
        self.assertIn('native_buffers', profile.verify(**old)[0])

    def test_actual_function_literal_thumb_entry_and_wrapper_are_required(self):
        f = self.fixture()
        records = f['data_bindings'][:-1]
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_bindings=records))
        objects = json.loads(f['data_mapping'])
        objects[f'func_{B:08X}'] = f'0x{B:08X}'
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_mapping=json.dumps(objects).encode()))
        rows = json.loads(f['mapping'])
        for changed in ([r for r in rows if int(r['rom'],16) != B],
                        [dict(r, mode='arm') if int(r['rom'],16) == B else r for r in rows]):
            mapping, index = functions.fill.fixtures.fixtures.indexes(changed)
            with self.subTest(rows=changed), self.assertRaises(ValueError):
                profile.verify(**dict(f, mapping=mapping, index=index))
        rom = bytearray(f['rom'])
        rom[functions.fill.bios.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, rom=bytes(rom)))

    def test_original_elf_and_linked_function_types_are_not_object_aliases(self):
        f = self.fixture()
        helper = self.base.base.base
        original = helper.data_image(f)
        linked = helper.linked_data_image(f, original)
        records = {}
        calls, _, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            selector=f['selector'], data_mapping=f['data_mapping'], data_relocations=records)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records, function_literals={f'func_{B:08X}'}), f['data'])
        bad = copy.deepcopy(linked)
        bad['symbols'][-1].update(type=1, value=B)
        with self.assertRaises(ValueError):
            profile.linked_bytes(original, bad, A, calls, targets,
                data_relocations=records, function_literals={f'func_{B:08X}'})

    def test_cli_report_keeps_actual_source_runtime_producer_and_policy_guards(self):
        f = self.fixture()
        with self.base.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = functions.fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'no BIOS memory effects', 'forged effects'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'addressed_signed_runtime_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
