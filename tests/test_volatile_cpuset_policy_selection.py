"""The stronger CpuSet source-observation premise is a distinct opt-in."""
import os
import sys
import tempfile
from pathlib import Path
from contextlib import contextmanager
import json
import unittest
from unittest.mock import patch
import test_volatile_bios_interface
import match
import match_evidence
import test_volatile_cpuset_local_source as local
import test_volatile_semantics as fixtures
import test_named_bios_fill_source as native
import bios_cpuset_fill_profile as bios
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import volatile_semantics as semantics

SELECTOR = 'bounded-buffer-bios-fill-local-source-semantics-v1'
SCHEMA = 'elf-symbol-thumb-bounded-buffer-bios-fill-local-source-semantics-v1'


class PolicySelectionTests(unittest.TestCase):
    def setUp(self):
        self.base = native.NamedBiosFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)
        self.bodies = local.LocalSourceTests('runTest')

    def provider(self, selector=None):
        f = self.base.fixture()
        keywords = {} if selector is None else {'selector': selector}
        return bios.ConditionalVolatileInterfaces(None, f['data'], f['address'],
            f['rom'], f['mapping'], f['index'], f['objects'], **keywords)

    def compare(self, provider):
        pre = fixtures.PREPROCESSED + f'\nvoid {bios.NAME}(void *, void *, unsigned int);\n'
        return semantics._compare_compiles(self.bodies.body(),
            self.bodies.body(saved='lr'), pre, fixtures.SYMBOL,
            fixtures.DECLARATION, interfaces=provider)

    def test_legacy_interface_does_not_authorize_source_observation_premise(self):
        provider = self.provider()
        with self.assertRaises(semantics.SemanticError):
            self.compare(provider)
        self.assertFalse(getattr(provider, 'local_fill_premise', None))
        self.assertNotIn('numeric source-pointer', provider.conditional_premises[bios.NAME])

    def test_new_explicit_selector_authorizes_and_records_only_its_premise(self):
        provider = self.provider(SELECTOR)
        result = self.compare(provider)
        self.assertIn('no numeric source-pointer observation or retention',
                      semantics.record(fixtures.SYMBOL, result))
        with self.assertRaises(ValueError):
            self.provider('unknown-policy')

    def test_independent_native_fill_verifier_has_distinct_replayable_schema(self):
        f = self.base.fixture()
        legacy, _ = owner.verify(**f)
        modern, _ = owner.verify(**dict(f, selector=SELECTOR))
        self.assertEqual(legacy['profile'], buffers.BIOS_FILL_SCHEMA)
        self.assertEqual(modern['profile'], SCHEMA)
        self.assertEqual(modern['proof']['schema'], SCHEMA)
        equivalent = json.loads(json.dumps(modern))
        equivalent['profile'] = equivalent['proof']['schema'] = buffers.BIOS_FILL_SCHEMA
        del equivalent['proof']['conditional_volatile_local_source_policy']
        self.assertEqual(equivalent, legacy)
        self.assertNotIn('conditional_volatile_local_source_policy', legacy['proof'])
        self.assertIn('no numeric source-pointer',
                      modern['proof']['conditional_volatile_local_source_policy'])
        for selector, schema in ((buffers.BIOS_FILL_SELECTOR, buffers.BIOS_FILL_SCHEMA),
                                 (SELECTOR, SCHEMA)):
            report = f'* verification: `{schema}`\n'
            self.assertEqual(owner.selector_for_report(report), selector)
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, selector=SELECTOR), manifest=legacy)
        with self.assertRaises(ValueError):
            owner.verify(**f, manifest=modern)

    def test_native_report_render_and_replay_keep_exact_selected_policy(self):
        f = self.base.fixture()
        for selector in (buffers.BIOS_FILL_SELECTOR, SELECTOR):
            manifest, instructions = owner.verify(**dict(f, selector=selector))
            result = (f['data'], manifest, '1' * 64, f['mapping'], f['index'],
                      f['objects'], f['rom'], len(instructions), b'synthetic ELF boundary')
            report = owner.render(f['address'], result)
            self.assertTrue(owner.selected(report))
            self.assertEqual(owner.selector_for_report(report), selector)
            if selector == SELECTOR:
                self.assertIn('* owner runtime: ' + SELECTOR, report)
                self.assertIn('no numeric source-pointer', report)
            else:
                self.assertNotIn('no numeric source-pointer', report)
            with patch.object(owner, 'build', return_value=result) as build:
                self.assertTrue(owner.report_matches(report, '.', f['address']))
                self.assertEqual(build.call_args.kwargs['selector'], selector)
                forged = report.replace(manifest['profile'], manifest['profile'] + '-forged')
                self.assertFalse(owner.report_matches(forged, '.', f['address']))

    def test_cli_dispatch_and_volatile_report_replay_select_new_policy_explicitly(self):
        import test_volatile_records_all_profiles as records
        for selector, schema in ((buffers.BIOS_FILL_SELECTOR, buffers.BIOS_FILL_SCHEMA),
                                 (SELECTOR, SCHEMA)):
            with patch.object(sys, 'argv', ['match.py', '--root', '.',
                    '--owner-runtime-profile', selector, '08010000']), \
                    patch.object(match, 'allowlisted_volatile_check', return_value=([], None, None)), \
                    patch.object(match, 'issue_with_volatile_records', return_value=0) as dispatch:
                self.assertEqual(match.main(), 0)
                self.assertIs(dispatch.call_args.args[0], owner.issue)
                self.assertEqual(dispatch.call_args.args[3].owner_runtime_profile, selector)
            report = records.owner_report(b'\x70\x47').replace(records.owner.ACYCLIC_SCHEMA, schema)
            uses, semantic = '* allowlisted volatile: fixture', '* allowlisted volatile semantics: fixture'
            report = match_evidence.carry_volatile_records(report, [uses, semantic])
            with patch.object(match.plausibility, 'allowlisted_volatile_uses', return_value=[uses]), \
                    patch.object(match, 'allowlisted_volatile_semantics', return_value=[semantic]) as replay, \
                    patch.object(owner, 'report_matches', return_value=False):
                self.assertFalse(match_evidence.report_matches(report, '.', native.A))
                self.assertEqual(replay.call_args.kwargs, {'owner_runtime_profile': selector})

    def test_match_constructs_only_the_explicitly_selected_semantic_provider(self):
        f = self.base.fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('src', 'symbols', 'config'):
                (root / name).mkdir()
            (root / 'src' / f'{f["address"]:08X}.c').write_text('')
            for relative, data in (('symbols/functions.txt', f['index']),
                                   ('config/functions.json', f['mapping']),
                                   ('config/data_symbols.json', f['objects']),
                                   ('baserom.bin', f['rom'])):
                (root / relative).write_bytes(data)
            class Runner:
                @contextmanager
                def workspace(self):
                    yield directory
                def read_binary(self, path):
                    return b''
            entry = dict(symbol=fixtures.SYMBOL, declaration=fixtures.DECLARATION)
            with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')), \
                    patch.object(match.plausibility, 'allowlisted_volatile_used', return_value=[entry]), \
                    patch.object(match, 'compile_object'), \
                    patch.object(semantics, 'compare', return_value=[]) as compare:
                for selector in (buffers.BIOS_FILL_SELECTOR, SELECTOR):
                    match.allowlisted_volatile_semantics(root, f['address'], runner=Runner(),
                        owner_runtime_profile=selector)
                    provider = compare.call_args.args[-1]
                    self.assertEqual(bool(provider.local_fill_premise), selector == SELECTOR)
                    if selector == SELECTOR:
                        self.compare(provider)
                    else:
                        with self.assertRaises(semantics.SemanticError):
                            self.compare(provider)

    def test_new_native_selector_keeps_legacy_bounds_and_binding_refusals(self):
        for changes in (dict(control=0), dict(control=0x04000010),
                        dict(source=0xA801), dict(source=0x2000), dict(destination=0x4669)):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                owner.verify(**dict(self.base.fixture(**changes), selector=SELECTOR))
        f = self.base.fixture()
        f['bindings']['data'] = []
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, selector=SELECTOR))

    def test_new_preflight_and_semantic_provider_refuse_changed_authentication(self):
        for kind in ('wrapper', 'index', 'mapping'):
            f = self.base.fixture()
            if kind == 'wrapper':
                image = bytearray(f['rom'])
                image[bios.ADDRESS-native.match.ROM_BASE] ^= 1
                f['rom'] = bytes(image)
            elif kind == 'index':
                f['index'] = f['index'].replace(b'08141870', b'08141872')
            else:
                f['mapping'] = json.dumps([row for row in json.loads(f['mapping'])
                    if int(row['rom'], 16) != bios.ADDRESS]).encode()
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=SELECTOR))
            with self.subTest(interface=kind), self.assertRaises(ValueError):
                bios.ConditionalVolatileInterfaces(None, f['data'], f['address'],
                    f['rom'], f['mapping'], f['index'], f['objects'], selector=SELECTOR)


if __name__ == '__main__':
    unittest.main()
