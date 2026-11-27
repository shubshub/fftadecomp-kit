"""Extension admission uses genuine relocations and a distinct report selector."""
from contextlib import contextmanager
import copy
import hashlib
import json
import sys
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import private_float_pack_admission_profile as admission
import private_float_extension_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_extension_effects_inventory as effects
import test_private_float_pack_admission_profile as old
import test_status_private_float_routing as status_fixtures


class ExtensionAdmissionTests(unittest.TestCase):
    @contextmanager
    def closure(self):
        fixture = effects.fixture()
        with patch.object(inventory, 'HELPERS', fixture[-1]), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(fixture[1]).hexdigest()), \
                patch.object(runtime, 'EDGES', ((effects.CONSTRUCT + 8, effects.PACK),)):
            yield fixture

    def test_original_genuine_bindings_and_nested_effects(self):
        with self.closure() as (body, rom, mapping, index, _):
            image, linked = old.elf_pair(body)
            before = copy.deepcopy(image)
            calls, targets = admission.original_bindings(image, effects.A, rom, mapping, index,
                selector=admission.EXTENSION_SELECTOR)
            self.assertEqual(calls, [[10, 'func_08000200'], [28, 'func_08000300']])
            self.assertEqual(admission.linked_bytes(image, linked, effects.A, calls, targets), body)
            self.assertEqual(image, before)
            manifest, _ = admission.verify(body, effects.A, rom, mapping, index, calls,
                selector=admission.EXTENSION_SELECTOR)
            self.assertEqual(manifest['schema'], admission.EXTENSION_SCHEMA)
            self.assertEqual(len(manifest['inventory']['helper_closure']), 4)
            self.assertEqual(manifest['inventory']['external_reads'], [])
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                admission.verify(body, effects.A, rom, mapping, index, calls,
                    selector=admission.EXTENSION_SELECTOR, manifest={})

    def test_implicit_old_selector_and_wrong_external_names_refuse(self):
        with self.closure() as (body, rom, mapping, index, _):
            image, _ = old.elf_pair(body)
            with self.assertRaises(ValueError):
                admission.original_bindings(image, effects.A, rom, mapping, index)
            for name in ('__extendsfdf2', 'func_08000240', 'func_08000302'):
                altered = copy.deepcopy(image)
                altered['symbols'][2]['name'] = name
                with self.subTest(name=name), self.assertRaises(ValueError):
                    admission.original_bindings(altered, effects.A, rom, mapping, index,
                        selector=admission.EXTENSION_SELECTOR)

    def test_report_selectors_cannot_mix_or_fall_back(self):
        marker = (f'* verification: `{admission.EXTENSION_SCHEMA}`\n'
                  f'* private float pack: `{admission.EXTENSION_SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), admission.EXTENSION_SELECTOR)
        self.assertTrue(admission.selected(marker))
        self.assertIsNone(admission.selector_for_report('unrelated report'))
        for changed in (marker + marker,
                        marker.replace(admission.EXTENSION_SCHEMA, admission.SCHEMA),
                        marker.replace(f'* private float pack: `{admission.EXTENSION_SELECTOR}`',
                                       f'* private float pack: `{admission.SELECTOR}`')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                admission.selected(changed)

    def test_cli_routes_new_explicit_selector(self):
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', '08000100', '--owner-runtime-profile',
                    admission.EXTENSION_SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, admission.EXTENSION_SELECTOR)

    def test_build_and_fresh_report_replay_keep_extension_profile(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as (body, rom, mapping, index, helpers):
            fixture = (body, rom, json.loads(mapping), mapping, index, helpers)
            with case.project(fixture) as (root, selected), case.fake_native(root, selected):
                result = admission.build(root, effects.A,
                    old.arguments(owner_runtime_profile=admission.EXTENSION_SELECTOR))
                self.assertEqual(result['body'], body)
                self.assertEqual(result['manifest']['selector'], admission.EXTENSION_SELECTOR)
                report = admission.render(result)
                self.assertEqual(admission.selector_for_report(report), admission.EXTENSION_SELECTOR)
                self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, effects.A), root, effects.A))

    def test_status_preserves_extension_selector_for_native_replay(self):
        case = status_fixtures.StatusPrivateFloatRoutingTests()
        case.setUp()
        self.addCleanup(case.doCleanups)
        report = status_fixtures.REPORT.replace(admission.SCHEMA, admission.EXTENSION_SCHEMA)
        report = report.replace(admission.SELECTOR, admission.EXTENSION_SELECTOR)
        case.report_path.write_text(report)
        with patch.object(status_fixtures.status.subprocess, 'run', return_value=
                subprocess.CompletedProcess([], 0, status_fixtures.OUTPUT, '')) as native, \
                patch.object(admission, 'report_matches', return_value=True):
            self.assertEqual(case.collect(), (1, 1, 8, 8, [], 0, 0))
            command = native.call_args.args[0]
            self.assertEqual(command[command.index('--owner-runtime-profile') + 1],
                             admission.EXTENSION_SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
