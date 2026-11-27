"""Genuine scalar-conversion ELF bindings, report routing and complete-symbol tails."""
from contextlib import contextmanager
import copy
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import private_float_pack_admission_profile as admission
import private_float_scalar_conversion_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_scalar_conversion_effects_inventory as effects
import test_private_float_pack_admission_profile as old
import test_status_private_float_routing as status_fixtures

SELECTOR = admission.SCALAR_CONVERSION_SELECTOR


def elf_pair(body):
    site, target = (14, effects.P) if len(body) == 24 else (10, effects.U)
    symbols = [dict(name=f'func_{effects.A:08X}', type=2, bind=1, section=1,
                    value=1, size=len(body)),
               dict(name=f'func_{target:08X}', type=2, bind=1, section=0, value=0, size=0)]
    original = body[:site]+effects.call(effects.A+site, effects.A+site)+body[site+4:]
    rels = struct.pack('<II', site, 1 << 8 | 10)
    tail = effects.words(0x46C0) if len(body) % 4 == 2 else b''
    text = original+tail
    image = dict(type=1, text_index=1, text=text, symbols=symbols,
        sections=[(0,)*10, (0,1,6,0,0,len(text),0,0,4,0), (0,9,0,0,0,8,3,1,4,8)],
        symbol_tables={3:symbols}, relocations=[2], section_data=[b'',text,rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body+tail, relocations=[])
    linked['sections'][1] = (0,1,6,effects.A,0,len(text),0,0,4,0)
    linked['symbols'][0]['value'] = effects.A | 1
    linked['symbols'][1].update(value=target | 1, section=0xFFF1)
    return image, linked


class ScalarConversionAdmissionTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None):
        fixture = selected or effects.fixture()
        with patch.object(inventory, 'HELPERS', fixture[-1]), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(fixture[1]).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            yield fixture

    def test_both_genuine_single_helper_relocations_and_effects(self):
        for direction in ('unpack', 'pack'):
            with self.subTest(direction=direction), self.closure(effects.fixture(direction=direction)) as selected:
                body, rom, _, mapping, index, _ = selected
                original, linked = elf_pair(body)
                before = copy.deepcopy(original)
                calls, targets = admission.original_bindings(original, effects.A, rom, mapping, index,
                    selector=SELECTOR)
                self.assertEqual(len(calls), 1)
                self.assertEqual(admission.linked_bytes(original, linked, effects.A, calls, targets,
                    selector=SELECTOR), body)
                self.assertEqual(original, before)
                manifest, _ = admission.verify(body, effects.A, rom, mapping, index, calls, selector=SELECTOR)
                self.assertEqual(manifest['schema'], admission.SCALAR_CONVERSION_SCHEMA)

    def test_literal_symbol_tail_is_excluded_only_under_new_complete_partition(self):
        with self.closure(effects.fixture(literal=True)) as selected:
            body, rom, _, mapping, index, _ = selected
            original, linked = elf_pair(body)
            calls, targets = admission.original_bindings(original, effects.A, rom, mapping, index,
                selector=SELECTOR)
            raw = admission.linked_bytes(original, linked, effects.A, calls, targets, selector=SELECTOR)
            self.assertEqual(raw, body)
            self.assertEqual(len(linked['text'])-len(raw), 2)
            manifest, _ = admission.verify(raw, effects.A, rom, mapping, index, calls, selector=SELECTOR)
            self.assertEqual(manifest['inventory']['partition']['literal_and_table_bytes'], 4)
            with self.assertRaises(ValueError):
                admission.function_size(original, effects.A)
            altered = copy.deepcopy(original)
            altered['text'] = altered['text'][:-2]+effects.words(0x4770)
            with self.assertRaises(ValueError):
                admission.original_bindings(altered, effects.A, rom, mapping, index, selector=SELECTOR)

    def test_old_profile_and_undefined_aliases_do_not_admit_single_helper(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, _ = elf_pair(body)
            with self.assertRaises(ValueError):
                admission.original_bindings(original, effects.A, rom, mapping, index)
            for name in ('__fixsfsi', 'func_08000202', 'extra'):
                changed = copy.deepcopy(original)
                changed['symbols'][1]['name'] = name
                with self.subTest(name=name), self.assertRaises(ValueError):
                    admission.original_bindings(changed, effects.A, rom, mapping, index, selector=SELECTOR)

    def test_report_selectors_are_distinct_and_mixed_markers_refuse(self):
        marker = (f'* verification: `{admission.SCALAR_CONVERSION_SCHEMA}`\n'
                  f'* private float pack: `{SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), SELECTOR)
        for changed in (marker+marker, marker.replace(admission.SCALAR_CONVERSION_SCHEMA, admission.SCHEMA),
                        marker.replace(f'* private float pack: `{SELECTOR}`',
                                       f'* private float pack: `{admission.SELECTOR}`')):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                admission.selected(changed)

    def test_cli_routes_only_explicit_new_selector(self):
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', '08000100', '--owner-runtime-profile', SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, SELECTOR)

    def test_full_build_and_fresh_report_replay_include_owned_literal_tail(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure(effects.fixture(literal=True)) as fixture, case.project(fixture) as (root, selected), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, effects.A, old.arguments(owner_runtime_profile=SELECTOR))
            self.assertEqual(result['body'], fixture[0])
            report = admission.render(result)
            self.assertEqual(admission.selector_for_report(report), SELECTOR)
            self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, effects.A), root, effects.A))

    def test_status_preserves_scalar_selector(self):
        case = status_fixtures.StatusPrivateFloatRoutingTests()
        case.setUp()
        self.addCleanup(case.doCleanups)
        report = status_fixtures.REPORT.replace(admission.SCHEMA, admission.SCALAR_CONVERSION_SCHEMA)
        case.report_path.write_text(report.replace(admission.SELECTOR, SELECTOR))
        with patch.object(status_fixtures.status.subprocess, 'run', return_value=
                subprocess.CompletedProcess([], 0, status_fixtures.OUTPUT, '')) as native, \
                patch.object(admission, 'report_matches', return_value=True):
            self.assertEqual(case.collect(), (1, 1, 8, 8, [], 0, 0))
            command = native.call_args.args[0]
            self.assertEqual(command[command.index('--owner-runtime-profile')+1], SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
