"""Scoped genuine compiler binding, complete ELF ownership and selector routing."""
from contextlib import contextmanager
import copy
import hashlib
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
import private_double_scalar_conversion_effects_inventory as inventory
import software_float_profile as runtime
import test_private_double_scalar_conversion_effects_inventory as effects
import test_private_float_pack_admission_profile as old
import test_status_private_float_routing as status_fixtures

SELECTOR = admission.DOUBLE_SCALAR_CONVERSION_SELECTOR


def elf_pair(body):
    symbols = [dict(name=f'func_{effects.A:08X}', type=2, bind=1, section=1, value=1, size=len(body)),
               dict(name=f'func_{effects.U:08X}', type=2, bind=1, section=0, value=0, size=0),
               dict(name='__lshrdi3', type=0, bind=1, section=0, value=0, size=0)]
    original = bytearray(body)
    for site in (12, 22):
        original[site:site+4] = effects.call(effects.A+site, effects.A+site)
    rels = b''.join(struct.pack('<II', site, number << 8 | 10)
                    for site, number in ((12, 1), (22, 2)))
    image = dict(type=1, text_index=1, text=bytes(original), symbols=symbols,
        sections=[(0,)*10, (0,1,6,0,0,len(body),0,0,4,0), (0,9,0,0,0,len(rels),3,1,4,8)],
        symbol_tables={3:symbols}, relocations=[2], section_data=[b'',bytes(original),rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0,1,6,effects.A,0,len(body),0,0,4,0)
    for symbol, target in zip(linked['symbols'], (effects.A, effects.U, effects.W)):
        symbol['value'] = target | 1
    linked['symbols'][1]['section'] = linked['symbols'][2]['section'] = 0xFFF1
    return image, linked


class DoubleScalarConversionAdmissionTests(unittest.TestCase):
    @contextmanager
    def closure(self):
        fixture = effects.fixture()
        with patch.object(inventory, 'HELPERS', fixture[-1]), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(fixture[1]).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            yield fixture

    def test_original_undefined_compiler_name_is_pinned_without_rewriting(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            before = copy.deepcopy(original)
            calls, targets = admission.original_bindings(original, effects.A, rom, mapping, index, selector=SELECTOR)
            self.assertEqual(calls, [[12, 'func_08000200'], [22, '__lshrdi3']])
            self.assertEqual(targets['__lshrdi3'], effects.W)
            self.assertEqual(admission.linked_bytes(original, linked, effects.A, calls, targets, selector=SELECTOR), body)
            self.assertEqual(original, before)
            manifest, _ = admission.verify(body, effects.A, rom, mapping, index, calls, selector=SELECTOR)
            self.assertEqual(manifest['schema'], admission.DOUBLE_SCALAR_CONVERSION_SCHEMA)
            self.assertEqual(manifest['bindings'], calls)

    def test_scoped_compiler_name_does_not_expand_legacy_profiles(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, _ = elf_pair(body)
            for selector in admission.SELECTORS:
                if selector == SELECTOR:
                    continue
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    admission.original_bindings(original, effects.A, rom, mapping, index, selector=selector)
                self.assertNotIn('__lshrdi3', getattr(admission.profile(selector)[0], 'COMPILER_ALIASES', {}))

    def test_other_names_definitions_duplicates_and_nonzero_addends_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, _ = elf_pair(body)
            mutations = []
            for name in ('__ashrdi3', '__fixdfsi', 'func_08000302'):
                changed = copy.deepcopy(original)
                changed['symbols'][2]['name'] = name
                mutations.append(changed)
            changed = copy.deepcopy(original)
            changed['symbols'][2]['section'] = 0xFFF1
            mutations.append(changed)
            changed = copy.deepcopy(original)
            changed['symbols'].append(dict(changed['symbols'][2]))
            mutations.append(changed)
            changed = copy.deepcopy(original)
            changed['text'] = changed['text'][:22]+effects.call(effects.A+22, effects.A+24)+changed['text'][26:]
            mutations.append(changed)
            for changed in mutations:
                with self.subTest(symbols=changed['symbols']), self.assertRaises(ValueError):
                    admission.original_bindings(changed, effects.A, rom, mapping, index, selector=SELECTOR)

    def test_linked_target_and_nonrelocation_bytes_remain_exact(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            calls, targets = admission.original_bindings(original, effects.A, rom, mapping, index, selector=SELECTOR)
            for site in (0, 22):
                changed = copy.deepcopy(linked)
                raw = bytearray(changed['text'])
                raw[site] ^= 1
                changed['text'] = bytes(raw)
                with self.subTest(site=site), self.assertRaises(ValueError):
                    admission.linked_bytes(original, changed, effects.A, calls, targets, selector=SELECTOR)

    def test_reports_and_cli_preserve_only_explicit_selector(self):
        marker = (f'* verification: `{admission.DOUBLE_SCALAR_CONVERSION_SCHEMA}`\n'
                  f'* private float pack: `{SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), SELECTOR)
        for changed in (marker+marker, marker.replace(admission.DOUBLE_SCALAR_CONVERSION_SCHEMA, admission.SCHEMA)):
            with self.assertRaises(ValueError):
                admission.selected(changed)
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', '08000100', '--owner-runtime-profile', SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, SELECTOR)

    def test_build_and_report_replay_keep_original_compiler_symbol(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as fixture, case.project(fixture) as (root, selected), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, effects.A, old.arguments(owner_runtime_profile=SELECTOR))
            self.assertEqual(result['body'], fixture[0])
            self.assertEqual(result['manifest']['bindings'][1][1], '__lshrdi3')
            report = admission.render(result)
            self.assertEqual(admission.selector_for_report(report), SELECTOR)
            self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, effects.A), root, effects.A))

    def test_status_reuses_the_distinct_selector(self):
        case = status_fixtures.StatusPrivateFloatRoutingTests()
        case.setUp()
        self.addCleanup(case.doCleanups)
        report = status_fixtures.REPORT.replace(admission.SCHEMA, admission.DOUBLE_SCALAR_CONVERSION_SCHEMA)
        case.report_path.write_text(report.replace(admission.SELECTOR, SELECTOR))
        with patch.object(status_fixtures.status.subprocess, 'run', return_value=
                subprocess.CompletedProcess([], 0, status_fixtures.OUTPUT, '')) as native, \
                patch.object(admission, 'report_matches', return_value=True):
            self.assertEqual(case.collect(), (1, 1, 8, 8, [], 0, 0))
            command = native.call_args.args[0]
            self.assertEqual(command[command.index('--owner-runtime-profile')+1], SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
