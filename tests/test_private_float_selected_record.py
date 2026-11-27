"""Returned record alternatives, conditional RAM reads and genuine ELF bindings."""
from contextlib import contextmanager
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import private_float_pack_admission_profile as admission
import private_float_selected_record_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures
import test_private_float_pack_admission_profile as old

A, U, S, P = 0x08000100, 0x08000200, 0x08000300, 0x08000400
words, call = fixtures.words, fixtures.call
SITES = (12, 20, 30, 34)


def fixture(*, output=8, selection=None, selected_target=S):
    caller = words(0xB500, 0xB08E, 0x900C, 0x910D, 0xA80C, 0x4669)
    caller += call(A+12, U) + words(0xA80D, 0xA904) + call(A+20, U)
    caller += words(0x4668, 0xA904, 0xAA00 | output)
    caller += call(A+30, selected_target) + call(A+34, P) + words(0xB00E, 0xBC02, 0x4708)
    unpack = words(0x6802, 0x600A, 0x604A, 0x608A, 0x60CA, 0x4770)
    selection = selection or words(0x2B00, 0xD004, 0x2B01, 0xD004, 0x2B02, 0xD004,
        0xE005, 0x1C00, 0xE004, 0x1C08, 0xE002, 0x1C10, 0xE000, 0x4801,
        0x4770, 0x0000, 0x5E68, 0x0300)
    pack = words(0x6802, 0x6842, 0x6882, 0x68C0, 0x4770)
    parts = {A: caller, U: unpack, S: selection, P: pack}
    counts = {A: 18, U: 6, S: 15, P: 5}
    rom, rows, mapping, index = fixtures.image(parts, counts)
    helpers = tuple((name, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (name, _, bounds), start in zip(inventory.HELPERS, (U, S, P)))
    return caller, rom, rows, mapping, index, helpers


def elf_pair(body):
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body))]
    symbols += [dict(name=f'func_{target:08X}', type=2, bind=1, section=0, value=0, size=0)
                for target in (U, S, P)]
    original = bytearray(body)
    for site in SITES:
        original[site:site+4] = call(A+site, A+site)
    rels = b''.join(struct.pack('<II', site, number << 8 | 10)
                    for site, number in zip(SITES, (1, 1, 2, 3)))
    image = dict(type=1, text_index=1, text=bytes(original), symbols=symbols,
        sections=[(0,)*10, (0, 1, 6, 0, 0, len(body), 0, 0, 2, 0),
                  (0, 9, 0, 0, 0, len(rels), 3, 1, 4, 8)],
        symbol_tables={3: symbols}, relocations=[2], section_data=[b'', bytes(original), rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0, 1, 6, A, 0, len(body), 0, 0, 2, 0)
    linked['symbols'][0]['value'] = A | 1
    for symbol, target in zip(linked['symbols'][1:], (U, S, P)):
        symbol.update(value=target | 1, section=0xFFF1)
    return image, linked


class SelectedRecordTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None):
        selected = selected or fixture()
        with patch.object(inventory, 'HELPERS', selected[-1]), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(selected[1]).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            yield selected

    def verify(self, selected=None, **changes):
        with self.closure(selected) as (body, rom, _, mapping, index, _):
            return inventory.verify(body, A, rom, mapping, index,
                selector=changes.pop('selector', inventory.SELECTOR), **changes)

    def test_all_returned_records_and_actual_fixed_reads_are_retained(self):
        result, decoded = self.verify()
        self.assertEqual(len(decoded), 18)
        self.assertEqual(result['helper_closure'][1]['native_proof']['return_pointers']['values'],
                         inventory.RETURN_POINTERS)
        self.assertEqual(result['external_reads'], inventory.ABSOLUTE_POLICY['reads'])
        self.assertEqual(result['external_formal_reads'], [])
        self.assertEqual(result['external_writes'], [])
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertFalse(result['physical_memory_claim'])
        self.assertFalse(result['arithmetic_C_equivalence'])
        self.assertIn('conditional', inventory.CONTRACT)

    def test_saved_register_alternative_refuses(self):
        with self.assertRaisesRegex(ValueError, 'saved|frame'):
            self.verify(fixture(output=14))

    def test_fixed_word_permission_cannot_be_omitted(self):
        altered = copy.deepcopy(inventory.ABSOLUTE_POLICY)
        altered['reads'].pop()
        with patch.object(inventory, 'ABSOLUTE_POLICY', altered), \
                self.assertRaisesRegex(ValueError, 'conditional footprint'):
            self.verify()

    def test_returned_pointer_alternative_cannot_be_omitted(self):
        with patch.object(inventory, 'RETURN_POINTERS', inventory.RETURN_POINTERS[:-1]), \
                self.assertRaisesRegex(ValueError, 'exceeds its policy'):
            self.verify()

    def test_exact_call_sequence_and_helper_identity_required(self):
        with self.assertRaisesRegex(ValueError, 'selected-record helper'):
            self.verify(fixture(selected_target=P))
        selected = list(fixture())
        helpers = list(selected[-1]); name, (start, end, count, digest), bounds = helpers[1]
        helpers[1] = name, (start, end, count+1, digest), bounds
        selected[-1] = tuple(helpers)
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(tuple(selected))

    def test_explicit_selector_and_exact_manifest_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})

    def test_original_four_call_bindings_and_bytes_are_authenticated(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, linked = elf_pair(body); before = copy.deepcopy(image)
            calls, targets = admission.original_bindings(image, A, rom, mapping, index,
                selector=admission.SELECTED_RECORD_SELECTOR)
            self.assertEqual(calls, [[site, f'func_{target:08X}']
                             for site, target in zip(SITES, (U, U, S, P))])
            self.assertEqual(admission.linked_bytes(image, linked, A, calls, targets,
                selector=admission.SELECTED_RECORD_SELECTOR), body)
            self.assertEqual(image, before)
            manifest, _ = admission.verify(body, A, rom, mapping, index, calls,
                selector=admission.SELECTED_RECORD_SELECTOR)
            self.assertEqual(manifest['schema'], admission.SELECTED_RECORD_SCHEMA)
            self.assertEqual(manifest['contract'], inventory.CONTRACT)
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                admission.verify(body, A, rom, mapping, index, calls,
                    selector=admission.SELECTED_RECORD_SELECTOR, manifest={})

    def test_implicit_profile_wrong_helper_and_nonzero_original_addend_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, _ = elf_pair(body)
            with self.assertRaises(ValueError):
                admission.original_bindings(image, A, rom, mapping, index)
            for value in ('__addsf3', f'func_{S+2:08X}'):
                altered = copy.deepcopy(image); altered['symbols'][2]['name'] = value
                with self.subTest(name=value), self.assertRaises(ValueError):
                    admission.original_bindings(altered, A, rom, mapping, index,
                        selector=admission.SELECTED_RECORD_SELECTOR)
            altered = copy.deepcopy(image)
            altered['text'] = altered['text'][:30]+call(A+30, A+32)+altered['text'][34:]
            with self.assertRaisesRegex(ValueError, 'zero-addend'):
                admission.original_bindings(altered, A, rom, mapping, index,
                    selector=admission.SELECTED_RECORD_SELECTOR)

    def test_explicit_cli_and_report_selector_cannot_mix(self):
        marker = (f'* verification: `{admission.SELECTED_RECORD_SCHEMA}`\n'
                  f'* private float pack: `{admission.SELECTED_RECORD_SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), admission.SELECTED_RECORD_SELECTOR)
        for altered in (marker+marker, marker.replace(admission.SELECTED_RECORD_SCHEMA, admission.SCHEMA),
                        marker.replace(f'* private float pack: `{admission.SELECTED_RECORD_SELECTOR}`', f'* private float pack: `{admission.SELECTOR}`')):
            with self.subTest(marker=altered), self.assertRaises(ValueError):
                admission.selected(altered)
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', f'{A:08X}', '--owner-runtime-profile',
                    admission.SELECTED_RECORD_SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, admission.SELECTED_RECORD_SELECTOR)

    def test_build_and_report_replay_preserve_conditional_contract(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected, case.project(selected) as (root, _), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, A, old.arguments(
                owner_runtime_profile=admission.SELECTED_RECORD_SELECTOR))
            self.assertEqual(result['body'], selected[0])
            report = admission.render(result)
            self.assertEqual(admission.selector_for_report(report), admission.SELECTED_RECORD_SELECTOR)
            self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, A), root, A))


if __name__ == '__main__':
    unittest.main(verbosity=2)
