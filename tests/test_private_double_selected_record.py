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
import private_double_selected_record_inventory as inventory
import software_float_profile as runtime
import software_double_profile as double
import test_private_float_pack_effects_inventory as fixtures
import test_private_float_pack_admission_profile as old

A, U, S, P, N, W = (0x08000100, 0x08000200, 0x08000300, 0x08000400, 0x08000500, 0x08000600)
words, call = fixtures.words, fixtures.call
SITES = (16, 24, 34, 38)
EDGES = ((S+12, N), (S+20, N), (P+14, W))


def fixture(*, output=10, selection=None, selected_target=S, negation=None, pack=None,
            fixed=inventory.FIXED_RECORD):
    caller = words(0xB500, 0xB093, 0x900F, 0x9110, 0x9211, 0x9312, 0xA80F, 0x4669)
    caller += call(A+16, U) + words(0xA811, 0xA905) + call(A+24, U)
    caller += words(0x4668, 0xA905, 0xAA00 | output)
    caller += call(A+34, selected_target) + call(A+38, P) + words(0xB013, 0xBC02, 0x4708)
    unpack = words(0x6802, 0x6843, 0x6888, 0x600A, 0x604B, 0x608A, 0x60CA, 0x610A, 0x4770)
    prefix = words(0xB570, 0x1C04, 0x1C0D, 0x1C16, 0x2000, 0x2100)
    prefix += call(S+12, N) + words(0x2001, 0x2100) + call(S+20, N)
    prefix += words(0x1C20, 0x1C29, 0x1C32)
    selection = selection or prefix + words(0x2B00, 0xD004, 0x2B01, 0xD004, 0x2B02, 0xD004,
        0xE005, 0x1C00, 0xE004, 0x1C08, 0xE002, 0x1C10, 0xE000, 0x4801,
        0xBC70, 0xBC08, 0x4718, fixed & 65535, fixed >> 16)
    pack = pack or (words(0xB510, 0x1C04, 0x6820, 0x6861, 0x68A2, 0x68E3, 0x6920)
                    + call(P+14, W) + words(0xBC10, 0xBC04, 0x4710))
    negation = negation or words(0xB510, 0x4240, 0x4249, 0xBC10, 0xBC04, 0x4710)
    parts = {A: caller, U: unpack, S: selection, P: pack, N: negation,
             W: words(0x0040, 0x0049, 0x4770)}
    counts = {start: len(list(match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB).disasm(body, start)))
              for start, body in parts.items()}
    counts[S] = 30
    rom = bytearray(max(start+len(body) for start, body in parts.items())-fixtures.BASE)
    rows = []
    for start, body in sorted(parts.items()):
        rom[start-fixtures.BASE:start-fixtures.BASE+len(body)] = body
        rows.append(dict(rom=f'0x{start:08X}', end=f'0x{start+len(body):08X}', mode='thumb', instrs=counts[start]))
    mapping = json.dumps(rows).encode()
    index = ''.join(f"{int(row['rom'],16):08X} {int(row['end'],16):08X} "
        f"{int(row['end'],16)-int(row['rom'],16)} {row['instrs']} return\n" for row in rows).encode()
    helpers = tuple((name, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (name, _, bounds), start in zip(inventory.HELPERS, (U, N, S, W, P)))
    return caller, bytes(rom), rows, mapping, index, helpers


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


class DoubleSelectedRecordTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None):
        selected = selected or fixture()
        with patch.object(inventory, 'HELPERS', selected[-1]), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(selected[1]).hexdigest()), \
                patch.object(double, 'EDGES', EDGES), \
                patch.object(inventory, 'FIXED_RECORD_ORIGIN', (S+56, S+64)):
            yield selected

    def verify(self, selected=None, **changes):
        with self.closure(selected) as (body, rom, _, mapping, index, _):
            return inventory.verify(body, A, rom, mapping, index,
                selector=changes.pop('selector', inventory.SELECTOR), **changes)

    def test_all_returned_records_and_actual_fixed_reads_are_retained(self):
        result, decoded = self.verify()
        self.assertEqual(len(decoded), 20)
        self.assertEqual(result['helper_closure'][2]['native_proof']['return_pointers']['values'],
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
            self.verify(fixture(output=19))

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
        helpers = list(selected[-1]); name, (start, end, count, digest), bounds = helpers[2]
        helpers[2] = name, (start, end, count+1, digest), bounds
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
                selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)
            self.assertEqual(calls, [[site, f'func_{target:08X}']
                             for site, target in zip(SITES, (U, U, S, P))])
            self.assertEqual(admission.linked_bytes(image, linked, A, calls, targets,
                selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR), body)
            self.assertEqual(image, before)
            manifest, _ = admission.verify(body, A, rom, mapping, index, calls,
                selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)
            self.assertEqual(manifest['schema'], admission.DOUBLE_SELECTED_RECORD_SCHEMA)
            self.assertEqual(manifest['contract'], inventory.CONTRACT)
            with self.assertRaisesRegex(ValueError, 'manifest differs'):
                admission.verify(body, A, rom, mapping, index, calls,
                    selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR, manifest={})

    def test_implicit_profile_wrong_helper_and_nonzero_original_addend_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, _ = elf_pair(body)
            with self.assertRaises(ValueError):
                admission.original_bindings(image, A, rom, mapping, index)
            for value in ('__addsf3', f'func_{S+2:08X}'):
                altered = copy.deepcopy(image); altered['symbols'][2]['name'] = value
                with self.subTest(name=value), self.assertRaises(ValueError):
                    admission.original_bindings(altered, A, rom, mapping, index,
                        selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)
            altered = copy.deepcopy(image)
            altered['text'] = altered['text'][:34]+call(A+34, A+36)+altered['text'][38:]
            with self.assertRaisesRegex(ValueError, 'zero-addend'):
                admission.original_bindings(altered, A, rom, mapping, index,
                    selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)

    def test_explicit_cli_and_report_selector_cannot_mix(self):
        marker = (f'* verification: `{admission.DOUBLE_SELECTED_RECORD_SCHEMA}`\n'
                  f'* private float pack: `{admission.DOUBLE_SELECTED_RECORD_SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), admission.DOUBLE_SELECTED_RECORD_SELECTOR)
        for altered in (marker+marker, marker.replace(admission.DOUBLE_SELECTED_RECORD_SCHEMA, admission.SCHEMA),
                        marker.replace(f'* private float pack: `{admission.DOUBLE_SELECTED_RECORD_SELECTOR}`', f'* private float pack: `{admission.SELECTOR}`')):
            with self.subTest(marker=altered), self.assertRaises(ValueError):
                admission.selected(altered)
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', f'{A:08X}', '--owner-runtime-profile',
                    admission.DOUBLE_SELECTED_RECORD_SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, admission.DOUBLE_SELECTED_RECORD_SELECTOR)

    def test_build_and_report_replay_preserve_conditional_contract(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected, case.project(selected) as (root, _), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, A, old.arguments(
                owner_runtime_profile=admission.DOUBLE_SELECTED_RECORD_SELECTOR))
            self.assertEqual(result['body'], selected[0])
            report = admission.render(result)
            self.assertEqual(admission.selector_for_report(report), admission.DOUBLE_SELECTED_RECORD_SELECTOR)
            self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, A), root, A))

    def test_transitive_negation_and_wide_shift_are_complete_native_dependencies(self):
        result, _ = self.verify()
        closure = {row['name']: row for row in result['helper_closure']}
        self.assertEqual(closure['private-selection']['calls'], [(S+12, N), (S+20, N)])
        self.assertEqual(closure['private-pack']['calls'], [(P+14, W)])
        for role in ('private-wide-negation', 'private-wide-shift'):
            proof = closure[role]['native_proof']
            self.assertEqual(proof['argument_effects']['reads'], [])
            self.assertEqual(proof['writes'], [])
            self.assertEqual(proof['stack_reads'], [])
            self.assertTrue(proof['returns'])
            self.assertTrue(proof['native_edges'])

    def test_omitted_and_redirected_transitive_call_edges_refuse(self):
        selected = fixture()
        with self.closure(selected):
            for edges in (EDGES[1:], EDGES[:-1], ((S+12, W),)+EDGES[1:]):
                with self.subTest(edges=edges), patch.object(double, 'EDGES', edges), self.assertRaises(ValueError):
                    inventory.verify(selected[0], A, selected[1], selected[3], selected[4], selector=inventory.SELECTOR)

    def test_transitive_dependency_must_precede_its_consumer(self):
        selected = list(fixture())
        helpers = list(selected[-1]); helpers[1], helpers[2] = helpers[2], helpers[1]
        selected[-1] = tuple(helpers)
        with self.assertRaisesRegex(ValueError, 'completed native dependency'):
            self.verify(tuple(selected))

    def test_transitive_helper_count_and_exact_body_are_authenticated(self):
        for position in (1, 3):
            for changed_field in ('count', 'body'):
                selected = list(fixture())
                if changed_field == 'count':
                    helpers = list(selected[-1]); name, (start, end, count, digest), bounds = helpers[position]
                    helpers[position] = name, (start, end, count+1, digest), bounds
                    selected[-1] = tuple(helpers)
                else:
                    rom = bytearray(selected[1]); start = selected[-1][position][1][0]
                    rom[start-fixtures.BASE] ^= 1; selected[1] = bytes(rom)
                with self.subTest(position=position, field=changed_field), self.assertRaisesRegex(ValueError, 'identity'):
                    self.verify(tuple(selected))

    def test_nested_saved_register_corruption_refuses(self):
        negation = words(0x2400, 0x4770)
        with self.assertRaisesRegex(ValueError, 'restoration'):
            self.verify(fixture(negation=negation))

    def test_nested_external_reads_have_no_implicit_permission(self):
        with self.assertRaisesRegex(ValueError, 'read|bound|policy'):
            self.verify(fixture(negation=words(0x6800, 0x4770)))

    def test_nested_scalar_constant_is_not_treated_as_a_pointer(self):
        selected = fixture()
        start, end = S-fixtures.BASE, S-fixtures.BASE+68
        selection = selected[1][start:end]
        # A scalar return, even from a leaf returning zero, cannot become a
        # record pointer. Observe it before the three incoming pointers restore.
        selection = selection[:24]+words(0x6800)+selection[26:]
        with self.assertRaisesRegex(ValueError, 'unbounded external read'):
            self.verify(fixture(selection=selection, negation=words(0x2000, 0x4770)))

    def test_all_five_absolute_record_words_are_required(self):
        for position in range(5):
            bounds = copy.deepcopy(inventory.ABSOLUTE_POLICY); bounds['reads'].pop(position)
            with self.subTest(position=position), patch.object(inventory, 'ABSOLUTE_POLICY', bounds), \
                    self.assertRaisesRegex(ValueError, 'conditional footprint'):
                self.verify()

    def test_absolute_record_policy_is_explicit_and_typed(self):
        for bounds in (None, {'schema': 'unknown', 'reads': []},
                       {'schema': 'thumb-conditional-absolute-reads-v1', 'reads': [[inventory.FIXED_RECORD, 3]]}):
            with self.subTest(bounds=bounds), patch.object(inventory, 'ABSOLUTE_POLICY', bounds), self.assertRaises(ValueError):
                self.verify()

    def test_fixed_record_literal_must_match_its_reached_owner(self):
        with self.assertRaisesRegex(ValueError, 'policy|literal'):
            self.verify(fixture(fixed=inventory.FIXED_RECORD+4))
        selected = fixture()
        with self.closure(selected), patch.object(inventory, 'FIXED_RECORD_ORIGIN', (S+54, S+64)), \
                self.assertRaisesRegex(ValueError, 'literal identity'):
            inventory.verify(selected[0], A, selected[1], selected[3], selected[4], selector=inventory.SELECTOR)

    def test_selected_pointer_union_may_not_add_an_unobserved_alternative(self):
        with patch.object(inventory, 'RETURN_POINTERS', sorted(inventory.RETURN_POINTERS+[['argument', 3, 0]])), \
                self.assertRaisesRegex(ValueError, 'all three formals'):
            self.verify()

    def test_child_effect_certificate_tampering_refuses(self):
        real = runtime.prove_runtime
        def altered(*args, **kwargs):
            proof = real(*args, **kwargs)
            if args[2] == N:
                proof['argument_effects']['complete'] = False
            return proof
        with patch.object(runtime, 'prove_runtime', side_effect=altered), self.assertRaisesRegex(ValueError, 'complete bound'):
            self.verify()

    def test_original_wrong_symbol_kind_and_duplicate_undefined_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, _ = elf_pair(body)
            for kind in ('data', 'duplicate', 'extra-transitive', 'addend'):
                changed = copy.deepcopy(image)
                if kind == 'data':
                    changed['symbols'][2]['type'] = 1
                elif kind == 'duplicate':
                    changed['symbols'].append(copy.deepcopy(changed['symbols'][2]))
                elif kind == 'extra-transitive':
                    changed['symbols'][2]['name'] = f'func_{N:08X}'
                else:
                    changed['symbols'][2]['value'] = 2
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    admission.original_bindings(changed, A, rom, mapping, index,
                        selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)

    def test_linked_bytes_outside_original_relocations_cannot_change(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            calls, targets = admission.original_bindings(original, A, rom, mapping, index,
                selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)
            linked['text'] = words(0xB510)+body[2:]
            with self.assertRaisesRegex(ValueError, 'outside original BL'):
                admission.linked_bytes(original, linked, A, calls, targets,
                    selector=admission.DOUBLE_SELECTED_RECORD_SELECTOR)

    def test_stale_source_runtime_maps_and_producer_refuse_before_rebuild(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected, case.project(selected) as (root, _), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, A, old.arguments(owner_runtime_profile=admission.DOUBLE_SELECTED_RECORD_SELECTOR))
            report = admission.render(result)
            for name in (f'src/{A:08X}.c', 'config/functions.json', 'symbols/functions.txt', 'synthetic.rom'):
                path = root/name; original = path.read_bytes(); path.write_bytes(original+b' ')
                try:
                    with self.subTest(path=name), patch.object(admission, 'build', side_effect=AssertionError('stale cannot rebuild')):
                        self.assertFalse(old.evidence.report_matches(report, root, A))
                finally:
                    path.write_bytes(original)
            for name in ('runtime_fingerprint', 'producer_fingerprint'):
                with self.subTest(fingerprint=name), patch.object(admission, name, return_value={}), \
                        patch.object(admission, 'build', side_effect=AssertionError('stale cannot rebuild')):
                    self.assertFalse(old.evidence.report_matches(report, root, A))

    def test_previous_float_selector_still_routes_to_its_existing_inventory(self):
        import private_float_selected_record_inventory as previous
        self.assertIs(admission.profile(admission.SELECTED_RECORD_SELECTOR)[0], previous)
        self.assertIs(admission.profile(admission.DOUBLE_SELECTED_RECORD_SELECTOR)[0], inventory)
        with patch.object(admission, 'issue', return_value=17) as issue, \
                patch.object(sys, 'argv', ['match.py', f'{A:08X}', '--owner-runtime-profile', admission.SELECTED_RECORD_SELECTOR]):
            self.assertEqual(match.main(), 17)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, admission.SELECTED_RECORD_SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
