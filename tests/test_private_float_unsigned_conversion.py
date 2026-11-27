"""Nested actual-byte float closures, conditional effects and compiler alias binding."""
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
import private_float_unsigned_conversion_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures
import test_private_float_pack_admission_profile as old

A, C, V, D, U, F, S, P = [0x08000000+offset for offset in range(0x100, 0x900, 0x100)]
words, call = fixtures.words, fixtures.call
SITES = (4, 14, 22, 26)


def fixture(*, addition_target=D, output=8):
    root = words(0xB510, 0x1C04)+call(A+4, C)+words(0x2800, 0xD003, 0x1C20)
    root += call(A+14, V)+words(0xE004, 0x1C20)+call(A+22, addition_target)
    root += call(A+26, V)+words(0xBC10, 0xBC02, 0x4708)
    compare = words(0xB500, 0xB08A, 0x9008, 0x9109, 0xA808, 0x4669)
    compare += call(C+12, U)+words(0xA809, 0xA904)+call(C+20, U)
    compare += words(0x4668, 0xA904)+call(C+28, F)+words(0xB00A, 0xBC02, 0x4708)
    convert = words(0xB500, 0xB085, 0x9004, 0xA804, 0x4669)
    convert += call(V+10, U)+words(0x9800, 0xB005, 0xBC02, 0x4708)
    add = words(0xB500, 0xB08E, 0x900C, 0x910D, 0xA80C, 0x4669)
    add += call(D+12, U)+words(0xA80D, 0xA904)+call(D+20, U)
    add += words(0x4668, 0xA904, 0xAA00 | output)+call(D+30, S)
    add += call(D+34, P)+words(0xB00E, 0xBC02, 0x4708)
    unpack = words(0x6802, 0x600A, 0x604A, 0x608A, 0x60CA, 0x4770)
    compare_leaf = words(0x6802, 0x6842, 0x6882, 0x68C2,
                         0x680A, 0x684A, 0x688A, 0x68CA, 0x2000, 0x4770)
    selection = words(0x2B00, 0xD004, 0x2B01, 0xD004, 0x2B02, 0xD004,
        0xE005, 0x1C00, 0xE004, 0x1C08, 0xE002, 0x1C10, 0xE000, 0x4801,
        0x4770, 0, 0x5E68, 0x0300)
    pack = words(0x6802, 0x6842, 0x6882, 0x68C0, 0x4770)
    parts = dict(zip((A, C, V, D, U, F, S, P),
                     (root, compare, convert, add, unpack, compare_leaf, selection, pack)))
    counts = dict(zip((A, C, V, D, U, F, S, P), (14, 16, 10, 18, 6, 10, 15, 5)))
    rom = bytearray(0xA00)
    rows = []
    for start, body in sorted(parts.items()):
        rom[start-0x08000000:start-0x08000000+len(body)] = body
        rows.append(dict(rom=f'0x{start:08X}', end=f'0x{start+len(body):08X}',
                         mode='thumb', instrs=counts[start]))
    mapping = json.dumps(rows).encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                    f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                    for r in rows).encode()
    def specs(module, addresses):
        return tuple((name, (start, start+len(parts[start]), counts[start],
            hashlib.sha256(parts[start]).hexdigest()), bounds)
            for (name, _, bounds), start in zip(module.HELPERS, addresses))
    helper_sets = [specs(inventory, (C, V, D)),
                   specs(inventory.comparison, (U, F)),
                   specs(inventory.scalar_conversion, (U, P)),
                   specs(inventory.selected_record, (U, S, P))]
    return root, bytes(rom), rows, mapping, index, helper_sets


def elf_pair(body):
    names = ('__ltsf2', '__fixsfsi', '__addsf3')
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body))]
    symbols += [dict(name=name, type=0, bind=1, section=0, value=0, size=0) for name in names]
    raw = bytearray(body)
    for site in SITES:
        raw[site:site+4] = call(A+site, A+site)
    rels = b''.join(struct.pack('<II', site, number << 8 | 10)
                    for site, number in zip(SITES, (1, 2, 3, 2)))
    image = dict(type=1, text_index=1, text=bytes(raw), symbols=symbols,
        sections=[(0,)*10, (0, 1, 6, 0, 0, len(body), 0, 0, 2, 0),
                  (0, 9, 0, 0, 0, len(rels), 3, 1, 4, 8)],
        symbol_tables={3:symbols}, relocations=[2], section_data=[b'', bytes(raw), rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0, 1, 6, A, 0, len(body), 0, 0, 2, 0)
    linked['symbols'][0]['value'] = A | 1
    for symbol, target in zip(linked['symbols'][1:], (C, V, D)):
        symbol.update(value=target | 1, section=0xFFF1)
    return image, linked


class UnsignedConversionTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None):
        selected = fixture() if selected is None else selected
        with patch.object(inventory, 'HELPERS', selected[-1][0]), \
                patch.object(inventory.comparison, 'HELPERS', selected[-1][1]), \
                patch.object(inventory.scalar_conversion, 'HELPERS', selected[-1][2]), \
                patch.object(inventory.selected_record, 'HELPERS', selected[-1][3]), \
                patch.object(runtime, 'ROM_SHA256', admission.sha(selected[1])), \
                patch.object(runtime, 'EDGES', ()):
            yield selected

    def verify(self, selected=None, **changes):
        with self.closure(selected) as (body, rom, _, mapping, index, _):
            return inventory.verify(body, A, rom, mapping, index,
                selector=changes.pop('selector', inventory.SELECTOR), **changes)

    def test_three_native_closures_and_fixed_reads_reach_root(self):
        result, instructions = self.verify()
        self.assertEqual(len(instructions), 14)
        self.assertEqual(len(result['helper_closure']), 3)
        self.assertEqual(result['external_reads'], inventory.selected_record.ABSOLUTE_POLICY['reads'])
        self.assertEqual(result['external_formal_reads'], [])
        self.assertEqual(result['external_writes'], [])
        self.assertEqual(result['numeric_input_preconditions'], [])
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertFalse(result['arithmetic_C_equivalence'])
        self.assertFalse(result['physical_memory_claim'])
        self.assertIn('conditional', inventory.CONTRACT)

    def test_exact_four_calls_and_selected_helper_identity(self):
        with self.assertRaisesRegex(ValueError, 'comparison/conversion/addition/conversion'):
            self.verify(fixture(addition_target=C))
        selected = list(fixture()); specs = copy.deepcopy(selected[-1])
        role, (start, end, count, digest), bounds = specs[0][1]
        altered = list(specs[0]); altered[1] = role, (start, end, count+1, digest), bounds
        specs[0] = tuple(altered); selected[-1] = specs
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(tuple(selected))

    def test_nested_live_local_bounds_remain_enforced(self):
        with self.assertRaisesRegex(ValueError, 'saved|frame'):
            self.verify(fixture(output=14))

    def test_child_absolute_reads_cannot_be_omitted_from_parent(self):
        prove = runtime.prove_runtime
        def omit(*args, **kwargs):
            if args[2] == A:
                kwargs['absolute_read_policy'] = dict(schema='thumb-conditional-absolute-reads-v1', reads=[])
            return prove(*args, **kwargs)
        with patch.object(runtime, 'prove_runtime', side_effect=omit), \
                self.assertRaisesRegex(ValueError, 'conditional footprint'):
            self.verify()

    def test_forged_nested_absolute_receipt_refuses(self):
        prove = runtime.prove_runtime
        def corrupt(*args, **kwargs):
            result = prove(*args, **kwargs)
            if args[2] == D:
                result['absolute_reads']['body_sha256'] = '0'*64
            return result
        with patch.object(runtime, 'prove_runtime', side_effect=corrupt), \
                self.assertRaisesRegex(ValueError, 'child absolute-read receipt'):
            self.verify()

    def test_typed_explicit_inventory_and_exact_manifest(self):
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})
        selected = list(fixture()); selected[3] = bytearray(selected[3])
        with self.assertRaisesRegex(ValueError, 'typed inputs'):
            self.verify(tuple(selected))

    def test_original_compiler_aliases_authenticate_actual_calls(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            before = copy.deepcopy(original)
            calls, targets = admission.original_bindings(original, A, rom, mapping, index,
                selector=admission.UNSIGNED_CONVERSION_SELECTOR)
            self.assertEqual(calls, [[site, name] for site, name in
                zip(SITES, ('__ltsf2', '__fixsfsi', '__addsf3', '__fixsfsi'))])
            self.assertEqual(admission.linked_bytes(original, linked, A, calls, targets,
                selector=admission.UNSIGNED_CONVERSION_SELECTOR), body)
            proof, _ = admission.verify(body, A, rom, mapping, index, calls,
                selector=admission.UNSIGNED_CONVERSION_SELECTOR)
            self.assertEqual(proof['schema'], admission.UNSIGNED_CONVERSION_SCHEMA)
            self.assertEqual(original, before)

    def test_other_compiler_names_and_original_nonzero_addends_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, _ = elf_pair(body)
            for name in ('__lesf2', '__fixunssfsi', f'func_{C+2:08X}'):
                changed = copy.deepcopy(original); changed['symbols'][1]['name'] = name
                with self.subTest(name=name), self.assertRaises(ValueError):
                    admission.original_bindings(changed, A, rom, mapping, index,
                        selector=admission.UNSIGNED_CONVERSION_SELECTOR)
            changed = copy.deepcopy(original)
            changed['text'] = changed['text'][:4]+call(A+4, A+6)+changed['text'][8:]
            with self.assertRaisesRegex(ValueError, 'zero-addend'):
                admission.original_bindings(changed, A, rom, mapping, index,
                    selector=admission.UNSIGNED_CONVERSION_SELECTOR)

    def test_explicit_cli_and_unmixed_report_selector(self):
        marker = (f'* verification: `{admission.UNSIGNED_CONVERSION_SCHEMA}`\n'
                  f'* private float pack: `{admission.UNSIGNED_CONVERSION_SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), admission.UNSIGNED_CONVERSION_SELECTOR)
        for changed in (marker+marker, marker.replace(admission.UNSIGNED_CONVERSION_SCHEMA, admission.SCHEMA)):
            with self.subTest(marker=changed), self.assertRaises(ValueError):
                admission.selected(changed)
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', f'{A:08X}', '--owner-runtime-profile',
                    admission.UNSIGNED_CONVERSION_SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, admission.UNSIGNED_CONVERSION_SELECTOR)

    def test_native_build_and_report_retain_conditional_closure(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected, case.project(selected) as (root, _), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, A, old.arguments(
                owner_runtime_profile=admission.UNSIGNED_CONVERSION_SELECTOR))
            self.assertEqual(result['body'], selected[0])
            self.assertEqual(result['manifest']['contract'], inventory.CONTRACT)
            self.assertEqual(result['manifest']['inventory']['external_reads'],
                             inventory.selected_record.ABSOLUTE_POLICY['reads'])
            report = admission.render(result)
            with patch.object(admission, 'build', return_value=result):
                self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, A), root, A))
            (root/'symbols/functions.txt').write_bytes(selected[4]+b' ')
            with patch.object(admission, 'build', side_effect=AssertionError('stale context must not build')):
                self.assertFalse(old.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main(verbosity=2)
