"""Inline record alternatives and explicitly pinned original data relocations."""
from contextlib import contextmanager
import copy
import hashlib
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
import private_float_inline_division_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures
import test_private_float_pack_admission_profile as old

A, U, P = 0x08000100, 0x08000200, 0x08000300
words, call = fixtures.words, fixtures.call
SITES = (12, 20, 42)


def fixture(*, local=0, target=P):
    root = words(0xB500, 0xB08A, 0x9008, 0x9109, 0xA808, 0x4669)
    root += call(A+12, U)+words(0xA809, 0xA904)+call(A+20, U)
    root += words(0x2B00, 0xD003, 0x2B01, 0xD003, 0x4804, 0xE002,
                  0xA800 | local, 0xE000, 0xA804)
    root += call(A+42, target)+words(0xB00A, 0xBC02, 0x4708)
    root += struct.pack('<I', inventory.FIXED_RECORD)
    unpack = words(0x6802, 0x600A, 0x604A, 0x608A, 0x60CA, 0x4770)
    pack = words(0x6802, 0x6842, 0x6882, 0x68C0, 0x4770)
    parts = {A: root, U: unpack, P: pack}
    counts = {A: 23, U: 6, P: 5}
    rom, rows, mapping, index = fixtures.image(parts, counts)
    helpers = tuple((name, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (name, _, bounds), start in zip(inventory.HELPERS, (U, P)))
    return root, rom, rows, mapping, index, helpers


def elf_pair(body):
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body))]
    symbols += [dict(name=f'func_{target:08X}', type=0, bind=1, section=0, value=0, size=0)
                for target in (U, P)]
    symbols.append(dict(name='data_03005E68', type=0, bind=1, section=0, value=0, size=0))
    raw = bytearray(body)
    for site in SITES:
        raw[site:site+4] = call(A+site, A+site)
    raw[52:56] = bytes(4)
    rels = b''.join(struct.pack('<II', site, number << 8 | kind)
                   for site, number, kind in ((12, 1, 10), (20, 1, 10), (42, 2, 10), (52, 3, 2)))
    image = dict(type=1, text_index=1, text=bytes(raw), symbols=symbols,
        sections=[(0,)*10, (0, 1, 6, 0, 0, len(body), 0, 0, 4, 0),
                  (0, 9, 0, 0, 0, len(rels), 3, 1, 4, 8)],
        symbol_tables={3: symbols}, relocations=[2], section_data=[b'', bytes(raw), rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0, 1, 6, A, 0, len(body), 0, 0, 4, 0)
    linked['symbols'][0]['value'] = A | 1
    for symbol, target in zip(linked['symbols'][1:3], (U, P)):
        symbol.update(type=2, value=target | 1, section=0xFFF1)
    linked['symbols'][3].update(type=1, value=inventory.FIXED_RECORD, section=0xFFF1)
    return image, linked


class InlineDivisionTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None):
        selected = fixture() if selected is None else selected
        with patch.object(inventory, 'HELPERS', selected[-1]), \
                patch.object(runtime, 'ROM_SHA256', admission.sha(selected[1])), \
                patch.object(runtime, 'EDGES', ()):
            yield selected

    def verify(self, selected=None, **changes):
        with self.closure(selected) as (body, rom, _, mapping, index, _):
            return inventory.verify(body, A, rom, mapping, index,
                selector=changes.pop('selector', inventory.SELECTOR), **changes)

    def test_inline_local_and_constant_alternatives_have_conditional_effects(self):
        result, decoded = self.verify()
        self.assertEqual(len(decoded), 23)
        self.assertEqual(result['external_reads'], inventory.ABSOLUTE_POLICY['reads'])
        self.assertEqual(result['external_formal_reads'], [])
        self.assertEqual(result['external_writes'], [])
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertFalse(result['physical_memory_claim'])
        self.assertFalse(result['arithmetic_C_equivalence'])
        self.assertIn('conditional', inventory.CONTRACT)

    def test_root_pointer_into_saved_register_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'saved|frame'):
            self.verify(fixture(local=10))

    def test_conditional_fixed_read_may_not_be_omitted(self):
        bounds = copy.deepcopy(inventory.ABSOLUTE_POLICY)
        bounds['reads'].pop()
        with patch.object(inventory, 'ABSOLUTE_POLICY', bounds), self.assertRaises(ValueError):
            self.verify()

    def test_exact_calls_and_complete_helper_identity(self):
        with self.assertRaisesRegex(ValueError, 'two pinned unpacks'):
            self.verify(fixture(target=U))
        selected = list(fixture()); helpers = list(selected[-1])
        name, (start, end, count, digest), bounds = helpers[0]
        helpers[0] = name, (start, end, count+1, digest), bounds
        selected[-1] = tuple(helpers)
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(tuple(selected))

    def test_explicit_selector_typed_inputs_and_manifest(self):
        with self.assertRaises(ValueError):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})
        selected = list(fixture()); selected[3] = bytearray(selected[3])
        with self.assertRaisesRegex(ValueError, 'typed inputs'):
            self.verify(tuple(selected))

    def test_original_zero_addend_call_and_data_bindings(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, linked = elf_pair(body); before = copy.deepcopy(image)
            calls, targets = admission.original_bindings(image, A, rom, mapping, index,
                selector=admission.INLINE_DIVISION_SELECTOR)
            self.assertEqual(calls, [[site, f'func_{target:08X}'] for site, target in zip(SITES, (U, U, P))])
            self.assertEqual(targets['data_03005E68'], inventory.FIXED_RECORD)
            self.assertEqual(admission.linked_bytes(image, linked, A, calls, targets,
                selector=admission.INLINE_DIVISION_SELECTOR), body)
            result, _ = admission.verify(body, A, rom, mapping, index, calls,
                selector=admission.INLINE_DIVISION_SELECTOR)
            self.assertEqual(result['schema'], admission.INLINE_DIVISION_SCHEMA)
            self.assertEqual(image, before)

    def test_wrong_data_symbol_addend_and_relocation_site_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, _ = elf_pair(body)
            for kind in ('symbol', 'addend', 'site', 'type'):
                changed = copy.deepcopy(image)
                if kind == 'symbol': changed['symbols'][3]['name'] = 'data_03005E6C'
                if kind == 'addend': changed['text'] = changed['text'][:52]+struct.pack('<I', 4)
                if kind == 'site': changed['section_data'][2] = changed['section_data'][2][:-8]+struct.pack('<II', 48, 3 << 8 | 2)
                if kind == 'type': changed['symbols'][3]['type'] = 2
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    admission.original_bindings(changed, A, rom, mapping, index,
                        selector=admission.INLINE_DIVISION_SELECTOR)
            with self.assertRaises(ValueError):
                admission.original_bindings(image, A, rom, mapping, index)

    def test_linked_data_definition_and_unrelocated_bytes_refuse(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            image, linked = elf_pair(body)
            calls, targets = admission.original_bindings(image, A, rom, mapping, index,
                selector=admission.INLINE_DIVISION_SELECTOR)
            for kind in ('definition', 'literal', 'ordinary'):
                changed = copy.deepcopy(linked)
                if kind == 'definition': changed['symbols'][3]['value'] += 4
                if kind == 'literal': changed['text'] = body[:52]+struct.pack('<I', inventory.FIXED_RECORD+4)
                if kind == 'ordinary': changed['text'] = bytes([body[0] ^ 1])+body[1:]
                with self.subTest(kind=kind), self.assertRaises(ValueError):
                    admission.linked_bytes(image, changed, A, calls, targets,
                        selector=admission.INLINE_DIVISION_SELECTOR)

    def test_literal_bearing_symbol_excludes_only_authentic_terminal_alignment(self):
        body = fixture()[0]+words(0x46C0)
        image, linked = elf_pair(body)
        for current in (image, linked):
            current['text'] += words(0x46C0)
            section = list(current['sections'][1]); section[5] = len(current['text'])
            current['sections'][1] = tuple(section)
            self.assertEqual(admission.function_size(current, A, partitioned_tail=True), len(body))
            with self.assertRaisesRegex(ValueError, 'references'):
                admission.function_size(current, A)
            changed = copy.deepcopy(current); changed['text'] = changed['text'][:-2]+words(0x4770)
            with self.assertRaisesRegex(ValueError, 'terminal Thumb NOP'):
                admission.function_size(changed, A, partitioned_tail=True)

    def test_cli_report_selector_and_native_report_replay(self):
        marker = (f'* verification: `{admission.INLINE_DIVISION_SCHEMA}`\n'
                  f'* private float pack: `{admission.INLINE_DIVISION_SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), admission.INLINE_DIVISION_SELECTOR)
        with self.assertRaises(ValueError): admission.selector_for_report(marker+marker)
        with patch.object(admission, 'issue', return_value=123), \
                patch.object(sys, 'argv', ['match.py', f'{A:08X}', '--owner-runtime-profile', admission.INLINE_DIVISION_SELECTOR]):
            self.assertEqual(match.main(), 123)
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected, case.project(selected) as (root, _), \
                patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, selected):
            result = admission.build(root, A, old.arguments(owner_runtime_profile=admission.INLINE_DIVISION_SELECTOR))
            report = admission.render(result)
            self.assertEqual(admission.selector_for_report(report), admission.INLINE_DIVISION_SELECTOR)
            self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, A), root, A))
            with (root/f'src/{A:08X}.c').open('a') as stream: stream.write('\n')
            self.assertFalse(old.evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main(verbosity=2)
