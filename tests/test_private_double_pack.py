"""Synthetic double unpack/pack effects and isolated source admission."""
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
import private_double_pack_effects_inventory as inventory
import private_float_pack_admission_profile as admission
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as base
import test_private_float_pack_admission_profile as old
import test_status_private_float_routing as status_fixtures

A, U, P = base.ADDRESS, base.UNPACK, base.PACK
words, call = base.words, base.call
SELECTOR = admission.DOUBLE_PACK_SELECTOR


def fixture(*, pointer=5, unpack=None, pack=None, reverse=False):
    if unpack is None:
        unpack = words(0x6802, 0x6843, 0x600A, 0x604A, 0x608A,
                       0x60CA, 0x610A, 0x688A, 0x4770)
    if pack is None:
        pack = words(0xB510, 0x1C04, 0x6820, 0x6861, 0x68A2,
                     0x68E3, 0x6920, 0xBC10, 0xBC02, 0x4708)
    caller = words(0xB500, 0xB087, 0x9005, 0x9106, 0xA800 | pointer, 0x4669)
    caller += call(A+12, P if reverse else U)
    caller += words(0x2100, 0x9801, 0x2800, 0xD100, 0x2101, 0x9101, 0x4668)
    caller += call(A+30, U if reverse else P)
    caller += words(0xB007, 0xBC02, 0x4708)
    parts = {A: caller, U: unpack, P: pack}
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    counts = {start: len(list(decoder.disasm(body, start))) for start, body in parts.items()}
    rom, rows, mapping, index = base.image(parts, counts)
    specs = tuple((role, (start, start+len(parts[start]), counts[start],
        hashlib.sha256(parts[start]).hexdigest()), bounds)
        for (role, _, bounds), start in zip((inventory.HELPERS[0], inventory.HELPERS[-1]), (U, P)))
    return caller, rom, rows, mapping, index, specs


def elf_pair(body):
    symbols = [dict(name=f'func_{A:08X}', type=2, bind=1, section=1, value=1, size=len(body)),
               dict(name=f'func_{U:08X}', type=2, bind=1, section=0, value=0, size=0),
               dict(name=f'func_{P:08X}', type=2, bind=1, section=0, value=0, size=0)]
    original = bytearray(body)
    for site in (12, 30):
        original[site:site+4] = call(A+site, A+site)
    rels = b''.join(struct.pack('<II', site, number << 8 | 10)
                    for site, number in ((12, 1), (30, 2)))
    image = dict(type=1, text_index=1, text=bytes(original), symbols=symbols,
        sections=[(0,)*10, (0, 1, 6, 0, 0, len(body), 0, 0, 4, 0),
                  (0, 9, 0, 0, 0, len(rels), 3, 1, 4, 8)],
        symbol_tables={3: symbols}, relocations=[2], section_data=[b'', bytes(original), rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0, 1, 6, A, 0, len(body), 0, 0, 4, 0)
    for symbol, target in zip(linked['symbols'], (A, U, P)):
        symbol['value'] = target | 1
    linked['symbols'][1]['section'] = linked['symbols'][2]['section'] = 0xFFF1
    return image, linked


class DoublePackTests(unittest.TestCase):
    @contextmanager
    def closure(self, selected=None, *, helpers=None):
        selected = fixture() if selected is None else selected
        with patch.object(inventory, 'HELPERS', selected[-1] if helpers is None else helpers), \
                patch.object(runtime, 'ROM_SHA256', hashlib.sha256(selected[1]).hexdigest()), \
                patch.object(runtime, 'EDGES', ()):
            yield selected

    def verify(self, selected=None, *, helpers=None, selector=inventory.SELECTOR, manifest=None):
        with self.closure(selected, helpers=helpers) as (body, rom, _, mapping, index, _):
            return inventory.verify(body, A, rom, mapping, index, selector=selector, manifest=manifest)

    def test_complete_double_effects_are_confined_to_live_locals(self):
        proof, _ = self.verify()
        unpack, pack = [v['native_proof']['argument_effects'] for v in proof['helper_closure']]
        self.assertEqual(unpack['reads'], [[0, 0, 4], [0, 4, 4], [1, 8, 4]])
        self.assertEqual(unpack['writes'], [[1, offset, 4] for offset in range(0, 20, 4)])
        self.assertEqual(pack['reads'], [[0, offset, 4] for offset in range(0, 20, 4)])
        self.assertEqual(pack['writes'], [])
        self.assertEqual(proof['external_reads'], [])
        self.assertEqual(proof['external_writes'], [])
        self.assertTrue(all(v[-1][:2] == ['stack', 0] for v in proof['caller']['argument_accesses']))
        self.assertEqual(proof['numeric_return_facts'], [])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertFalse(proof['physical_memory_claim'])

    def test_second_double_word_cannot_cross_into_saved_or_incoming_words(self):
        for pointer in (6, 7, 8):
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                self.verify(fixture(pointer=pointer))

    def test_each_reached_helper_effect_requires_its_own_bound(self):
        selected = fixture()
        for helper in (0, 1):
            for kind in ('reads', 'writes'):
                for position in range(len(selected[-1][helper][2][kind])):
                    specs = copy.deepcopy(selected[-1])
                    specs[helper][2][kind].pop(position)
                    with self.subTest(helper=helper, kind=kind, position=position), self.assertRaises(ValueError):
                        self.verify(selected, helpers=specs)

    def test_packer_narrow_stores_remain_within_its_own_frame(self):
        pack = words(0xB510, 0xB081, 0x1C04, 0x466B, 0x2200, 0x701A, 0x781A,
                     0x6820, 0x6861, 0x68A2, 0x68E3, 0x6920, 0xB001, 0xBC10, 0xBC02, 0x4708)
        proof, _ = self.verify(fixture(pack=pack))
        self.assertTrue(proof['complete_argument_effect_proof'])
        altered = bytearray(pack)
        altered[10:12] = words(0x721A)  # STRB into the saved-register word at SP+8.
        with self.assertRaises(ValueError):
            self.verify(fixture(pack=bytes(altered)))

    def test_exact_helper_identity_order_and_explicit_manifest(self):
        with self.assertRaisesRegex(ValueError, 'one pinned unpack'):
            self.verify(fixture(reverse=True))
        with self.assertRaisesRegex(ValueError, 'explicit inventory'):
            self.verify(selector='default')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(manifest={})
        selected = fixture()
        specs = list(selected[-1])
        role, (start, end, count, digest), bounds = specs[1]
        specs[1] = role, (start, end, count+1, digest), bounds
        with self.assertRaisesRegex(ValueError, 'identity'):
            self.verify(selected, helpers=specs)

    def test_dual_indexes_and_hidden_helper_calls_cannot_change(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            rows = json.loads(mapping)
            rows[-1]['instrs'] += 1
            with self.assertRaises(ValueError):
                inventory.verify(body, A, rom, json.dumps(rows).encode(), index, selector=inventory.SELECTOR)
            with patch.object(runtime, 'EDGES', ((P, P+0x80),)), self.assertRaisesRegex(ValueError, 'completed native dependency'):
                inventory.verify(body, A, rom, mapping, index, selector=inventory.SELECTOR)

    def test_genuine_bindings_and_linked_bytes_preserve_the_original(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            before = copy.deepcopy(original)
            calls, targets = admission.original_bindings(original, A, rom, mapping, index, selector=SELECTOR)
            self.assertEqual(calls, [[12, 'func_08000200'], [30, 'func_08000300']])
            self.assertEqual(admission.linked_bytes(original, linked, A, calls, targets, selector=SELECTOR), body)
            self.assertEqual(original, before)
            proof, _ = admission.verify(body, A, rom, mapping, index, calls, selector=SELECTOR)
            self.assertEqual(proof['schema'], admission.DOUBLE_PACK_SCHEMA)

    def test_names_definitions_duplicate_symbols_and_addends_are_rejected(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, _ = elf_pair(body)
            mutations = []
            for name in ('__extendsfdf2', 'func_08000302'):
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
            changed['text'] = changed['text'][:30]+call(A+30, A+32)+changed['text'][34:]
            mutations.append(changed)
            for changed in mutations:
                with self.subTest(changed=changed), self.assertRaises(ValueError):
                    admission.original_bindings(changed, A, rom, mapping, index, selector=SELECTOR)

    def test_linker_cannot_change_nonrelocation_bytes_or_function_size(self):
        with self.closure() as (body, rom, _, mapping, index, _):
            original, linked = elf_pair(body)
            calls, targets = admission.original_bindings(original, A, rom, mapping, index, selector=SELECTOR)
            for site in (0, 30):
                changed = copy.deepcopy(linked)
                raw = bytearray(changed['text'])
                raw[site] ^= 1
                changed['text'] = bytes(raw)
                with self.subTest(site=site), self.assertRaises(ValueError):
                    admission.linked_bytes(original, changed, A, calls, targets, selector=SELECTOR)
            changed = copy.deepcopy(linked)
            changed['symbols'][0]['size'] -= 2
            with self.assertRaises(ValueError):
                admission.linked_bytes(original, changed, A, calls, targets, selector=SELECTOR)

    def test_report_and_cli_require_the_distinct_selector(self):
        marker = (f'* verification: `{admission.DOUBLE_PACK_SCHEMA}`\n'
                  f'* private float pack: `{SELECTOR}`\n')
        self.assertEqual(admission.selector_for_report(marker), SELECTOR)
        for changed in (marker+marker, marker.replace(admission.DOUBLE_PACK_SCHEMA, admission.SCHEMA)):
            with self.assertRaises(ValueError):
                admission.selected(changed)
        with patch.object(admission, 'issue', return_value=123) as issue, \
                patch.object(sys, 'argv', ['match.py', '08000100', '--owner-runtime-profile', SELECTOR]):
            self.assertEqual(match.main(), 123)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile, SELECTOR)

    def test_native_build_and_report_replay_keep_double_pack_selector(self):
        case = old.PrivateFloatPackAdmissionTests()
        with self.closure() as selected:
            with case.project(selected) as (root, frozen), \
                    patch.object(old, 'elf_pair', side_effect=elf_pair), case.fake_native(root, frozen):
                result = admission.build(root, A, old.arguments(owner_runtime_profile=SELECTOR))
                self.assertEqual(result['body'], selected[0])
                report = admission.render(result)
                self.assertEqual(admission.selector_for_report(report), SELECTOR)
                self.assertTrue(old.evidence.report_matches(report_fixtures.carried(report, root, A), root, A))

    def test_status_replay_preserves_double_pack_selector(self):
        case = status_fixtures.StatusPrivateFloatRoutingTests()
        case.setUp()
        self.addCleanup(case.doCleanups)
        report = status_fixtures.REPORT.replace(admission.SCHEMA, admission.DOUBLE_PACK_SCHEMA)
        case.report_path.write_text(report.replace(admission.SELECTOR, SELECTOR))
        with patch.object(status_fixtures.status.subprocess, 'run', return_value=
                subprocess.CompletedProcess([], 0, status_fixtures.OUTPUT, '')) as native, \
                patch.object(admission, 'report_matches', return_value=True):
            self.assertEqual(case.collect(), (1, 1, 8, 8, [], 0, 0))
            command = native.call_args.args[0]
            self.assertEqual(command[command.index('--owner-runtime-profile')+1], SELECTOR)


if __name__ == '__main__':
    unittest.main(verbosity=2)
