"""The double packer must include its actual native wide-shift dependency."""
import copy
import hashlib
from pathlib import Path
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
import test_private_double_pack as base

W = 0x08000280


def fixture(*, wide=None, pack=None, pointer=5):
    if wide is None:
        wide = base.words(0x4770)
    if pack is None:
        pack = base.words(0xB510, 0x1C04, 0x6820, 0x6861, 0x68A2, 0x68E3, 0x6920)
        pack += base.call(base.P+14, W)+base.words(0xBC10, 0xBC02, 0x4708)
    leaf_specs = (inventory.HELPERS[0], inventory.HELPERS[-1])
    with patch.object(inventory, 'HELPERS', leaf_specs):
        body, _, _, _, _, specs = base.fixture(pack=pack, pointer=pointer)
    unpack = base.words(0x6802, 0x6843, 0x600A, 0x604A, 0x608A,
                        0x60CA, 0x610A, 0x688A, 0x4770)
    parts = {base.A: body, base.U: unpack, W: wide, base.P: pack}
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    counts = {start: len(list(decoder.disasm(data, start))) for start, data in parts.items()}
    rom, rows, mapping, index = base.base.image(parts, counts)
    middle = ('private-wide-shift', (W, W+len(wide), counts[W],
        hashlib.sha256(wide).hexdigest()), inventory.policy())
    return body, rom, rows, mapping, index, (specs[0], middle, specs[1])


class DoublePackClosureTests(unittest.TestCase):
    def verify(self, selected=None, *, helpers=None):
        selected = fixture() if selected is None else selected
        with base.DoublePackTests().closure(selected, helpers=helpers), \
                patch.object(runtime, 'EDGES', ((base.P+14, W),)):
            return inventory.verify(selected[0], base.A, selected[1], selected[3], selected[4],
                selector=inventory.SELECTOR)

    def test_three_complete_helpers_close_the_packers_actual_call(self):
        proof, _ = self.verify()
        self.assertEqual([v['name'] for v in proof['helper_closure']],
                         ['private-unpack', 'private-wide-shift', 'private-pack'])
        self.assertEqual(proof['helper_closure'][-1]['calls'], [(base.P+14, W)])
        self.assertEqual(len(proof['private_bindings']), 2)
        self.assertEqual(proof['external_reads'], [])
        self.assertEqual(proof['external_writes'], [])
        self.assertEqual(proof['numeric_return_facts'], [])

    def test_missing_or_late_dependency_cannot_be_assumed(self):
        selected = fixture()
        unpack, wide, pack = selected[-1]
        for helpers in ((unpack, pack), (unpack, pack, wide)):
            with self.subTest(helpers=helpers), self.assertRaisesRegex(ValueError, 'completed native dependency'):
                self.verify(selected, helpers=helpers)

    def test_wide_shift_cannot_gain_an_unbound_argument_memory_effect(self):
        with self.assertRaises(ValueError):
            self.verify(fixture(wide=base.words(0x6800, 0x4770)))

    def test_dependency_closure_keeps_both_input_words_within_live_storage(self):
        for pointer in (6, 7, 8):
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                self.verify(fixture(pointer=pointer))

    def test_each_packer_read_still_needs_an_explicit_bound_with_dependencies(self):
        selected = fixture()
        for position in range(5):
            helpers = copy.deepcopy(selected[-1])
            helpers[-1][2]['reads'].pop(position)
            with self.subTest(position=position), self.assertRaises(ValueError):
                self.verify(selected, helpers=helpers)

    def test_two_original_root_bindings_with_three_helper_native_replay(self):
        selected = fixture()
        case = base.old.PrivateFloatPackAdmissionTests()
        with base.DoublePackTests().closure(selected), \
                patch.object(runtime, 'EDGES', ((base.P+14, W),)):
            body, rom, _, mapping, index, _ = selected
            original, linked = base.elf_pair(body)
            calls, targets = admission.original_bindings(original, base.A, rom, mapping, index,
                selector=admission.DOUBLE_PACK_SELECTOR)
            self.assertEqual(admission.linked_bytes(original, linked, base.A, calls, targets,
                selector=admission.DOUBLE_PACK_SELECTOR), body)
            with case.project(selected) as (root, frozen), \
                    patch.object(base.old, 'elf_pair', side_effect=base.elf_pair), case.fake_native(root, frozen):
                result = admission.build(root, base.A,
                    base.old.arguments(owner_runtime_profile=admission.DOUBLE_PACK_SELECTOR))
                self.assertEqual(len(result['manifest']['inventory']['helper_closure']), 3)
                self.assertTrue(base.old.evidence.report_matches(report_fixtures.carried(admission.render(result), root, base.A), root, base.A))


if __name__ == '__main__':
    unittest.main(verbosity=2)
