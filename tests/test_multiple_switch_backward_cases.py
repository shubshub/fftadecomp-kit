"""Isolated backward-case composition, full graph and stale evidence regressions."""
import copy
import json
import struct
import unittest
from unittest.mock import patch

import test_multiple_switch_owner_prerequisite as fixtures
import multiple_switch_owner_prerequisite as policy
import multiple_switch_native_profile as native


class BackwardMultipleSwitchTests(unittest.TestCase):
    def fixture(self):
        return fixtures.fixture(3, shared_backward=True)

    def retarget(self, f, target, table=2, entry=2):
        at = f[1][f'table{table}'] + 4*entry
        f[2][at] = target
        struct.pack_into('<I', f[0], at, fixtures.BASE+target)

    def test_multiple_shared_backward_targets_and_forward_path(self):
        for f in (self.fixture(), fixtures.fixture(3)):
            result = fixtures.verify(f)
            self.assertEqual(len(result['switches']), 3)
            self.assertFalse(result['cycles_present'])
            self.assertEqual(result['instructions'], f[5][0]['instrs'])
        f = self.fixture()
        for n in (1, 2):
            self.assertEqual(f[2][f[1][f'table{n}']+8], f[1]['case0a'])

    def test_cross_table_entry_at_complete_comparison_is_valid(self):
        f = self.fixture()
        # Root case 0 can enter table 2 at its actual comparison. Its former
        # block stays reachable through the two backward table entries.
        self.retarget(f, f[1]['cmp2'], table=0, entry=0)
        fixtures.verify(f)

    def test_targets_into_table_pool_guard_dispatch_and_call_interior_refuse(self):
        for name, delta in (('table0', 0), ('pointer0', 0), ('guard0', 0),
                            ('dispatch0', 0), ('dispatch0', 2), ('dispatch0', 8),
                            ('scalar', 0), ('call', 2)):
            f = self.fixture()
            self.retarget(f, f[1][name]+delta)
            with self.subTest(target=name, delta=delta), self.assertRaises(ValueError):
                fixtures.verify(f)

    def test_foreign_outside_and_odd_targets_refuse(self):
        for target in (-2, 1, 0x1000, 0x1000000):
            f = self.fixture(); self.retarget(f, target)
            with self.subTest(target=target), self.assertRaises(ValueError):
                policy.layout(bytes(f[0]), fixtures.BASE, f[2],
                              multiple_switch_profile=policy.SELECTOR)

    def test_real_cross_table_cycle_refuses(self):
        f = self.fixture(); self.retarget(f, f[1]['cmp0'])
        with self.assertRaisesRegex(ValueError, 'CFG cycles'):
            fixtures.verify(f)

    def test_overlapping_word_ownership_and_ambiguous_partition_refuse(self):
        f = self.fixture()
        raw = bytes(f[0]); mapping = json.dumps(f[5]).encode()
        refinement = policy.owner.refine(raw, fixtures.BASE, mapping,
                                          multiple_switch_profile=policy.SELECTOR)
        refinement['word_switches'].append(copy.deepcopy(refinement['word_switches'][0]))
        with self.assertRaisesRegex(ValueError, 'ambiguous|overlap'):
            policy.graph.graph(raw, fixtures.BASE, refinement, multiple_switch_profile=policy.SELECTOR)
        descriptor = policy.layout(raw, fixtures.BASE, f[2],
                                   multiple_switch_profile=policy.SELECTOR)['switches'][0]
        with patch.object(policy.match, 'switch_layout', return_value=descriptor):
            with self.assertRaisesRegex(ValueError, 'no unique complete'):
                policy.layout(raw, fixtures.BASE, f[2], multiple_switch_profile=policy.SELECTOR)

    def test_explicit_qualification_and_default_consumers_stay_isolated(self):
        f = self.fixture(); raw = bytes(f[0]); mapping = json.dumps(f[5]).encode()
        with self.assertRaises(ValueError): policy.layout(raw, fixtures.BASE, f[2])
        self.assertFalse(policy.owner.refine(raw, fixtures.BASE, mapping)['cfg_closed'])
        for selector in (True, False, '', native.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                policy.owner.refine(raw, fixtures.BASE, mapping, multiple_switch_profile=selector)
        for name in ('one_object_word_switch', 'two_constant_word_switch',
                     'one_numeric_word_switch', 'arm_inventory', 'stack_adjusted_returns'):
            with self.subTest(flag=name), self.assertRaises(ValueError):
                policy.analyze.refine_function(raw, fixtures.BASE, f[5],
                    multiple_switch_profile=policy.SELECTOR, **{name: True})
        refined = policy.owner.refine(raw, fixtures.BASE, mapping, multiple_switch_profile=policy.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'qualification differs'):
            policy.graph.graph(raw, fixtures.BASE, refined)

    def test_stale_maps_proof_code_and_manifest_refuse(self):
        f = self.fixture(); args = list(fixtures.inputs(f))
        manifest = fixtures.verify(f)
        stale = copy.deepcopy(manifest); stale['producer_sha256']['analyze.py'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            fixtures.verify(f, manifest=stale)
        stale = copy.deepcopy(manifest); stale.pop('backward_case_policy')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            fixtures.verify(f, manifest=stale)
        args[4] += b' '
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            policy.verify(*args, selector=policy.SELECTOR, manifest=manifest)

    def test_changed_call_target_and_role_refuse(self):
        f = self.fixture(); args = list(fixtures.inputs(f))
        # A changed real BL destination in the linked bytes is not authorized by
        # its unchanged original symbol, even if it remains an instruction.
        linked = bytearray(args[1]); image = policy.match.elf_image(args[1])
        at = image['sections'][image['text_index']][4] + f[1]['call']
        linked[at+2] ^= 1; args[1] = bytes(linked)
        with self.assertRaises(ValueError): policy.verify(*args, selector=policy.SELECTOR)
        bindings = dict(calls=[], data=[], functions=f[4]['calls'],
                        switches=[list(row) for row in sorted(f[2].items())])
        with self.assertRaisesRegex(ValueError, 'actual original ELF roles'):
            native.verify_original(*fixtures.inputs(f), bindings)


if __name__ == '__main__':
    unittest.main()
