"""Mutually exclusive wrapper calls preserve descriptor and complete-frame checks."""
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import owner_admission_profile as owner
import scheduler_entry_branch_profile as profile
import scheduler_entry_profile as entry
from test_scheduler_entry import bound, verified, pool_caller
from test_scheduler_predicates import half, bl, A, R0, LOCAL, SAVED


def caller(*, sequential=False, extra_alias=False, offset=0, unbalanced=False,
           wrong_target=False, third=False, pointer_slot=False, bad_return=False):
    data = half(0xB500, 0xB087, 0x2800, 0)
    calls = {}

    def append_call(data, target=entry.POOL, *, unsafe=False):
        data += half(0xAA00 + offset if unsafe else 0xAA00, 0x2108, 0x2300)
        if unsafe and extra_alias:
            data += half(0x1C13)  # r3 = r2
        if unsafe and pointer_slot:
            data += half(0x9200)  # descriptor word contains its own stack alias
        site = A+len(data)
        calls[site] = target
        return data + bl(site, target)

    data = append_call(data)
    skip = len(data)
    data += half(0)
    second = len(data)
    data = append_call(data, entry.DIRECT if wrong_target else entry.POOL, unsafe=True)
    if third:
        data = append_call(data)
    end = len(data)
    data += half(0xB006 if unbalanced else 0xB007, 0xBC02,
                 0x4700 if bad_return else 0x4708)
    data = data[:6] + half(0xD000 | ((second-10)//2)) + data[8:]
    data = data[:skip] + half(0x2100 if sequential else 0xE000 | ((end-skip-4)//2)) + data[skip+2:]
    return data, calls


class EntryBranchGraphTests(unittest.TestCase):
    def test_exclusive_sites_and_no_call_path(self):
        result = profile.phases({0:(2,4,8),2:(8,),4:(8,),8:()}, {2:entry.POOL,4:entry.POOL})
        self.assertEqual(result['scheduler_sites'], [2,4])
        self.assertEqual(result['maximum_scheduler_calls_per_path'], 1)
        self.assertFalse(result['calls_after_scheduler'])

    def test_propagation_uses_cfg_order_and_union_at_join(self):
        profile.phases({0:(60,),60:(20,40),20:(80,),40:(80,),80:()},
                       {20:entry.POOL,40:entry.POOL})
        with self.assertRaisesRegex(ValueError, 'after a scheduler'):
            profile.phases({0:(20,40),20:(40,),40:()}, {20:entry.POOL,40:entry.POOL})

    def test_sequential_sites_refused(self):
        with self.assertRaisesRegex(ValueError, 'after a scheduler'):
            profile.phases({0:(2,),2:(4,),4:()}, {0:entry.POOL,2:entry.POOL})

    def test_cycles_and_unknown_edges_refused(self):
        for edges in ({0:(2,),2:(0,)}, {0:(2,),2:(4,)}):
            with self.subTest(edges=edges), self.assertRaises(ValueError):
                profile.phases(edges, {0:entry.POOL,2:entry.POOL})

    def test_exact_target_and_two_site_budget(self):
        for calls in ({}, {0:entry.POOL}, {0:entry.POOL,2:entry.DIRECT},
                      {0:entry.POOL,2:entry.POOL+2}, {0:entry.POOL,2:entry.POOL,4:entry.POOL},
                      {0:entry.POOL,2:entry.POOL,4:0x08005B6C}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'exactly two pinned'):
                profile.phases({0:(),2:(),4:()}, calls)

    def test_call_site_outside_graph_refused(self):
        with self.assertRaises(ValueError):
            profile.phases({0:()}, {0:entry.POOL,2:entry.POOL})


class EntryBranchReplayTests(unittest.TestCase):
    def test_complete_caller_observes_two_private_descriptors(self):
        data, calls = caller()
        p = verified(data, calls, policy=profile.SELECTOR)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA)
        self.assertEqual(report['entry']['address'], entry.POOL)
        self.assertEqual(sorted(p.dependencies), [entry.DIRECT,entry.POOL])
        self.assertEqual([o['bytes'] for o in report['observations']], [28,28])
        self.assertEqual([o['local_offset'] for o in report['observations']], [-32,-32])
        self.assertEqual(report['branch_calls']['scheduler_sites'], sorted(calls))
        for flag in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):
            self.assertFalse(report[flag])
        self.assertIn('ambient original R9', ' '.join(report['assumptions']))
        self.assertIn('data_020159CC', ' '.join(report['assumptions']))
        self.assertNotEqual(report['entry_source_sha256'], report['source_sha256'])

    def test_old_entry_selector_still_refuses_two_calls(self):
        with self.assertRaisesRegex(ValueError, 'one actual pinned entry'):
            bound(*caller(), policy=entry.SELECTOR)

    def test_new_selector_does_not_replace_single_call_selector(self):
        with self.assertRaisesRegex(ValueError, 'exactly two pinned'):
            bound(*pool_caller(), policy=profile.SELECTOR)

    def test_sequential_and_third_calls_refused(self):
        for options in (dict(sequential=True), dict(third=True)):
            with self.subTest(options=options), self.assertRaises(ValueError):
                bound(*caller(**options), policy=profile.SELECTOR)

    def test_wrong_actual_call_target_refused(self):
        with self.assertRaisesRegex(ValueError, 'exactly two pinned'):
            bound(*caller(wrong_target=True), policy=profile.SELECTOR)

    def test_forged_call_manifest_refused(self):
        data, calls = caller()
        calls[max(calls)] = entry.POOL+2
        with self.assertRaisesRegex(ValueError, 'exclude local BL and switches'):
            bound(data, calls, policy=profile.SELECTOR)

    def test_second_call_extra_register_alias_and_pointer_slot_refused(self):
        for options in (dict(extra_alias=True), dict(pointer_slot=True)):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'additional register or pointer-word'):
                verified(*caller(**options), policy=profile.SELECTOR)

    def test_second_descriptor_crossing_saved_frame_refused(self):
        with self.assertRaises(ValueError):
            verified(*caller(offset=1), policy=profile.SELECTOR)

    def test_unbalanced_frame_and_wrong_return_provenance_refused(self):
        for options in (dict(unbalanced=True), dict(bad_return=True)):
            with self.subTest(options=options), self.assertRaises(ValueError):
                verified(*caller(**options), policy=profile.SELECTOR)

    def test_changed_dependency_identity_refused(self):
        with self.assertRaisesRegex(ValueError, 'dependency identity differs'):
            bound(*caller(), policy=profile.SELECTOR,
                  pins={entry.POOL:(44,'0'*64)})

    def test_every_site_requires_observation_and_consistent_aliases(self):
        p = bound(*caller(), policy=profile.SELECTOR)
        sites = sorted(p.calls)
        with self.assertRaises(ValueError):
            p.contract_manifest()
        p.check_call(entry.POOL, {R0+2:-32}, [LOCAL]*7+[SAVED], {}, site=sites[0])
        with self.assertRaises(ValueError):
            p.contract_manifest()
        with self.assertRaisesRegex(ValueError, 'differs across incoming paths'):
            p.check_call(entry.POOL, {R0+2:-36}, [LOCAL]*8+[SAVED], {}, site=sites[0])

    def test_word_provenance_and_unknown_site_refused(self):
        p = bound(*caller(), policy=profile.SELECTOR)
        site = min(p.calls)
        for options in (dict(site=site,words={R0:'opaque'}), dict(site=site+2)):
            with self.subTest(options=options), self.assertRaises(ValueError):
                p.check_call(entry.POOL,{R0+2:-32},[LOCAL]*7+[SAVED],{},**options)

    def test_selector_registration_and_report_replay_dispatch(self):
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'), profile.SELECTOR)
        run = subprocess.run([sys.executable,'-B',str(Path(match.__file__)),
                              '--owner-runtime-profile',profile.SELECTOR,'--help'],
                             capture_output=True,text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


if __name__ == '__main__':
    unittest.main()
