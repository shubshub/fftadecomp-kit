"""Bounded extended call inventories retain every frame and alias obligation."""
import hashlib
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_branch_profile as branch
import owner_admission_profile as owner
from test_scheduler_predicates import half, bl, fixture, A, B, R0, LOCAL, SAVED

S = branch.SCHEDULER
SELECTOR = local.SCHEDULER_24
TARGETS = tuple(B + 0x20*i for i in range(25))


def graph(count=24, sites=None):
    targets = list(TARGETS[:count])
    if sites is not None:
        targets += [targets[0]]*(sites-len(targets)-1)
    targets.append(S)
    edges = {2*i: (2*i+2,) for i in range(len(targets)-1)}
    edges[2*(len(targets)-1)] = ()
    return edges, {2*i:t for i,t in enumerate(targets)}


def caller(*, count=24, alias_at=None, saved_alias=False):
    data = half(0xB510, 0xB087)
    calls = {}
    for i, target in enumerate(TARGETS[:count]):
        if i == alias_at:
            data += half(0xAC00 if saved_alias else 0xA800)
        site = A+len(data)
        calls[site] = target
        data += bl(site, target)
    data += half(0xAA00)
    site = A+len(data)
    calls[site] = S
    data += bl(site, S)+half(0xB007, 0xBC10, 0xBC02, 0x4708)
    return data, calls


def bound(data, calls, policy=SELECTOR):
    bodies = {A:data, **{t:half(0x6008, 0x4770) for t in TARGETS},
              S:bytes(60), 0x08005954:bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtime = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtime else span(a)
    pins = {a:(len(b),hashlib.sha256(b).hexdigest()) for a,b in bodies.items()
            if a in (S,0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES,pins), mock.patch.object(local.thunk,'dependencies',return_value=[]):
        p.bind_root(data,A,calls)
    return p


class TwentyFourTargetTests(unittest.TestCase):
    def test_complete_raw_twenty_four_helpers_and_scheduler_frame(self):
        data,calls=caller();p=bound(data,calls)
        self.assertTrue(match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p))
        report=p.contract_manifest()
        self.assertEqual(len(report['observations']),25)
        self.assertEqual(set(p.records),set(TARGETS[:24])|{S,0x08005954})
        self.assertEqual(p.dependency_budget,28)
        self.assertEqual(report['branch_calls']['ordinary_target_budget'],24)

    def test_old_branch_selector_keeps_four_target_limit(self):
        data,calls=caller(count=5)
        with self.assertRaisesRegex(ValueError,'bounds'):bound(data,calls,local.SCHEDULER_BRANCH)

    def test_eight_target_selector_retains_its_limits(self):
        data,calls=caller(count=9)
        with self.assertRaisesRegex(ValueError,'bounds'):bound(data,calls,local.SCHEDULER_WIDE)
        edges,calls=graph(count=8,sites=13)
        with self.assertRaisesRegex(ValueError,'bounds'):branch.phases(edges,calls,wide_targets=True)

    def test_no_combination_with_eight_targets(self):
        edges,calls=graph()
        with self.assertRaises(ValueError):
            branch.phases(edges,calls,wide_targets=True,twenty_four_targets=True)

    def test_following_selector_keeps_four_target_limit(self):
        edges,calls=graph(count=5)
        with self.assertRaisesRegex(ValueError,'bounds'):branch.phases(edges,calls,following_calls=True)

    def test_twenty_fifth_target_is_refused(self):
        data,calls=caller(count=25)
        with self.assertRaisesRegex(ValueError,'bounds'):bound(data,calls)

    def test_thirty_two_call_sites_are_bounded_and_thirty_third_refused(self):
        edges,calls=graph(sites=32)
        self.assertEqual(branch.phases(edges,calls,twenty_four_targets=True)['call_site_budget'],32)
        edges,calls=graph(sites=33)
        with self.assertRaisesRegex(ValueError,'bounds'):branch.phases(edges,calls,twenty_four_targets=True)

    def test_late_caller_clobbered_alias_is_not_skipped(self):
        data,calls=caller(alias_at=23);p=bound(data,calls)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_callee_saved_alias_is_not_lost_across_helper_sequence(self):
        data,calls=caller(alias_at=4,saved_alias=True);p=bound(data,calls)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_pointer_words_and_opaque_word_facts_refused_at_twenty_fourth_helper(self):
        data,calls=caller()
        for slots,words in (({-36:-32},None),({}, {-36:'opaque'})):
            p=bound(data,calls);site=next(s for s,t in calls.items() if t==TARGETS[23])
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                p.check_call(TARGETS[23],{},[LOCAL]*7+[SAVED]*2,slots,site=site,words=words)

    def test_scheduler_retains_exact_descriptor_alias_and_private_bounds(self):
        data,calls=caller();site=max(calls)
        for aliases in ({R0+2:-32},{R0+2:-36,R0:-36},{}):
            p=bound(data,calls)
            with self.subTest(aliases=aliases),self.assertRaises(ValueError):
                p.check_call(S,aliases,[LOCAL]*7+[SAVED]*2,site=site)

    def test_unknown_call_site_and_changed_target_refused(self):
        data,calls=caller();p=bound(data,calls)
        for target,site in ((TARGETS[0],A),(TARGETS[24],min(calls))):
            with self.subTest(site=site),self.assertRaises(ValueError):p.check_call(target,{},[],site=site)

    def test_missing_twenty_fourth_complete_indexed_body_refused(self):
        edges,calls=graph();p=fixture({t:half(0x4770) for t in TARGETS[:23]},policy=SELECTOR)
        with self.assertRaises(ValueError):branch.bind(p,edges,calls,twenty_four_targets=True)

    def test_overlapping_twenty_fourth_body_refused(self):
        edges,calls=graph();p=fixture({**{t:half(0x2000,0x4770) for t in TARGETS[:24]},
            TARGETS[23]+2:half(0x4770)},policy=SELECTOR)
        with self.assertRaises(ValueError):branch.bind(p,edges,calls,twenty_four_targets=True)

    def test_runtime_and_thunk_targets_cannot_use_wider_inventory(self):
        for target in (next(iter(match.RUNTIME_HELPERS.values())),match.function_thunk.ALIASES['_call_via_r2']):
            p=fixture({B:half(0x4770)},policy=SELECTOR)
            with self.subTest(target=target),self.assertRaises(ValueError):
                branch.bind(p,{0:(2,),2:()},{0:target,2:S},twenty_four_targets=True)

    def test_cyclic_root_is_refused(self):
        with self.assertRaises(ValueError):branch.phases({0:(2,),2:(0,)},{0:B,2:S},twenty_four_targets=True)

    def test_unknown_graph_edge_is_refused(self):
        with self.assertRaises(ValueError):branch.phases({0:(2,),2:(4,)},{0:B,2:S},twenty_four_targets=True)

    def test_calls_after_scheduler_remain_refused_even_at_join(self):
        with self.assertRaisesRegex(ValueError,'after a scheduler'):
            branch.phases({0:(2,4),2:(4,),4:()},{2:S,4:B},twenty_four_targets=True)

    def test_second_scheduler_on_path_remains_refused(self):
        with self.assertRaisesRegex(ValueError,'after a scheduler'):
            branch.phases({0:(2,),2:(4,),4:()},{0:B,2:S,4:S},twenty_four_targets=True)

    def test_two_disjoint_scheduler_arms_remain_supported(self):
        r=branch.phases({0:(2,4),2:(),4:()},{0:B,2:S,4:S},twenty_four_targets=True)
        self.assertEqual(r['maximum_scheduler_calls_per_path'],1)

    def test_no_hidden_combined_or_truthy_selector(self):
        edges,calls=graph()
        for flag in (1,None,'yes'):
            with self.subTest(flag=flag),self.assertRaises(ValueError):branch.phases(edges,calls,twenty_four_targets=flag)
        with self.assertRaises(ValueError):branch.phases(edges,calls,twenty_four_targets=True,following_calls=True)

    def test_manifest_requires_all_sites_observed(self):
        data,calls=caller();p=bound(data,calls)
        p.check_call(S,{R0+2:-36},[LOCAL]*7+[SAVED]*2,site=max(calls))
        with self.assertRaises(ValueError):p.contract_manifest()

    def test_effect_lifetime_and_termination_conditions_remain_explicit(self):
        data,calls=caller();p=bound(data,calls)
        match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)
        report=p.contract_manifest()
        for field in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):
            self.assertFalse(report[field])
        for field in ('ordinary_callee_effects_proved','nested_execution_proved','ordinary_calls_after_scheduler'):
            self.assertFalse(report['branch_calls'][field])
        self.assertIn('allocation separation',report['branch_calls']['ordinary_call_contract'])

    def test_three_disjoint_scheduler_sites_remain_refused(self):
        with self.assertRaisesRegex(ValueError,'bounds'):
            branch.phases({0:(2,4,6),2:(),4:(),6:()},
                          {0:B,2:S,4:S,6:S},twenty_four_targets=True)

    def test_complete_root_must_restore_frame_and_entry_return(self):
        data,calls=caller()
        for broken in (data[:-8]+half(0xB006)+data[-6:], data[:-2]+half(0x4700)):
            with self.subTest(body=broken.hex()),self.assertRaises(ValueError):
                p=bound(broken,calls)
                match.verify_leaf_instructions(broken,A,True,calls,buffer_proof=p)

    def test_dependency_budget_is_specific_to_new_selector(self):
        bodies={B:half(0x4770)}
        self.assertEqual(fixture(bodies,policy=local.SCHEDULER_24).dependency_budget,28)
        self.assertEqual(fixture(bodies,policy=local.SCHEDULER_WIDE).dependency_budget,12)
        self.assertLess(fixture(bodies,policy=local.SCHEDULER_BRANCH).dependency_budget,28)

    def test_native_CLI_report_and_replay_registration(self):
        data,calls=caller();p=bound(data,calls)
        self.assertTrue(match._ordinary_call_replay(p,B))
        self.assertIn(SELECTOR,owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `elf-symbol-thumb-'+SELECTOR+'`'),SELECTOR)
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--owner-runtime-profile',SELECTOR,'--help'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)


if __name__=='__main__':unittest.main()
