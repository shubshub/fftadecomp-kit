"""Full bounded following-call composition preserves frame and identity gates."""
from pathlib import Path
import subprocess
import sys
import unittest

from test_scheduler_twenty_four_targets import caller, bound, graph, TARGETS, S
from test_scheduler_predicates import half, bl, A, B, R0, LOCAL, SAVED
import match
import conditional_local_buffer_profile as local
import scheduler_branch_profile as branch
import owner_admission_profile as owner

SELECTOR = local.SCHEDULER_24_FOLLOWING


def following(*, alias=None, count=24, sites=32):
    data,calls=caller(count=count)
    tail=data[-8:]
    data=data[:-8]
    for i in range(sites-len(calls)):
        if alias is not None and i==0:
            data+=half(alias)
        site=A+len(data)
        calls[site]=TARGETS[i%count]
        data+=bl(site,calls[site])
    return data+tail,calls


class TwentyFourFollowingTests(unittest.TestCase):
    def test_full_bounds_complete_native_frame_and_manifest(self):
        data,calls=following();p=bound(data,calls,SELECTOR)
        self.assertTrue(match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p))
        manifest=p.contract_manifest();r=manifest['branch_calls']
        self.assertEqual(len(calls),32)
        self.assertEqual(len(r['ordinary_targets']),24)
        self.assertEqual(r['call_site_budget'],32)
        self.assertEqual(r['ordinary_target_budget'],24)
        self.assertEqual(len(r['scheduler_sites']),1)
        self.assertEqual(len(r['following_ordinary_sites']),7)
        self.assertEqual(p.dependency_budget,28)
        for field in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):
            self.assertFalse(manifest[field])
        for field in ('ordinary_callee_effects_proved','nested_execution_proved'):
            self.assertFalse(r[field])
        self.assertIn('No tracked local-register alias',r['ordinary_call_contract'])

    def test_old_selectors_retain_bounds_and_no_following_rule(self):
        data,calls=following()
        for policy in (local.SCHEDULER_FOLLOWING,local.SCHEDULER_24,local.SCHEDULER_WIDE):
            with self.subTest(policy=policy),self.assertRaises(ValueError):bound(data,calls,policy)

    def test_budget_excesses_refused(self):
        for count,sites in ((25,32),(24,33)):
            data,calls=following(count=count,sites=sites)
            with self.subTest(count=count,sites=sites),self.assertRaises(ValueError):bound(data,calls,SELECTOR)

    def test_following_call_required(self):
        data,calls=caller()
        with self.assertRaisesRegex(ValueError,'reached following ordinary call'):bound(data,calls,SELECTOR)

    def test_exactly_one_scheduler_site(self):
        for edges,calls in (({0:(2,),2:(4,),4:()},{0:S,2:S,4:B}),
                            ({0:(2,4),2:(6,),4:(6,),6:()},{2:S,4:S,6:B})):
            with self.subTest(calls=calls),self.assertRaises(ValueError):
                branch.phases(edges,calls,twenty_four_following_calls=True)

    def test_existing_flag_combinations_still_refused(self):
        edges,calls=graph()
        for flags in (dict(following_calls=True,twenty_four_targets=True),
                      dict(following_calls=True,wide_targets=True)):
            with self.subTest(flags=flags),self.assertRaises(ValueError):branch.phases(edges,calls,**flags)
        for name in ('following_calls','wide_targets','twenty_four_targets'):
            with self.subTest(name=name),self.assertRaises(ValueError):
                branch.phases(edges,calls,twenty_four_following_calls=True,**{name:True})
        for value in (None,1,'yes'):
            with self.subTest(value=value),self.assertRaises(ValueError):
                branch.phases(edges,calls,twenty_four_following_calls=value)

    def test_following_aliases_not_discarded(self):
        for alias in (0xA800,0xAC00):
            data,calls=following(alias=alias);p=bound(data,calls,SELECTOR)
            with self.subTest(alias=alias),self.assertRaisesRegex(ValueError,'every live local alias'):
                match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_prior_aliases_not_discarded(self):
        data,calls=caller(alias_at=23);site=A+len(data)-8
        data=data[:-8]+bl(site,B)+data[-8:];calls[site]=B
        p=bound(data,calls,SELECTOR)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_following_slots_and_word_facts_refused(self):
        data,calls=following()
        for slots,words in (({-36:-32},None),({}, {-36:'opaque'})):
            p=bound(data,calls,SELECTOR)
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                p.check_call(calls[max(calls)],{},[LOCAL]*7+[SAVED]*2,slots,site=max(calls),words=words)

    def test_scheduler_descriptor_stays_exact_and_private(self):
        data,calls=following();site=next(s for s,t in calls.items() if t==S)
        for aliases in ({R0+2:-32},{R0+2:-36,R0:-36},{}):
            p=bound(data,calls,SELECTOR)
            with self.subTest(aliases=aliases),self.assertRaises(ValueError):
                p.check_call(S,aliases,[LOCAL]*7+[SAVED]*2,site=site)

    def test_saved_frame_and_entry_return_preserved(self):
        data,calls=following()
        for broken in (data[:-8]+half(0xB006)+data[-6:],data[:-2]+half(0x4700)):
            with self.subTest(body=broken.hex()),self.assertRaises(ValueError):
                p=bound(broken,calls,SELECTOR)
                match.verify_leaf_instructions(broken,A,True,calls,buffer_proof=p)

    def test_complete_call_observation_and_target_identity(self):
        data,calls=following();p=bound(data,calls,SELECTOR)
        with self.assertRaises(ValueError):p.contract_manifest()
        for target,site in ((TARGETS[24],max(calls)),(B,A)):
            with self.subTest(target=target),self.assertRaises(ValueError):p.check_call(target,{},[],site=site)

    def test_runtime_or_thunk_ordinary_targets_still_refused(self):
        for target in (next(iter(match.RUNTIME_HELPERS.values())),match.function_thunk.ALIASES['_call_via_r2']):
            data,calls=following();site=max(calls);calls[site]=target
            data=data[:site-A]+bl(site,target)+data[site-A+4:]
            with self.subTest(target=target),self.assertRaises(ValueError):bound(data,calls,SELECTOR)

    def test_cyclic_and_unknown_edge_roots_refused(self):
        for edges in ({0:(2,),2:(0,)},{0:(2,),2:(4,)}):
            with self.subTest(edges=edges),self.assertRaises(ValueError):
                branch.phases(edges,{0:S,2:B},twenty_four_following_calls=True)

    def test_join_retains_scheduler_path_and_following_obligation(self):
        r=branch.phases({0:(2,4),2:(6,),4:(6,),6:()},{2:S,6:B},twenty_four_following_calls=True)
        self.assertEqual(r['following_ordinary_sites'],[6])
        self.assertTrue(r['ordinary_calls_after_scheduler'])

    def test_native_report_replay_and_CLI_registration(self):
        data,calls=following();p=bound(data,calls,SELECTOR)
        self.assertTrue(match._ordinary_call_replay(p,B))
        self.assertIn(SELECTOR,owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `elf-symbol-thumb-'+SELECTOR+'`'),SELECTOR)
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--owner-runtime-profile',SELECTOR,'--help'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)


if __name__=='__main__':unittest.main()
