"""New following-call fixtures; prior successful producer tests are not replayed."""
import hashlib
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_branch_profile as branch
import owner_admission_profile as owner
from test_scheduler_predicates import half, bl, fixture, A, B, C, R0, LOCAL, SAVED

# A stand-in for the pinned scheduler that is a function: callers keep stack addresses in
# R4-R11 across it, and the callee-saved check walks it (kit #350). 29 x movs r0,r0; bx lr.
SCHEDULER_STUB = bytes(58) + b'\x70\x47'

S=branch.SCHEDULER
SELECTOR=local.SCHEDULER_FOLLOWING


def raw_caller(*, preserved_alias=False, reintroduce_alias=False, following_target=B):
    data=half(0xB530,0xB087,0xAA00,0x2000,0x2118,0x2300)
    if preserved_alias:data+=half(0x466C)
    first=A+len(data);data+=bl(first,S)
    data+=half(0x4669 if reintroduce_alias else 0x1C29)
    second=A+len(data);data+=bl(second,following_target)
    data+=half(0xB007,0xBC30,0xBC02,0x4708)
    return data,{first:S,second:following_target}


def bound(data,calls,policy=SELECTOR):
    bodies={A:data,B:half(0x4770),S: SCHEDULER_STUB,0x08005954:bytes(206)}
    p=fixture(bodies,policy=policy);span=p.span
    runtimes=set(match.function_thunk.ALIASES.values())
    p.span=lambda a:half(0x4710) if a in runtimes else span(a)
    pins={a:(len(b),hashlib.sha256(b).hexdigest()) for a,b in bodies.items() if a in (S,0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES,pins),mock.patch.object(local.thunk,'dependencies',return_value=[]):
        p.bind_root(data,A,calls)
    return p


def context():
    p=object.__new__(local.ConditionalLocalBufferProof)
    p.policy=SELECTOR;p.calls={100:S,200:B};p.branch_calls={'ordinary_targets':[B]}
    p.observations={};p.environment={};p.runtime_dependencies=[]
    return p


class FollowingCallTests(unittest.TestCase):
    def test_complete_raw_frame_scheduler_then_ordinary_call(self):
        data,calls=raw_caller();p=bound(data,calls)
        self.assertTrue(match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p))
        report=p.contract_manifest();self.assertEqual(len(report['observations']),2)
        self.assertTrue(report['branch_calls']['ordinary_calls_after_scheduler'])
        self.assertEqual(report['branch_calls']['following_ordinary_sites'],[max(calls)])
        self.assertEqual(set(p.records),{B,S,0x08005954})

    def test_old_branch_selector_still_refuses_same_raw_caller(self):
        data,calls=raw_caller()
        with self.assertRaisesRegex(ValueError,'after a scheduler return'):bound(data,calls,local.SCHEDULER_BRANCH)

    def test_old_single_scheduler_selector_still_refuses_same_raw_caller(self):
        data,calls=raw_caller()
        with self.assertRaisesRegex(ValueError,'one actual scheduler call'):bound(data,calls,local.SCHEDULER)

    def test_preserved_local_alias_cannot_enter_following_helper(self):
        data,calls=raw_caller(preserved_alias=True);p=bound(data,calls)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_reintroduced_caller_clobbered_alias_cannot_enter_following_helper(self):
        data,calls=raw_caller(reintroduce_alias=True);p=bound(data,calls)
        with self.assertRaisesRegex(ValueError,'every live local alias'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)

    def test_full_ordinary_interface_refuses_slots_and_word_provenance(self):
        for slots,words in (({-24:-40},None),({}, {-40:'opaque'})):
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context().check_call(B,{},[LOCAL]*7+[SAVED]*3,slots,site=200,words=words)

    def test_unknown_site_or_target_refused(self):
        for target,site in ((B,202),(C,200)):
            with self.subTest(target=target),self.assertRaises(ValueError):
                context().check_call(target,{},[],site=site)

    def test_scheduler_still_requires_only_r2_descriptor(self):
        for aliases in ({},{R0+2:-40,R0:-40}):
            with self.subTest(aliases=aliases),self.assertRaises(ValueError):
                context().check_call(S,aliases,[LOCAL]*7+[SAVED]*3,site=100)

    def test_scheduler_descriptor_must_fit_private_frame(self):
        with self.assertRaises(ValueError):
            context().check_call(S,{R0+2:-36},[LOCAL]*7+[SAVED]*3,site=100)

    def test_following_calls_are_opt_in_boolean(self):
        edges={0:(2,),2:()};calls={0:S,2:B}
        for flag in (1,None,'yes'):
            with self.subTest(flag=flag),self.assertRaises(ValueError):branch.phases(edges,calls,following_calls=flag)
        with self.assertRaises(ValueError):branch.phases(edges,calls)

    def test_ordinary_before_and_after_preserves_call_order(self):
        result=branch.phases({0:(2,),2:(4,),4:()},{0:B,2:S,4:B},following_calls=True)
        self.assertEqual(result['following_ordinary_sites'],[4])
        self.assertEqual(result['maximum_scheduler_calls_per_path'],1)

    def test_multiple_following_calls_are_all_recorded(self):
        result=branch.phases({0:(2,),2:(4,),4:()},{0:S,2:B,4:C},following_calls=True)
        self.assertEqual(result['following_ordinary_sites'],[2,4])

    def test_second_scheduler_on_path_refused(self):
        with self.assertRaises(ValueError):branch.phases({0:(2,),2:(4,),4:()},{0:S,2:B,4:S},following_calls=True)

    def test_two_scheduler_sites_on_disjoint_arms_refused(self):
        with self.assertRaises(ValueError):
            branch.phases({0:(2,4),2:(6,),4:(6,),6:()},{2:S,4:S,6:B},following_calls=True)

    def test_following_site_required(self):
        with self.assertRaises(ValueError):branch.phases({0:(2,),2:()},{0:B,2:S},following_calls=True)

    def test_cycle_refused(self):
        with self.assertRaises(ValueError):branch.phases({0:(2,),2:(0,)},{0:S,2:B},following_calls=True)

    def test_join_retains_scheduler_path(self):
        result=branch.phases({0:(2,4),2:(6,),4:(6,),6:()},{2:S,6:B},following_calls=True)
        self.assertEqual(result['following_ordinary_sites'],[6])

    def test_call_site_budget_refused(self):
        edges={i:(i+2,) for i in range(0,16,2)};edges[16]=()
        with self.assertRaises(ValueError):branch.phases(edges,{i:S if i==0 else B for i in edges},following_calls=True)

    def test_runtime_or_reserved_following_target_refused(self):
        for target in (next(iter(match.RUNTIME_HELPERS.values())),match.function_thunk.ALIASES['_call_via_r2']):
            data,calls=raw_caller(following_target=target)
            with self.subTest(target=target),self.assertRaises(ValueError):bound(data,calls)

    def test_manifest_preserves_effect_nonescape_and_termination_conditions(self):
        data,calls=raw_caller();p=bound(data,calls)
        match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p)
        report=p.contract_manifest()
        for flag in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):self.assertFalse(report[flag])
        self.assertFalse(report['branch_calls']['ordinary_callee_effects_proved'])
        self.assertFalse(report['branch_calls']['nested_execution_proved'])
        self.assertIn('No tracked local-register alias',report['branch_calls']['ordinary_call_contract'])

    def test_every_call_must_be_observed(self):
        p=context();p.check_call(S,{R0+2:-40},[LOCAL]*7+[SAVED]*3,site=100)
        with self.assertRaises(ValueError):p.contract_manifest()

    def test_native_report_and_CLI_paths_registered(self):
        self.assertIn(SELECTOR,owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `elf-symbol-thumb-'+SELECTOR+'`'),SELECTOR)
        self.assertTrue(match._ordinary_call_replay(context(),B))
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--owner-runtime-profile',SELECTOR,'--help'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)


if __name__=='__main__':unittest.main()
