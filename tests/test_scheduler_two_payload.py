"""Independent frame layouts and raw Thumb integration for two payloads."""
import hashlib
import itertools
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_two_payload_profile as profile
import owner_admission_profile as owner
from test_scheduler_predicates import half, bl, fixture, A, R0, LOCAL, SAVED

# A stand-in for the pinned scheduler that is a function: callers keep stack addresses in
# R4-R11 across it, and the callee-saved check walks it (kit #350). 29 x movs r0,r0; bx lr.
SCHEDULER_STUB = bytes(58) + b'\x70\x47'

S = profile.SCHEDULER
STACK = [LOCAL]*15+[SAVED]*3
BASE, DESCRIPTOR = -72, -44
SLOTS = {DESCRIPTOR+4: BASE, DESCRIPTOR+8: -16}


def context(policy=profile.SELECTOR):
    p = object.__new__(local.ConditionalLocalBufferProof)
    p.policy, p.calls = policy, {100:S}
    p.observations, p.environment, p.runtime_dependencies = {}, {}, []
    return p


def raw_caller(words, descriptor_word, first_word, second_word, *, partial=False, escape=False):
    data = half(0xB530, 0xB080+words, 0xAA00+descriptor_word,
                0xAC00+first_word, 0xAD00+second_word,
                0x8054 if partial else 0x6054, 0x6095,
                0x2000, 0x2114, 0x2300)
    if escape:
        data += half(0x1C23)  # R3 still aliases payload at call.
    site = A+len(data)
    return data+bl(site, S)+half(0xB000+words, 0xBC30, 0xBC02, 0x4708), {site:S}


def bound(data, calls, policy=profile.SELECTOR):
    bodies = {A:data, S: SCHEDULER_STUB, 0x08005954:bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a:(len(b),hashlib.sha256(b).hexdigest()) for a,b in bodies.items() if a != A}
    with mock.patch.dict(local.DEPENDENCIES,pins), mock.patch.object(local.thunk,'dependencies',return_value=[]):
        p.bind_root(data,A,calls)
    return p


class TwoPayloadTests(unittest.TestCase):
    def test_raw_descriptor_between_28_and_4_byte_payloads(self):
        data,calls=raw_caller(15,7,0,14)
        p=bound(data,calls)
        self.assertTrue(match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p))
        observation=p.contract_manifest()['observations'][0]
        self.assertEqual([x['frame_bound_bytes'] for x in observation['frame']['payloads']],[28,4])
        self.assertEqual(observation['aliases'],[(R0+2,-44),(R0+4,-72),(R0+5,-16)])

    def test_raw_descriptor_before_two_8_byte_payloads(self):
        data,calls=raw_caller(11,0,7,9)
        p=bound(data,calls)
        self.assertTrue(match.verify_leaf_instructions(data,A,True,calls,buffer_proof=p))
        self.assertEqual([x['frame_bound_bytes'] for x in p.contract_manifest()['observations'][0]['frame']['payloads']],[8,8])

    def test_all_object_orders_and_field_permutations_have_disjoint_coverage(self):
        for order in itertools.permutations(('descriptor','p4','p8')):
            sizes={'descriptor':28,'p4':12,'p8':8};cursor=-60;starts={}
            for obj in order:starts[obj]=cursor;cursor+=sizes[obj]
            frame=profile.layout([LOCAL]*12+[SAVED]*3,starts['descriptor'],
                {starts['descriptor']+4:starts['p4'],starts['descriptor']+8:starts['p8']})
            actual={x['descriptor_field']:x['frame_bound_bytes'] for x in frame['payloads']}
            self.assertEqual(actual,{4:12,8:8})

    def test_duplicate_payload_start_refused(self):
        with self.assertRaises(ValueError):profile.layout(STACK,DESCRIPTOR,{DESCRIPTOR+4:BASE,DESCRIPTOR+8:BASE})

    def test_payload_inside_descriptor_refused(self):
        with self.assertRaises(ValueError):profile.layout(STACK,DESCRIPTOR,{DESCRIPTOR+4:BASE,DESCRIPTOR+8:DESCRIPTOR+24})

    def test_missing_extra_and_wrong_field_pointer_words_refused(self):
        for slots in ({},{DESCRIPTOR+4:BASE},{**SLOTS,BASE:-16},{DESCRIPTOR+12:BASE,DESCRIPTOR+8:-16}):
            with self.subTest(slots=slots),self.assertRaises(ValueError):profile.layout(STACK,DESCRIPTOR,slots)

    def test_saved_incoming_unaligned_and_outside_pointer_refused(self):
        for offset in (-12,0,BASE-4,BASE+1):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                profile.layout(STACK,DESCRIPTOR,{DESCRIPTOR+4:offset,DESCRIPTOR+8:-16})

    def test_frame_gaps_and_protected_words_refused(self):
        for stack in ([LOCAL]*7+[SAVED]+[LOCAL]*7+[SAVED]*2,
                      [(True,False,True)]+STACK[1:],[(False,True,True)]+STACK[1:]):
            with self.subTest(stack=stack),self.assertRaises(ValueError):profile.layout(stack,DESCRIPTOR,SLOTS)

    def test_private_budget_refused(self):
        with self.assertRaises(ValueError):profile.layout([LOCAL]*65+[SAVED],-264,{-260:-236,-256:-232})

    def test_uncovered_private_prefix_refused(self):
        with self.assertRaises(ValueError):profile.layout(STACK,DESCRIPTOR,{DESCRIPTOR+4:BASE+4,DESCRIPTOR+8:-16})

    def test_descriptor_gap_or_oversize_refused(self):
        with self.assertRaises(ValueError):profile.layout(STACK,DESCRIPTOR-4,{DESCRIPTOR:BASE,DESCRIPTOR+4:-16})

    def test_preserved_alias_must_still_be_private(self):
        with self.assertRaises(ValueError):context().check_call(S,{R0+2:DESCRIPTOR,R0+4:-12},STACK,SLOTS,site=100)

    def test_other_outgoing_alias_refused_in_real_caller(self):
        data,calls=raw_caller(11,0,7,9,escape=True)
        with self.assertRaisesRegex(ValueError,'outgoing register aliases'):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=bound(data,calls))

    def test_partial_pointer_store_refused_in_real_caller(self):
        data,calls=raw_caller(11,0,7,9,partial=True)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(data,A,True,calls,buffer_proof=bound(data,calls))

    def test_old_one_payload_selector_still_refuses_two_payloads(self):
        data,calls=raw_caller(11,0,7,9)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(data,A,True,calls,buffer_proof=bound(data,calls,local.SCHEDULER_PAYLOAD))

    def test_root_wrong_target_or_extra_call_refused(self):
        data,calls=raw_caller(11,0,7,9)
        for alternate in ({next(iter(calls)):S+2},{**calls,A:S}):
            with self.subTest(alternate=alternate),self.assertRaises(ValueError):bound(data,alternate)

    def test_wrong_site_word_facts_and_absent_descriptor_refused(self):
        for args in ({'site':102},{'site':100,'words':{BASE:'opaque'}}):
            with self.subTest(args=args),self.assertRaises(ValueError):
                context().check_call(S,{R0+2:DESCRIPTOR},STACK,SLOTS,**args)
        with self.assertRaises(ValueError):context().check_call(S,{},STACK,SLOTS,site=100)

    def test_changed_path_state_refused_and_identical_observation_idempotent(self):
        p=context();aliases={R0+2:DESCRIPTOR}
        p.check_call(S,aliases,STACK,SLOTS,site=100)
        p.check_call(S,aliases,STACK,SLOTS,site=100)
        self.assertEqual(len(p.observations),1)
        with self.assertRaises(ValueError):p.check_call(S,{**aliases,R0+4:BASE},STACK,SLOTS,site=100)

    def test_manifest_retains_all_conditional_boundaries(self):
        p=context()
        with self.assertRaises(ValueError):p.contract_manifest()
        p.check_call(S,{R0+2:DESCRIPTOR},STACK,SLOTS,site=100)
        report=p.contract_manifest();text=' '.join(report['assumptions'])
        for flag in ('actual_callback_effects_proved','physical_memory_claim','nonescape_proved','termination_proved'):
            self.assertFalse(report[flag])
        for word in ('Unknown','separate from every caller stack word','ambient original R9','before the scheduler returns'):
            self.assertIn(word,text)

    def test_native_report_and_CLI_registration(self):
        self.assertIn(profile.SELECTOR,owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'),profile.SELECTOR)
        self.assertTrue(match._ordinary_call_replay(context(),S))
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--owner-runtime-profile',profile.SELECTOR,'--help'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)


if __name__=='__main__':unittest.main()
