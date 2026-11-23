"""New composition fixtures; old successful producer suites are not replayed."""
import hashlib
import json
from pathlib import Path
import sys
import subprocess
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import conditional_local_buffer_profile as local
import scheduler_halfword_payload_profile as profile
from test_scheduler_predicates import half, bl, A, B, R0, LOCAL, SAVED

# A stand-in for the pinned scheduler that is a function: callers keep stack addresses in
# R4-R11 across it, and the callee-saved check walks it (kit #350). 29 x movs r0,r0; bx lr.
SCHEDULER_STUB = bytes(58) + b'\x70\x47'

S = profile.SCHEDULER
LEAF = half(0x4B02, 0x8C9A, 0x8002, 0x8CD8, 0x8008, 0x4770, 0x7F40, 0x0200)
STACK = [LOCAL]*13 + [SAVED]*5
BASE, DESCRIPTOR, OUTPUTS = -72, -52, -24


def context():
    p = object.__new__(local.ConditionalLocalBufferProof)
    p.policy, p.calls = profile.SELECTOR, {100: profile.leaf.IDENTITY[0], 200: S}
    p.observations, p.environment, p.runtime_dependencies = {}, {}, []
    p.halfword_payload = dict(incoming_registers=[R0, R0+1], written_registers=[R0, R0+2, R0+3])
    return p


def raw_caller(*, bad_return_alias=False):
    data = half(0xB530, 0xB08D, 0x466B, 0x2A00, 0)
    data += half(0xAC0C, 0x466D, 0x3532, 0x1C20, 0x1C29)
    helper = A+len(data)
    data += bl(helper, B)
    # A partial store through returned R1 must still be recognized as a stack
    # pointer and refuse an out-of-frame access, rather than become arbitrary.
    if bad_return_alias:
        data += half(0x31FF, 0x8008)
    else:
        data += half(0x8820, 0x4669)
    join = A+len(data)
    data = data[:8] + half(0xD000 | ((join-(A+8)-4)//2)) + data[10:]
    data += half(0xAA05, 0x4668, 0x6050, 0x2000, 0x211C, 0x2300)
    scheduler = A+len(data)
    data += bl(scheduler, S) + half(0xB00D, 0xBC30, 0xBC02, 0x4708)
    return data, {helper: B, scheduler: S}


def bound(data, calls, *, leaf_data=LEAF, helper_count=6, policy=profile.SELECTOR):
    # The output helper is fully proved from actual instructions and exact dual
    # indexes at a synthetic address. Only the old conditional scheduler byte
    # identities/runtime transport are substituted; caller frame replay is real.
    bodies = {A: data, B: leaf_data, S: SCHEDULER_STUB, 0x08005954: bytes(206)}
    rom = bytearray(max(a+len(b) for a, b in bodies.items())-match.ROM_BASE)
    rows, lines = [], []
    for a, b in sorted(bodies.items()):
        rom[a-match.ROM_BASE:a-match.ROM_BASE+len(b)] = b
        count = helper_count if a == B else 0
        rows.append(dict(rom=f'0x{a:08X}', end=f'0x{a+len(b):08X}', mode='thumb', instrs=count))
        lines.append(f'{a:08X} {a+len(b):08X} {len(b)} {count} return\n')
    objects = json.dumps({profile.leaf.named.NAME: f'0x{profile.leaf.named.GLOBAL:08X}'}).encode()
    p = local.ConditionalLocalBufferProof(bytes(rom), json.dumps(rows).encode(),
        ''.join(lines).encode(), objects, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items() if a in (S, 0x08005954)}
    identity = (B, B+16, 6, hashlib.sha256(LEAF).hexdigest())
    with mock.patch.object(profile.leaf, 'IDENTITY', identity), \
            mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
        return p


class HalfwordPayloadTests(unittest.TestCase):
    def test_CLI_accepts_explicit_selector_before_help(self):
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
            '--owner-runtime-profile', profile.SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(profile.SELECTOR, run.stdout)

    def test_full_raw_branch_frame_and_effect_composition(self):
        data, calls = raw_caller()
        p = bound(data, calls)
        with mock.patch.object(profile.leaf, 'IDENTITY', (B, B+16, 6, hashlib.sha256(LEAF).hexdigest())):
            instructions = match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
        report = p.contract_manifest()
        self.assertTrue(instructions)
        self.assertEqual(set(p.records), {B, S, 0x08005954})
        self.assertTrue(report['actual_output_leaf_effects_proved'])
        self.assertFalse(report['actual_callback_effects_proved'])
        self.assertFalse(report['physical_memory_claim'])
        scheduler = [o for o in report['observations'] if o['target'] == S]
        self.assertTrue(scheduler)
        self.assertTrue(all(o['payload_frame_bytes'] == 20 for o in scheduler))
        helper = next(o for o in report['observations'] if o['target'] == B)
        self.assertEqual(helper['returned_aliases'], [(R0+1, -14)])
        self.assertIn((R0+3, -64), helper['aliases'])

    def test_actual_returned_r1_alias_is_not_dropped(self):
        data, calls = raw_caller(bad_return_alias=True)
        p = bound(data, calls)
        with mock.patch.object(profile.leaf, 'IDENTITY', (B, B+16, 6, hashlib.sha256(LEAF).hexdigest())), \
                self.assertRaisesRegex(ValueError, 'arithmetic leaves'):
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_new_selector_is_registered_in_native_and_report_paths(self):
        self.assertIn(profile.SELECTOR, owner.named_buffer.SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'), profile.SELECTOR)
        self.assertTrue(match._ordinary_call_replay(context(), S))

    def test_old_payload_profile_refuses_two_call_fixture(self):
        data, calls = raw_caller()
        with self.assertRaisesRegex(ValueError, 'one actual scheduler call'):
            bound(data, calls, policy=local.SCHEDULER_PAYLOAD)

    def test_wrong_complete_helper_bytes_refused(self):
        data, calls = raw_caller()
        with self.assertRaises(ValueError):bound(data, calls, leaf_data=LEAF[:2]+half(0x8C5A)+LEAF[4:])

    def test_wrong_helper_instruction_count_refused(self):
        data, calls = raw_caller()
        with self.assertRaises(ValueError):bound(data, calls, helper_count=8)

    def test_unknown_call_target_refused(self):
        with self.assertRaises(ValueError):profile.phases({0:(2,), 2:()}, {0: S+4, 2:S})

    def test_helper_after_scheduler_refused(self):
        with self.assertRaisesRegex(ValueError, 'after scheduler'):
            profile.phases({0:(2,), 2:()}, {0:S, 2:profile.leaf.IDENTITY[0]})

    def test_cycles_refused(self):
        with self.assertRaises(ValueError):
            profile.phases({0:(2,), 2:(0,)}, {0:profile.leaf.IDENTITY[0], 2:S})

    def test_missing_call_and_unknown_edge_refused(self):
        for edges,calls in (({0:()}, {0:S}), ({0:(4,), 2:()}, {0:profile.leaf.IDENTITY[0], 2:S})):
            with self.subTest(edges=edges),self.assertRaises(ValueError):profile.phases(edges,calls)

    def test_exact_local_outputs_keep_unmodified_r1_and_preserved_aliases(self):
        p = context()
        aliases = {R0:OUTPUTS, R0+1:OUTPUTS+2, R0+3:BASE, R0+4:OUTPUTS, R0+5:OUTPUTS+2}
        result = p.check_call(profile.leaf.IDENTITY[0], aliases, STACK, site=100)
        self.assertEqual(result, {R0+1:OUTPUTS+2})
        self.assertEqual(p.observations[100][0]['writes'], [[OUTPUTS,2], [OUTPUTS+2,2]])

    def test_reversed_output_pair_preserves_actual_write_order(self):
        p = context()
        p.check_call(profile.leaf.IDENTITY[0], {R0:OUTPUTS+2, R0+1:OUTPUTS}, STACK, site=100)
        self.assertEqual(p.observations[100][0]['writes'], [[OUTPUTS+2,2],[OUTPUTS,2]])

    def test_overlapping_misaligned_missing_or_descriptor_outputs_refused(self):
        for aliases in ({R0:OUTPUTS,R0+1:OUTPUTS}, {R0:OUTPUTS+1,R0+1:OUTPUTS+3},
                        {R0:DESCRIPTOR,R0+1:OUTPUTS+2}, {R0:OUTPUTS}):
            with self.subTest(aliases=aliases),self.assertRaises(ValueError):
                context().check_call(profile.leaf.IDENTITY[0], aliases, STACK, site=100)

    def test_saved_incoming_and_outside_aliases_refused(self):
        for offset in (-20,0,-76):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                context().check_call(profile.leaf.IDENTITY[0],
                    {R0:OUTPUTS,R0+1:OUTPUTS+2,R0+3:offset}, STACK, site=100)

    def test_output_call_pointer_slots_or_word_facts_refused(self):
        for slots,words in (({DESCRIPTOR+4:BASE},None), ({},{BASE:'opaque'})):
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context().check_call(profile.leaf.IDENTITY[0], {R0:OUTPUTS,R0+1:OUTPUTS+2},
                    STACK, slots, site=100, words=words)

    def test_holes_protected_private_words_and_frame_bounds_refused(self):
        cases = [[LOCAL]*8+[SAVED]*5, [LOCAL]*65+[SAVED]*5,
                 [LOCAL]*4+[SAVED]+[LOCAL]*8+[SAVED]*4,
                 [(True,False,True)]+[LOCAL]*12+[SAVED]*5,
                 [(False,True,True)]+[LOCAL]*12+[SAVED]*5]
        for stack in cases:
            with self.subTest(stack=stack),self.assertRaises(ValueError):profile.layout(stack)

    def test_scheduler_prefix_bound_excludes_output_pair(self):
        p = context()
        p.check_call(S, {R0+2:DESCRIPTOR,R0+4:OUTPUTS}, STACK, {DESCRIPTOR+4:BASE}, site=200)
        o = p.observations[200][0]
        self.assertEqual(o['payload_frame_bytes'],20)
        self.assertEqual(o['frame']['descriptor']+28,o['frame']['outputs'])
        self.assertTrue(o['output_pair_excluded_from_payload'])

    def test_scheduler_wrong_pointer_field_value_or_extra_slot_refused(self):
        for slots in ({}, {DESCRIPTOR+8:BASE}, {DESCRIPTOR+4:BASE+4},
                      {DESCRIPTOR+4:OUTPUTS}, {DESCRIPTOR+4:BASE,BASE:OUTPUTS}):
            with self.subTest(slots=slots),self.assertRaises(ValueError):
                context().check_call(S,{R0+2:DESCRIPTOR},STACK,slots,site=200)

    def test_scheduler_additional_outgoing_alias_refused(self):
        for reg in (R0,R0+1,R0+3,R0+12):
            with self.subTest(reg=reg),self.assertRaises(ValueError):
                context().check_call(S,{R0+2:DESCRIPTOR,reg:BASE},STACK,{DESCRIPTOR+4:BASE},site=200)

    def test_scheduler_shifted_descriptor_refused(self):
        with self.assertRaises(ValueError):
            context().check_call(S,{R0+2:DESCRIPTOR+4},STACK,{DESCRIPTOR+8:BASE},site=200)

    def test_every_reached_alias_alternative_is_retained(self):
        p=context()
        for aliases in ({R0+2:DESCRIPTOR},{R0+2:DESCRIPTOR,R0+4:OUTPUTS}):
            p.check_call(S,aliases,STACK,{DESCRIPTOR+4:BASE},site=200)
        self.assertEqual(len(p.observations[200]),2)

    def test_observation_budget_refuses_instead_of_dropping_state(self):
        p=context()
        for n in range(profile.MAX_OBSERVATIONS):profile.observe(p,200,{'alternative':n})
        with self.assertRaises(ValueError):profile.observe(p,200,{'alternative':8})

    def test_missing_observation_and_wrong_site_refused(self):
        p=context()
        with self.assertRaises(ValueError):p.contract_manifest()
        with self.assertRaises(ValueError):p.check_call(S,{R0+2:DESCRIPTOR},STACK,site=100)

    def test_pointer_store_is_aligned_complete_and_still_default_off(self):
        for policy,width in ((local.SCHEDULER_BRANCH,4),(profile.SELECTOR,2)):
            p=context();p.policy=policy
            with self.subTest(policy=policy),self.assertRaises(ValueError):
                match.stack_alias_store(list(STACK),{}, {R0:BASE},set(),DESCRIPTOR+4,width,R0,pointer_proof=p)
        slots={}
        match.stack_alias_store(list(STACK),slots,{R0:BASE},set(),DESCRIPTOR+4,4,R0,pointer_proof=context())
        self.assertEqual(slots,{DESCRIPTOR+4:BASE})

    def test_manifest_keeps_readability_lifetime_and_allocation_conditions(self):
        p=context()
        p.check_call(profile.leaf.IDENTITY[0],{R0:OUTPUTS,R0+1:OUTPUTS+2},STACK,site=100)
        p.check_call(S,{R0+2:DESCRIPTOR},STACK,{DESCRIPTOR+4:BASE},site=200)
        report=p.contract_manifest();assumptions=' '.join(report['assumptions'])
        self.assertIn('unknown',assumptions)
        self.assertIn('separate from every caller stack word',assumptions)
        self.assertIn('ambient original R9',assumptions)
        self.assertFalse(report['nonescape_proved'])
        self.assertFalse(report['termination_proved'])


if __name__ == '__main__':unittest.main()
