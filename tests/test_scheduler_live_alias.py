"""Live private-local aliases across ordinary calls in the explicit live-alias selectors."""
import copy
import hashlib
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import scheduler_branch_profile as branch
import scheduler_live_alias_profile as live
from test_scheduler_predicates import half, bl, fixture, A, B, R0, LOCAL, SAVED

S = branch.SCHEDULER
SELECTOR = local.SCHEDULER_LIVE_ALIAS
PAYLOAD = local.SCHEDULER_LIVE_ALIAS_PAYLOAD
H1, H2 = B, B+0x20
FRAME = [LOCAL]*7+[SAVED]*2
BASE = -36                      # lowest private word: SP after push {r4,lr}; sub sp,#28
LEAF = half(0x4770)             # bx lr
ADD_R4_SP = 0xAC00              # r4 = sp+0, a callee-saved alias
ADD_R0_SP = 0xA800              # r0 = sp+0, a passed alias
ADD_R2_SP = 0xAA00              # r2 = sp+0, the scheduler descriptor


def caller(*, first=(), second=()):
    """push {r4,lr}; sub sp,#28; <first> BL H1; <second> BL H2; add r2,sp,#0; BL scheduler; return."""
    data, calls = half(0xB510, 0xB087), {}
    for pre, target in ((first, H1), (second, H2)):
        data += half(*pre)
        site = A+len(data)
        calls[site] = target
        data += bl(site, target)
    data += half(ADD_R2_SP)
    site = A+len(data)
    calls[site] = S
    data += bl(site, S)+half(0xB007, 0xBC10, 0xBC02, 0x4708)
    return data, calls


def bound(data, calls, h1=LEAF, h2=LEAF, policy=SELECTOR, extra=None):
    bodies = {A: data, H1: h1, H2: h2, S: bytes(60), 0x08005954: bytes(206), **(extra or {})}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtime = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtime else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items() if a in (S, 0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES, pins), mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p


def verify(data, calls, **kw):
    p = bound(data, calls, **kw)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
    return p


class LiveAliasTests(unittest.TestCase):
    def test_preserved_alias_survives_ordinary_calls_and_is_recorded(self):
        data, calls = caller(first=(ADD_R4_SP,))
        p = verify(data, calls)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], local.SCHEMAS[SELECTOR])
        by_target = {o['target']: o for o in report['observations']}
        for target in (H1, H2):
            o = by_target[target]
            self.assertEqual(o['kind'], 'live-local-alias-ordinary-call')
            self.assertEqual(o['preserved_aliases'], [(match.ARM_REG_R0+4, BASE)])
            self.assertEqual(o['passed_aliases'], [])
            self.assertIn('callee-saved registers R4-R11', o['premise'])
        self.assertEqual(by_target[S]['aliases'], [(R0+2, BASE), (R0+4, BASE)])
        self.assertIn('callee-saved registers R4-R11', report['branch_calls']['ordinary_call_contract'])
        self.assertNotIn('No tracked local-register alias', report['branch_calls']['ordinary_call_contract'])
        self.assertEqual(report['branch_calls']['live_alias_source_sha256'],
                         hashlib.sha256(Path(live.__file__).read_bytes()).hexdigest())
        self.assertFalse(report['nonescape_proved'])
        self.assertFalse(report['actual_callback_effects_proved'])
        self.assertEqual(p.dependency_budget, 36)

    def test_alias_free_calls_keep_the_ordinary_observation(self):
        data, calls = caller()
        o = verify(data, calls).contract_manifest()['observations'][0]
        self.assertEqual(o['kind'], 'conditional-ordinary-ABI-call')
        self.assertNotIn('premise', o)

    def test_existing_selectors_still_refuse_the_same_bytes(self):
        data, calls = caller(first=(ADD_R4_SP,))
        for policy in (local.SCHEDULER_24, local.SCHEDULER_BRANCH, local.SCHEDULER_SEQUENTIAL):
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'every live local alias'):
                verify(data, calls, policy=policy)
        for policy in (local.SCHEDULER_LEAF_OUTPUT, local.SCHEDULER_KILLED_ALIAS):
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'preserved-register aliases'):
                verify(data, calls, policy=policy)

    def test_bounded_nonretaining_callee_may_receive_an_alias(self):
        data, calls = caller(first=(ADD_R0_SP,))
        p = verify(data, calls, h1=half(0x6001, 0x2000, 0x4770))   # str r1,[r0,#0]; movs r0,#0; bx lr
        o = next(o for o in p.contract_manifest()['observations'] if o['target'] == H1)
        self.assertEqual(o['passed_aliases'], [(R0, BASE)])
        self.assertEqual((o['access_lowest'], o['access_end']), (BASE, BASE+4))
        self.assertEqual(o['nested_dependencies'], [])
        self.assertEqual(o['source_sha256'], hashlib.sha256(Path(live.__file__).read_bytes()).hexdigest())

    def test_passed_and_preserved_aliases_together(self):
        data, calls = caller(first=(ADD_R4_SP, ADD_R0_SP))
        p = verify(data, calls, h1=half(0x6841, 0x2000, 0x4770))   # ldr r1,[r0,#4]; movs r0,#0; bx lr
        o = next(o for o in p.contract_manifest()['observations'] if o['target'] == H1)
        self.assertEqual((o['passed_aliases'], o['preserved_aliases']),
                         ([(R0, BASE)], [(match.ARM_REG_R0+4, BASE)]))

    def test_alias_passed_to_unbounded_callee_refused(self):
        data, calls = caller(first=(ADD_R0_SP,))
        for name, body in (('read past frame', half(0x6A81, 0x4770)),        # ldr r1,[r0,#40]
                           ('unknown access form', half(0x4401, 0x4770))):   # add r1,r0
            with self.subTest(name=name), self.assertRaises(ValueError):
                verify(data, calls, h1=body)

    def test_alias_written_past_its_extent_refused(self):
        data, calls = caller(first=(ADD_R0_SP,))
        # str r1,[r0,#28] lands on the saved-register word just above the private frame.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            verify(data, calls, h1=half(0x61C1, 0x4770))

    def test_access_below_the_lowest_passed_alias_refused(self):
        data, calls = caller(first=(0xA802,))   # add r0,sp,#8
        p = bound(data, calls)
        def reach_below(*args, **kwargs):
            p.access(BASE, 4, FRAME)
            return {}
        with mock.patch.object(p, 'check_arguments', side_effect=reach_below):
            with self.assertRaisesRegex(ValueError, 'below its lowest passed alias'):
                match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_alias_retained_by_callee_refused(self):
        data, calls = caller(first=(ADD_R0_SP,))
        for name, body in (('store to memory', half(0x6008, 0x4770)),         # str r0,[r1,#0]
                           ('push', half(0xB501, 0xBD01)),                     # push {r0,lr}; pop {r0,pc}
                           ('move to callee-saved', half(0x1C04, 0x4770))):    # adds r4,r0,#0; bx lr
            with self.subTest(name=name), self.assertRaises(ValueError):
                verify(data, calls, h1=body)

    def test_alias_returned_by_callee_refused(self):
        data, calls = caller(first=(ADD_R0_SP,))
        with self.assertRaisesRegex(ValueError, 'cannot return a local alias'):
            verify(data, calls, h1=LEAF)

    def test_callee_reaching_a_thunk_is_refused(self):
        thunk = match.function_thunk.ALIASES['_call_via_r3']
        # push {lr}; movs r0,#0; bl _call_via_r3; pop {r1}; bx r1
        body = half(0xB500, 0x2000)+bl(H1+4, thunk)+half(0xBC02, 0x4708)
        # A replayed callee meets the indirect-target rule first; a preserved-register walk meets its own.
        for pre, message in (((ADD_R0_SP,), 'indirect call differs|thunk or runtime helper'),
                             ((ADD_R4_SP,), 'thunk or runtime helper')):
            data, calls = caller(first=pre)
            with self.subTest(pre=pre), self.assertRaisesRegex(ValueError, message):
                verify(data, calls, h1=body, extra={thunk: half(0x4718)})

    def test_nested_dependencies_are_logged_and_stable_across_paths(self):
        data, calls = caller(first=(ADD_R0_SP,))
        # H1: push {lr}; bl H2; pop {r1}; bx r1.  H2: ldr r1,[r0,#0]; movs r0,#0; bx lr
        h1 = half(0xB500)+bl(H1+2, H2)+half(0xBC02, 0x4708)
        p = verify(data, calls, h1=h1, h2=half(0x6801, 0x2000, 0x4770))
        site = min(calls)
        o = p.observations[site]
        self.assertEqual(o['nested_dependencies'], [H2])
        # A second incoming path to the same site produces the identical observation.
        p.check_call(H1, {R0: BASE}, FRAME, site=site)
        self.assertEqual(p.observations[site], o)

    def test_preserved_alias_walk_is_recorded(self):
        data, calls = caller(first=(ADD_R4_SP,))
        # push {r4,lr}; movs r4,#0; pop {r4}; pop {r0}; bx r0 saves, clobbers and restores r4.
        p = verify(data, calls, h1=half(0xB510, 0x2400, 0xBC10, 0xBC01, 0x4700))
        o = p.observations[min(calls)]
        self.assertEqual((o['preserved_register_reads'], o['preserved_register_restore']), ('push-only', 'every-return'))
        self.assertEqual(o['preserved_walk_targets'], [H1])
        self.assertEqual(o['source_sha256'], hashlib.sha256(Path(live.__file__).read_bytes()).hexdigest())

    def test_unwalked_nested_call_is_named(self):
        data, calls = caller(first=(ADD_R4_SP,))
        # H1: push {r4,lr}; movs r4,#0; bl H2; pop {r4}; pop {r0}; bx r0 - only the saved copy is live at the call.
        h2 = half(0x2000, 0x4770)
        p = verify(data, calls, h1=half(0xB510, 0x2400)+bl(H1+4, H2)+half(0xBC10, 0xBC01, 0x4700), h2=h2)
        o = p.observations[min(calls)]
        self.assertEqual(o['preserved_walk_targets'], [H1])
        self.assertEqual(o['unwalked_nested_targets'], [[H2, hashlib.sha256(h2).hexdigest()]])

    def test_preserved_alias_read_or_lost_by_callee_refused(self):
        cases = (
            ('stored', half(0x600C, 0x2000, 0x4770), None,                           # str r4,[r1,#0]; movs r0,#0; bx lr
             'reads a preserved alias register'),
            ('copied to argument', half(0xB500, 0x1C20)+bl(H1+4, H2)+half(0xBC02, 0x4708), None,  # adds r0,r4,#0; bl H2
             'reads a preserved alias register'),
            ('overwritten without restore', half(0x2400, 0x4770), None,              # movs r4,#0; bx lr
             'without restoring'),
            ('restored from the wrong slot', half(0xB530, 0x2400, 0xBC20, 0xBC10, 0xBC01, 0x4700), None,
             'pops a saved alias into another register'),                            # push {r4,r5,lr}; pop {r5}; pop {r4}
            ('read by a nested callee', half(0xB500)+bl(H1+2, H2)+half(0xBC02, 0x4708),
             half(0x600C, 0x4770), 'reads a preserved alias register'),              # H2: str r4,[r1,#0]
            ('saved copy popped into another register', half(0xB410, 0xBC20, 0x6028, 0x4770), None,
             'pops a saved alias into another register'),                            # push {r4}; pop {r5}; str r0,[r5]
            ('saved copy popped into pc', half(0xB410, 0xBD00), None,
             'pops a saved alias into another register'),                            # push {r4}; pop {pc}
            ('saved copy loaded through sp', half(0xB410, 0x9D00, 0x6028, 0xB001, 0x4770), None,
             'loads a saved alias through SP'),                                      # push {r4}; ldr r5,[sp,#0]; ...
            ('frame pointer over the save slot', half(0xB410, 0x2400, 0x4669, 0x2000, 0x6008, 0xBC10, 0x4770), None,
             'copies SP while a saved alias'),                                       # push {r4}; mov r1,sp; str r0,[r1]
            ('frame pointer taken before the save', half(0xA900, 0xB410, 0x2400, 0x2000, 0x6008, 0xBC10, 0x4770), None,
             'saves a preserved alias after copying SP'),                            # add r1,sp,#0; push {r4}; ...
            ('unbalanced return', half(0xB410, 0x4770), None,
             'unbalanced stack'),                                                    # push {r4}; bx lr
            ('literal sp adjustment from a second predecessor',
             half(0xB410, 0x2400, 0xB081, 0x2300, 0x2800, 0xD000, 0x4B02, 0x449D, 0xBC10, 0x4770, 0, 0)
             + (4).to_bytes(4, 'little'), None, 'lacks its sole literal load'),      # beq lands on add sp,r3
            ('ARMv6-only low-register mov', half(0x4608, 0x4770), None,
             'not ARMv4T|undefined on ARMv4T'),                                      # mov r0,r1
            ('saved slot released by add sp', half(0xB410, 0xB001, 0xB081, 0x9D00, 0x6028, 0xB001, 0x4770), None,
             'releases a saved alias slot'),                                         # push {r4}; add sp,#4; sub sp,#4; ldr r5,[sp]
            ('stale slot loaded after sub sp', half(0xB410, 0xBC10, 0xB081, 0x9D00, 0x6028, 0xB001, 0x4770), None,
             'loads an unwritten stack slot'),                                       # push {r4}; pop {r4}; sub sp,#4; ldr r5,[sp]
            ('stale slot popped after sub sp', half(0xB410, 0xBC10, 0xB081, 0xBC20, 0x6028, 0x4770), None,
             'pops an unwritten stack slot'),                                        # ...; sub sp,#4; pop {r5}
            ('walked nested callee loads the caller save slot', half(0xB510)+bl(H1+2, H2)+half(0xBC10, 0xBC01, 0x4700),
             half(0x9D00, 0x6028, 0x4770), 'loads a saved alias through SP'),        # H2: ldr r5,[sp,#0]; str r0,[r5]
            ('walked nested callee overwrites the caller save slot', half(0xB510)+bl(H1+2, H2)+half(0xBC10, 0xBC01, 0x4700),
             half(0x9000, 0x4770), 'overwrites a caller save slot'),                 # H2: str r0,[sp,#0]
            ('SP copied in the caller of a walked nested callee', half(0xB500, 0x4669)+bl(H1+4, H2)+half(0xBC02, 0x4708),
             half(0xB410, 0x2400, 0x3904, 0x680D, 0x6028, 0xBC10, 0x4770),
             'saves a preserved alias after copying SP'),                            # H1: mov r1,sp; H2: push {r4}; ldr via r1-4
        )
        for pre in ((ADD_R4_SP,), (ADD_R4_SP, ADD_R0_SP)):
            data, calls = caller(first=pre)
            for name, h1, h2, message in cases:
                with self.subTest(pre=pre, name=name), self.assertRaisesRegex(ValueError, message):
                    verify(data, calls, h1=h1, **({'h2': h2} if h2 else {}))

    def test_pointer_words_word_facts_and_wrong_sites_refused(self):
        data, calls = caller(first=(ADD_R4_SP,))
        site = min(calls)
        for kwargs in (dict(aliases={match.ARM_REG_R0+4: BASE}, slots={-32: BASE}),
                       dict(aliases={match.ARM_REG_R0+4: BASE}, words={-32: 'opaque'})):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                bound(data, calls).check_call(H1, kwargs['aliases'], FRAME, kwargs.get('slots'),
                                              site=site, words=kwargs.get('words'))
        for target, at in ((H2, site), (S+4, site), (H1, A)):
            with self.subTest(target=target, at=at), self.assertRaises(ValueError):
                bound(data, calls).check_call(target, {match.ARM_REG_R0+4: BASE}, FRAME, site=at)

    def test_alias_outside_private_words_refused(self):
        data, calls = caller(first=(ADD_R4_SP,))
        for offset in (-40, 0):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                bound(data, calls).check_call(H1, {match.ARM_REG_R0+4: offset}, FRAME, site=min(calls))

    def test_link_register_alias_cannot_be_passed(self):
        data, calls = caller(first=(ADD_R4_SP,))
        with self.assertRaises(ValueError):
            bound(data, calls).check_call(H1, {match.ARM_REG_LR: BASE}, FRAME, site=min(calls))


class SchedulerContractTests(unittest.TestCase):
    def setUp(self):
        self.data, self.calls = caller(first=(ADD_R4_SP,))
        self.site = max(self.calls)

    def test_descriptor_contract_unchanged_for_scheduler_call(self):
        for aliases in ({R0+2: BASE, R0: BASE}, {R0+2: BASE, R0+1: BASE}, {}, {R0: BASE}):
            with self.subTest(aliases=aliases), self.assertRaises(ValueError):
                bound(self.data, self.calls).check_call(S, aliases, FRAME, site=self.site)
        for slots in ({-32: BASE+28}, {BASE+4: BASE}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                bound(self.data, self.calls).check_call(S, {R0+2: BASE}, FRAME, slots, site=self.site)
        bound(self.data, self.calls).check_call(S, {R0+2: BASE, R0+4: BASE}, FRAME, site=self.site)

    def test_alias_live_into_descriptor_word_refused_without_payload_selector(self):
        # An alias stored into a descriptor word is a pointer-bearing slot, which only the payload variant admits.
        with self.assertRaisesRegex(ValueError, 'additional register or pointer-word aliases'):
            bound(self.data, self.calls).check_call(S, {R0+2: BASE, R0+4: BASE+28}, [LOCAL]*9+[SAVED]*2,
                                                    {BASE-8+4: BASE+28-8}, site=self.site)

    def test_payload_variant_keeps_the_existing_descriptor_plus_four_contract(self):
        frame, offset = [LOCAL]*9+[SAVED]*2, -44
        p = bound(self.data, self.calls, policy=PAYLOAD)
        p.check_call(S, {R0+2: offset, R0+4: offset+28}, frame, {offset+4: offset+28}, site=self.site)
        o = p.observations[self.site]
        self.assertEqual((o['payload_offset'], o['payload_extent']), (offset+28, 'remaining-private-frame'))
        for slots in ({}, {offset+8: offset+28}, {offset+4: offset+32}):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                bound(self.data, self.calls, policy=PAYLOAD).check_call(
                    S, {R0+2: offset}, frame, slots, site=self.site)

    def test_payload_variant_admits_preserved_aliases_at_ordinary_calls(self):
        data, calls = caller(first=(ADD_R4_SP,))
        p = bound(data, calls, policy=PAYLOAD)
        site = min(calls)
        p.check_call(H1, {match.ARM_REG_R0+4: BASE}, FRAME, site=site)
        self.assertEqual(p.observations[site]['kind'], 'live-local-alias-ordinary-call')

    def test_existing_payload_selector_still_refuses_ordinary_alias(self):
        with self.assertRaises(ValueError):
            bound(self.data, self.calls, policy=local.SCHEDULER_PAYLOAD)


class TamperTests(unittest.TestCase):
    def setUp(self):
        self.data, self.calls = caller(first=(ADD_R0_SP,))
        self.helper = half(0x6001, 0x2000, 0x4770)

    def test_changed_callee_body_changes_fingerprint_and_record(self):
        a = verify(self.data, self.calls, h1=self.helper)
        b = verify(self.data, self.calls, h1=half(0x6041, 0x2000, 0x4770))   # str r1,[r0,#4], r0 cleared
        self.assertNotEqual(a.fingerprint(), b.fingerprint())
        digest = lambda p: p.records[H1]['body_sha256']
        self.assertNotEqual(digest(a), digest(b))
        self.assertEqual(digest(a), hashlib.sha256(self.helper).hexdigest())

    def test_recorded_observation_cannot_be_rewritten_at_a_site(self):
        p = verify(self.data, self.calls, h1=self.helper)
        site = min(p.observations)
        p.observations[site] = dict(p.observations[site], access_end=0)
        with self.assertRaisesRegex(ValueError, 'differs across incoming paths'):
            p.check_call(H1, {R0: BASE}, FRAME, site=site)

    def test_every_call_must_be_observed_for_the_manifest(self):
        p = verify(self.data, self.calls, h1=self.helper)
        del p.observations[min(p.observations)]
        with self.assertRaisesRegex(ValueError, 'every conditional local-buffer call must be observed'):
            p.contract_manifest()

    def test_manifest_binds_profile_source_and_premise(self):
        p = verify(self.data, self.calls, h1=self.helper)
        report = p.contract_manifest()
        self.assertEqual(report['source_sha256'], hashlib.sha256(Path(local.__file__).read_bytes()).hexdigest())
        self.assertIn(live.PREMISE, report['branch_calls']['ordinary_call_contract'])
        altered = copy.deepcopy(report)
        altered['observations'][0]['access_end'] = 0
        self.assertNotEqual(altered, report)


if __name__ == '__main__':
    unittest.main()
