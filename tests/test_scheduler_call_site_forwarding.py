"""conditional-scheduler-call-site-summaries-v2: forwarded callee stack arguments (issue #238)."""
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
import named_data_buffer_profile as named
import owner_admission_profile as owner
import scheduler_call_site_profile as profile
import stack_index_precondition_profile as stack_index
from test_scheduler_predicates import half, fixture, A, B, C, R0
from test_scheduler_call_site_summaries import (Owner, scheduler_call, epilogue, two_sites, BODIES,
                                                CALLBACK)
from test_scheduler_call_site_summaries import admitted, REFUSAL

V1, V2 = profile.SELECTOR, profile.SELECTOR_V2
S = profile.SCHEDULER
D, E = 0x08001800, 0x08001900
# Leaf: ldr r1,[sp,#0]; movs r0,#0; strh r0,[r1]; bx lr - writes through its fifth argument.
LEAF = (0x9900, 0x2000, 0x8008, 0x4770)


def forwarder(*before, after=(), base=B, leaf=C, push=0xB500, pop=(0xBC01, 0x4700)):
    """push {lr}; sub sp,#4; [before]; bl leaf; add sp,#4; [after]; pop {r0}; bx r0.
    By default `before` is `str r1,[sp]`: the caller's R1 pointer becomes the leaf's fifth argument."""
    p = Owner(base)
    p.emit(push, 0xB081, *(before or (0x9100,)))
    p.call(leaf, 'leaf')
    p.emit(0xB001, *after, *pop)
    return p


def owner_program(*, before=(), tail=(), frame=8, forwarded=0xA907):
    """push {r4,lr}; sub sp,#32; [before]; scheduler site; add r1,sp,#28; bl B; [tail]; epilogue.
    The descriptor is sp+0..27 and the forwarded pointer addresses the free local word sp+28."""
    p = Owner()
    p.emit(0xB510, 0xB080 | frame, *before)
    scheduler_call(p, name='site')
    p.emit(forwarded)
    p.call(B, 'forwarding')
    for item in tail:
        if isinstance(item, tuple):
            p.call(*item)
        else:
            p.emit(item)
    epilogue(p, frame)
    return p


def bound(program, bodies, *, policy=V2):
    data, calls = program.build()
    p = fixture({A: data, **bodies, **BODIES}, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in BODIES.items()}
    with mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p, data, calls


def code(program):
    """A callee body: no trailing pad, since a callee here has no literal pool."""
    size = len(program.data)
    return program.build()[0][:size]


def bodies(forward=None, leaf=LEAF, extra=None):
    return {B: code(forward or forwarder()), C: half(*leaf), **(extra or {})}


def verified(program, found=None, *, policy=V2):
    p, data, calls = bound(program, bodies() if found is None else found, policy=policy)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
    return p


def record(p):
    return p.contract_manifest()['forwarded_stack_arguments']


class ForwardedCallSiteTests(unittest.TestCase):
    def test_v2_admits_a_pointer_forwarded_as_a_callee_stack_argument(self):
        program = owner_program()
        p = verified(program)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA_V2)
        found = report['forwarded_stack_arguments']
        # push {lr}; sub sp,#4: the slot is the callee's word at entry_SP-8, stored at +4; it
        # holds the owner's sp+28, which is owner entry_SP-12 under the 40-byte owner frame.
        self.assertEqual(found['slots'], [[B, B + 4, -8, -12]])
        # The slot is released at the callee's ADD SP: owner entry_SP-40-8.
        self.assertEqual(found['released'], [[program.labels['forwarding'], [-48]]])
        self.assertEqual((found['trusted_calls'], found['trusted_callee_calls']), ([], []))
        self.assertIs(found['premise'], stack_index.FORWARD_PREMISE)
        self.assertIs(found['premise_proved'], False)
        self.assertEqual(sorted(p.dependencies), sorted([S, profile.DIRECT, B, C]))
        self.assertEqual(p.dependency_budget, profile.DEPENDENCY_BUDGET)
        # The scheduler site keeps its v1 observation.
        self.assertEqual(p.observations[program.labels['site']]['aliases'], [(R0+2, -40)])

    def test_v1_still_refuses_the_forwarded_pointer(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08001200: unsupported buffer pointer use'):
            verified(owner_program(), policy=V1)

    def test_v1_admitted_owner_is_refused_under_v2(self):
        # v1 and v2 are disjoint, so a v1 report never becomes a v2 one. Whether a callee
        # forwards is known only from the walk, so v2 refuses once the walk has run, when the
        # manifest finds no forwarded slot. With no callee to inspect, the walk is v1's.
        v1 = verified(two_sites(), {}, policy=V1).contract_manifest()
        self.assertEqual(v1['schema'], profile.SCHEMA)
        self.assertNotIn('forwarded_stack_arguments', v1)
        p = verified(two_sites(), {})
        self.assertEqual(p.forward_slot_records, set())
        self.assertEqual([p.observations[site] for site in sorted(p.observations)], v1['observations'])
        with self.assertRaisesRegex(ValueError, 'require a forwarded callee stack argument'):
            p.contract_manifest()

    def test_v2_keeps_the_v1_site_rules(self):
        # add r1,sp,#28 with movs r3,#8 in place of the size: R1 is a second caller-clobbered
        # alias at the scheduler site, which v1's first obligation refuses.
        program = Owner()
        program.emit(0xB510, 0xB088, 0xA907)
        program.load(0, CALLBACK)
        program.emit(0x2308, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 8)
        with self.assertRaisesRegex(ValueError, 'admits only the descriptor register'):
            verified(program, {})

    def test_v2_observes_a_site_without_a_local_descriptor(self):
        # movs r2,#0: no local alias reaches the call, so only the site hook sees it.
        program = Owner()
        program.emit(0xB510, 0xB087)
        scheduler_call(program, name='site', descriptor=0x2200)
        epilogue(program, 7)
        with self.assertRaisesRegex(ValueError, 'only the descriptor register'):
            verified(program, {})

    def test_inspected_callee_own_frame_calls_keep_the_buffer_rules(self):
        # B passes a word of its own frame to D (mov r0,sp; bl D): its walk checks that call
        # with the ordinary buffer rules, not the owner's site interface.
        own = Owner(B)
        own.emit(0xB500, 0xB081, 0x4668)
        own.call(D)
        own.emit(0xB001, 0xBC01, 0x4700)
        p = verified(owner_program(), bodies(own, extra={D: half(0x2100, 0x6001, 0x4770)}))
        self.assertIn(D, p.dependencies)
        with self.assertRaisesRegex(ValueError, 'require a forwarded callee stack argument'):
            p.contract_manifest()

    def test_forwarded_pointer_stays_bounded_in_the_next_callee(self):
        # strh r0,[r1,#8]: owner sp+28+8 is past the owner's local words.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            verified(owner_program(), bodies(leaf=(0x9900, 0x2000, 0x8108, 0x4770)))

    def test_slot_outside_the_callee_frame_refuses(self):
        # str r1,[sp,#8]: the owner's own frame, above the callee's entry SP.
        with self.assertRaisesRegex(ValueError, "outside the callee's own frame|outside the tracked frame"):
            verified(owner_program(), bodies(forwarder(0x9102)))

    def test_slot_in_a_saved_register_word_refuses(self):
        # push {r4,lr}; str r1,[sp,#4] after sub sp,#4: the pushed R4 word; pop {r4} restores it.
        # The forwarder's own frame walk now refuses the store into its saved R4 word first.
        with self.assertRaisesRegex(ValueError, 'restored into a register|'
                                    'stack-frame store overlaps a saved register or return-address word'):
            verified(owner_program(), bodies(forwarder(0x9101, push=0xB510, pop=(0xBC10, 0xBC01, 0x4700))))

    def test_forwarder_may_not_materialize_sp(self):
        # mov r2,sp; ldr r3,[r2] after the store would read the slot as a scalar.
        with self.assertRaisesRegex(ValueError, 'only immediate SP uses'):
            verified(owner_program(), bodies(forwarder(0x9100, 0x466A, 0x6813, 0x2200)))

    def test_released_word_read_refuses(self):
        # After ADD SP the word still holds the pointer: sub sp,#4; ldr r2,[sp] reads it.
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            verified(owner_program(), bodies(forwarder(after=(0xB081, 0x9A00, 0x2200, 0xB001))))

    def test_released_word_overwritten_is_admitted(self):
        # sub sp,#4; movs r2,#0; str r2,[sp]; add sp,#4: the pointer is gone.
        found = record(verified(owner_program(), bodies(forwarder(after=(0xB081, 0x2200, 0x9200, 0xB001)))))
        self.assertEqual(found['released'], [])

    def test_slot_overwritten_before_release_leaves_no_premise(self):
        # movs r1,#0; str r1,[sp] after the leaf: no released word, so no premise line.
        program = Owner(B)
        program.emit(0xB500, 0xB081, 0x9100)
        program.call(C, 'leaf')
        program.emit(0x2100, 0x9100, 0xB001, 0xBC01, 0x4700)
        found = record(verified(owner_program(), bodies(program)))
        self.assertEqual(found['slots'], [[B, B + 4, -8, -12]])
        self.assertEqual((found['released'], found['premise']), ([], None))
        self.assertEqual(stack_index.forwarded_lines({'forwarded_stack_arguments': found}), [])

    def test_scalar_store_kills_the_slot(self):
        # movs r2,#0; str r2,[sp] before the call: the leaf gets a scalar, so its
        # out-of-bounds write is no buffer access. The store is still recorded.
        found = record(verified(owner_program(), bodies(forwarder(0x9100, 0x2200, 0x9200),
                                                       leaf=(0x9900, 0x2000, 0x8108, 0x4770))))
        self.assertEqual((found['slots'], found['released']), ([[B, B + 4, -8, -12]], []))

    def test_owner_may_not_hand_a_scheduler_site_a_stack_pointer_after_a_release(self):
        program = Owner()
        program.emit(0xB510, 0xB088, 0xA907)
        program.call(B, 'forwarding')
        scheduler_call(program, name='site')
        epilogue(program, 8)
        p = verified(program)
        with self.assertRaisesRegex(ValueError, profile.STACK_POINTER_REFUSAL):
            p.contract_manifest()

    def test_owner_may_not_walk_a_callee_after_a_release(self):
        # add r1,sp,#28; bl B a second time: its walk would not see the released word.
        p = verified(owner_program(tail=(0xA907, (B,))))
        with self.assertRaisesRegex(ValueError, profile.STACK_POINTER_REFUSAL):
            p.contract_manifest()

    def test_pointer_handed_back_after_a_release_walks_the_next_callee(self):
        # The leaf returns the pointer in R1 (ldr r1,[sp]); a later call receives it.
        p = verified(owner_program(tail=((D,),)), bodies(extra={D: half(0x4770)}))
        with self.assertRaisesRegex(ValueError, profile.STACK_POINTER_REFUSAL):
            p.contract_manifest()

    def test_owner_may_not_move_sp_down_after_a_release(self):
        p = verified(owner_program(tail=(0xB081, 0xB001)))
        with self.assertRaisesRegex(ValueError, profile.SP_DOWN_REFUSAL):
            p.contract_manifest()

    def test_release_inside_a_loop_reaches_its_own_call(self):
        program = Owner()
        program.emit(0xB530, 0xB088)
        scheduler_call(program, name='site')
        program.emit(0x2400)                               # movs r4,#0
        program.label('header')
        program.emit(0xA907)
        program.call(B, 'forwarding')
        program.emit(0x3401, 0x2C02)                       # adds r4,#1; cmp r4,#2
        program.branch(0xDB00, 'header')                   # blt header
        epilogue(program, 8, 0xBC30)
        p = verified(program)
        with self.assertRaisesRegex(ValueError, profile.STACK_POINTER_REFUSAL):
            p.contract_manifest()

    def test_calls_after_a_release_without_stack_pointers_are_trusted(self):
        # The leaf hands the pointer back in R1 (ldr r1,[sp]), so the owner clears R1 first;
        # otherwise D would receive it and be walked. Every later BL rests on the premise, so
        # each is listed with its site: D, E, and D again.
        program = owner_program(tail=(0x2100, (D,), (E,), (D,)))
        found = record(verified(program, bodies(extra={D: half(0x4770), E: half(0x4770)})))
        later = sorted(site for site, target in program.calls.items() if target in (D, E))
        self.assertEqual(found['trusted_calls'], [[site, program.calls[site]] for site in later])
        self.assertEqual([target for _, target in found['trusted_calls']], [D, E, D])
        line, = stack_index.forwarded_lines({'forwarded_stack_arguments': found})
        self.assertIn(f'released words entry_SP-0x30 after call 0x{program.labels["forwarding"]:08X}', line)
        self.assertIn('trusted calls ' + ', '.join(f'0x{site:08X}' for site in later) + ';', line)

    def test_callee_calls_after_its_release_are_recorded(self):
        # The forwarder clears R1 (the leaf hands the pointer back in it) and calls E with no
        # stack pointer after releasing the slot.
        program = Owner(B)
        program.emit(0xB500, 0xB081, 0x9100)
        program.call(C, 'leaf')
        program.emit(0xB001, 0x2100)
        program.call(E, 'later')
        program.emit(0xBC01, 0x4700)
        found = record(verified(owner_program(), bodies(program, extra={E: half(0x4770)})))
        self.assertEqual(found['trusted_callee_calls'], [[B, program.labels['later'], E]])

    def test_release_handed_back_through_a_walked_callee(self):
        # B is a pass-through (push {lr}; bl D; pop {r0}; bx r0); D forwards to C.
        through = Owner(B)
        through.emit(0xB500)
        through.call(D)
        through.emit(0xBC01, 0x4700)
        found = record(verified(owner_program(), bodies(through, extra={D: code(forwarder(base=D))})))
        self.assertEqual(found['slots'], [[D, D + 4, -8, -12]])
        # D's entry SP is the owner's SP-4 (B pushed LR), so its slot is owner entry_SP-52.
        self.assertEqual(found['released'][0][1], [-52])

    def test_inspected_callee_own_frame_forwarding_keeps_the_v1_rules(self):
        # B passes its own frame to D (push {lr}; sub sp,#16; movs r1,#0; mov r0,sp; bl D) and D
        # forwards it to the leaf as a stack argument. That slot would hold B's frame, not the
        # owner's, so it is refused as under v1: with the slot overwritten before the release
        # (no released word) and without (a released word in B's frame).
        own = Owner(B)
        own.emit(0xB500, 0xB084, 0x2100, 0x4668)
        own.call(D)
        own.emit(0xB004, 0xBC01, 0x4700)
        for after in ((0x2000, 0x9000, 0x2100), (0x2100,)):
            nested = Owner(D)
            nested.emit(0xB500, 0xB081, 0x9000)
            nested.call(C, 'leaf')
            nested.emit(*after, 0xB001, 0xBC01, 0x4700)
            with self.subTest(after=after), self.assertRaisesRegex(
                    ValueError, 'buffer callee 0x08001800: unsupported buffer pointer use or escape'):
                verified(owner_program(), {B: code(own), D: code(nested), C: half(*LEAF)})

    def test_sp_decrement_on_a_fall_through_arm_after_a_release_refuses(self):
        # movs r1,#0; cmp r0,#0; beq skip; sub sp,#4; add sp,#4; skip: only the fall-through
        # arm moves SP down.
        program = Owner()
        program.emit(0xB510, 0xB088)
        scheduler_call(program, name='site')
        program.emit(0xA907)
        program.call(B, 'forwarding')
        program.emit(0x2100, 0x2800)
        program.branch(0xD000, 'skip')
        program.emit(0xB081, 0xB001)
        program.label('skip')
        epilogue(program, 8)
        p = verified(program)
        with self.assertRaisesRegex(ValueError, profile.SP_DOWN_REFUSAL):
            p.contract_manifest()

    def test_every_release_site_is_followed(self):
        # Two exclusive arms each release a slot; only the later arm then moves SP down.
        program = Owner()
        program.emit(0xB510, 0xB088)
        scheduler_call(program, name='site')
        program.emit(0x2800)
        program.branch(0xD000, 'other')                    # beq other
        program.emit(0xA907)
        program.call(B, 'first')
        program.branch(0xE000, 'join')                     # b join
        program.label('other')
        program.emit(0xA906)
        program.call(B, 'second')
        program.emit(0xB081, 0xB001)                       # sub sp,#4; add sp,#4
        program.label('join')
        epilogue(program, 8)
        p = verified(program)
        self.assertEqual(sorted(p.forward_releases), [program.labels['first'], program.labels['second']])
        with self.assertRaisesRegex(ValueError, profile.SP_DOWN_REFUSAL):
            p.contract_manifest()

    def test_stack_pointer_in_r12_or_a_frame_word_after_a_release_refuses(self):
        # mov r12,r1 (the pointer the leaf hands back); and add r0,sp,#28; str r0,[sp,#24]:
        # D then receives a stack pointer in R12, or one in a frame word, so it is walked.
        for tail in ((0x468C, 0x2100, (D,)), (0xA807, 0x9006, 0x2100, 0x2000, (D,))):
            p = verified(owner_program(tail=tail), bodies(extra={D: half(0x4770)}))
            with self.subTest(tail=tail), self.assertRaisesRegex(ValueError, profile.STACK_POINTER_REFUSAL):
                p.contract_manifest()

    def test_manifest_states_the_forwarding_premise(self):
        report = verified(owner_program()).contract_manifest()
        self.assertEqual(report['assumptions'][:len(profile.PREMISES)], profile.PREMISES)
        extra, = report['assumptions'][len(profile.PREMISES):]
        for phrase in ('issue #183', 'its own callee\'s outgoing stack argument',
                       'every SP use is immediate', 'incoming stack argument',
                       'tracked until written', 'no owner path moves SP down or hands a callee a stack pointer',
                       'trusted under the recorded forwarded stack argument premise'):
            self.assertIn(phrase, extra)
        for flag in ('actual_callback_effects_proved', 'nonescape_proved', 'termination_proved',
                     'manager_memory_access_proved', 'caller_shape_bounds'):
            self.assertIs(report[flag], False)

    def test_report_states_the_forwarding_premise_line(self):
        p = verified(owner_program())
        calls = p.contract_manifest()
        manifest = {'profile': profile.SCHEMA_V2, 'proof': {'buffers': {'conditional_local_calls': calls}}}
        result = (p.root[1], manifest, hashlib.sha256(b's').hexdigest(), b'[]', b'', b'{}', bytes(16), 1, b'elf')
        report = owner.render(A, result)
        self.assertEqual(owner.selector_for_report(report), V2)
        line, = stack_index.forwarded_lines({'forwarded_stack_arguments': calls['forwarded_stack_arguments']})
        self.assertIn(line, report.splitlines())
        self.assertIn('unproved runtime premise', line)
        v1 = owner.render(A, (result[0], dict(manifest, profile=profile.SCHEMA), *result[2:]))
        self.assertNotIn('* forwarded stack argument premise:', v1)

    def test_registration(self):
        self.assertEqual(local.SCHEDULER_CALL_SITES_V2, V2)
        self.assertEqual(local.SCHEMAS[V2], profile.SCHEMA_V2)
        self.assertIn(V2, named.LOCAL_CALL_SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA_V2+'`'), V2)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)), '--owner-runtime-profile',
                              V2, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)



class ForwardedOwnerAdmissionBindingTests(unittest.TestCase):
    """check_bindings as owner.verify applies it under the v2 selector."""

    def test_call_site_v2_selector_refuses_a_callback_bound_as_data(self):
        manifest, _ = admitted(owner_program(), selector=V2, bodies=bodies())
        self.assertEqual(manifest['profile'], profile.SCHEMA_V2)
        self.assertEqual([name for _, name in manifest['bindings']['functions']], ['func_08001600'])
        with self.assertRaisesRegex(ValueError, REFUSAL):
            admitted(owner_program(), selector=V2, bodies=bodies(), as_data=(CALLBACK,))


if __name__ == '__main__':
    unittest.main()
