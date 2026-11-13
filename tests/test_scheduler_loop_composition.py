"""Raw Thumb fixtures for sequential live-alias scheduler compositions with counted loops."""
import hashlib
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import conditional_local_buffer_profile as local
import scheduler_loop_composition_profile as composition
from test_scheduler_predicates import half, bl, fixture, A, B
from test_scheduler_counted_loop import decoded

S = composition.SCHEDULER
SELECTOR = local.SCHEDULER_LOOP_LIVE_ALIAS
C = 0x08001300


class Program:
    """Assemble a small Thumb owner with labels and patched branches."""

    def __init__(self, base=A):
        self.base, self.data, self.labels, self.calls, self.patches = base, bytearray(), {}, {}, []

    def here(self):
        return self.base + len(self.data)

    def label(self, name):
        self.labels[name] = self.here()

    def emit(self, *words):
        self.data += half(*words)

    def call(self, target, name=None):
        if name:
            self.label(name)
        self.calls[self.here()] = target
        self.data += bl(self.here(), target)

    def branch(self, word, destination):
        self.patches.append((self.here(), word, destination))
        self.emit(word)

    def build(self):
        for site, word, destination in self.patches:
            offset = (self.labels[destination] - site - 4) // 2
            if word & 0xF800 == 0xE000:
                word |= offset & 0x7FF
            else:
                word |= offset & 0xFF
            struct.pack_into('<H', self.data, site - self.base, word)
        return bytes(self.data), dict(self.calls), dict(self.labels)


def descriptor_call(p, name='scheduler'):
    # R0 callback 0, R1 payload size, R2 = SP (the complete 28-byte frame), R3 parent 0.
    p.emit(0x2000, 0x2118, 0xAA00, 0x2300)
    p.call(S, name)


def caller(*, width=8, form='load', counter=4, temp=0, limit=1, loaded=None,
           latch=None, imm=2, add=1, right_shift=None, scheduler_in_loop=True,
           body=(), preserved_alias=False, side_entry=False, tail_entry=False,
           schedulers_after=0, second_loop=0, before_ordinary=(), extra_latch=False, prefix=0, base=A):
    shift = 32 - width
    p = Program(base)
    p.emit(0xB5F0, 0xB087)                      # push {r4-r7,lr}; sub sp,#28
    p.emit(*(0x46C0,) * prefix)                 # straight-line padding before the loop
    if preserved_alias:
        p.emit(0xAE00)                          # add r6, sp, #0
    if side_entry:
        p.emit(0x2800)
        p.branch(0xD000, 'inside')              # beq into the body, not the header
    p.emit(0x2000 | (counter << 8))             # movs rC, #0
    p.label('header')
    if scheduler_in_loop:
        descriptor_call(p)
    p.emit(*before_ordinary)
    p.call(B, 'ordinary')
    p.label('inside')
    p.emit(*body)
    if extra_latch:
        p.emit(0x2800)
        p.branch(0xD300, 'header')             # a second conditional back edge
    if tail_entry:
        p.emit(0x2800)
        p.branch(0xD000, 'compare')            # beq straight to the latch test
    p.label('tail')
    p.emit(0x1C00 | (add << 6) | (counter << 3) | temp,
           (shift << 6) | (temp << 3) | temp,
           0x0800 | ((right_shift or shift) << 6) | (temp << 3) | counter)
    if form == 'load':
        p.emit(loaded if loaded is not None else 0x7800 | (3 << 6) | (5 << 3) | limit)
        p.label('compare')
        p.emit(0x4280 | (limit << 3) | counter)
        p.label('latch')
        p.branch(0xD300 if latch is None else latch, 'header')
    else:
        p.label('compare')
        p.emit(0x2800 | (counter << 8) | imm)
        p.label('latch')
        p.branch(0xD900 if latch is None else latch, 'header')
    if not scheduler_in_loop:
        descriptor_call(p)
    for index in range(schedulers_after):
        descriptor_call(p, f'after{index}')
    for index in range(second_loop):
        p.emit(0x2700)                          # movs r7, #0
        p.label(f'header{index}')
        p.call(C)
        p.emit(0x1C78, 0x0600, 0x0E07, 0x2F03)  # adds r0,r7,#1; lsls; lsrs r7; cmp r7,#3
        p.branch(0xD300, f'header{index}')
    p.call(C, 'following')
    p.label('exit')
    p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
    return p.build()


def phases(data, calls, base=A):
    ins, edges = decoded(data, calls, base)
    return composition.phases(ins, edges, calls, base)


def bound(data, calls, policy=SELECTOR, callee=half(0x4770)):
    bodies = {A: data, B: callee, C: half(0x4770), S: bytes(60), 0x08005954: bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items()
            if a in (S, 0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p


def iterations(width, incoming, limits, *, inclusive=False, limit_bits=None):
    """Independent arithmetic oracle of the tail: header entries until the latch falls through."""
    counter, entries = incoming & 0xFFFFFFFF, 0
    mask = (1 << width) - 1
    for limit in limits:
        entries += 1
        if entries > (1 << width) + 1:
            return None
        counter = ((counter + 1) << (32 - width) & 0xFFFFFFFF) >> (32 - width)
        if limit_bits is not None:
            limit &= (1 << limit_bits) - 1
        if not (counter <= limit if inclusive else counter < limit):
            return entries
        assert counter <= mask
    return entries


class LayoutTests(unittest.TestCase):
    def test_u8_load_bound_loop_with_scheduler_inside(self):
        data, calls, labels = caller()
        result = phases(data, calls)
        [loop] = result['counted_loops']
        self.assertEqual((loop['header'], loop['latch']), (labels['header'], labels['latch']))
        self.assertEqual((loop['counter_bits'], loop['limit_maximum']), (8, 255))
        self.assertEqual(loop['maximum_header_entries'], 256)
        self.assertEqual(loop['maximum_scheduler_calls'], 256)
        self.assertEqual(result['looped_scheduler_sites'], [labels['scheduler']])
        self.assertEqual(result['maximum_scheduler_calls_per_path_outside_loops'], 0)
        self.assertIn(labels['ordinary'], result['following_ordinary_sites'])
        self.assertIn(labels['following'], result['following_ordinary_sites'])

    def test_u16_counter_admits_byte_and_halfword_limits(self):
        for loaded in (0x7800 | (3 << 6) | (5 << 3) | 1, 0x8800 | (1 << 6) | (5 << 3) | 1,
                       0x5C00 | (2 << 6) | (5 << 3) | 1, 0x5A00 | (2 << 6) | (5 << 3) | 1):
            with self.subTest(load=hex(loaded)):
                [loop] = phases(*caller(width=16, loaded=loaded)[:2])['counted_loops']
                self.assertEqual(loop['maximum_header_entries'], 65536)

    def test_immediate_bounds_at_the_range_edge(self):
        for width, latch, imm in ((8, 0xD900, 254), (8, 0xD300, 255), (8, 0xD900, 2), (16, 0xD900, 255)):
            with self.subTest(width=width, latch=hex(latch), imm=imm):
                phases(*caller(width=width, form='imm', latch=latch, imm=imm)[:2])

    def test_scheduler_outside_loop_counts_against_the_path_budget(self):
        data, calls, labels = caller(scheduler_in_loop=False, schedulers_after=2)
        result = phases(data, calls)
        self.assertEqual(result['maximum_scheduler_calls_per_path_outside_loops'], 3)
        self.assertEqual(result['looped_scheduler_sites'], [])
        self.assertEqual(result['counted_loops'][0]['maximum_scheduler_calls'], 0)
        with self.assertRaisesRegex(ValueError, 'per-path'):
            phases(*caller(scheduler_in_loop=False, schedulers_after=3)[:2])

    def test_acyclic_owner_is_admitted_without_loops(self):
        p = Program()
        p.emit(0xB5F0, 0xB087)
        descriptor_call(p)
        p.call(B, 'ordinary')
        p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
        data, calls, labels = p.build()
        result = phases(data, calls)
        self.assertEqual(result['counted_loops'], [])
        self.assertEqual(result['following_ordinary_sites'], [labels['ordinary']])

    def test_site_and_loop_budgets(self):
        with self.assertRaisesRegex(ValueError, 'bounds'):
            phases(*caller(schedulers_after=4)[:2])
        phases(*caller(second_loop=1)[:2])
        with self.assertRaisesRegex(ValueError, 'loop budget'):
            phases(*caller(second_loop=2)[:2])

    def test_instruction_budget(self):
        size = len(decoded(*caller()[:2])[0])
        data, calls, _ = caller(prefix=composition.MAX_INSTRUCTIONS - size)
        self.assertEqual(len(decoded(data, calls)[0]), composition.MAX_INSTRUCTIONS)
        phases(data, calls)
        data, calls, _ = caller(prefix=composition.MAX_INSTRUCTIONS - size + 1)
        with self.assertRaisesRegex(ValueError, 'bounded instruction graph'):
            phases(data, calls)

    def test_register_roles_are_generic(self):
        for counter, temp, limit in ((5, 0, 1), (6, 2, 3), (7, 1, 1)):
            with self.subTest(counter=counter):
                [loop] = phases(*caller(counter=counter, temp=temp, limit=limit)[:2])['counted_loops']
                self.assertEqual((loop['counter_register'], loop['limit_register']), (counter, limit))

    def test_owner_address_is_not_a_whitelist(self):
        data, calls, labels = caller(base=A + 0x400)
        self.assertEqual(phases(data, calls, A + 0x400)['counted_loops'][0]['header'], labels['header'])


class AttackTests(unittest.TestCase):
    def refused(self, message, **kw):
        data, calls, _ = caller(**kw)
        with self.assertRaisesRegex(ValueError, message):
            phases(data, calls)

    def test_wider_limit_than_counter_is_refused(self):
        # u8 counter against a halfword limit: counter 255 < 256 wraps to 0 forever.
        self.refused('wider than its counter', loaded=0x8800 | (1 << 6) | (5 << 3) | 1)
        self.refused('wider than its counter', loaded=0x5A00 | (2 << 6) | (5 << 3) | 1)

    def test_sign_extending_or_word_limit_is_refused(self):
        for loaded in (0x5600 | (2 << 6) | (5 << 3) | 1, 0x5E00 | (2 << 6) | (5 << 3) | 1,
                       0x6800 | (1 << 6) | (5 << 3) | 1, 0x2100 | 9):
            with self.subTest(load=hex(loaded)):
                self.refused('zero-extended', loaded=loaded)

    def test_limit_not_defined_by_the_tail_is_refused(self):
        # Limit loaded into another register: the compared register is stale.
        self.refused('zero-extended', loaded=0x7800 | (3 << 6) | (5 << 3) | 2)

    def test_signed_and_other_latches_are_refused(self):
        for latch in (0xDB00, 0xDD00, 0xD100, 0xD800, 0xD200):
            with self.subTest(latch=hex(latch)):
                self.refused('unsigned lower', latch=latch)
        self.refused('fresh zero-extended', latch=0xD900)   # register compare with BLS

    def test_immediate_bound_admitting_wrap_is_refused(self):
        self.refused('admits counter wrap', form='imm', latch=0xD900, imm=255)

    def test_increment_other_than_one_is_refused(self):
        for add in (0, 2, 7):
            with self.subTest(add=add):
                self.refused('add exactly one', add=add)

    def test_mismatched_or_missing_narrowing_is_refused(self):
        self.refused('narrowing', right_shift=16)
        self.refused('narrowing', width=24)

    def test_caller_clobbered_counter_is_refused(self):
        for counter in (1, 2, 3):
            with self.subTest(counter=counter):
                self.refused('caller-clobbered', counter=counter, temp=0, limit=5 if counter != 5 else 6)

    def test_counter_written_in_body_is_refused(self):
        self.refused('writes its counter', body=(0x2400,))       # movs r4, #0
        self.refused('writes its counter', body=(0x3401,))       # adds r4, #1 (second increment)
        self.refused('writes its counter', body=(0xBC10, 0xB410))  # pop {r4}; push {r4}

    def test_second_cycle_inside_the_component_is_refused(self):
        p_data, calls, labels = caller(body=(0x2800, 0xD000))
        # Retarget the body's beq backwards to the ordinary call: a second inner cycle.
        site = labels['inside'] + 2
        offset = ((labels['ordinary'] - site - 4) // 2) & 0xFF
        data = bytearray(p_data)
        struct.pack_into('<H', data, site - A, 0xD000 | offset)
        with self.assertRaisesRegex(ValueError, 'exactly one conditional backward edge'):
            phases(bytes(data), calls)

    def test_inner_unconditional_cycle_is_refused(self):
        # cmp r0,#0; beq over; b ordinary: an unconditional inner back edge beside the latch.
        data, calls, labels = caller(body=(0x2800, 0xD000, 0xE000))
        data = bytearray(data)
        site = labels['inside'] + 4
        struct.pack_into('<H', data, site - A, 0xE000 | (((labels['ordinary'] - site - 4) // 2) & 0x7FF))
        with self.assertRaisesRegex(ValueError, 'further cycle'):
            phases(bytes(data), calls)

    def test_second_conditional_latch_is_refused(self):
        self.refused('exactly one conditional backward edge', extra_latch=True)

    def test_counter_written_by_multiword_and_high_register_forms_is_refused(self):
        for word in (0xC810, 0xCC01, 0x4644, 0xAC00, 0xA400, 0x4364):
            # ldmia r0!,{r4}; ldmia r4!,{r0}; mov r4,r8; add r4,sp,#0; adr r4; muls r4,r4
            with self.subTest(word=hex(word)):
                self.refused('writes its counter', body=(word,))

    def test_header_at_owner_entry_is_admitted(self):
        p = Program()
        p.label('header')
        descriptor_call(p)
        p.call(B, 'ordinary')
        p.emit(0x1C60, 0x0600, 0x0E04, 0x2C03)     # adds r0,r4,#1; lsls; lsrs r4; cmp r4,#3
        p.branch(0xD300, 'header')
        p.emit(0x4770)
        data, calls, labels = p.build()
        [loop] = phases(data, calls)['counted_loops']
        self.assertEqual(loop['header'], A)

    def test_side_entry_into_the_body_is_refused(self):
        self.refused('entry other than its header', side_entry=True)

    def test_branch_into_the_tail_is_refused(self):
        self.refused('alternate entry or exit', tail_entry=True)

    def test_unconditional_back_edge_is_refused(self):
        data, calls, labels = caller()
        data = bytearray(data)
        site = labels['latch']
        struct.pack_into('<H', data, site - A, 0xE000 | (((labels['header'] - site - 4) // 2) & 0x7FF))
        with self.assertRaisesRegex(ValueError, 'conditional backward edge'):
            phases(bytes(data), calls)


class RankOracleTests(unittest.TestCase):
    def test_u8_load_form_is_bounded_for_every_incoming_value_and_limit_sequence(self):
        incoming = list(range(256)) + [0x1FF, 0x12345678, 0xFFFFFFFF]
        for start in incoming:
            for limit in range(256):
                with self.subTest(start=start, limit=limit):
                    entries = iterations(8, start, [limit] * 300, limit_bits=8)
                    self.assertIsNotNone(entries)
                    self.assertLessEqual(entries, 256)
        # Adversarial limits that change every iteration stay bounded too.
        import random
        generator = random.Random(8)
        for start in incoming:
            for _ in range(20):
                limits = [generator.choice((0, 1, 254, 255, generator.randrange(256))) for _ in range(300)]
                self.assertLessEqual(iterations(8, start, limits, limit_bits=8), 256)
            self.assertLessEqual(iterations(8, start, [255, 0] * 150, limit_bits=8), 256)

    def test_u8_immediate_forms(self):
        for start in range(256):
            self.assertLessEqual(iterations(8, start, [254] * 300, inclusive=True), 256)
            self.assertLessEqual(iterations(8, start, [255] * 300), 256)

    def test_refused_forms_really_wrap(self):
        # The shapes the recognizer refuses do not terminate on this oracle.
        self.assertIsNone(iterations(8, 0, [256] * 600, limit_bits=16))
        self.assertIsNone(iterations(8, 0, [255] * 600, inclusive=True))
        self.assertIsNone(iterations(8, 0, [0xFFFFFFFF] * 600))

    def test_u16_counter_never_wraps_below_its_bound(self):
        for counter in range(65535):
            successor = ((counter + 1) << 16 & 0xFFFFFFFF) >> 16
            self.assertEqual(successor, counter + 1)


class ReplayTests(unittest.TestCase):
    def test_complete_frame_replay_and_manifest(self):
        data, calls, labels = caller()
        p = bound(data, calls)
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
        report = p.contract_manifest()
        self.assertEqual(report['schema'], 'elf-symbol-thumb-' + SELECTOR)
        self.assertEqual(set(p.observations), set(calls))
        loops = report['branch_calls']['counted_loops']
        self.assertEqual(loops[0]['maximum_scheduler_calls'], 256)
        self.assertFalse(report['termination_proved'])
        self.assertFalse(report['branch_calls']['unconditional_termination_proved'])
        self.assertIn('live private-local aliases may', report['branch_calls']['ordinary_call_contract'])
        self.assertIn('at most once per iteration', ' '.join(report['assumptions']))
        self.assertIn('without rewriting it', ' '.join(report['assumptions']))

    def test_preserved_live_alias_across_looped_ordinary_calls(self):
        data, calls, labels = caller(preserved_alias=True, scheduler_in_loop=False)
        p = bound(data, calls)
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
        self.assertEqual(p.observations[labels['ordinary']]['kind'], 'live-local-alias-ordinary-call')

    def test_preserved_alias_across_a_looped_scheduler_call_is_refused(self):
        data, calls, _ = caller(preserved_alias=True)
        p = bound(data, calls)
        with self.assertRaisesRegex(ValueError, 'other than the R2 descriptor'):
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_alias_passed_in_an_argument_register_replays_the_callee(self):
        # mov r0, sp before the looped ordinary call: the callee body is replayed.
        data, calls, labels = caller(before_ordinary=(0x4668,))
        p = bound(data, calls, callee=half(0x7801, 0x2000, 0x4770))   # ldrb r1,[r0]; movs r0,#0; bx lr
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
        observation = p.observations[labels['ordinary']]
        self.assertEqual(observation['passed_aliases'], [(match.ARM_REG_R0, -48)])
        self.assertEqual((observation['access_lowest'], observation['access_end']), (-48, -47))

    def test_passed_alias_attacks_are_refused(self):
        data, calls, _ = caller(before_ordinary=(0x4668,))
        for callee, message in ((half(0x4770), 'return a local alias'),          # returns R0 = alias
                                (half(0x61C1, 0x2000, 0x4770), 'outside allocated local words'),               # str r1,[r0,#28]: saved r4 slot
                                (half(0x3804, 0x6801, 0x2000, 0x4770), 'outside allocated local words'),       # subs r0,#4; ldr r1,[r0]: below
                                (half(0x6000, 0x2000, 0x4770), 'cannot be stored')):  # str r0,[r0]: stores the alias
            with self.subTest(callee=callee.hex()):
                p = bound(data, calls, callee=callee)
                with self.assertRaisesRegex(ValueError, message):
                    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_old_selectors_still_refuse_the_loop(self):
        data, calls, _ = caller()
        for policy in (local.SCHEDULER_SEQUENTIAL, local.SCHEDULER_LIVE_ALIAS, local.SCHEDULER_BRANCH):
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'cycles'):
                bound(data, calls, policy)
        with self.assertRaises(ValueError):
            bound(data, calls, local.SCHEDULER_LOOP)

    def test_sequential_selector_still_refuses_the_live_alias(self):
        p = Program()
        p.emit(0xB5F0, 0xB087, 0xAE00)
        descriptor_call(p)
        p.call(B, 'ordinary')
        p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
        data, calls, _ = p.build()
        q = bound(data, calls, local.SCHEDULER_SEQUENTIAL)
        with self.assertRaisesRegex(ValueError, 'every live local alias'):
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=q)
        q = bound(data, calls)
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=q))

    def test_scheduler_descriptor_contract_is_unchanged(self):
        data, calls, labels = caller()
        p = bound(data, calls)
        stack = [(False, False, True)] * 7 + [(False, True, False)] * 5
        r2 = match.ARM_REG_R0 + 2
        for aliases, slots in (({r2: -48, match.ARM_REG_R0: -48}, {}), ({r2: -48}, {-44: -48}),
                               ({r2: -44}, {})):
            with self.subTest(aliases=aliases, slots=slots), self.assertRaises(ValueError):
                p.check_call(S, aliases, stack, slots, site=labels['scheduler'])

    def test_pointer_words_and_provenance_cannot_enter_ordinary_calls(self):
        data, calls, labels = caller()
        p = bound(data, calls)
        stack = [(False, False, True)] * 7 + [(False, True, False)] * 5
        for slots, words in (({-44: -48}, None), ({}, {-48: 'opaque'})):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                p.check_call(B, {}, stack, slots, site=labels['ordinary'], words=words)

    def test_selector_and_native_replay_registered(self):
        self.assertIn(SELECTOR, owner.named_buffer.SELECTORS)
        schema = local.SCHEMAS[SELECTOR]
        self.assertEqual(owner.selector_for_report('* verification: `' + schema + '`'), SELECTOR)
        data, calls, _ = caller()
        self.assertTrue(match._ordinary_call_replay(bound(data, calls), B))
        result = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
            '--owner-runtime-profile', SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == '__main__':
    unittest.main()
