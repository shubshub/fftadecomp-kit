"""Fresh raw Thumb fixtures for the isolated u16 scheduler loop selector."""
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
import owner_graph_profile as graph
import conditional_local_buffer_profile as local
import scheduler_counted_loop_profile as counted
from test_scheduler_predicates import half, bl, fixture, A, B, C, R0, LOCAL, SAVED

# A stand-in for the pinned scheduler that is a function: callers keep stack addresses in
# R4-R11 across it, and the callee-saved check walks it (kit #350). 29 x movs r0,r0; bx lr.
SCHEDULER_STUB = bytes(58) + b'\x70\x47'

S = counted.SCHEDULER


def caller(*, counter=5, limit=6, alias=False, extra_cycle=False, high_saves=False, base=A):
    data = bytearray(half(0xb5f0))
    if high_saves:
        data += half(0x464f, 0x4646, 0xb4c0)
    data += half(0xb087, 0x0412, 0x0c10 | limit, 0x2000 | (counter << 8))
    comparison = 0x4280 | (limit << 3) | counter
    labels = {}
    calls = {}
    def emit(*words):
        data.extend(half(*words))
    def label(name):
        labels[name] = base + len(data)
    label('guard_cmp'); emit(comparison)
    label('guard'); emit(0xd200)
    label('header')
    emit(0x4669, 0x2000, 0x8288, 0x2100, 0x2118, 0xaa00, 0x2300)
    if alias:
        emit(0x466c)
    if extra_cycle:
        emit(0xe7fe)
    label('scheduler'); calls[base + len(data)] = S
    data.extend(bl(base + len(data), S))
    emit(0x2800)
    label('skip'); emit(0xd000)
    label('ordinary'); calls[base + len(data)] = B
    data.extend(bl(base + len(data), B))
    label('tail')
    emit(0x1c40 | (counter << 3), 0x0400, 0x0c00 | counter, comparison)
    label('latch'); emit(0xd300)
    label('exit'); emit(0xb007)
    if high_saves:
        emit(0xbc18, 0x4698, 0x46a1)
    emit(0xbcf0, 0xbc01, 0x4700)
    for source, destination in (('guard', 'exit'), ('skip', 'tail'), ('latch', 'header')):
        off = labels[source] - base
        word = struct.unpack_from('<H', data, off)[0]
        struct.pack_into('<H', data, off, word | (((labels[destination] - labels[source] - 4) // 2) & 255))
    return bytes(data), calls, labels


def decoded(data, calls, base=A):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    instructions = {i.address: i for i in decoder.disasm(data, base)}
    edges = {}
    for s, i in instructions.items():
        if i.mnemonic == 'bx':
            edges[s] = ()
        elif i.id == match.ARM_INS_B:
            edges[s] = ((i.operands[0].imm,) if i.mnemonic == 'b' else
                        (i.operands[0].imm, s + i.size))
        else:
            edges[s] = (s + i.size,)
    return instructions, edges


def layout(data, calls, base=A):
    ins, edges = decoded(data, calls, base)
    return counted.layout(ins, edges, calls, base)


def bound(data, calls, policy=local.SCHEDULER_LOOP):
    bodies = {A: data, B: half(0x4770), S: SCHEDULER_STUB, 0x08005954: bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items()
            if a in (S, 0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES, pins), mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p


def altered(data, site, word):
    result = bytearray(data)
    struct.pack_into('<H', result, site - A, word)
    return bytes(result)


def raw_counter_oracle(data, labels, incoming):
    """Raw arithmetic/flag oracle, independent of the layout recognizer."""
    regs = [0] * 8
    regs[2] = incoming
    start = A + 4
    stop = labels['guard']
    visits = 0
    while True:
        for s in range(start, stop, 2):
            h = struct.unpack_from('<H', data, s - A)[0]
            d, n = h & 7, (h >> 3) & 7
            if h & 0xf800 == 0:
                regs[d] = (regs[n] << ((h >> 6) & 31)) & 0xffffffff
            elif h & 0xf800 == 0x0800:
                regs[d] = regs[n] >> (((h >> 6) & 31) or 32)
            elif h & 0xf800 == 0x2000:
                regs[(h >> 8) & 7] = h & 255
            elif h & 0xfe00 == 0x1c00:
                regs[d] = (regs[n] + ((h >> 6) & 7)) & 0xffffffff
            elif h & 0xffc0 == 0x4280:
                carry = regs[d] >= regs[n]
            else:
                raise AssertionError('oracle encountered an unexpected control instruction')
        branch = struct.unpack_from('<H', data, stop - A)[0]
        taken = carry if branch & 0xff00 == 0xd200 else not carry
        if (stop == labels['guard'] and taken) or (stop == labels['latch'] and not taken):
            return visits
        visits += 1
        if visits > 65535:
            raise AssertionError('oracle observed an extra iteration')
        start, stop = labels['tail'], labels['latch']


class CountedSchedulerTests(unittest.TestCase):
    def test_complete_raw_frame_and_conditional_helper(self):
        data, calls, labels = caller()
        p = bound(data, calls)
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
        report = p.contract_manifest()
        self.assertEqual(report['branch_calls']['maximum_iterations'], 65535)
        self.assertEqual(set(p.observations), set(calls))
        self.assertEqual(report['branch_calls']['header'], labels['header'])

    def test_high_register_save_frame(self):
        data, calls, _ = caller(high_saves=True)
        p = bound(data, calls)
        self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))

    def test_register_roles_are_generic(self):
        for counter, limit in ((4, 7), (6, 5), (7, 4)):
            with self.subTest(counter=counter, limit=limit):
                data, calls, _ = caller(counter=counter, limit=limit)
                result = layout(data, calls)
                self.assertEqual((result['counter_register'], result['limit_register']), (counter, limit))

    def test_owner_address_is_not_a_whitelist(self):
        data, calls, labels = caller(base=A + 0x400)
        self.assertEqual(layout(data, calls, A + 0x400)['header'], labels['header'])

    def test_independent_raw_oracle_zero_small_and_maximum_counts(self):
        data, _, labels = caller()
        for incoming in (0, 1, 2, 257, 65534, 65535, 0x12340000, 0xabcd0001, 0xffffffff):
            with self.subTest(incoming=incoming):
                self.assertEqual(raw_counter_oracle(data, labels, incoming), incoming & 65535)

    def test_rank_and_increment_no_wrap_for_all_u16_counters(self):
        for counter in range(65535):
            successor = ((counter + 1) << 16 & 0xffffffff) >> 16
            self.assertEqual(successor, counter + 1)
            self.assertEqual(65535 - successor, 65535 - counter - 1)

    def test_old_acyclic_selectors_still_reject_loop(self):
        data, calls, _ = caller()
        for policy in (local.SCHEDULER_BRANCH, local.SCHEDULER_FOLLOWING, local.SCHEDULER_WIDE):
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'cycles'):
                bound(data, calls, policy)

    def test_old_single_scheduler_selector_still_rejects_helper(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'one actual scheduler call'):
            bound(data, calls, local.SCHEDULER)

    def test_inclusive_backedge_rejected(self):
        data, calls, labels = caller()
        with self.assertRaisesRegex(ValueError, 'strict less-than'):
            layout(altered(data, labels['latch'], 0xd900 | (data[labels['latch'] - A])), calls)

    def test_signed_backedge_rejected(self):
        data, calls, labels = caller()
        with self.assertRaisesRegex(ValueError, 'strict less-than'):
            layout(altered(data, labels['latch'], 0xdb00 | data[labels['latch'] - A]), calls)

    def test_wrong_entry_guard_rejected(self):
        data, calls, labels = caller()
        with self.assertRaises(ValueError):
            layout(altered(data, labels['guard'], 0xd300 | data[labels['guard'] - A]), calls)

    def test_nonzero_counter_initialization_rejected(self):
        data, calls, labels = caller()
        with self.assertRaisesRegex(ValueError, 'zero initialization'):
            layout(altered(data, labels['guard'] - 4, 0x2501), calls)

    def test_missing_bound_narrowing_rejected(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'right16'):
            layout(altered(data, A + 6, 0x4616), calls)

    def test_mismatched_bound_narrowing_rejected(self):
        data, calls, _ = caller()
        with self.assertRaisesRegex(ValueError, 'left16'):
            layout(altered(data, A + 4, 0x03d2), calls)

    def test_wrong_update_increment_rejected(self):
        data, calls, labels = caller()
        with self.assertRaisesRegex(ValueError, 'exactly one'):
            layout(altered(data, labels['tail'], 0x1ca8), calls)

    def test_wrong_successor_narrowing_rejected(self):
        data, calls, labels = caller()
        with self.assertRaisesRegex(ValueError, 'u16 successor'):
            layout(altered(data, labels['tail'] + 4, 0x0bc5), calls)

    def test_clobbered_counter_register_rejected(self):
        data, calls, _ = caller(counter=3)
        with self.assertRaisesRegex(ValueError, 'ABI-preserved counter'):
            layout(data, calls)

    def test_clobbered_limit_register_rejected(self):
        data, calls, _ = caller(limit=2)
        with self.assertRaisesRegex(ValueError, 'limit must be distinct'):
            layout(data, calls)

    def test_body_counter_or_bound_write_rejected(self):
        data, calls, labels = caller()
        for word in (0x2500, 0x2600):
            with self.subTest(word=word), self.assertRaisesRegex(ValueError, 'modifies its counter or bound'):
                layout(altered(data, labels['header'], word), calls)

    def test_additional_cycle_rejected(self):
        data, calls, _ = caller(extra_cycle=True)
        with self.assertRaisesRegex(ValueError, 'one backward edge'):
            layout(data, calls)

    def test_unguarded_loop_entry_rejected(self):
        data, calls, labels = caller()
        ins, edges = decoded(data, calls)
        edges[A] = (A + 2, labels['header'] + 2)
        with self.assertRaises(ValueError):
            counted.layout(ins, edges, calls, A)

    def test_tail_bypass_rejected(self):
        data, calls, labels = caller()
        ins, edges = decoded(data, calls)
        edges[labels['skip']] = (labels['exit'], labels['ordinary'])
        with self.assertRaisesRegex(ValueError, 'bypasses its update'):
            counted.layout(ins, edges, calls, A)

    def test_second_scheduler_site_rejected(self):
        data, calls, labels = caller()
        calls[labels['ordinary']] = S
        with self.assertRaisesRegex(ValueError, 'one scheduler site'):
            layout(data, calls)

    def test_call_outside_loop_rejected(self):
        data, calls, _ = caller()
        calls[A] = B
        with self.assertRaisesRegex(ValueError, 'call-free'):
            layout(data, calls)

    def test_live_local_alias_at_ordinary_helper_rejected(self):
        data, calls, _ = caller(alias=True)
        p = bound(data, calls)
        with self.assertRaisesRegex(ValueError, 'every live local alias'):
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_scheduler_frame_extent_stays_strict(self):
        data, calls, labels = caller()
        data = altered(data, labels['header'] + 10, 0xaa01)
        p = bound(data, calls)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_pointer_words_and_provenance_cannot_enter_helper(self):
        data, calls, labels = caller()
        p = bound(data, calls)
        for slots, words in (({-24: -48}, None), ({}, {-48: 'opaque'})):
            with self.subTest(slots=slots), self.assertRaises(ValueError):
                p.check_call(B, {}, [LOCAL] * 7 + [SAVED] * 5, slots,
                             site=labels['ordinary'], words=words)

    def test_manifest_keeps_lifetime_memory_and_termination_conditions(self):
        data, calls, _ = caller()
        p = bound(data, calls)
        match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
        report = p.contract_manifest()
        self.assertFalse(report['actual_callback_effects_proved'])
        self.assertFalse(report['nonescape_proved'])
        self.assertFalse(report['termination_proved'])
        self.assertFalse(report['branch_calls']['actual_count_or_capacity_proved'])
        self.assertFalse(report['branch_calls']['unconditional_termination_proved'])
        self.assertIn('previous invocations retain no local pointer', ' '.join(report['branch_calls']['conditions']))

    def test_selector_and_native_replay_registered(self):
        self.assertIn(local.SCHEDULER_LOOP, owner.named_buffer.SELECTORS)
        schema = local.SCHEMAS[local.SCHEDULER_LOOP]
        self.assertEqual(owner.selector_for_report('* verification: `' + schema + '`'), local.SCHEDULER_LOOP)
        data, calls, _ = caller()
        self.assertTrue(match._ordinary_call_replay(bound(data, calls), B))
        result = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
            '--owner-runtime-profile', local.SCHEDULER_LOOP, '--help'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)


def looped_alias_caller(before=(), after=(), *, high_saves=False):
    """The counted loop over a 32-byte frame: the descriptor at SP, one more private word at SP+28.

    before and after are emitted on each side of the looped scheduler call.
    """
    data = bytearray(half(0xb5f0))
    if high_saves:
        data += half(0x464f, 0x4646, 0xb4c0)
    data += half(0xb088, 0x0412, 0x0c16, 0x2500, 0x42b5)    # sub sp, #32; r6 = (u16)r2; r5 = 0; cmp r5, r6
    guard = len(data)
    data += half(0xd200, 0x4669, 0x2000, 0x8288, 0x2100, 0x2118, 0xaa00, 0x2300, *before)
    scheduler = A + len(data)
    data += bl(scheduler, S) + half(*after, 0x2800)
    skip = len(data)
    data += half(0xd000)
    ordinary = A + len(data)
    data += bl(ordinary, B)
    tail = len(data)
    data += half(0x1c68, 0x0400, 0x0c05, 0x42b5)            # r5 = (u16)(r5 + 1); cmp r5, r6
    latch = len(data)
    data += half(0xd300, 0xb008)
    if high_saves:
        data += half(0xbc18, 0x4698, 0x46a1)
    data += half(0xbcf0, 0xbc01, 0x4700)
    for source, destination in ((guard, latch + 2), (skip, tail), (latch, guard + 2)):
        data[source] = (destination - source - 4) // 2 & 255
    return bytes(data), {scheduler: S, ordinary: B}, scheduler


class LoopedSiteAliasTests(unittest.TestCase):
    """The one scheduler site of this selector is inside its loop, and neither it nor its callback is walked."""

    def test_descriptor_alone_at_the_looped_scheduler_site(self):
        for shape, offset in ((dict(), -52), (dict(high_saves=True), -60)):
            with self.subTest(shape=shape):
                data, calls, site = looped_alias_caller(**shape)
                p = bound(data, calls)
                self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
                self.assertEqual(p.observations[site]['aliases'], [(R0 + 2, offset)])

    def test_descriptor_address_copy_across_the_looped_scheduler_call(self):
        # The copy dies before the ordinary helper, which admits no alias at all.
        for register in (4, 7):
            with self.subTest(register=register):
                data, calls, site = looped_alias_caller((0xA800 | register << 8,),      # add rX, sp, #0
                                                        (0x2000 | register << 8,))      # movs rX, #0
                p = bound(data, calls)
                self.assertTrue(match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p))
                self.assertEqual(p.observations[site]['aliases'], [(R0 + 2, -52), (R0 + register, -52)])

    def test_looped_scheduler_call_refuses_every_other_preserved_alias(self):
        # Each alias dies before the ordinary helper, so only the looped scheduler site can refuse it.
        cases = (('another private object', dict(), (0xAC07,), (0x2400,)),      # add r4, sp, #28; movs r4, #0
                 ('interior address', dict(), (0xAF01,), (0x2700,)),            # add r7, sp, #4; movs r7, #0
                 ('high register', dict(high_saves=True),                       # r8 = sp through r4
                  (0xAC00, 0x46A0, 0x2400), (0x46A0,)))                         # mov r8, r4 on each side
        for name, shape, before, after in cases:
            with self.subTest(case=name):
                data, calls, _ = looped_alias_caller(before, after, **shape)
                p = bound(data, calls)
                with self.assertRaisesRegex(ValueError, 'other than the R2 descriptor and R4-R7 copies'):
                    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)

    def test_looped_site_alias_rule_on_the_tracked_state(self):
        stack = [LOCAL] * 8 + [SAVED] * 5
        data, calls, site = looped_alias_caller()
        for aliases, message in (({R0+2: -52, R0+4: -24}, 'R4-R7 copies'),
                                 ({R0+2: -52, R0+7: -48}, 'R4-R7 copies'),
                                 ({R0+2: -52, R0+4: -52, R0+5: -24}, 'R4-R7 copies'),
                                 ({R0+2: -48, R0+4: -52}, 'R4-R7 copies'),       # descriptor at SP+4, R4 at SP
                                 ({R0+2: -52, R0+8: -52}, 'R4-R7 copies'),
                                 ({R0+2: -52, R0+9: -52}, 'R4-R7 copies'),
                                 ({R0+2: -52, R0+11: -52}, 'R4-R7 copies'),
                                 ({R0+2: -52, R0+3: -52}, 'additional register'),
                                 ({R0+2: -52, R0+12: -52}, 'additional register')):
            with self.subTest(aliases=aliases), self.assertRaisesRegex(ValueError, message):
                bound(data, calls).check_call(S, aliases, stack, {}, site=site)
        p = bound(data, calls)
        p.check_call(S, {R0+2: -52, R0+4: -52, R0+7: -52}, stack, {}, site=site)
        self.assertEqual(p.observations[site]['aliases'], [(R0+2, -52), (R0+4, -52), (R0+7, -52)])


if __name__ == '__main__':
    unittest.main()
