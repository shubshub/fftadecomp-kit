"""named-data-buffer-stack-index-v2: forwarded callee stack arguments and ASR congruence."""
import copy
import hashlib
import itertools
import types
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import stack_index_precondition_profile as sip
from test_nested_known_query import assemble
from test_rom_table_copy import fixture, OWNER
from test_stack_index_precondition import admit, evidence, owner_code

V1, V2 = sip.SELECTOR, sip.SELECTOR_V2
FORWARDER, LEAF, OTHER = 0x08014000, 0x08015000, 0x08016000

# Leaf: ldr r1,[sp,#0]; movs r0,#0; strh r0,[r1]; bx lr - writes through its fifth argument.
LEAF_CODE = (0x9900, 0x2000, 0x8008, 0x4770)
# Forwarder: push {lr}; sub sp,#4; str r1,[sp]; bl LEAF; add sp,#4; pop {r0}; bx r0.
FORWARDER_CODE = (0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xbc01, 0x4700)


def forwarding(forwarder=FORWARDER_CODE, leaf=LEAF_CODE, selector=V2, tail=(0xa901, FORWARDER),
               other=(0x4770,)):
    """The masked-index owner, then by default `add r1,sp,#4; bl FORWARDER` passing its free
    local word. OTHER is a further function the forwarder or the owner may call."""
    patch = {}
    spans = []
    for address, code in ((FORWARDER, forwarder), (LEAF, leaf), (OTHER, other)):
        raw = assemble(address, code)
        patch.update({address + offset: value for offset, value in enumerate(raw)})
        spans.append((address, len(raw), len(code)))
    return dict(code=owner_code(tail=tail), selector=selector, patch_rom=patch,
                extra_functions=tuple(spans))


def forwarded(manifest):
    return evidence(manifest)['forwarded_stack_arguments']


class ForwardedStackArgumentTests(unittest.TestCase):
    def test_v2_admits_a_pointer_forwarded_as_a_callee_stack_argument(self):
        arguments, (manifest, _) = admit(**forwarding())
        self.assertEqual(manifest['profile'], sip.SCHEMA_V2)
        self.assertEqual(evidence(manifest)['schema'], sip.SCHEMA_V2)
        # The manifest replays under v2 and is stale under v1.
        owner.verify(**arguments, manifest=copy.deepcopy(manifest))
        with self.assertRaises(ValueError):
            owner.verify(**dict(arguments, selector=V1), manifest=copy.deepcopy(manifest))

    def test_v1_still_refuses_the_forwarded_pointer(self):
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            admit(**forwarding(selector=V1))

    def test_forwarded_pointer_stays_bounded_in_the_next_callee(self):
        # strh r0,[r1,#8]: sp+4+8 is past the owner's two local words.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            admit(**forwarding(leaf=(0x9900, 0x2000, 0x8108, 0x4770)))

    def test_reloaded_slot_is_the_pointer_again(self):
        # ldr r2,[sp]; strh r0,[r2,#8]; movs r2,#0 after the call: the reload is tracked and refused.
        code = (0xb500, 0xb081, 0x9100, LEAF, 0x9a00, 0x8110, 0x2200, 0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            admit(**forwarding(forwarder=code))
        # The in-bounds reload is admitted.
        admit(**forwarding(forwarder=(0xb500, 0xb081, 0x9100, LEAF, 0x9a00, 0x8010, 0x2200,
                                      0xb001, 0xbc01, 0x4700)))

    def test_slot_outside_the_callee_frame_refuses(self):
        # str r1,[sp,#8]: the caller's incoming argument area (the core refuses it first).
        code = (0xb500, 0xb081, 0x9102, LEAF, 0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, "outside the callee's own frame|outside the tracked frame"):
            admit(**forwarding(forwarder=code))

    def test_slot_in_a_saved_register_word_refuses(self):
        # push {r4,lr}; str r1,[sp]; bl; pop {r4}; pop {r0}; bx r0: R4 would receive the pointer.
        code = (0xb510, 0x9100, LEAF, 0xbc10, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'restored into a register'):
            admit(**forwarding(forwarder=code))

    def test_forwarder_may_not_materialize_sp(self):
        # mov r2,sp; ldr r3,[r2]; movs r2,#0 after the store reads the slot as a scalar.
        code = (0xb500, 0xb081, 0x9100, 0x466a, 0x6813, 0x2200, LEAF, 0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'only immediate SP uses'):
            admit(**forwarding(forwarder=code))

    def test_scalar_store_kills_the_slot(self):
        # movs r2,#0; str r2,[sp] before the call: the leaf receives a scalar, not the pointer,
        # so its out-of-bounds write is not a buffer access.
        code = (0xb500, 0xb081, 0x9100, 0x2200, 0x9200, LEAF, 0xb001, 0xbc01, 0x4700)
        admit(**forwarding(forwarder=code, leaf=(0x9900, 0x2000, 0x8108, 0x4770)))

    def test_report_selects_v2(self):
        arguments, (manifest, instructions) = admit(**forwarding())
        result = (arguments['data'], manifest, hashlib.sha256(b's').hexdigest(), arguments['mapping'],
                  arguments['index'], arguments['objects'], arguments['rom'], len(instructions), b'elf')
        report = owner.render(OWNER, result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), V2)
        self.assertIn(f'* owner runtime: {V2}', report)
        self.assertIn(sip.CONTROL_FLOW_V2, report)
        relabelled = report.replace(sip.SCHEMA_V2, sip.SCHEMA)
        self.assertEqual(owner.selector_for_report(relabelled), V1)
        line, = sip.forwarded_lines(evidence(manifest))
        self.assertIn(line, report.splitlines())
        self.assertIn('unproved runtime premise', line)

    def test_evidence_lists_each_forwarded_slot_and_released_word(self):
        _, (manifest, _) = admit(**forwarding())
        found = forwarded(manifest)
        (callee, site, slot, _), = found['slots']
        # push {lr}; sub sp,#4: the slot is the callee's word at entry_SP-8, stored at +4.
        self.assertEqual((callee, site, slot), (FORWARDER, FORWARDER + 4, -8))
        # The owner called with two saved and two local words live, so the released
        # word is at owner entry_SP-24, after the BL of the tail.
        (call, positions), = found['released']
        self.assertEqual(positions, [-24])
        self.assertEqual((found['premise'], found['premise_proved']), (sip.FORWARD_PREMISE, False))


class ReleasedWordTests(unittest.TestCase):
    """`add sp,#n` frees a forwarded slot but the pointer stays in memory below SP."""

    def test_shape1_forwarder_re_covers_and_reads_the_released_word(self):
        # ...; add sp,#4; sub sp,#4; ldr r2,[sp]; movs r0,#0; strh r0,[r2,#8]; movs r2,#0; ...
        code = (0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xb081, 0x9a00, 0x2000, 0x8110, 0x2200,
                0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=code))
        # Writing the word first (movs r2,#0; str r2,[sp]) removes the pointer.
        admit(**forwarding(forwarder=(0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xb081, 0x2200, 0x9200,
                                      0x9a00, 0x2200, 0xb001, 0xbc01, 0x4700)))

    def test_shape1_push_then_sub_re_covers_the_released_word(self):
        # push {lr}; sub sp,#8; str r1,[sp]; bl; add sp,#8; push {r0}; sub sp,#4; ldr r2,[sp]; ...
        code = (0xb500, 0xb082, 0x9100, LEAF, 0xb002, 0xb401, 0xb081, 0x9a00, 0x2000, 0x8110, 0x2200,
                0xb001, 0xbc02, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=code))

    def test_shape2_walked_next_callee_re_covers_and_reads_it(self):
        # Forwarder: str r1,[sp]; add sp,#4; bl OTHER with r1 still the alias, so OTHER is walked
        # and inherits the word. OTHER: sub sp,#4; ldr r1,[sp]; add sp,#4; strh r0,[r1,#8].
        forwarder = (0xb500, 0xb081, 0x9100, 0xb001, OTHER, 0xbc01, 0x4700)
        other = (0xb081, 0x9900, 0xb001, 0x2000, 0x8108, 0x2100, 0x4770)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=forwarder, other=other))

    def test_shape2_trusted_next_callee_with_word_below_sp(self):
        # add sp,#4 leaves the released word at entry_SP-8, below the forwarder's SP; movs r1,#0;
        # bl OTHER with no stack pointer. OTHER is below SP, so it is trusted, not walked.
        forwarder = (0xb500, 0xb081, 0x9100, 0xb001, 0x2100, OTHER, 0xbc01, 0x4700)
        other = (0x4770,)
        _, (manifest, _) = admit(**forwarding(forwarder=forwarder, other=other))
        found = forwarded(manifest)
        self.assertEqual(found['trusted_callee_calls'], [[FORWARDER, FORWARDER + 10, OTHER]])
        self.assertEqual(found['premise'], sip.FORWARD_PREMISE)

    def test_blocker_recovered_word_in_a_trusted_callee_is_refused(self):
        # push{lr}; sub sp,#4; str r1,[sp]; add sp,#4; sub sp,#4; movs r1,#0; bl LEAF; add sp,#4;
        # pop{r0}; bx r0. The release-then-recover leaves the word at the forwarder's SP, so LEAF
        # (which reads it in its incoming area) is walked, not trusted, and its read refuses.
        forwarder = (0xb500, 0xb081, 0x9100, 0xb001, 0xb081, 0x2100, LEAF, 0xb001, 0xbc01, 0x4700)
        leaf = (0x9900, 0x2000, 0x8108, 0x4770)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=forwarder, leaf=leaf))


    def test_shape3a_owner_re_covers_the_released_word(self):
        # Owner after the call: sub sp,#8; ldr r0,[sp]; movs r1,#0; strh r1,[r0,#8]; movs r0,#0; add sp,#8.
        tail = (0xa901, FORWARDER, 0xb082, 0x9800, 0x2100, 0x8101, 0x2000, 0xb002)
        with self.assertRaisesRegex(ValueError, 'owner moves SP down after a callee released'):
            admit(**forwarding(tail=tail))

    def test_shape3b_trusted_owner_callee_is_under_the_recorded_premise(self):
        # movs r1,#0; bl OTHER (the leaf hands the alias back in r1, so clear it): OTHER gets no
        # stack pointer and the released word is below the owner's SP, so it is trusted.
        other = (0x4770,)
        _, (manifest, _) = admit(**forwarding(tail=(0xa901, FORWARDER, 0x2100, OTHER), other=other))
        found = forwarded(manifest)
        self.assertTrue(found['released'])
        self.assertEqual(found['premise'], sip.FORWARD_PREMISE)
        self.assertIn('trusted calls', sip.forwarded_lines(evidence(manifest))[0])

    def test_owner_trusted_callee_that_reads_below_its_sp_is_not_caught(self):
        # Documents the premise: a pointer-free owner callee reading below its entry SP is
        # trusted, not inspected. It is admitted; soundness rests on FORWARD_PREMISE.
        other = (0xb082, 0x9900, 0x2000, 0x8108, 0xb002, 0x2100, 0x4770)
        admit(**forwarding(tail=(0xa901, FORWARDER, 0x2100, OTHER), other=other))

    def test_one_path_release_joins_then_refuses_or_clears(self):
        # cmp r0,#0; beq SKIP; (release path) add sp,#4; sub sp,#4; SKIP: ldr r2,[sp]; strh r0,[r2,#8].
        # On the taken path the word is live; on the fall path it is released and re-covered.
        refuse = (0xb500, 0xb081, 0x9100, LEAF, 0x2800, 0xd001, 0xb001, 0xb081, 0x9a00, 0x2000,
                  0x8110, 0x2200, 0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=refuse))
        # The same, but the merged read is preceded by a store that clears the word.
        clear = (0xb500, 0xb081, 0x9100, LEAF, 0x2800, 0xd001, 0xb001, 0xb081, 0x2200, 0x9200,
                 0x9a00, 0x2200, 0xb001, 0xbc01, 0x4700)
        admit(**forwarding(forwarder=clear))

    def test_loop_releases_inside_its_body(self):
        # A back-edge over a release-and-recover: cmp r0,#0; beq END; str r1,[sp]; add sp,#4;
        # sub sp,#4; ldr r2,[sp]; strh r0,[r2,#8]; b LOOP; END.
        # push{lr}; sub sp,#4; LOOP: str r1,[sp]; add sp,#4; sub sp,#4; ldr r2,[sp];
        # strh r0,[r2,#8]; cmp r0,#0; bne LOOP; add sp,#4; pop{r0}; bx r0.
        body = (0xb500, 0xb081, 0x9100, 0xb001, 0xb081, 0x9a00, 0x8110, 0x2800, 0xd1f8,
                0xb001, 0xbc01, 0x4700)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=body))

    def test_walked_callee_re_covers_inherited_word_then_makes_a_pointer_free_call(self):
        # Forwarder: push{lr}; sub sp,#8; str r1,[sp]; add sp,#8; bl OTHER with r1 still the
        # alias, so OTHER is walked and inherits the word at its entry_SP-8.
        # OTHER: push{lr}; sub sp,#4 (re-covers the word); movs r1,#0; bl LEAF; add sp,#4;
        # pop{r0}; bx r0. The word is now at OTHER's SP, so the pointer-free LEAF is walked and
        # its ldr r1,[sp] of the word refuses.
        forwarder = (0xb500, 0xb082, 0x9100, 0xb002, OTHER, 0xbc01, 0x4700)
        other = (0xb500, 0xb081, 0x2100, LEAF, 0xb001, 0xbc01, 0x4700)
        leaf = (0x9900, 0x2000, 0x8108, 0x2100, 0x4770)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=forwarder, leaf=leaf, other=other))

    def test_released_word_inherited_at_or_above_a_callee_entry_sp(self):
        # push{lr}; sub sp,#4; str r1,[sp]; add sp,#4; sub sp,#4; movs r1,#0; bl LEAF: the recover
        # puts the word at the forwarder's SP, i.e. LEAF's incoming area, so LEAF is walked even
        # with no stack pointer and its read of the word refuses.
        forwarder = (0xb500, 0xb081, 0x9100, 0xb001, 0xb081, 0x2100, LEAF, 0xb001, 0xbc01, 0x4700)
        leaf = (0x9900, 0x2000, 0x8108, 0x4770)
        with self.assertRaisesRegex(ValueError, 'released forwarded pointer word before it is written'):
            admit(**forwarding(forwarder=forwarder, leaf=leaf))

    def test_owner_may_not_walk_a_callee_after_a_release(self):
        # A second `add r1,sp,#4; bl FORWARDER`: the walked callee is not told about the word.
        with self.assertRaisesRegex(ValueError, 'passes stack pointers to a callee after'):
            admit(**forwarding(tail=(0xa901, FORWARDER, 0xa901, FORWARDER)))


class ForwardedSlotShapeTests(unittest.TestCase):
    def test_conditional_store_merges_at_a_join(self):
        # cmp r0,#0; beq over the store: the merged slot is still the pointer, still bounded.
        code = (0xb500, 0xb081, 0x2800, 0xd000, 0x9100, LEAF, 0xb001, 0xbc01, 0x4700)
        admit(**forwarding(forwarder=code))
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            admit(**forwarding(forwarder=code, leaf=(0x9900, 0x2000, 0x8108, 0x4770)))

    def test_slot_live_across_two_calls(self):
        code = (0xb500, 0xb081, 0x9100, LEAF, LEAF, 0xb001, 0xbc01, 0x4700)
        _, (manifest, _) = admit(**forwarding(forwarder=code))
        self.assertEqual(len(forwarded(manifest)['slots']), 1)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            admit(**forwarding(forwarder=code, leaf=(0x9900, 0x2000, 0x8108, 0x4770)))

    def test_multiple_live_slots(self):
        # Owner: add r1,sp,#4; adds r2,r1,#2. Forwarder: sub sp,#8; str r1,[sp]; str r2,[sp,#4].
        # Leaf: ldr r1,[sp]; ldr r2,[sp,#4]; strh r0,[r1]; strh r0,[r2]; clear r1, r2.
        tail = (0xa901, 0x1c8a, FORWARDER)
        forwarder = (0xb500, 0xb082, 0x9100, 0x9201, LEAF, 0xb002, 0xbc01, 0x4700)
        leaf = (0x9900, 0x9a01, 0x2000, 0x8008, 0x8010, 0x2100, 0x2200, 0x4770)
        _, (manifest, _) = admit(**forwarding(forwarder=forwarder, leaf=leaf, tail=tail))
        self.assertEqual(len(forwarded(manifest)['slots']), 2)
        self.assertEqual(len(forwarded(manifest)['released'][0][1]), 2)
        bad = (0x9900, 0x9a01, 0x2000, 0x8008, 0x8110, 0x2100, 0x2200, 0x4770)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            admit(**forwarding(forwarder=forwarder, leaf=bad, tail=tail))

    def test_literal_sp_release_is_refused(self):
        # add sp,r3 (ldr r3,=4) is not an immediate SP use, so the forwarder may not hold a slot.
        code = (0xb500, 0xb081, 0x9100, LEAF, 0x4b02, 0x449d, 0xbc01, 0x4700, 0x0000, 0x0004, 0x0000)
        with self.assertRaisesRegex(ValueError, 'only immediate SP uses'):
            admit(**forwarding(forwarder=code))

    def test_leaf_may_not_write_its_incoming_forwarded_word(self):
        # movs r0,#0; str r0,[sp]: the receiving callee's core refuses the incoming-area write.
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            admit(**forwarding(leaf=(0x2000, 0x9000, 0x4770)))

    def test_receiver_may_not_read_the_word_through_a_materialised_sp(self):
        # mov r2,sp; ldr r1,[r2]: the receiving callee's core refuses a stack-alias access
        # outside its tracked frame, so only `ldr [sp,#imm]` (which yields the alias) reaches it.
        leaf = (0x466a, 0x6811, 0x2000, 0x8008, 0x2100, 0x2200, 0x4770)
        with self.assertRaisesRegex(ValueError, 'outside the tracked frame'):
            admit(**forwarding(leaf=leaf))

    def test_step_refuses_replay_and_frame_content_profiles(self):
        for flags in (dict(callee_frames=True), dict(word_provenance=True), dict(single_word_stores=True)):
            proof = types.SimpleNamespace(**dict(dict(callee_frames=False, word_provenance=False,
                                                      single_word_stores=False), **flags))
            with self.subTest(**flags), self.assertRaisesRegex(ValueError, 'exclude replay'):
                match.BufferCallProof.forwarded_slot_step(proof, 0, None, {}, {}, 0, {}, False)
        proof = types.SimpleNamespace(callee_frames=False, word_provenance=False, single_word_stores=False)
        with self.assertRaisesRegex(ValueError, 'exclude replay'):
            match.BufferCallProof.forwarded_slot_step(proof, 0, None, {}, {}, 0, {}, True)


class SignedShiftTests(unittest.TestCase):
    # lsls r4,r0,#24; asrs r4,r4,#22; ldr r0,[r0,r4]: an s8 index times four into two words.
    CODE = dict(count=8, index=(0x0604, 0x15A4), access=(0x5900,))

    def test_v1_cannot_align_a_sign_extended_word_index(self):
        with self.assertRaisesRegex(sip.Refusal, '4-byte aligned'):
            admit(owner_code(**self.CODE), selector=V1)

    def test_v2_aligns_it_and_still_needs_a_premise(self):
        arguments, _ = fixture(owner_code(**self.CODE), selector=V2)
        with self.assertRaises(sip.PremiseRefusal):
            owner.verify(**arguments)
        _, (manifest, _) = admit(owner_code(**self.CODE), selector=V2)
        row, = evidence(manifest)['preconditions']
        self.assertEqual((row['expression'], row['bound'], row['width']),
                         ('(u32)((entry_R0 << 24) >>s 22)', 5, 4))
        self.assertIn('index (u32)((entry_R0 << 24) >>s 22) < 5', sip.precondition_lines(evidence(manifest))[0])

    def test_odd_residue_stays_misaligned(self):
        # adds r4,#2 after the shift: every address is 4k+2, refused under v2 as well.
        with self.assertRaisesRegex(sip.Refusal, '4-byte aligned'):
            admit(owner_code(count=8, index=(0x0604, 0x15A4, 0x3402), access=(0x5900,)), selector=V2)

    def test_arithmetic_shift_contains_every_concrete_result(self):
        def members(value):
            _, lo, hi, modulus = value
            return range(lo, hi + 1, 1 << min(modulus, 32))

        def asr(x, amount):
            signed = x - (1 << 32) if x & 0x80000000 else x
            return (signed >> amount) & sip.MASK

        for modulus, residue, amount in itertools.product(range(0, 9), range(0, 7), range(1, 10)):
            lo = (0xFFFFFF00 + residue) & sip.MASK
            value = sip.norm('S', lo, sip.MASK - ((sip.MASK - lo) % (1 << modulus)), modulus)
            result = sip.arithmetic_shift_right(value, amount)
            for x in members(value):
                y = asr(x, amount)
                self.assertTrue(result[1] <= y <= result[2] and
                                (y - result[1]) % (1 << min(result[3], 32)) == 0,
                                (value, amount, x, y, result))
        # The s8-times-four case: (x << 24) has 24 low zero bits, ASR #22 leaves two.
        self.assertEqual(sip.arithmetic_shift_right(sip.shift_left(sip.TOP, 24), 22)[3], 2)
        self.assertEqual(sip.arithmetic_shift_right(sip.TOP, 3), sip.TOP)


if __name__ == '__main__':
    unittest.main()
