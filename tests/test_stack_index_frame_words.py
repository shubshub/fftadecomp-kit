"""Stack-index owners whose locals hold spilled stack addresses and counters (frame words)."""
import copy
from pathlib import Path
import struct
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import stack_index_frame_words_profile as fw
import stack_index_precondition_profile as sip
from test_nested_known_query import assemble
from test_rom_table_copy import fixture, HELPER, OWNER
from test_stack_index_precondition import reviewed

SELECTOR = sip.SELECTOR
RANGED = (0x1c04, 0x2103, 0x400c)        # r4 = entry_R0 & 3
MASKED = (0x1c04, 0x0624, 0x0e24)        # r4 = entry_R0 & 255
ACCESS = (0x4669, 0x5D08)                # mov r1,sp; ldrb r0,[r1,r4]
FORCE = (0x4668, 0x9003, 0x9B03)         # mov r0,sp; str r0,[sp,#12]; ldr r3,[sp,#12]: frame words
RELOAD = (0x9801, 0x4669, 0x5C0A)        # ldr r0,[sp,#4]; mov r1,sp; ldrb r2,[r1,r0]
CALLEE = 0x08014000
INNER = CALLEE + 0x100


def frame_owner(body, *, words=4, count=3, index=MASKED, tail=None):
    """push {r4-r7,lr}; sub sp,#4*words; <index into r4>; mov r0,sp; ldr r1,=table;
    movs r2,#count; bl copy; <body>; add sp,#4*words; pop {r4-r7}; pop {r1}; bx r1.

    The frame is 5 + words words, so sp+k is entry_SP + k - 4*(5 + words)."""
    head = [0xb5f0, 0xb080 | words, *index, 0x4668, 0, 0x2200 | count, HELPER]
    # movs r0..r3,#0 first: no stack address may reach the return.
    clear = (0x2000, 0x2100, 0x2200, 0x2300)
    code = head + list(body) + list(clear) + \
        list(tail if tail is not None else (0xb000 | words, 0xbcf0, 0xbc02, 0x4708))
    raw = len(assemble(OWNER, code))
    literal = raw + (-raw % 4)
    ldr = 2 * (2 + len(index) + 1)
    code[2 + len(index) + 1] = 0x4900 | ((literal - ((ldr + 4) & ~3)) // 4)
    return code


def site(code, position):
    """The address of token ``position`` in ``code`` (a BL token is four bytes)."""
    return OWNER + len(assemble(OWNER, code[:position]))


def callee(*halfwords, address=CALLEE):
    raw = struct.pack(f'<{len(halfwords)}H', *halfwords)
    return dict(extra_functions=[(address, len(raw), len(halfwords))],
                patch_rom={address + n: byte for n, byte in enumerate(raw)})


def admit(code, selector=SELECTOR, **kwargs):
    arguments, _ = fixture(code, selector=selector, **kwargs)
    try:
        return arguments, owner.verify(**arguments)
    except sip.PremiseRefusal as refusal:
        arguments['premises'] = reviewed(refusal.entry)
        return arguments, owner.verify(**arguments)


def evidence(manifest):
    return manifest['proof']['buffers']['stack_index_preconditions']


def words(manifest):
    return evidence(manifest)['frame_words']


class FrameWordTests(unittest.TestCase):
    # ---- F3/F4: exact and ranged spills ------------------------------------------------
    def test_exact_spill_reloads_as_an_index_zero_base_under_the_same_premise(self):
        # mov r0,sp; str r0,[sp,#12]; ldr r1,[sp,#12]; ldrb r0,[r1,r4]
        code = frame_owner((0x4668, 0x9003, 0x9903, 0x5D08))
        _, (manifest, _) = admit(code)
        found = evidence(manifest)
        row, = found['preconditions']
        self.assertEqual((row['expression'], row['bound'], row['array_sp']), ('(entry_R0 & 255)', 3, [0, 3]))
        self.assertEqual(words(manifest)['pointer_words'], [12 - 36])
        self.assertEqual(words(manifest)['spills'], [site(code, code.index(0x9003))])
        line = sip.precondition_lines(found)[-1]
        self.assertTrue(line.startswith('* stack index frame words: pointer-bearing local words entry_SP-0x18;'))
        self.assertIn(f'deferred exact spills 0x{site(code, code.index(0x9003)):08X}', line)

    def test_version_two_takes_the_same_rule(self):
        code = frame_owner((0x4668, 0x9003, 0x9903, 0x5D08))
        _, (manifest, _) = admit(code, selector=sip.SELECTOR_V2)
        self.assertEqual(manifest['profile'], sip.SCHEMA_V2)
        self.assertEqual(evidence(manifest)['preconditions'][0]['expression'], '(u32)(entry_R0 & 255)')
        self.assertEqual(words(manifest)['pointer_words'], [-24])

    def test_a_plain_admission_carries_no_frame_words(self):
        _, (manifest, _) = admit(frame_owner(ACCESS))
        self.assertNotIn('frame_words', evidence(manifest))
        self.assertEqual(len(sip.precondition_lines(evidence(manifest))), 1)

    def test_disabled_policy_restores_the_core_refusal(self):
        code = frame_owner((0x4668, 0x9003, 0x9903, 0x5D08))
        with mock.patch.object(fw.POLICY, 'enabled', False):
            with self.assertRaisesRegex(ValueError, '^variable stack indices exclude pointer-bearing'):
                admit(code)
            # A plain refusal stays the plain one: the reloaded counter has no defined source.
            with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
                admit(frame_owner(LOOP, index=()))

    def test_ranged_spill_reload_reads_the_element_it_stored(self):
        # mov r1,sp; adds r1,r1,r4; str r1,[sp,#12]; movs r0,#7; strb r0,[r1];
        # ldr r2,[sp,#12]; ldrb r0,[r2]: byte 3 is not copied, but it is the byte just stored.
        # The element is stored twice; only the load is an identity-initialised access.
        code = frame_owner((0x4669, 0x1909, 0x9103, 0x2007, 0x7008, 0x7008, 0x9A03, 0x7810), index=RANGED)
        _, (manifest, _) = admit(code)
        self.assertEqual(evidence(manifest)['preconditions'], [])
        self.assertEqual(words(manifest)['identity_loads'], [site(code, code.index(0x7810))])
        self.assertEqual(words(manifest)['pointer_words'], [12 - 36])
        self.assertEqual(words(manifest)['spills'], [])

    def test_another_displacement_is_not_the_stored_element(self):
        # ldrb r0,[r2,#1] reads sp+1..sp+4: the stored byte is not that one.
        code = frame_owner((0x4669, 0x1909, 0x9103, 0x2007, 0x7008, 0x9A03, 0x7850), index=RANGED)
        _, (manifest, _) = admit(code)
        self.assertEqual(words(manifest)['identity_loads'], [])
        row, = evidence(manifest)['preconditions']
        self.assertEqual((row['kind'], row['expression'], row['bound']), ('load', '(entry_R0 & 3)', 2))

    def test_a_store_initialises_only_as_wide_a_load(self):
        # r4 = (entry_R0 & 1) << 1 and one copied byte; mov r1,sp; adds r1,r1,r4;
        # str r1,[sp,#12]; movs r0,#7; <store>; ldr r2,[sp,#12]; <load>
        index = (0x1c04, 0x2101, 0x400c, 0x0064)
        body = lambda store, load: (0x4669, 0x1909, 0x9103, 0x2007, store, 0x9A03, load)
        _, (manifest, _) = admit(frame_owner(body(0x8008, 0x7810), count=1, index=index))  # strh; ldrb
        self.assertEqual(len(words(manifest)['identity_loads']), 1)
        # Both analyses refuse, so the plain refusal is the one reported.
        with self.assertRaisesRegex(sip.Refusal, 'ranged stack address escapes to memory'):
            admit(frame_owner(body(0x7008, 0x8810), count=1, index=index))                  # strb; ldrh

    def test_identity_follows_exact_copies_and_new_values(self):
        # r1 = sp + (entry_R0 & 3), then <body>; byte 3 is not copied, so only identity covers it.
        def identity(body):
            _, (manifest, _) = admit(frame_owner(FORCE + (0x4669, 0x1909) + body, index=RANGED))
            return words(manifest)['identity_loads'], evidence(manifest)['preconditions']
        # adds r2,r1,#1; movs r0,#7; strb r0,[r2]; ldrb r0,[r2]: a new value with its own identity
        loads, rows = identity((0x1C4A, 0x2007, 0x7010, 0x7810))
        self.assertEqual((len(loads), rows), (1, []))
        # movs r0,#7; strb r0,[r1]; adds r2,r1,#1; ldrb r0,[r2]: not the stored element
        loads, rows = identity((0x2007, 0x7008, 0x1C4A, 0x7810))
        self.assertEqual((loads, len(rows)), ([], 1))
        # adds r2,r1,#0; movs r0,#7; strb r0,[r2]; ldrb r0,[r1]: a copy keeps the identity
        loads, rows = identity((0x1C0A, 0x2007, 0x7010, 0x7808))
        self.assertEqual((len(loads), rows), (1, []))
        # mov r8,r1; movs r0,#7; strb r0,[r1]; mov r2,r8; ldrb r0,[r2]; movs r0,#0; mov r8,r0
        loads, rows = identity((0x4688, 0x2007, 0x7008, 0x4642, 0x7810, 0x2000, 0x4680))
        self.assertEqual((len(loads), rows), (1, []))

    def test_joins_keep_only_what_both_paths_hold(self):
        def owner(body):
            return frame_owner(FORCE + (0x4669, 0x1909, 0x2007, 0x7008) + body, index=RANGED)
        # cmp r4,#0; beq; movs r0,#7; strb r0,[r1]; ldrb r0,[r1]: stored on one path only
        _, (manifest, _) = admit(frame_owner(FORCE + (0x4669, 0x1909, 0x2C00, 0xD001, 0x2007, 0x7008, 0x7808),
                                             index=RANGED))
        self.assertEqual(words(manifest)['identity_loads'], [])
        self.assertEqual(len(evidence(manifest)['preconditions']), 1)
        # cmp r4,#0; beq T; adds r2,r1,#1; b J; T: adds r2,r1,#0; J: ldrb r0,[r2], both orders
        for other, same in ((0x1C4A, 0x1C0A), (0x1C0A, 0x1C4A)):
            with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
                admit(owner((0x2C00, 0xD001, other, 0xE000, same, 0x7810)))
        # the same through a spill: beq T; adds r2,r1,#1; str r2,[sp,#8]; b J; T: adds r2,r1,#0;
        # str r2,[sp,#8]; J: ldr r2,[sp,#8]; ldrb r0,[r2], both orders
        for other, same in ((0x1C4A, 0x1C0A), (0x1C0A, 0x1C4A)):
            with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
                admit(owner((0x2C00, 0xD002, other, 0x9202, 0xE001, same, 0x9202, 0x9A02, 0x7810)))

    def test_a_word_scalar_on_one_path_and_pointer_on_the_other_is_poison(self):
        # cmp r4,#0; beq T; mov r0,sp; b J; T: movs r0,#0; J: str r0,[sp,#12] is the register join;
        # here the word itself joins: beq T; mov r0,sp; str r0,[sp,#12]; b J; T: movs r0,#0;
        # str r0,[sp,#12]; J: ldr r1,[sp,#12]; ldrb r0,[r1]
        code = frame_owner((0x2C00, 0xD002, 0x4668, 0x9003, 0xE001, 0x2000, 0x9003, 0x9903, 0x7808) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'mixed provenance used as a base'):
            admit(code)

    def test_a_join_keeps_a_mirror_only_from_both_paths(self):
        # FORCE; movs r0,#200; str r0,[sp,#8]; cmp r4,#0; beq T; movs r1,#0; b J; T: ldr r1,[sp,#8];
        # J: cmp r1,#2; bls .+2; ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0].  A kept mirror would
        # refine the word to [0,2], a proved access; the word holds 200, outside the frame.
        body = (0x20C8, 0x9002, 0x2C00, 0xD001, 0x2100, 0xE000, 0x9902, 0x2902, 0xD9FF, 0x9802, 0x4669, 0x5C0A)
        with self.assertRaisesRegex(sip.Refusal, 'index is the constant 200'):
            admit(frame_owner(FORCE + body))

    def test_a_release_on_one_path_is_a_release(self):
        # cmp r4,#0; beq T; add sp,#4; b J; T: mov r0,sp; str r0,[sp,#0]; movs r0,#0; add sp,#4;
        # J: bl callee
        body = ACCESS + (0x2100, 0x2C00, 0xD001, 0xB001, 0xE003, 0x4668, 0x9000, 0x2000, 0xB001, CALLEE)
        with self.assertRaisesRegex(sip.Refusal, 'call after a pointer-bearing local word was released'):
            admit(frame_owner(body, tail=(0xb003, 0xbcf0, 0xbc02, 0x4708)), **callee(0x4770))

    def test_a_spilled_returned_alias_is_a_pointer_word(self):
        # mov r0,sp; bl callee; str r0,[sp,#12]: the core keeps the callee's returned alias in R0,
        # a possible stack address here, so the deferred spill makes a pointer word.
        code = frame_owner((0x4668, CALLEE, 0x9003) + ACCESS)
        _, (manifest, _) = admit(code, **callee(0x4770))
        self.assertEqual(words(manifest)['pointer_words'], [-24])
        self.assertEqual(words(manifest)['spills'], [site(code, code.index(0x9003))])
        # Reloaded, a possible address is no base: ldr r1,[sp,#12]; ldrb r0,[r1]
        with self.assertRaisesRegex(sip.Refusal, 'mixed provenance used as a base'):
            admit(frame_owner((0x4668, CALLEE, 0x9003, 0x9903, 0x7808) + ACCESS), **callee(0x4770))

    def test_a_spill_the_analysis_does_not_see_as_an_address_refuses(self):
        # The same owner, with the core's returned aliases withheld from the analysis: R0 is an
        # unknown scalar to it, so the deferred spill is not tracked, and that refuses.
        with mock.patch.object(sip.Policy, 'note_returned', lambda *arguments: None):
            with self.assertRaisesRegex(sip.Refusal, 'is not a tracked local word'):
                admit(frame_owner((0x4668, CALLEE, 0x9003) + ACCESS), **callee(0x4770))

    def test_identity_ends_at_a_release(self):
        # movs r0,#7; strb r0,[r1]; add sp,#4; sub sp,#4; ldrb r0,[r1]: the word was released.
        with self.assertRaisesRegex(sip.Refusal, 'uninitialised|no array bytes'):
            admit(frame_owner((0x4669, 0x1909, 0x2007, 0x7008, 0xB001, 0xB081, 0x7808), index=RANGED))

    # ---- F8: possible stack addresses ----------------------------------------------------
    # mov r0,sp; bl callee (bx lr): the core keeps R0 = sp+0 as the callee's returned alias.
    RETURNED = (0x4668, CALLEE)

    def test_store_through_a_returned_alias_over_a_pointer_word_refuses(self):
        # adds r5,r0,#0; mov r0,sp; str r0,[sp,#12] (pointer word); str r6,[r5,#12] overwrites it;
        # ldr r1,[sp,#12]; movs r5,#7; strb r5,[r1,r4]
        code = frame_owner(self.RETURNED + (0x1C05, 0x4668, 0x9003, 0x60EE, 0x9903, 0x2507, 0x550D))
        with self.assertRaisesRegex(sip.Refusal, 'store through a possible stack address may reach '
                                    'the pointer-bearing local word at entry-SP-24'):
            admit(code, **callee(0x4770))

    def test_load_through_a_returned_alias_of_a_pointer_word_refuses(self):
        # ... str r0,[sp,#12]; ldr r2,[r5,#12] reads the pointer word; str r6,[r2,#32]
        code = frame_owner(self.RETURNED + (0x1C05, 0x4668, 0x9003, 0x68EA, 0x6216) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'load through a possible stack address may reach '
                                    'the pointer-bearing local word at entry-SP-24'):
            admit(code, **callee(0x4770))

    def test_a_returned_alias_handed_to_a_callee_beside_a_pointer_word_refuses(self):
        # adds r5,r0,#0; mov r0,sp; str r0,[sp,#12]; adds r0,r5,#0; bl inner (movs r1,#9;
        # str r1,[r0,#12]; bx lr); ldr r1,[sp,#12]; ldrb r0,[r1,r4]
        code = frame_owner(self.RETURNED + (0x1C05, 0x4668, 0x9003, 0x1C28, INNER, 0x9903, 0x5D08))
        with self.assertRaisesRegex(sip.Refusal, 'receives a stack address in R0 while a local word holds one'):
            admit(code, **two_callees((0x4770,), (0x2109, 0x60C1, 0x4770)))

    def test_store_through_a_possible_address_forgets_its_candidate_words(self):
        # FORCE; add r0,sp,#4; bl callee (R0 = sp+4, returned); <r5 = r0 moved>; movs r0,#1;
        # str r0,[sp,#8]; str r6,[r5,#4]; ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]
        def owner(adjust):
            return frame_owner(FORCE + (0xA801, CALLEE, adjust, 0x2001, 0x9002, 0x606E, 0x9802, 0x4669, 0x5C0A),
                               index=())
        # adds r5,r0,#0: the store may overwrite the counter word at sp+8, so no source is left.
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(owner(0x1C05), **callee(0x4770))
        # adds r5,r0,#4: it may reach sp+12 only, the pointer word.
        with self.assertRaisesRegex(sip.Refusal, 'store through a possible stack address may reach '
                                    'the pointer-bearing local word at entry-SP-24'):
            admit(owner(0x1D05), **callee(0x4770))
        # subs r5,r0,#4: it reaches sp+4 only, so the counter word keeps its value.
        _, (manifest, _) = admit(owner(0x1F05), **callee(0x4770))
        self.assertEqual([row[1:] for row in evidence(manifest)['accesses']], [['load', 1, -35, -35, 32]])

    def test_a_possible_address_from_a_join_reaches_its_candidates(self):
        # movs r0,#1; str r0,[sp,#8]; cmp r4,#0; beq T; mov r5,sp; b J; T: movs r5,#0;
        # J: str r6,[r5,#8] (the core: r5 may be sp+0); ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]
        body = (0x2001, 0x9002, 0x2C00, 0xD001, 0x466D, 0xE000, 0x2500, 0x60AE, 0x9802, 0x4669, 0x5C0A)
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner(FORCE + body))
        # The join keeps its offset: str r6,[r5,#4] reaches sp+4 only, clear of the pointer word.
        body = (0x2C00, 0xD001, 0x466D, 0xE000, 0x2500, 0x606E)
        _, (manifest, _) = admit(frame_owner(FORCE + body + ACCESS))
        self.assertEqual(words(manifest)['pointer_words'], [-24])
        # stmia r5!,{r6} writes back past the word: a later store through r5 reaches sp+12.
        body = (0x2C00, 0xD001, 0x466D, 0xE000, 0x2500, 0xC540, 0x60AE)
        with self.assertRaisesRegex(sip.Refusal, 'store through a possible stack address may reach '
                                    'the pointer-bearing local word at entry-SP-24'):
            admit(frame_owner(FORCE + body + ACCESS))
        # A block store or load through r5 = sp+12 or a scalar covers the pointer word itself:
        # beq T; add r5,sp,#12; b J; T: movs r5,#0; J: stmia r5!,{r6} or ldmia r5!,{r6}
        for transfer, kind in ((0xC540, 'store'), (0xCD40, 'load')):
            with self.subTest(transfer=kind):
                body = (0x2C00, 0xD001, 0xAD03, 0xE000, 0x2500, transfer)
                with self.assertRaisesRegex(sip.Refusal, f'{kind} through a possible stack address may '
                                            'reach the pointer-bearing local word at entry-SP-24'):
                    admit(frame_owner(FORCE + body + ACCESS))

    def test_block_write_back_moves_a_possible_address(self):
        # FORCE; mov r0,sp; bl callee; adds r5,r0,#0 (r5 = sp+0, returned); <transfer>; <store>
        def owner(*body):
            return frame_owner(FORCE + self.RETURNED + (0x1C05,) + body + ACCESS)
        # stmia r5!,{r6} or ldmia r5!,{r6} leaves r5 = sp+4: str r6,[r5,#8] reaches the pointer word.
        for transfer in (0xC540, 0xCD40):
            with self.subTest(transfer=hex(transfer)):
                with self.assertRaisesRegex(sip.Refusal, 'store through a possible stack address may reach '
                                            'the pointer-bearing local word at entry-SP-24'):
                    admit(owner(transfer, 0x60AE), **callee(0x4770))
        # str r6,[r5,#4] reaches sp+8 only.
        admit(owner(0xC540, 0x606E), **callee(0x4770))

    def test_possible_addresses_keep_their_offsets_up_to_a_bound(self):
        self.assertEqual(fw.possible({-8, -4}), ('O', frozenset({-8, -4})))
        self.assertEqual(fw.possible(range(-4 * (fw.MAX_POSSIBLE + 1), 0, 4)), sip.OPAQUE)
        self.assertEqual(fw.possible_join(sip.exact_alias(-8), sip.TOP), ('O', frozenset({-8})))
        self.assertEqual(fw.possible_join(fw.possible({-8}), sip.exact_alias(-4)), ('O', frozenset({-8, -4})))
        self.assertEqual(fw.possible_join(sip.OPAQUE, sip.exact_alias(-4)), sip.OPAQUE)
        self.assertIsNone(fw.candidates(sip.OPAQUE))
        # OPAQUE may be any local word.
        analysis = fw.FrameWordsAnalysis(b'\x70\x47', OWNER, frozenset(), frozenset(), {})
        state = fw.WordState(('L',) * 3, frozenset(), (sip.TOP,) * 16, (None,) * 16, None)
        self.assertEqual(analysis.spans(state, sip.OPAQUE, 0, 4), [(-12, 0)])
        self.assertEqual(analysis.spans(state, fw.possible({-8}), 2, 2), [(-6, -4)])
        self.assertEqual(analysis.spans(state, fw.possible({-8}), None, 2), [(-12, 0)])

    def test_a_returned_alias_outside_r0_r12_refuses(self):
        # bl callee; bx lr, with the core reporting a returned alias under a key that is no register.
        data = assemble(OWNER, (CALLEE, 0x4770))
        for returned, refused in (({None: frozenset({-4})}, True), ({1: frozenset({-4})}, False)):
            with self.subTest(returned=returned):
                analysis = fw.FrameWordsAnalysis(data, OWNER, frozenset(), frozenset(), {},
                                                 returned={OWNER: returned})
                if refused:
                    with self.assertRaisesRegex(sip.Refusal, 'returns a stack alias outside R0-R12'):
                        analysis.run()
                else:
                    states = analysis.run()
                    self.assertEqual(states[OWNER + 4].regs[1], fw.possible({-4}))

    def test_the_policy_records_every_returned_alternative(self):
        class Result(dict):
            pass
        policy = sip.Policy(OWNER, 2)
        result = Result({match.ARM_REG_R0: -8})
        result.alternatives = (Result({match.ARM_REG_R0: -4, match.ARM_REG_R12: -12}),)
        policy.note_returned(0x100, result, result.alternatives)
        policy.note_returned(0x100, Result({match.ARM_REG_R1: -16}))
        policy.note_returned(0x104, Result({match.ARM_REG_LR: -20}))
        self.assertEqual(policy.returned, {0x100: {0: {-8, -4}, 12: {-12}, 1: {-16}}, 0x104: {None: {-20}}})

    def test_a_premise_may_name_loads_and_call_results(self):
        # Under frame words, an index read from memory or returned by a call is a variable:
        # FORCE; movs r2,#128; lsls r2,r2,#18; ldrb r4,[r2] (u8 at 0x02000000); mov r1,sp;
        # movs r5,#7; strb r5,[r1,r4]
        code = frame_owner(FORCE + (0x2280, 0x0492, 0x7814, 0x4669, 0x2507, 0x550D), index=())
        _, (manifest, _) = admit(code)
        self.assertEqual(evidence(manifest)['preconditions'][0]['expression'],
                         f'u8[0x02000000]@0x{site(code, code.index(0x7814)):08X}')
        # ... movs r0,#0; bl callee; lsls r4,r0,#24; lsrs r4,r4,#24; mov r1,sp; movs r5,#7;
        # strb r5,[r1,r4]
        code = frame_owner(FORCE + (0x2000, CALLEE, 0x0604, 0x0E24, 0x4669, 0x2507, 0x550D), index=())
        _, (manifest, _) = admit(code, **callee(0x4770))
        self.assertEqual(evidence(manifest)['preconditions'][0]['expression'],
                         f'(ret(0x{site(code, code.index(CALLEE)):08X}) & 255)')

    # ---- F5: variable accesses avoid pointer-bearing words ------------------------------
    def test_variable_store_may_not_overlap_a_pointer_word(self):
        # The spill at sp+12 is never reloaded, so the store's array runs to the frame top.
        code = frame_owner((0x4668, 0x9003, 0x4669, 0x2507, 0x550D))
        with self.assertRaisesRegex(sip.Refusal, 'overlaps a pointer-bearing local word at entry-SP-24'):
            admit(code)
        # Reloading the word makes it an object of its own: the array stops before it.
        _, (manifest, _) = admit(frame_owner((0x4668, 0x9003, 0x4669, 0x2507, 0x550D, 0x9A03)))
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 12)

    def test_proved_range_may_not_overlap_a_pointer_word(self):
        # r4 = entry_R0 & 15: the proved range sp+0..sp+15 covers the pointer word at sp+12, so
        # the store needs the premise, whose array stops before it.
        code = frame_owner((0x4668, 0x9003, 0x4669, 0x2507, 0x550D, 0x9A03), index=(0x1c04, 0x210f, 0x400c))
        _, (manifest, _) = admit(code)
        self.assertEqual(evidence(manifest)['accesses'], [])
        self.assertEqual(evidence(manifest)['preconditions'][0]['bound'], 12)
        # Without the spill the same proved range needs no premise.
        _, (manifest, _) = admit(frame_owner((0x4669, 0x2507, 0x550D, 0x9A03), index=(0x1c04, 0x210f, 0x400c)))
        self.assertEqual(evidence(manifest)['preconditions'], [])

    def test_a_wide_access_overlaps_by_its_last_byte(self):
        # r4 = (entry_R0 & 3) << 2; mov r1,sp; str r5,[r1,r4]: index 3 writes sp+12..15,
        # the pointer word, so the store needs the premise that stops the array before it.
        code = frame_owner((0x4668, 0x9003, 0x4669, 0x510D, 0x9A03), index=RANGED + (0x00A4,))
        _, (manifest, _) = admit(code)
        row, = evidence(manifest)['preconditions']
        self.assertEqual((row['kind'], row['bound'], row['scale']), ('store', 3, 4))

    def test_partial_access_to_a_pointer_word_refuses(self):
        spill = (0x4668, 0x9003, 0xA903)          # ..., add r1,sp,#12
        with self.assertRaisesRegex(sip.Refusal, 'partial read of a pointer-bearing local word'):
            admit(frame_owner(spill + (0x7808,) + ACCESS))
        with self.assertRaisesRegex(sip.Refusal, 'partial store over a pointer-bearing local word'):
            admit(frame_owner(spill + (0x2000, 0x7008) + ACCESS))
        # A whole-word store of a scalar ends the pointer: the reload is a plain value again.
        _, (manifest, _) = admit(frame_owner(spill + (0x2000, 0x6008, 0x9A03, 0x7810) + ACCESS))
        self.assertEqual(words(manifest)['pointer_words'], [-24])

    def test_block_transfer_over_a_pointer_word_refuses(self):
        # add r1,sp,#12; ldmia r1!,{r2} reads the pointer word at sp+12.
        with self.assertRaisesRegex(sip.Refusal, 'block transfer over a pointer-bearing local word'):
            admit(frame_owner((0x4668, 0x9003, 0xA903, 0xC904) + ACCESS))
        # The same block reload of the word below it is a plain reload.
        admit(frame_owner((0x4668, 0x9003, 0xA902, 0xC904) + ACCESS))

    def test_maybe_pointer_word_refuses_as_a_base(self):
        # cmp r4,#0; beq; mov r0,sp; str r0,[sp,#12]; ldr r1,[sp,#12]; ldrb r0,[r1]
        code = frame_owner((0x2C00, 0xD001, 0x4668, 0x9003, 0x9903, 0x7808) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'mixed provenance used as a base'):
            admit(code)
        # A register that is a stack address on one path and a scalar on the other, spilled.
        code = frame_owner((0x2C00, 0xD001, 0x4668, 0xE000, 0x2000, 0x9003, 0x9903, 0x7808) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'mixed provenance used as a base'):
            admit(code)
        # Spilled and never reloaded, it is still a pointer word that accesses must avoid.
        code = frame_owner((0x2C00, 0xD001, 0x4668, 0xE000, 0x2000, 0x9003) + ACCESS)
        _, (manifest, _) = admit(code)
        self.assertEqual(words(manifest)['pointer_words'], [-24])
        self.assertEqual(words(manifest)['spills'], [site(code, code.index(0x9003))])

    def test_variable_access_may_not_overlap_a_maybe_pointer_word(self):
        # cmp r4,#0; beq; mov r0,sp; str r0,[sp,#12]; then strb r5,[r1,r4] over the frame.
        code = frame_owner((0x2C00, 0xD001, 0x4668, 0x9003, 0x4669, 0x2507, 0x550D))
        with self.assertRaisesRegex(sip.Refusal, 'overlaps a pointer-bearing local word at entry-SP-24'):
            admit(code)

    def test_reloaded_address_may_not_escape(self):
        spill = (0x4668, 0x9003, 0x9903)
        with self.assertRaisesRegex(sip.Refusal, 'escapes to memory'):
            admit(frame_owner(spill + (0x2200, 0x6011) + ACCESS))         # str r1,[r2]
        with self.assertRaisesRegex(sip.Refusal, 'comparison'):
            admit(frame_owner(spill + (0x2900,) + ACCESS))                 # cmp r1,#0
        with self.assertRaisesRegex(sip.Refusal, 'stored outside a whole allocated local word'):
            admit(frame_owner(spill + (0xAA01, 0x7011) + ACCESS))         # add r2,sp,#4; strb r1,[r2]

    # ---- F10/F11: scalar words and compare refinement -----------------------------------
    def test_an_overwritten_word_drops_its_mirrors(self):
        # FORCE; movs r0,#0; str r0,[sp,#8]; ldr r1,[sp,#8]; movs r2,#200; str r2,[sp,#8];
        # cmp r1,#2; bls .+2; ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]: refining R1 says
        # nothing about the word any more, which holds 200, outside the frame.  No premise is
        # stated on a constant index.
        body = (0x2000, 0x9002, 0x9902, 0x22C8, 0x9202, 0x2902, 0xD9FF, 0x9802, 0x4669, 0x5C0A)
        with self.assertRaisesRegex(sip.Refusal, r'outside \[-36, 0\)\); index is the constant 200 '
                                    r'\(no premise can be stated\)'):
            admit(frame_owner(FORCE + body, index=()))
        # The same mirror on a word nothing tracked (only half-initialised by strh) ends too:
        # FORCE; mov r3,sp; movs r2,#0; strh r2,[r3,#8]; strh r2,[r3,#10]; ldr r0,[sp,#8];
        # movs r1,#200; str r1,[sp,#8]; cmp r0,#2; bhi .+4; ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]
        body = (0x466B, 0x2200, 0x811A, 0x815A, 0x9802, 0x21C8, 0x9102, 0x2802, 0xD802, 0x9802, 0x4669, 0x5C0A)
        with self.assertRaisesRegex(sip.Refusal, 'index is the constant 200'):
            admit(frame_owner(FORCE + body, index=()))

    def test_a_stored_register_mirrors_its_word(self):
        # The loop compares the stored register itself: ... str r0,[sp,#8]; cmp r0,#2; bls loop
        loop = (0x2000, 0x9002, 0x9802, 0x4669, 0x5C0A, 0x3001, 0x9002, 0x2802, 0xD9F8)
        _, (manifest, _) = admit(frame_owner(loop, index=()))
        self.assertEqual(evidence(manifest)['preconditions'], [])

    def test_a_narrow_fixed_load_is_its_full_unsigned_range(self):
        # 40-word frame; add r1,sp,#8; ldrb r4,[r1]; mov r1,sp; movs r5,#7; strb r5,[r1,r4]
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner((0xA902, 0x780C, 0x4669, 0x2507, 0x550D), words=40, index=()))

    def test_a_fixed_store_initialises_its_bytes(self):
        # Four copied bytes and movs r0,#5; str r0,[sp,#4]: sp+0..7 is initialised for r4 < 8.
        body = FORCE + (0x2005, 0x9001, 0x4669, 0x5D08)
        _, (manifest, _) = admit(frame_owner(body, count=4, index=(0x1c04, 0x2107, 0x400c)))
        self.assertEqual(evidence(manifest)['preconditions'], [])

    def test_words_a_store_may_reach_are_forgotten(self):
        # movs r0,#0; str r0,[sp,#4]; <write>; ldr r0,[sp,#4]; mov r1,sp; ldrb r2,[r1,r0]
        cases = {
            # mov r1,sp; str r5,[r1,r4] with r4 in {0, 4}: the last element is the word
            'variable store': ((0x4669, 0x510D), dict(index=(0x1c04, 0x2101, 0x400c, 0x00A4))),
            # add r1,sp,#4; movs r2,#200; stmia r1!,{r2}
            'block store': ((0xA901, 0x22C8, 0xC104), {}),
            # a callee that writes [sp,#4]: movs r1,#9; str r1,[sp,#4]; bx lr
            'callee reach': ((CALLEE,), callee(0x2109, 0x9101, 0x4770)),
            # a callee handed mov r0,sp that writes [r0,#4]: movs r1,#9; str r1,[r0,#4]; bx lr
            'callee handed the frame': ((0x4668, CALLEE), callee(0x2109, 0x6041, 0x4770)),
        }
        for name, (write, kwargs) in cases.items():
            with self.subTest(write=name):
                index = kwargs.pop('index', MASKED)
                with self.assertRaisesRegex(ValueError, 'no defined source'):
                    admit(frame_owner((0x2000, 0x9001) + write + RELOAD, index=index), **kwargs)
        # add sp,#4; sub sp,#4 releases sp+0 and allocates it again: movs r0,#0; str r0,[sp,#0];
        # ...; ldr r0,[sp,#0]; mov r1,sp; strb r5,[r1,r0]
        with self.assertRaisesRegex(ValueError, 'no defined source'):
            admit(frame_owner((0x2000, 0x9000, 0xB001, 0xB081, 0x9800, 0x4669, 0x540D)))
        # A callee that leaves the word alone keeps it.
        _, (manifest, _) = admit(frame_owner((0x2000, 0x9001, CALLEE) + RELOAD), **callee(0x4770))
        self.assertEqual(evidence(manifest)['preconditions'], [])

    def test_a_call_ends_the_mirrors_of_the_registers_it_clobbers(self):
        # FORCE; movs r0,#200; str r0,[sp,#8]; ldr r0,[sp,#8]; bl callee; cmp r0,#2; bls .+2;
        # ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]: the compare is of the callee's R0.
        body = (0x20C8, 0x9002, 0x9802, CALLEE, 0x2802, 0xD9FF, 0x9802, 0x4669, 0x5C0A)
        with self.assertRaisesRegex(sip.Refusal, 'index is the constant 200'):
            admit(frame_owner(FORCE + body, index=()), **callee(0x2000, 0x4770))

    def test_a_callee_ends_the_mirrors_of_the_words_it_reaches(self):
        # mov r3,sp; movs r2,#0; strh r2,[r3,#8]; strh r2,[r3,#10] (sp+8 initialised, untracked);
        # movs r0,#0; movs r3,#0; ldr r4,[sp,#8] (R4 mirrors it and survives calls); bl callee;
        # cmp r4,#2; bhi .+4;
        # ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0].  The callee writes [sp,#8] (movs r1,#200;
        # str r1,[sp,#8]; bx lr), so the compare of R4 says nothing about the word.
        # movs r0,#0; movs r3,#0 first: the core walks a callee handed a stack alias itself.
        body = (0x466B, 0x2200, 0x811A, 0x815A, 0x2000, 0x2300, 0x9C02, CALLEE, 0x2C02, 0xD802,
                0x9802, 0x4669, 0x5C0A)
        writes = callee(0x21C8, 0x9102, 0x4770)
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner(FORCE + body, index=()), **writes)
        # A callee that leaves the word alone keeps the mirror: the access is proved.
        _, (manifest, _) = admit(frame_owner(FORCE + body, index=()), **callee(0x4770))
        self.assertEqual(evidence(manifest)['preconditions'], [])
        # With no word tracked at all, the mirror alone needs the walk.
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner(body, index=()), **writes)
        code = frame_owner(body, index=())
        _, (manifest, _) = admit(code, **callee(0x4770))
        self.assertEqual(evidence(manifest)['preconditions'], [])
        self.assertEqual(words(manifest)['calls'], [[site(code, code.index(CALLEE)), CALLEE, 0, [], []]])

    def test_spilled_loop_counter_is_bounded_by_its_compare(self):
        _, (manifest, _) = admit(frame_owner(LOOP, index=()))
        found = evidence(manifest)
        self.assertEqual(found['preconditions'], [])
        self.assertEqual([row[1:] for row in found['accesses']], [['load', 1, -36, -34, 0]])
        self.assertEqual(words(manifest)['pointer_words'], [])

    def test_a_rewritten_register_no_longer_refines_the_word(self):
        # adds r1,#0 after the reload: the compare refines a register that no longer mirrors it.
        broken = LOOP[:8] + (0x3100,) + LOOP[8:9] + (0xD9F6,)
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner(broken, index=()))

    def test_a_variable_store_forgets_the_scalar_words_it_may_overwrite(self):
        # movs r0,#0; str r0,[sp,#8]; [add r1,sp,#8; movs r2,#9; strb r2,[r1,r4]];
        # ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]
        store = (0xA902, 0x2209, 0x550A)
        body = lambda middle: (0x2000, 0x9002, *middle, 0x9802, 0x4669, 0x5C0A)
        _, (manifest, _) = admit(frame_owner(body(()), index=RANGED))
        self.assertEqual(evidence(manifest)['preconditions'], [])
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner(body(store), index=RANGED))

    # ---- F2/F6: calls ---------------------------------------------------------------------
    def test_pointer_word_inside_a_callee_stack_reach_refuses(self):
        # add r0,sp,#4; str r0,[sp,#12]; movs r0,#0; bl callee
        code = frame_owner((0xA801, 0x9003, 0x2000, CALLEE) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'may reach the pointer-bearing local word at entry-SP-24'):
            admit(code, **callee(0x9803, 0x4770))                             # ldr r0,[sp,#12]; bx lr
        admit(code, **callee(0x9802, 0x4770))                                 # ldr r0,[sp,#8]
        _, (manifest, _) = admit(code, **callee(0x4770))
        self.assertEqual(words(manifest)['calls'], [[site(code, code.index(CALLEE)), CALLEE, 0, [], []]])
        self.assertEqual(words(manifest)['unwalked'], [])
        with self.assertRaisesRegex(sip.Refusal, 'uses SP or PC'):
            admit(code, **callee(0x4668, 0x4770))                             # mov r0,sp

    def test_a_callee_handed_a_stack_address_may_not_run_beside_pointer_words(self):
        # movs r1,#0; strb r1,[r0]; bx lr is a bounded buffer callee of the array.
        body = (0x4668, 0x9003, 0x4668, CALLEE, 0x9903, 0x7808) + ACCESS
        admit(frame_owner((0x4668, CALLEE) + ACCESS), **callee(0x2100, 0x7001, 0x4770))
        with self.assertRaisesRegex(sip.Refusal, 'receives a stack address in R0'):
            admit(frame_owner(body), **callee(0x2100, 0x7001, 0x4770))

    def test_a_callee_reading_r12_receives_the_stack_address_in_it(self):
        # FORCE (pointer word at sp+12); add r0,sp,#4; mov r12,r0; movs r0,#0; movs r3,#0;
        # bl callee (mov r0,r12; movs r1,#9; str r1,[r0,#8]: the pointer word; bx lr);
        # ldr r1,[sp,#12]; ldrb r0,[r1,r4]
        code = frame_owner(FORCE + (0xA801, 0x4684, 0x2000, 0x2300, CALLEE, 0x9903, 0x5D08))
        with self.assertRaisesRegex(sip.Refusal, 'receives a stack address in R12 while a local word holds one'):
            admit(code, **callee(0x4660, 0x2109, 0x6081, 0x4770))

    def test_a_call_this_analysis_does_not_walk_is_a_listed_premise(self):
        # movs r0,#0; bl callee (add r0,sp,#0; bx lr: the address of its first stack argument,
        # which is the owner's sp+0); adds r5,r0,#0; mov r0,sp; str r0,[sp,#12] (a pointer word);
        # str r6,[r5,#12] (overwrites it); ldr r1,[sp,#12]; movs r5,#7; strb r5,[r1,r4].
        # No word exists at the call, so nothing walks the callee and its result is a scalar to
        # the core and to this analysis: the core's own trust, which the report names.
        body = (0x4668, 0x9003, 0x60EE, 0x9903, 0x2507, 0x550D)
        code = frame_owner((0x2000, CALLEE, 0x1C05) + body)
        _, (manifest, _) = admit(code, **callee(0xA800, 0x4770))
        call = site(code, code.index(CALLEE))
        self.assertEqual(words(manifest)['unwalked'], [call])
        self.assertIn(f'calls this analysis did not walk (0x{call:08X}): their results are trusted',
                      sip.precondition_lines(evidence(manifest))[-1])
        # With the pointer word spilled before the call, the walk runs and refuses `add r0,sp`.
        code = frame_owner((0x4668, 0x9003, 0x2000, CALLEE, 0x1C05) + body[2:])
        with self.assertRaisesRegex(sip.Refusal, 'may reach the pointer-bearing local word'):
            admit(code, **callee(0xA800, 0x4770))

    def test_ranged_address_in_an_unread_argument_register_is_not_an_escape(self):
        # mov r3,sp; adds r3,r3,r4; bl callee; mov r1,sp; ldrb r0,[r1,r4]
        code = frame_owner((0x466B, 0x191B, 0x2000, CALLEE) + ACCESS, index=RANGED)
        _, (manifest, _) = admit(code, **callee(0x0040, 0x4770))             # lsls r0,r0,#1
        self.assertEqual(words(manifest)['calls'], [[site(code, code.index(CALLEE)), CALLEE, 0, [0], [3]]])
        self.assertIn('R3 at', sip.precondition_lines(evidence(manifest))[-1])
        self.assertIsNone(words(manifest)['premise'])
        # The BIOS division wrapper reads R0 and R1 only, under the printed GBATEK premise.
        _, (manifest, _) = admit(code, **callee(0xDF06, 0x4770))
        self.assertEqual((words(manifest)['swis'], words(manifest)['premise']), ([6], fw.SWI_PREMISE))
        # GBATEK: the handler saves four words on the supervisor stack and uses the user stack after.
        for fact in ('SPSR, R11, R12 and R14 on the supervisor stack', 'System mode',
                     'use the user stack, the caller\'s, below its SP', 'no word at or above the caller\'s SP'):
            self.assertIn(fact, fw.SWI_PREMISE)
        self.assertTrue(sip.precondition_lines(evidence(manifest))[-1].endswith('; ' + fw.SWI_PREMISE))
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code, **callee(0x1C18, 0x4770))                             # adds r0,r3,#0
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code, **callee(0xB408, 0xBC08, 0x4770))                     # push {r3}; pop {r3}

    def test_an_unread_argument_register_the_callee_keeps_is_unusable_after_the_call(self):
        # ... bl callee; ldrb r0,[r3]: the callee neither reads nor writes R3, so R3 may still
        # hold the stack address; it is POISON after the call.  Both analyses refuse, so the
        # plain refusal is the one reported.
        code = frame_owner((0x466B, 0x191B, 0x2000, CALLEE, 0x7818) + ACCESS, index=RANGED)
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code, **callee(0x0040, 0x4770))
        # A callee that writes R3 on every path replaces it: the load is an ordinary one.
        admit(code, **callee(0x0040, 0x2300, 0x4770))

    def test_released_pointer_word_ends_calls_and_stack_growth(self):
        spill = (0x4668, 0x9003) + ACCESS
        with self.assertRaisesRegex(sip.Refusal, 'call after a pointer-bearing local word was released'):
            admit(frame_owner(spill, tail=(0xb004, CALLEE, 0xbcf0, 0xbc02, 0x4708)), **callee(0x4770))
        with self.assertRaisesRegex(ValueError, 'moves SP down after releasing|stack'):
            admit(frame_owner(spill, tail=(0xb004, 0xb084, 0xb004, 0xbcf0, 0xbc02, 0x4708)))

    def test_tampered_frame_words_make_the_manifest_stale(self):
        arguments, (manifest, _) = admit(frame_owner((0x4668, 0x9003, 0x9903, 0x5D08)))
        edits = {
            'pointer word': lambda found: found['pointer_words'].append(-28),
            'spill': lambda found: found['spills'].clear(),
            'premise': lambda found: found.__setitem__('premise', fw.SWI_PREMISE),
            'removed': None,
        }
        for name, edit in edits.items():
            with self.subTest(edit=name):
                changed = copy.deepcopy(manifest)
                if edit is None:
                    del evidence(changed)['frame_words']
                else:
                    edit(words(changed))
                with self.assertRaisesRegex(ValueError, 'differs from complete fresh native replay'):
                    owner.verify(**arguments, manifest=changed)
        owner.verify(**arguments, manifest=copy.deepcopy(manifest))


# movs r0,#0; str r0,[sp,#8]; loop: ldr r0,[sp,#8]; mov r1,sp; ldrb r2,[r1,r0]; adds r0,#1;
# str r0,[sp,#8]; ldr r1,[sp,#8]; cmp r1,#2; bls loop
LOOP = (0x2000, 0x9002, 0x9802, 0x4669, 0x5C0A, 0x3001, 0x9002, 0x9902, 0x2902, 0xD9F7)


class ReviewReproducerTests(unittest.TestCase):
    """Owners an adversarial review built against the first version; each must refuse."""

    def test_returned_aliases(self):
        cases = {
            # store through the returned alias over a pointer word, then a premise-bounded store
            # through the reloaded word
            'A': (0x4668, CALLEE, 0x1C05, 0x4668, 0x9003, 0x60EE, 0x9903, 0x2507, 0x550D),
            # load of the pointer word through the returned alias, then a store over saved LR
            'A2': (0x4668, CALLEE, 0x1C05, 0x4668, 0x9003, 0x68EA, 0x6216) + ACCESS,
        }
        for name, code in cases.items():
            with self.subTest(case=name):
                with self.assertRaisesRegex(sip.Refusal, 'through a possible stack address'):
                    admit(frame_owner(code), **callee(0x4770))
        # A3: the returned alias handed to a callee that writes the pointer word
        with self.assertRaisesRegex(sip.Refusal, 'receives a stack address in R0'):
            admit(frame_owner((0x4668, CALLEE, 0x1C05, 0x4668, 0x9003, 0x1C28, INNER, 0x9903, 0x5D08)),
                  **two_callees((0x4770,), (0x2109, 0x60C1, 0x4770)))
        # A4: the returned alias overwrites a scalar counter word; no spill, no pointer word
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admit(frame_owner((0x4668, CALLEE, 0x1C05, 0x2001, 0x9002, 0x60AE, 0x9802, 0x4669, 0x5C0A),
                              index=()), **callee(0x4770))

    def test_stale_mirrors(self):
        # B: a mirror on an untracked word survived a store to it
        with self.assertRaises(sip.Refusal):
            admit(frame_owner((0x466B, 0x2200, 0x811A, 0x815A, 0x9802, 0x21C8, 0x9102, 0x2802, 0xD802,
                               0x9802, 0x4669, 0x5C0A), index=()))
        # B2: the stale mirror turned a pointer word into the scalar [0,2]
        with self.assertRaisesRegex(sip.Refusal, 'saved register word'):
            admit(frame_owner((0x466B, 0x2200, 0x819A, 0x81DA, 0x9803, 0x4669, 0x9103, 0x2802, 0xD801,
                               0x9A03, 0x6216) + ACCESS))

    def test_a_premise_store_keeps_the_pointer_word_above_its_array(self):
        # C: mov r0,sp; str r0,[sp,#12]; mov r1,sp; movs r5,#7; strb r5,[r1,r4] (premise
        # (entry_R0 & 255) < 12); ldr r2,[sp,#12] is still the pointer; str r6,[r2,#32]
        with self.assertRaisesRegex(sip.Refusal, 'saved register word'):
            admit(frame_owner((0x4668, 0x9003, 0x4669, 0x2507, 0x550D, 0x9A03, 0x6216)))
        # Used inside the frame, the reload is the index-zero base of the array it addresses.
        _, (manifest, _) = admit(frame_owner((0x4668, 0x9003, 0x4669, 0x2507, 0x550D, 0x9A03, 0x5D16)))
        self.assertEqual([row['bound'] for row in evidence(manifest)['preconditions']], [12, 3])

    def test_a_nested_call_writes_only_what_every_return_writes(self):
        # D: mov r3,sp; adds r3,r3,r5; movs r0,#0; bl outer (push {lr}; bl inner; pop {pc}),
        # inner = bx lr leaves R3 alone; str r6,[r3,#0]
        code = frame_owner((0x466B, 0x195B, 0x2000, CALLEE, 0x601E) + ACCESS)
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code, **two_callees(nested_outer(), (0x4770,)))
        # D0: the same with a direct callee
        with self.assertRaisesRegex(sip.Refusal, 'escapes through a call argument register'):
            admit(code, **callee(0x4770))


def two_callees(outer, inner):
    a, b = callee(*outer), callee(*inner, address=INNER)
    return dict(extra_functions=a['extra_functions'] + b['extra_functions'],
                patch_rom={**a['patch_rom'], **b['patch_rom']})


def nested_outer():
    """push {lr}; bl INNER; pop {pc}"""
    return struct.unpack('<3H', assemble(CALLEE, (0xB500, INNER))) + (0xBD00,)


class CalleeReachTests(unittest.TestCase):
    def reach(self, functions, address=CALLEE, swis=fw.POLICY.swis):
        spans = {start: struct.pack(f'<{len(body)}H', *body) for start, body in functions.items()}

        def span(target):
            if target not in spans:
                raise ValueError('no span')
            return spans[target]
        return fw.CalleeReach(span, swis)(address)

    def test_leaf_and_framed_returns(self):
        self.assertEqual(self.reach({CALLEE: (0x0040, 0x4770)}),
                         (0, frozenset({0}), frozenset(), frozenset({0})))
        # push {r4,lr}; movs r4,#0; pop {r4}; pop {r1}; bx r1
        self.assertEqual(self.reach({CALLEE: (0xB510, 0x2400, 0xBC10, 0xBC02, 0x4708)})[0], 0)
        # push {lr}; pop {pc}
        self.assertEqual(self.reach({CALLEE: (0xB500, 0xBD00)})[0], 0)

    def test_stack_arguments_and_nested_reach(self):
        # ldr r0,[sp,#8]; bx lr: reads the third stack argument word.
        self.assertEqual(self.reach({CALLEE: (0x9802, 0x4770)})[0], 12)
        # push {r4,lr}; bl inner; pop {r4}; pop {r0}; bx r0 with inner reading [sp,#12]
        inner = CALLEE + 0x100
        outer = assemble(CALLEE, (0xB510, inner, 0xBC10, 0xBC01, 0x4700))
        functions = {CALLEE: struct.unpack(f'<{len(outer) // 2}H', outer), inner: (0x9803, 0x4770)}
        self.assertEqual(self.reach(functions)[0], 8)
        functions[inner] = (0x9801, 0x4770)
        self.assertEqual(self.reach(functions)[0], 0)
        # push {r4,lr}; ldr r0,[sp,#8]; pop {r4,pc}: [sp,#8] is the entry SP word.
        self.assertEqual(self.reach({CALLEE: (0xB510, 0x9802, 0xBD10)})[0], 4)
        self.assertEqual(self.reach({CALLEE: (0xB510, 0x9801, 0xBD10)})[0], 0)

    def test_argument_reads_are_before_writes(self):
        self.assertEqual(self.reach({CALLEE: (0x1C18, 0x4770)})[1], frozenset({3}))
        # A nested callee's reads are the caller's: push {lr}; bl inner; pop {pc}.
        inner = CALLEE + 0x100
        outer = struct.unpack('<3H', assemble(CALLEE, (0xB500, inner))) + (0xBD00,)
        self.assertEqual(self.reach({CALLEE: outer, inner: (0x1C18, 0x4770)})[1], frozenset({3}))
        # cmp r0,#0; bne; movs r1,#0; b; movs r3,#0; adds r0,r3,#0; bx lr: the path that
        # reaches the read first defines R3, the other does not.
        self.assertEqual(self.reach({CALLEE: (0x2800, 0xD101, 0x2100, 0xE000, 0x2300, 0x1C18, 0x4770)})[1],
                         frozenset({0, 3}))
        self.assertEqual(self.reach({CALLEE: (0x2300, 0x1C18, 0x4770)})[1], frozenset())
        # Only the path that writes R3 first is clean: the join keeps R3 as read.
        self.assertEqual(self.reach({CALLEE: (0x2800, 0xD000, 0x2300, 0x1C18, 0x4770)})[1],
                         frozenset({0, 3}))

    def test_writes_hold_on_every_return(self):
        # cmp r0,#0; beq; movs r3,#0; movs r2,#0; bx lr: R2 is written on both paths, R3 on one.
        self.assertEqual(self.reach({CALLEE: (0x2800, 0xD000, 0x2300, 0x2200, 0x4770)})[3],
                         frozenset({2}))
        # push {lr}; movs r1,#0; pop {r0}; bx r0: R0 carries the return address, R1 is written.
        self.assertEqual(self.reach({CALLEE: (0xB500, 0x2100, 0xBC01, 0x4700)})[3],
                         frozenset({0, 1}))
        # cmp r0,#0; beq; movs r3,#0; bx lr; movs r2,#0; bx lr: each return writes a different one.
        self.assertEqual(self.reach({CALLEE: (0x2800, 0xD001, 0x2300, 0x4770, 0x2200, 0x4770)})[3],
                         frozenset())
        # push {r4,lr}; movs r2,#0; pop {r4,pc}
        self.assertEqual(self.reach({CALLEE: (0xB510, 0x2200, 0xBD10)})[3], frozenset({2}))

    def test_nested_calls_surely_write_only_what_every_inner_return_writes(self):
        # push {lr}; bl inner; pop {pc}: the call may clobber R0-R3, but writes only what inner does.
        for inner, writes in (((0x4770,), frozenset()),                                 # bx lr
                              ((0x2300, 0x4770), frozenset({3})),                       # movs r3,#0
                              ((0x2800, 0xD000, 0x2300, 0x2200, 0x4770), frozenset({2}))):
            with self.subTest(inner=inner):
                self.assertEqual(self.reach({CALLEE: nested_outer(), INNER: inner})[3], writes)

    def test_an_inner_store_over_the_saved_lr_refuses_the_return(self):
        # push {lr}; bl inner; pop {pc} with inner = str r0,[sp,#0]; bx lr: the word pop {pc}
        # reads is the one inner wrote.
        with self.assertRaisesRegex(sip.Refusal, 'pops PC from a word other than its saved LR'):
            self.reach({CALLEE: nested_outer(), INNER: (0x9000, 0x4770)})
        # A load of it changes nothing: ldr r0,[sp,#0]; bx lr
        self.assertEqual(self.reach({CALLEE: nested_outer(), INNER: (0x9800, 0x4770)})[0], 0)

    def test_only_armv4t_encodings_are_walked(self):
        for name, half in (('cbz r0', 0xB100), ('uxtb r0,r0', 0xB2C0), ('rev r0,r0', 0xBA00),
                           ('cpsid i', 0xB672), ('bkpt', 0xBE00), ('it eq', 0xBF08)):
            with self.subTest(instruction=name):
                with self.assertRaisesRegex(sip.Refusal, 'not ARMv4T Thumb'):
                    self.reach({CALLEE: (half, 0x4770, 0x4770)})

    def test_r12_is_a_passed_register(self):
        # mov r0,r12; bx lr reads R12 before writing it; movs r0,#0 does not read R0.
        self.assertEqual(self.reach({CALLEE: (0x4660, 0x4770)})[1], frozenset({12}))
        self.assertEqual(self.reach({CALLEE: (0x2000, 0x4770)})[1:4:2], (frozenset(), frozenset({0})))

    def test_bios_division_is_the_only_admitted_swi(self):
        # The SWI handler stores R2 below SP and restores it: R2 counts as read.
        self.assertEqual(self.reach({CALLEE: (0xDF06, 0x4770)}),
                         (0, frozenset({0, 1, 2}), frozenset({6}), frozenset({0, 1, 3})))
        with self.assertRaisesRegex(sip.Refusal, 'SWI 5'):
            self.reach({CALLEE: (0xDF05, 0x4770)})
        with self.assertRaisesRegex(sip.Refusal, 'SWI 6'):
            self.reach({CALLEE: (0xDF06, 0x4770)}, swis=frozenset())

    def test_unproved_shapes_refuse(self):
        cases = {
            'indirect branch': (0x4718,),                          # bx r3
            'SP or PC': (0x4668, 0x4770),                          # mov r0,sp
            'SP or PC ': (0xA801, 0x4770),                         # add r0,sp,#4
            'saved LR': (0xB410, 0xBD00),                          # push {r4}; pop {pc}
            'pops past': (0xBC01, 0x4700),                         # pop {r0}; bx r0
            'outside its mapped span': (0xE7FF,),                  # b . + 2 past the end
            'different stack depths': (0x2800, 0xD000, 0xB082, 0x4770),
            'indirect branch ': (0xB500, 0x4770),                  # push {lr}; bx lr at depth 1
            # push {lr}; mov lr,r3; push {lr}; pop {r0}; add sp,#4; bx r0 returns to R3
            'saves LR twice': (0xB500, 0x469E, 0xB500, 0xBC01, 0xB001, 0x4700),
            # push {r4}; push {lr}; pop {pc} leaves SP one word below its entry value
            'saved LR ': (0xB410, 0xB500, 0xBD00),
            'releases past': (0xB001, 0xB081, 0x4770),             # add sp,#4; sub sp,#4; bx lr
            'indirect branch  ': (0x469E, 0x4770),                 # mov lr,r3; bx lr
            # cmp r0,#0; beq; mov lr,r3; bx lr: one path keeps LR, the join does not
            'indirect branch   ': (0x2800, 0xD000, 0x469E, 0x4770),
        }
        for reason, body in cases.items():
            with self.subTest(reason=reason):
                with self.assertRaisesRegex(sip.Refusal, reason.strip()):
                    self.reach({CALLEE: body})
        with self.assertRaisesRegex(sip.Refusal, 'inside itself'):
            self.reach({CALLEE: struct.unpack('<3H', assemble(CALLEE, (0xB500, CALLEE))) + (0xBD00,)})
        other = CALLEE + 0x100
        with self.assertRaisesRegex(sip.Refusal, 'recursive'):
            self.reach({CALLEE: struct.unpack('<3H', assemble(CALLEE, (0xB500, other))) + (0xBD00,),
                        other: struct.unpack('<3H', assemble(other, (0xB500, CALLEE))) + (0xBD00,)})
        with self.assertRaisesRegex(sip.Refusal, 'no mapped span'):
            self.reach({}, address=CALLEE)


class ShadowedRefusalTests(unittest.TestCase):
    """Three refusals that another check shadows for the owners the core hands to the analysis.
    The analysis is run alone, with deferred spills, ROM copies and returned aliases given directly.

    The owner is push {r4,lr}; sub sp,#8; <body>; movs r0,#0; add sp,#8; pop {r4}; pop {r1};
    bx r1, so sp+k is entry_SP + k - 16.  Its body starts at OWNER + 4, and CALLEE is `bx lr`."""

    def analyse(self, *body, spills=(), copies=None, returned=None):
        code = (0xB510, 0xB082) + body + (0x2000, 0xB002, 0xBC10, 0xBC02, 0x4708)
        reach = fw.CalleeReach(lambda target: struct.pack('<H', 0x4770), fw.POLICY.swis)
        analysis = fw.FrameWordsAnalysis(assemble(OWNER, code), OWNER, set(), set(), copies or {},
                                         spills=frozenset(spills), reach=reach, returned=returned)
        analysis.run()
        return analysis.frame_words_evidence()

    def test_exact_address_stored_where_the_core_did_not_defer_refuses(self):
        """No owner is known to reach this refusal through `owner.verify`.  The core defers every
        `str Rd,[sp,#k]` of a stack alias, so that site is always in ``spills``, and it refuses
        the same store through an alias register ("stack aliases cannot be stored or spilled")."""
        message = 'exact stack address stored to a local word the core did not defer'
        spill, site = (0x4668, 0x9001), OWNER + 6          # mov r0,sp; str r0,[sp,#4]
        cases = {'sp': spill,
                 'alias': (0x4668, 0x4669, 0x6048)}        # mov r0,sp; mov r1,sp; str r0,[r1,#4]
        for name, body in cases.items():
            with self.subTest(name), self.assertRaisesRegex(sip.Refusal, message):
                self.analyse(*body)
        # At a site the core deferred, the SP store makes the pointer word.
        found = self.analyse(*spill, spills={site})
        self.assertEqual((found['pointer_words'], found['spills']), ([-12], [site]))
        # A deferred site does not cover another one: str r0,[sp,#0] follows it.
        with self.assertRaisesRegex(sip.Refusal, message):
            self.analyse(*spill, 0x9000, spills={site})

    def test_stack_address_stored_through_a_possible_address_refuses(self):
        """Reached through `owner.verify`, with a spill deferred, only by values the inherited check
        refuses too, under another message: a variable address (the last owner below) or a reloaded
        pointer word.  The core refuses an exact or a possible address stored this way ("stack
        aliases cannot be stored or spilled")."""
        message = 'stack address stored through a possible stack address'
        # The call leaves R0 = sp+0, or no address.
        returned = {OWNER + 4: {0: frozenset({-16})}}
        cases = {'exact': (0x4669, 0x6001),                # mov r1,sp; str r1,[r0]
                 'possible': (0x6000,),                    # str r0,[r0]
                 # mov r1,sp; movs r2,#0; stmia r0!,{r1,r2}: one address among the stored values
                 'block': (0x4669, 0x2200, 0xC006)}
        for name, store in cases.items():
            with self.subTest(name), self.assertRaisesRegex(sip.Refusal, message):
                self.analyse(CALLEE, *store, returned=returned)
        # Scalars go through the same address, by either store (movs r1,#0 first).
        self.analyse(CALLEE, 0x2100, 0x6001, returned=returned)
        self.analyse(CALLEE, 0x2100, 0x2200, 0xC006, returned=returned)
        # adds r5,r0,#0; mov r1,sp; adds r1,r1,r4; str r1,[r5,#4] stores a variable address through
        # a returned alias.  FORCE defers a spill, so the plain analysis is not run first.
        body = FrameWordTests.RETURNED + (0x1C05, 0x4669, 0x1909, 0x6069) + ACCESS
        with self.assertRaisesRegex(sip.Refusal, message):
            admit(frame_owner(FORCE + body), **callee(0x4770))
        with self.assertRaisesRegex(sip.Refusal, 'ranged stack address escapes to memory'):
            admit(frame_owner(body), **callee(0x4770))

    def test_rom_copy_over_a_pointer_word_refuses(self):
        """No owner reaches this refusal through `owner.verify`.  A copy helper reads R0, its
        destination, and a callee that reads a register holding a stack address either refuses
        ("receives a stack address") or has every tracked word forgotten before the copy is
        checked.  The refusal fires only for a callee whose walk reports R0 unread: here `bx lr`,
        which the core would not take for a copy helper."""
        message = 'ROM copy destination overlaps a pointer-bearing local word'
        spill, call = OWNER + 6, OWNER + 8

        def copy(store, destination, count):
            # mov r0,sp; <str r0 to a local word>; bl callee, a ROM copy of ``count`` bytes
            return self.analyse(0x4668, store, CALLEE, spills={spill},
                                copies={call: (destination, count)})
        # Five bytes to sp+0 reach the word at sp+4 by their last byte, and the one at sp+0 by
        # their first.
        for store in (0x9001, 0x9000):
            with self.subTest(store=hex(store)), self.assertRaisesRegex(sip.Refusal, message):
                copy(store, -16, 5)
        # Four bytes end where the word at sp+4 begins, or begin where the one at sp+0 ends.
        found = copy(0x9001, -16, 4)
        self.assertEqual((found['pointer_words'], found['calls']), ([-12], [[call, CALLEE, 0, [], []]]))
        self.assertEqual(copy(0x9000, -12, 4)['pointer_words'], [-16])


class PoppedPointerWordTests(unittest.TestCase):
    """F7: a pop never reads a word that may be pointer-bearing."""

    def test_a_pop_of_a_pointer_word_refuses(self):
        # The core pops into an unknown scalar, so a popped pointer word would be a stack address
        # no check sees.  <release>; movs r2,#0; <use>; pop {r4-r7}; pop {r1}; bx r1, where
        # add sp,#12; pop {r1} reads the pointer word at sp+12 (entry_SP-24).
        spill = (0x4668, 0x9003) + ACCESS

        def popped(*use, body=spill, release=(0xb003, 0xbc02), index=MASKED):
            return frame_owner(body, tail=release + (0x2200,) + use + (0xbcf0, 0xbc02, 0x4708),
                               index=index)
        walked = callee(0x4770)
        cases = {
            'str over the saved r4': (popped(0x610A), {}),                 # str r2,[r1,#16]
            'str over the saved lr': (popped(0x620A), {}),                 # str r2,[r1,#32]
            'strb': (popped(0x740A), {}),
            'strh': (popped(0x820A), {}),
            'register offset': (popped(0x2310, 0x50CA), {}),               # movs r3,#16; str r2,[r1,r3]
            'stmia': (popped(0xC104), {}),                                 # stmia r1!,{r2}
            'a copy': (popped(0x1C0B, 0x611A), {}),                        # adds r3,r1,#0; str r2,[r3,#16]
            'a load of the saved lr': (popped(0x6A0A), {}),                # ldr r2,[r1,#32]
            'never used': (popped(), {}),
            'the last of four': (popped(0x611A, release=(0xbc0f,)), {}),   # pop {r0-r3}; str r2,[r3,#16]
            'one word at a time': (popped(0x610A, release=(0xbc01, 0xbc01, 0xbc01, 0xbc02)), {}),
            'into r4': (popped(0x6122, release=(0xb003, 0xbc10)), {}),     # str r2,[r4,#16]
            'after a push and pop': (popped(0x610A, release=(0xb401, 0xbc01, 0xb003, 0xbc02)), {}),
            # str r0,[sp,#8] too: add sp,#12 releases that pointer word first (released frame)
            'after a release': (popped(0x610A, body=(0x4668, 0x9003, 0x9002) + ACCESS), {}),
            # add sp,#12; pop {r0,r4-r7}; pop {r1}; bx r1: the address is returned in R0
            'the first of five': (frame_owner(spill, tail=(0xb003, 0xbcf1, 0xbc02, 0x4708)), {}),
            # cmp r4,#0; beq; mov r0,sp; str r0,[sp,#12]: pointer-bearing on one path only
            'a maybe pointer word': (popped(0x610A, body=(0x2C00, 0xD001, 0x4668, 0x9003) + ACCESS), {}),
            'a call before': (popped(0x610A, body=(0x4668, 0x9003, CALLEE) + ACCESS), walked),
            # mov r0,sp; bl callee; str r0,[sp,#12]: the core's returned alias, spilled
            'a returned alias': (popped(0x610A, body=(0x4668, CALLEE, 0x9003) + ACCESS), walked),
        }
        for selector in sip.SELECTORS:
            for name, (code, extra) in cases.items():
                with self.subTest(selector=selector, case=name):
                    with self.assertRaisesRegex(sip.Refusal, 'pop of the pointer-bearing local word at '
                                                'entry-SP-24'):
                        admit(code, selector=selector, **extra)
            with self.subTest(selector=selector, case='a ranged spill'):
                # mov r1,sp; adds r1,r1,r4; str r1,[sp,#12]; movs r0,#7; strb r0,[r1] (twice);
                # ldr r2,[sp,#12]; ldrb r0,[r2]: both analyses refuse, so the plain refusal is the
                # one reported.
                body = (0x4669, 0x1909, 0x9103, 0x2007, 0x7008, 0x7008, 0x9A03, 0x7810)
                with self.assertRaisesRegex(sip.Refusal, 'ranged stack address escapes to memory'):
                    admit(popped(0x610A, body=body, index=RANGED), selector=selector)
        # Popped into PC: push {lr}; sub sp,#4; mov r0,sp; str r0,[sp,#0]; pop {pc}
        data = assemble(OWNER, (0xB500, 0xB081, 0x4668, 0x9000, 0xBD00))
        with self.assertRaisesRegex(sip.Refusal, 'pop of the pointer-bearing local word at entry-SP-8'):
            fw.FrameWordsAnalysis(data, OWNER, frozenset(), frozenset(), {}, spills={OWNER + 6}).run()
        # Popping a scalar word, or any word beside a live pointer word, is no pop of one; and
        # add sp releases a pointer word without reading it.
        admit(popped(0x610A, body=(0x2000, 0x9003) + ACCESS))             # movs r0,#0; str r0,[sp,#12]
        admit(frame_owner(spill + (0xB401, 0xBC01)))                       # push {r0}; pop {r0}
        admit(frame_owner(spill))


if __name__ == '__main__':
    unittest.main()
