"""Stack-index owners whose locals hold spilled stack addresses and counters (frame words)."""
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
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
    # ---- F2: calls ------------------------------------------------------------------------
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


class ReviewReproducerTests(unittest.TestCase):
    """Owners an adversarial review built against the first version; each must refuse."""

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


if __name__ == '__main__':
    unittest.main()
