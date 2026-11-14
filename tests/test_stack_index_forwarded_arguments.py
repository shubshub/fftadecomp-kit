"""named-data-buffer-stack-index-v2: forwarded callee stack arguments and ASR congruence."""
import copy
import hashlib
import itertools
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
FORWARDER, LEAF = 0x08014000, 0x08015000

# Leaf: ldr r1,[sp,#0]; movs r0,#0; strh r0,[r1]; bx lr - writes through its fifth argument.
LEAF_CODE = (0x9900, 0x2000, 0x8008, 0x4770)
# Forwarder: push {lr}; sub sp,#4; str r1,[sp]; bl LEAF; add sp,#4; pop {r0}; bx r0.
FORWARDER_CODE = (0xb500, 0xb081, 0x9100, LEAF, 0xb001, 0xbc01, 0x4700)


def forwarding(forwarder=FORWARDER_CODE, leaf=LEAF_CODE, selector=V2):
    """The masked-index owner, then `add r1,sp,#4; bl FORWARDER` passing its free local word."""
    patch = {}
    spans = []
    for address, code in ((FORWARDER, forwarder), (LEAF, leaf)):
        raw = assemble(address, code)
        patch.update({address + offset: value for offset, value in enumerate(raw)})
        spans.append((address, len(raw), len(code)))
    return dict(code=owner_code(tail=(0xa901, FORWARDER)), selector=selector, patch_rom=patch,
                extra_functions=tuple(spans))


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
                         ('((entry_R0 << 24) >>s 22)', 5, 4))

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
