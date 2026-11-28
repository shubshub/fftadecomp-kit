"""Copy classes in the stack-index walk: a branch refines every exact register copy of the compared value."""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match_evidence as evidence
import stack_index_precondition_profile as sip
from test_stack_index_precondition import admit, evidence as index_evidence, owner_code
# Modules only: importing their TestCase classes would run them here again.
import test_data_buffer_calls as data_calls
import test_default_stack_index as default_tests

# Before the copy call: r4 = entry_R0 & 3 (adds r4,r0,#0; lsls r4,r4,#30; lsrs r4,r4,#30).
MODE3 = (0x1C04, 0x07A4, 0x0FA4)
# ...then cmp r4,#2; bls +0; movs r4,#2: r4 is 0, 1 or 2, as the mode of 0x080EF970 is.
MODE = MODE3 + (0x2C02, 0xD900, 0x2402)
COPY = 0x1C23            # adds r3, r4, #0
MOV_SP = 0x4668          # mov r0, sp
LOAD = 0x5CC0            # ldrb r0, [r0, r3]
# cmp r4,#1; bls +0; movs r3,#0; mov r0,sp: r3 is the index when r4 <= 1, else 0.
GUARD = (0x2C01, 0xD900, 0x2300, MOV_SP)


def admitted(prefix, index=MODE3, access=(LOAD,)):
    """Admit a two-byte copied table read at r3 after <prefix>; return the stack-index evidence."""
    _, (manifest, _) = admit(owner_code(count=2, index=index, prefix=prefix, access=access))
    return index_evidence(manifest)


class CopyClassTests(unittest.TestCase):
    def assert_proved(self, found):
        # In bounds by the value range alone: no premise row, one proved access.
        self.assertEqual(found['preconditions'], [])
        self.assertIsNone(found['accepted'])
        self.assertEqual(len(found['accesses']), 1)

    def assert_refused(self, prefix, index=MODE3, access=(LOAD,)):
        with self.assertRaises(sip.Refusal):
            admitted(prefix, index=index, access=access)

    def test_the_copy_of_a_compared_mode_is_refined(self):
        # 0x080EF970: index = mode; if (mode == 2) index = 0; table[index], mode in {0,1,2}.
        # adds r3,r4,#0; cmp r4,#2; bne +0; movs r3,#0; mov r0,sp; ldrb r0,[r0,r3]
        self.assert_proved(admitted((COPY, 0x2C02, 0xD100, 0x2300, MOV_SP), index=MODE))
        # Each exact copy encoding: lsls r3,r4,#0 (movs r3,r4) and adds r3,r4,#0.
        for copy in (0x0023, COPY):
            with self.subTest(copy=hex(copy)):
                self.assert_proved(admitted((copy,) + GUARD))

    def test_an_equal_value_that_is_not_a_copy_is_not_refined(self):
        # adds r3,r4,#1; subs r3,#1 holds r4's value, but by arithmetic: no class, no bound.
        with self.assertRaisesRegex(sip.Refusal, 'no defined source'):
            admitted((0x1C63, 0x3B01, 0x2C02, 0xD100, 0x2300, MOV_SP), index=MODE)

    def test_a_copy_through_a_high_register_after_the_compare_is_refined(self):
        # cmp r4,#2; mov r12,r4; bne +1; movs r3,#0; mov r12,r3; mov r3,r12; mov r0,sp.
        # MOV between high registers sets no flags, so the compare still decides the branch.
        self.assert_proved(admitted((0x2C02, 0x46A4, 0xD101, 0x2300, 0x469C, 0x4663, MOV_SP),
                                    index=MODE))

    def test_a_write_between_the_copy_and_the_branch_is_not_refined(self):
        self.assert_proved(admitted((COPY,) + GUARD))
        for name, write in (('reload of the copy', (0x9B01,)),          # ldr r3,[sp,#4]
                            ('add to the copy', (0x3301,)),             # adds r3,#1
                            ('add to the source', (0x3401,)),           # adds r4,#1
                            ('equal-range twin', (0x2103, 0x404B))):    # movs r1,#3; eors r3,r1
            with self.subTest(name):
                self.assert_refused((COPY,) + write + GUARD)

    def test_a_call_takes_its_clobbered_registers_out_of_their_classes(self):
        # adds r3,r4,#0 before the copy call: R3 is clobbered by it and no longer holds r4's value.
        self.assert_refused(GUARD, index=MODE3 + (COPY,))

    def test_a_register_written_again_does_not_rejoin_its_old_copies(self):
        # adds r2,r3,#0; ldr r3,[sp,#4]; cmp r3,#1; bls +0; movs r2,#0; mov r0,sp; ldrb r0,[r0,r2].
        self.assert_refused((0x1C1A, 0x9B01, 0x2B01, 0xD900, 0x2200, MOV_SP), access=(0x5C80,))

    def test_a_join_keeps_a_class_only_where_both_paths_agree(self):
        copy_only = (COPY,)
        twin = (0x2103, COPY, 0x404B)                 # movs r1,#3; adds r3,r4,#0; eors r3,r1

        def split(first, second):
            # cmp r1,#0; beq second; <first>; b join; second: <second>; join: GUARD.
            return (0x2900, 0xD000 | (len(first)), *first, 0xE000 | (len(second) - 1), *second) + GUARD
        self.assert_proved(admitted(split(copy_only, (0x2103, COPY))))
        for name, first, second in (('copy first', copy_only, twin), ('copy second', twin, copy_only)):
            with self.subTest(name):
                self.assert_refused(split(first, second))
        # A branch straight to the join: movs r3,#3; cmp r1,#0; beq J; adds r3,r4,#0; J: GUARD.  The
        # fall-through copy reaches J before the taken edge's own state is walked on, so a join that
        # kept the incoming classes would refine r3 = 3 by r4's compare (rv-R's T10).
        self.assert_refused((0x2303, 0x2900, 0xD000, COPY) + GUARD)
        self.assert_proved(admitted((COPY, 0x2900, 0xD000, COPY) + GUARD))

    def test_a_join_meets_the_two_partitions_whichever_path_arrives_first(self):
        # join_states keeps only what both sides share, whichever side is the state already there.
        analysis = sip.Analysis(bytes(4), 0x08010000, {}, {}, {})

        def state(*groups):
            labels = list(range(16))
            for group in groups:
                for register in group:
                    labels[register] = group[0]
            return sip.State((), frozenset(), tuple([sip.TOP] * 16), tuple([None] * 16), None,
                             sip.classes(labels))

        def together(joined, *registers):
            return len({joined.same[register] for register in registers}) == 1
        for old, new in ((state((3, 4)), state()), (state(), state((3, 4)))):
            joined = analysis.join_states(old, new, 0x08010000, 1)
            self.assertFalse(together(joined, 3, 4))
        for old, new in ((state((2, 3, 4)), state((3, 4), (2, 5))), (state((3, 4), (2, 5)), state((2, 3, 4)))):
            joined = analysis.join_states(old, new, 0x08010000, 1)
            self.assertTrue(together(joined, 3, 4))
            self.assertFalse(together(joined, 2, 3) or together(joined, 2, 5))
        self.assertTrue(together(analysis.join_states(state((3, 4)), state((3, 4)), 0x08010000, 1), 3, 4))


class FarJumpTests(unittest.TestCase):
    def test_a_far_jump_takes_lr_out_of_its_copy_class(self):
        # bl +4 (a same-function far jump to 0x08010008); LR := the continuation, so it holds no copy.
        # far_jump_profile proves LR dead after the jump, so only the state itself can show this.
        address = 0x08010000
        data = bytes.fromhex('00f002f8') + bytes.fromhex('c046') * 4
        analysis = sip.Analysis(data, address, {}, {}, {})
        analysis.far_jumps = {address: address + 8}
        labels = list(range(16))
        labels[14] = 4                                  # mov lr, r4 earlier: LR in r4's class
        state = sip.State((), frozenset(), tuple([sip.TOP] * 16), tuple([None] * 16), None,
                          sip.classes(labels))
        (target, after), = analysis.step(state, address)
        self.assertEqual(target, address + 8)
        self.assertNotEqual(after.same[14], after.same[4])
        self.assertEqual(after.same[:14], state.same[:14])


# 0x080EF970's shape in C: the mode stays live after the index is taken from it.
MODE_SOURCE = """typedef unsigned char u8;
typedef unsigned int u32;
extern void func_08000400(u32 value);
u32 func_08000200(u32 value)
{
    u8 table[2];
    u32 mode, index;

    table[0] = 3;
    table[1] = 1;
    func_08000400(value);
    mode = 2;
    if (value & 1)
        mode = 1;
    else if (value & 2)
        mode = 0;
    index = mode;
    if (mode == 2)
        index = 0;
    return table[index] + mode;
}
"""


@unittest.skipUnless(data_calls.tools_present(), 'fixed compiler and ARM tools required')
class NativeTests(unittest.TestCase):
    """match.py end to end on compiled C, through the default stack-index retry."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='stack_index_copy_classes_', dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, root, report):
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def test_the_copied_mode_index_matches_and_replays(self):
        root = data_calls.build(self.base / 'mode', MODE_SOURCE, default_tests.CALLEES)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        self.assertEqual(data_calls.verification(report), evidence.STACK_BUFFER_SCHEMA)
        lines = report.splitlines()
        self.assertTrue(any(line.startswith('* buffer stack index: `default-stack-index-retry-v1`')
                            for line in lines))
        self.assertFalse(any(line.startswith('* buffer stack index premise: ') for line in lines))
        self.assertTrue(self.replays(root, report))
        self.assertFalse(self.replays(root, report.replace('accesses proved', 'accesses  proved')))


if __name__ == '__main__':
    unittest.main()
