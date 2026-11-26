"""Limits of the volatile check's loop induction that byte-identical sources met."""

import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_semantics as semantics
import test_volatile_loop_induction as T

FRAME, END, MEMBER, loop = T.FRAME, T.END, T.MEMBER, T.loop

# the frame escapes before the loop; each iteration passes a fifth argument on the stack
ESCAPE = ("mov\tr6, r1", "add\tsp, sp, #-8", "mov\tr0, sp", "bl\tfunc_0802A2C0")
FIVE = ("mov\tr5, #7", "str\tr5, [sp]", "mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0", "mov\tr3, #0",
        "bl\tfunc_0802A300")


def after_five(*reads):
    """the reads after the call, their byte stored to the object's unknown_02 + 4"""
    return FRAME + ESCAPE + loop(*FIVE, *reads, "ldr\tr1, .L3", "strb\tr0, [r1, #6]", "mov\tr0, #0", start="r7") + \
        MEMBER + ("add\tsp, sp, #8",) + END


class CalleeArgumentTests(T.Base):
    """After the frame escapes, the induction lets a callee write its stack argument words."""

    def test_a_named_object_read_after_the_call(self):
        # one byte of the object's unknown_02, read after the call: a named object is never
        # in the frame, so the callee's argument word does not stop it
        body = after_five("ldr\tr1, .L3", "ldrb\tr0, [r1, #2]")
        self.bounded(body)
        (result,) = self.compare(body)
        self.assertEqual(result[0], "func_08028C34")

    def test_the_compiles_still_compare_that_read(self):
        body = after_five("ldr\tr1, .L3", ("real", "ldrb\tr0, [r1, #2]"), ("stripped", "ldrb\tr0, [r1, #3]"))
        self.refused(body, "differ in observable behaviour")

    def test_a_read_moved_across_the_next_call(self):
        # between two five-argument calls in the real compile, after the second in the
        # stripped one: each read is versioned by the call before it, so they differ
        between = ("ldr\tr1, .L3", "ldrb\tr7, [r1, #2]")
        self.refused(after_five(*(("real", line) for line in between), *FIVE,
                                *(("stripped", line) for line in between), "mov\tr0, r7"),
                     "differ in observable behaviour")
        (result,) = self.compare(after_five(*between, *FIVE, "mov\tr0, r7"))
        self.assertEqual(result[0], "func_08028C34")

    def test_a_read_that_may_be_in_the_frame(self):
        # through a pointer the function was given, which may point into the escaped frame
        self.refused(after_five("ldrb\tr0, [r6, #1]"), "partially overlapping stack access")
        # one byte of the argument word itself
        self.refused(after_five("add\tr1, sp, #1", "ldrb\tr0, [r1]"), "partially overlapping stack access")


class CalleeArgumentMutantTests(T.Base):
    def test_without_the_named_object_condition(self):
        # every non-frame address passes the argument word: the pointer read is admitted
        original = semantics.global_symbol
        with mock.patch.object(semantics, "global_symbol", lambda address: original(address) or "any"):
            (result,) = self.compare(after_five("ldrb\tr0, [r6, #1]"))
        self.assertEqual(result[0], "func_08028C34")


if __name__ == "__main__":
    unittest.main()
