"""A frame word released by an sp increase holds no defined value: it is not read back as the value
stored before the release.

Memory below sp is written by any call made while sp is above it (the callee's frame), by a BIOS call's
stack work and by an interrupt handler between any two instructions.  Executor.load refuses a read the
scan finds behind a release of its bytes, and frame_read refuses a read that may reach a byte released
since its store.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

RELEASED = "reads a frame word released by an sp increase"
BELOW = "a frame access below sp"


def framed(*body):
    return fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", *body, "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")


STRIPPED = framed("ldr\tr2, .L3", "str\tr0, [r2]")
AGAIN = ("str\tr0, [sp]", "add\tsp, sp, #8", "add\tsp, sp, #-8")


def around(*use):
    """a call made while the word is released: its frame lands on the word"""
    return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "mov\tr4, r0", "str\tr0, [sp]",
                             "add\tsp, sp, #8", "bl\tfunc_0802A2C0", "add\tsp, sp, #-8", "ldr\tr2, .L3", *use,
                             "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}", "bx\tr0")


class ReleasedWordTests(unittest.TestCase):
    def refused(self, real, stripped=STRIPPED, reason=RELEASED):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)
        self.assertIn(reason, str(caught.exception))

    def test_a_word_released_and_allocated_again(self):
        self.refused(framed(*AGAIN, "ldr\tr2, .L3", "ldr\tr0, [sp]", "str\tr0, [r2]"))

    def test_a_word_read_below_sp(self):
        # memory below sp is never private, whatever was stored there before the release
        real = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "str\tr0, [sp]", "add\tsp, sp, #8",
                                 "ldr\tr2, .L3", "mov\tr1, sp", "sub\tr1, r1, #8", "ldr\tr0, [r1]", "str\tr0, [r2]",
                                 "pop\t{r0}", "bx\tr0")
        stripped = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "add\tsp, sp, #8", "ldr\tr2, .L3",
                                     "str\tr0, [r2]", "pop\t{r0}", "bx\tr0")
        self.refused(real, stripped, BELOW)

    def test_plain_accesses_below_sp_are_refused(self):
        # a store below sp and its reload, with no release between: an interrupt may write the word
        below = ("mov\tr1, sp", "sub\tr1, r1, #4")
        for width, (store, load) in ((4, ("str", "ldr")), (2, ("strh", "ldrh")), (1, ("strb", "ldrb"))):
            with self.subTest(width=width):
                self.refused(framed(*below, f"{store}\tr0, [r1]", "ldr\tr2, .L3", f"{load}\tr0, [r1]",
                                    f"{store}\tr0, [r2]"), reason=BELOW)
                # a load below sp alone, with nothing stored there
                self.refused(framed(*below, "ldr\tr2, .L3", f"{load}\tr0, [r1]", f"{store}\tr0, [r2]"),
                             reason=BELOW)
        # sp itself and above are the frame
        self.assertEqual(fixtures.compare(framed("str\tr0, [sp]", "ldr\tr2, .L3", "ldr\tr0, [sp]", "str\tr0, [r2]"),
                                          STRIPPED)[0][1], 1)

    def test_push_and_pop_are_no_plain_accesses(self):
        # push stores below the old sp and pop reads at sp before rising: both admitted
        real = fixtures.assembly("push\t{lr}", "push\t{r0}", "ldr\tr2, .L3", "pop\t{r1}", "str\tr1, [r2]",
                                 "pop\t{r0}", "bx\tr0")
        stripped = fixtures.assembly("push\t{lr}", "ldr\tr2, .L3", "str\tr0, [r2]", "pop\t{r0}", "bx\tr0")
        self.assertEqual(fixtures.compare(real, stripped)[0][1], 1)

    def test_a_word_released_across_a_call(self):
        self.refused(around("ldr\tr0, [sp]", "str\tr0, [r2]"), around("str\tr4, [r2]"))

    def test_the_word_kept_allocated_is_read_back(self):
        results = fixtures.compare(framed("str\tr0, [sp]", "ldr\tr2, .L3", "ldr\tr0, [sp]", "str\tr0, [r2]"),
                                   STRIPPED)
        self.assertEqual(results[0][1], 1)

    def test_a_word_stored_again_after_the_release_is_read_back(self):
        results = fixtures.compare(framed(*AGAIN, "str\tr0, [sp]", "ldr\tr2, .L3", "ldr\tr0, [sp]",
                                          "str\tr0, [r2]"), STRIPPED)
        self.assertEqual(results[0][1], 1)

    def test_a_push_into_a_released_slot_reads_back_its_own_word(self):
        real = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "str\tr1, [sp]", "add\tsp, sp, #8",
                                 "push\t{r0}", "ldr\tr2, .L3",
                                 "ldr\tr0, [sp]", "str\tr0, [r2]", "add\tsp, sp, #4", "pop\t{r0}", "bx\tr0")
        stripped = fixtures.assembly("push\t{lr}", "ldr\tr2, .L3", "str\tr0, [r2]", "pop\t{r0}", "bx\tr0")
        self.assertEqual(fixtures.compare(real, stripped)[0][1], 1)

    def test_epilogues_are_unchanged(self):
        # `add sp, #8; pop {r4}; pop {r0}`: each pop reads its word before it releases it
        body = fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "ldr\tr2, .L3", "str\tr0, [r2]",
                                 "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.assertEqual(fixtures.compare(body, body)[0][1], 1)

    def test_a_store_of_a_loaded_value_into_a_released_slot(self):
        # the store's self-assignment probe meets the release: no failure, and no self-assignment
        real = framed("str\tr1, [sp]", "add\tsp, sp, #8", "add\tsp, sp, #-8", "ldr\tr2, .L3", "ldrb\tr0, [r2, #2]",
                      "str\tr0, [sp]", "ldr\tr3, [sp]", "strb\tr3, [r2, #3]")
        stripped = framed("ldr\tr2, .L3", "ldrb\tr0, [r2, #2]", "strb\tr0, [r2, #3]")
        self.assertEqual(fixtures.compare(real, stripped)[0][1], 1)

    def test_frame_reads_refuse_released_bytes(self):
        # a read at a variable offset once a byte is released: it may reach it
        indexed = ("lsl\tr3, r1, #2", "mov\tr2, sp", "add\tr2, r2, r3")
        self.refused(framed(*AGAIN, *indexed, "ldr\tr0, [r2]", "ldr\tr2, .L3", "str\tr0, [r2]"))
        # a fixed slot read behind a store at a variable offset: the scan stops at that store, and the
        # frame read's window holds the released word
        self.refused(framed(*AGAIN, *indexed, "str\tr1, [r2]", "ldr\tr2, .L3", "ldr\tr0, [sp]", "str\tr0, [r2]"))
        # the same reads with the word kept allocated, or stored again after the release, are frame
        # reads of bound bytes
        for kept in (("str\tr0, [sp]",), AGAIN + ("str\tr0, [sp]",)):
            body = framed(*kept, *indexed, "ldr\tr0, [r2]", "ldr\tr2, .L3", "str\tr0, [r2]")
            self.assertEqual(fixtures.compare(body, body)[0][1], 1)

    def test_a_word_written_only_at_a_variable_offset(self):
        # stored at sp + 4*r5, released, allocated again and read at the same variable offset: the
        # store may have been to a released byte
        def body(*tail):
            return framed("lsl\tr3, r5, #2", "mov\tr1, sp", "add\tr1, r1, r3", "str\tr0, [r1]", "add\tsp, sp, #8",
                          "add\tsp, sp, #-8", *tail)
        read = body("mov\tr1, sp", "add\tr1, r1, r3", "ldr\tr0, [r1]", "ldr\tr2, .L3", "str\tr0, [r2]")
        self.refused(read, read)
        # a fixed slot read behind a later store at a variable offset: the earlier one may have
        # written the slot before the release, unless a fixed store wrote it again since
        later = ("mov\tr1, sp", "add\tr1, r1, r3", "str\tr4, [r1]", "ldr\tr2, .L3", "ldr\tr0, [sp]", "str\tr0, [r2]")
        self.refused(body(*later), body(*later))
        again = body("str\tr0, [sp]", *later)
        self.assertEqual(fixtures.compare(again, again)[0][1], 1)
        # without the release the variable read is a frame read of bound stores
        kept = framed("lsl\tr3, r5, #2", "mov\tr1, sp", "add\tr1, r1, r3", "str\tr0, [r1]", "ldr\tr0, [r1]",
                      "ldr\tr2, .L3", "str\tr0, [r2]")
        self.assertEqual(fixtures.compare(kept, kept)[0][1], 1)

    def test_a_pointer_after_an_escape(self):
        # after the frame escapes, a pointer not built from sp may point at the released word
        def body(*use):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "add\tr4, r1, #0", "str\tr0, [sp]",
                                     "mov\tr0, sp", "bl\tfunc_0802A2C0", "add\tsp, sp, #8", "add\tsp, sp, #-8",
                                     "ldr\tr2, .L3", *use, "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.refused(body("ldr\tr0, [r4]", "str\tr0, [r2]"), body("ldr\tr0, [r4]", "str\tr0, [r2]"))
        # and so may an offset from sp that is not constant
        indexed = body("lsl\tr3, r5, #2", "mov\tr0, sp", "add\tr0, r0, r3", "ldr\tr0, [r0]", "str\tr0, [r2]")
        self.refused(indexed, indexed)
        # a named object is never in the frame
        self.assertEqual(fixtures.compare(body("ldrb\tr0, [r2, #2]", "strb\tr0, [r2, #3]"),
                                          body("ldrb\tr0, [r2, #2]", "strb\tr0, [r2, #3]"))[0][1], 1)


if __name__ == "__main__":
    unittest.main()
