"""The callee owns its stack-argument words: a word the caller stored for a call's fifth or later
argument is not read back after the call as the caller's value.

agbcc writes into its own stack arguments (`ldr r1, [sp, #4]; add r1, r0; str r1, [sp, #4]` for
`e += a`), so after the call the word may hold anything.  Executor.call stores an opaque value of
the callee's into each word before an escape, named by the call; relational loop induction already
did the same.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

FIVE = fixtures.PREPROCESSED + "extern void func_0802A2C4(int, int, int, int, int);\n"
DIFFER = "differ in observable behaviour"


def outgoing(*use, before=()):
    """func_0802A2C4(1, 2, 3, 4, arg0), arg0 also kept in r4; the fifth argument is the word at sp"""
    return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "mov\tr4, r0", "str\tr0, [sp]", *before,
                             "mov\tr0, #1", "mov\tr1, #2", "mov\tr2, #3", "mov\tr3, #4", "bl\tfunc_0802A2C4",
                             "ldr\tr2, .L3", *use, "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}", "bx\tr0")


KEPT = outgoing("str\tr4, [r2]")


def records(body):
    function = semantics.parse_assembly(body)[0]["func_08028C34"]
    signatures = {"func_0802A2C4": (False, 5)}
    return semantics.explore("func_08028C34", function, signatures, "real",
                             (fixtures.SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1}))[0].records


class CalleeArgumentTests(unittest.TestCase):
    def refused(self, real, stripped=KEPT, reason=DIFFER):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped, FIVE)
        self.assertIn(reason, str(caught.exception))

    def test_a_reload_after_the_call_reads_the_callees_word(self):
        self.refused(outgoing("ldr\tr0, [sp]", "str\tr0, [r2]"))
        load = [r for r in records(outgoing("ldr\tr0, [sp]", "str\tr0, [r2]")) if r.kind == "load"][-1]
        self.assertEqual(load.value, ("callee-argument", 0, 4, ("arg", 0)))

    def test_the_callees_word_builds_no_object_offset(self):
        # a zero stored as the fifth argument, reloaded after the call as an index into the object
        body = outgoing("ldr\tr3, [sp]", "ldrb\tr0, [r2, r3]", "strb\tr0, [r2, #3]",
                        before=("mov\tr0, #0", "str\tr0, [sp]"))
        self.refused(body, outgoing("ldrb\tr0, [r2]", "strb\tr0, [r2, #3]", before=("mov\tr0, #0", "str\tr0, [sp]")),
                     "read back from memory")

    def test_the_word_stored_again_after_the_call_is_read_back(self):
        results = fixtures.compare(outgoing("str\tr4, [sp]", "ldr\tr0, [sp]", "str\tr0, [r2]"), KEPT, FIVE)
        self.assertEqual(results[0][1], 1)

    def test_a_reload_before_the_call_is_read_back(self):
        def body(*use):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "mov\tr4, r0", "str\tr0, [sp]",
                                     "ldr\tr2, .L3", *use, "mov\tr0, #1", "mov\tr1, #2", "mov\tr2, #3",
                                     "mov\tr3, #4", "bl\tfunc_0802A2C4", "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}",
                                     "bx\tr0")
        results = fixtures.compare(body("ldr\tr0, [sp]", "str\tr0, [r2]"), body("str\tr4, [r2]"), FIVE)
        self.assertEqual(results[0][1], 1)

    def test_a_call_whose_arguments_are_not_read_back_keeps_its_record(self):
        results = fixtures.compare(KEPT, KEPT, FIVE)
        self.assertEqual(semantics.record(fixtures.SYMBOL, results),
                         "* allowlisted volatile semantics: `g_control_flags_03000940` stripped of volatile compiles "
                         "to the same behaviour; `func_08028C34` agrees on 1 path; read-modify-write loads at [], "
                         "chained re-reads at []")

    def test_each_stack_word_is_the_callees_after_the_call(self):
        layout = (fixtures.SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1})
        explorer = semantics.Executor("func_08028C34", semantics.parse_assembly(KEPT)[0]["func_08028C34"],
                                      {"func_0802A2C4": (False, 5)}, "real", layout)
        explorer.run([])
        argument = [entry for entry in explorer.memory
                    if entry[0] == "store" and entry[3][:1] == ("callee-argument",)]
        word = semantics.add(semantics.SP, -16)
        self.assertEqual(argument, [("store", 4, word, ("callee-argument", 0, 4, ("arg", 0)), None, False, True)])

    def test_an_escaped_frame_keeps_the_call_as_its_barrier(self):
        # the frame escapes to the call itself (r0 = sp): the call stops the reload, no store stands for it
        def body(*use):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "mov\tr4, r0", "str\tr0, [sp]",
                                     "mov\tr0, sp", "mov\tr1, #2", "mov\tr2, #3", "mov\tr3, #4", "bl\tfunc_0802A2C4",
                                     "ldr\tr2, .L3", *use, "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        load = [r for r in records(body("ldr\tr0, [sp]", "str\tr0, [r2]")) if r.kind == "load"][-1]
        self.assertEqual(load.value[0], "load")
        self.assertEqual(load.value[3][0], "call")


if __name__ == "__main__":
    unittest.main()
