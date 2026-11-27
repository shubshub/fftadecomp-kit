"""kit#165: a spill reload inside a volatile member store's read-modify-write window.

agbcc's reload pass puts the reload of a spilled stored value just before the
store that uses it, so it lands between the bit-field insertion's dead load
and the store (0813F22C 0x0813F2AC: `ldrh r0, [r5, #10]; movs r2, #0;
ldr r3, [sp, #8]; strh r3, [r5, #10]`).  The window admits it only when it
provably reloads what the nearest earlier store to its slot wrote, and feeds
only the stored value.
"""
import copy
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

SYMBOL = fixtures.SYMBOL


def framed(*body):
    return fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", *body, "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")


def window(*between, spill=("str\tr3, [sp, #4]",), load="ldrb\tr2, [r1]", store="strb\tr3, [r1]",
           value="mov\tr3, r0"):
    """`sym.unknown_3C = arg0`, with the value spilled to sp+4 and reloaded in the window"""
    return framed("ldr\tr1, .L3", "add\tr1, r1, #60", value, *spill, load, *between, store)


STRIPPED = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "strb\tr0, [r1]")


class SpillReloadTests(unittest.TestCase):
    def refused(self, real, stripped=STRIPPED, reason="not directly followed by a store"):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)
        self.assertIn(reason, str(caught.exception))

    def test_a_reload_of_the_spilled_value_is_admitted(self):
        results = fixtures.compare(window("ldr\tr3, [sp, #4]"), STRIPPED)
        self.assertEqual(results[0][2], [6])
        self.assertIn("read-modify-write windows holding a spill reload (kit#165) at [7]",
                      semantics.record(SYMBOL, results))
        # only where the rule is used: a window without a reload keeps the record's text
        plain = fixtures.compare(framed("ldr\tr1, .L3", "add\tr1, r1, #60", "ldrb\tr2, [r1]",
                                        "strb\tr0, [r1]"), STRIPPED)
        self.assertNotIn("spill reload", semantics.record(SYMBOL, plain))

    def test_with_a_scheduled_in_constant_and_a_copy(self):
        # 0813F22C's shape: an immediate for later code, then the reload
        real = window("mov\tr2, #0", "ldr\tr3, [sp, #4]", spill=("str\tr3, [sp, #4]",), store="strb\tr3, [r1]")
        self.assertEqual(fixtures.compare(real, STRIPPED)[0][2], [6])
        copied = window("ldr\tr2, [sp, #4]", "mov\tr3, r2")
        self.assertEqual(fixtures.compare(copied, STRIPPED)[0][2], [6])

    def test_a_halfword_member(self):
        real = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "ldr\tr1, .L3", "mov\tr3, r0",
                                 "str\tr3, [sp, #4]", "ldrh\tr2, [r1, #2]", "ldr\tr3, [sp, #4]",
                                 "strh\tr3, [r1, #2]", "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")
        stripped = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "ldr\tr1, .L3", "strh\tr0, [r1, #2]",
                                     "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")
        report, = semantics._compare_compiles(real, stripped, fixtures.PREPROCESSED, SYMBOL,
                                              fixtures.DECLARATION16)
        self.assertEqual(report[2], [5])

    def test_a_load_of_a_slot_nothing_stored_is_refused(self):
        # the planted case: a frame word this function never wrote (an incoming
        # stack argument above the frame) reads like a reload but reloads nothing
        planted = window("ldr\tr3, [sp, #12]", spill=())
        stripped = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "ldr\tr3, [sp, #12]", "strb\tr3, [r1]")
        self.refused(planted, stripped)

    def test_an_overlapping_store_or_a_moved_stack_is_refused(self):
        # the executor refuses the partial overlap itself; spill_reload would too
        self.refused(window("ldr\tr3, [sp, #4]", spill=("str\tr3, [sp, #4]", "strh\tr2, [sp, #6]")),
                     reason="partially overlapping stack access")
        self.refused(window("ldr\tr3, [sp, #4]", spill=("str\tr3, [sp, #4]", "add\tsp, sp, #-8",
                                                          "add\tsp, sp, #8")))
        # a store through a frame address at a variable offset may reach the slot
        self.refused(window("ldr\tr3, [sp, #4]", spill=("str\tr3, [sp, #4]", "mov\tr2, sp",
                                                          "add\tr2, r2, r5", "str\tr4, [r2]")))

    def test_a_reload_that_builds_the_address_or_is_not_a_word_is_refused(self):
        address = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "str\tr1, [sp, #4]", "ldrb\tr2, [r1]",
                         "ldr\tr1, [sp, #4]", "strb\tr0, [r1]")
        # the object's address never reaches a frame slot at all
        self.refused(address, reason="is stored to memory")
        # a reload into the address register of another, plain, store target
        plain = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "str\tr4, [sp, #4]", "ldrb\tr2, [r1]",
                       "ldr\tr1, [sp, #4]", "strb\tr0, [r1]")
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(plain, framed("ldr\tr1, .L3", "add\tr1, r1, #60", "strb\tr0, [r4]"))
        self.refused(window("ldrh\tr3, [sp, #4]", spill=("strh\tr3, [sp, #4]",)))
        self.refused(window("ldr\tr3, [sp, r4]"))
        self.refused(window("ldr\tr3, [r4]"))
        # a second object load between still refuses: the window holds one dead load
        self.refused(window("ldrb\tr2, [r1]", "ldr\tr3, [sp, #4]"))

    def test_a_reload_across_a_call_that_may_write_the_slot_is_refused(self):
        # the slot's address escapes to the call, so it may hold anything after it: the
        # executor reads back a value of its own, not the spilled one
        def body(*load):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "ldr\tr4, .L3", "add\tr4, r4, #60",
                                     "str\tr0, [sp, #4]", "add\tr0, sp, #4", "bl\tfunc_0802A2C0", *load,
                                     "ldr\tr3, [sp, #4]", "strb\tr3, [r4]", "add\tsp, sp, #8", "pop\t{r4}",
                                     "pop\t{r0}", "bx\tr0")
        self.refused(body("ldrb\tr2, [r4]"), body())

    def test_a_reload_into_an_address_register_is_refused(self):
        # the reloaded zero is the store's index register, not its value
        real = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr2, #0", "str\tr2, [sp, #4]",
                      "ldrb\tr3, [r1]", "ldr\tr2, [sp, #4]", "strb\tr0, [r1, r2]")
        self.refused(real)

    def test_a_reload_before_an_all_ones_store_is_refused(self):
        self.refused(window("ldr\tr3, [sp, #4]", value="mov\tr3, #255"),
                     framed("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr3, #255", "strb\tr3, [r1]"))

    def test_spill_reload_names_the_store(self):
        records = semantics.explore("func_08028C34", semantics.parse_assembly(window("ldr\tr3, [sp, #4]"))[0][
            "func_08028C34"], {}, "real", (SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1}))[0].records
        position = next(i for i, r in enumerate(records) if r.kind == "load" and r.width == 4)
        store = semantics.spill_reload(records, position)
        self.assertIsNotNone(store)
        self.assertEqual((store.kind, store.width), ("store", 4))
        # the reload must be an unsigned word load: Thumb has no signed word load, so the same record
        # marked signed stands for any load the executor might come to mark so, and reloads nothing
        signed = copy.copy(records[position])
        signed.signed = True
        self.assertIsNone(semantics.spill_reload(records[:position] + [signed] + records[position + 1:], position))


if __name__ == "__main__":
    unittest.main()
