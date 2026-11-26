"""Limits of the volatile check's loop induction that byte-identical sources met."""

import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_loop_induction as induction
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


# exact BIOS wrappers at 0x08000270 (svc 0x11 LZ77UnCompWram, which reads r0 and r1), 0x08000274
# (svc 0x0F ObjAffineSet, r0-r3), 0x08000278 (svc 0x30, not in the table) and 0x0800027C
# (svc 0x11 with a second instruction before the return)
WRAPPERS = ((0x08000270, [0xDF11, 0x4770]), (0x08000274, [0xDF0F, 0x4770]), (0x08000278, [0xDF30, 0x4770]),
            (0x0800027C, [0xDF11, 0x2000, 0x4770]))
BIOS_PREPROCESSED = T.PREPROCESSED + ("extern void func_08000270(const void *, void *);\n"
                                      "extern void func_08000274(const void *, void *);\n"
                                      "extern void func_08000278(const void *, void *);\n"
                                      "extern void func_0800027C(const void *, void *);\n")


def bios_call(callee, register="r2"):
    """a call in a loop, whose real and stripped compiles leave different dead values in an
    argument register the prototype does not name (the induction compares those)"""
    return FRAME + loop("mov\tr0, r6", "mov\tr1, r7", ("real", f"mov\t{register}, #5"),
                        ("stripped", f"mov\t{register}, #6"), f"bl\tfunc_{callee}", start="r5") + MEMBER + END


def after_bios(*after):
    """a read-modify-write load of the member into r3 (real compile only) that stays in r3
    across a call of the LZ77UnCompWram wrapper, which reads r0 and r1"""
    return FRAME + ("ldr\tr1, .L3", "add\tr1, r1, #@P@", ("real", "ldrb\tr3, [r1]"), "mov\tr2, #1",
                    "strb\tr2, [r1]", "mov\tr0, r6", "mov\tr1, r7", "bl\tfunc_08000270", *after,
                    "bl\tfunc_0802A2C0") + MEMBER + END


class BiosBase(T.Base):
    def interfaces(self, mode="thumb", extra=()):
        """the wrappers' ROM; mode is the index row's at 0x08000270, extra rows are added"""
        import synthetic_thumb_rom
        image, rows = synthetic_thumb_rom.image(T.CALLEES + WRAPPERS, 0x300)
        for row in rows:
            if row["rom"] == "0x08000270":
                row["mode"] = mode
        return semantics.RomInterfaces(image, rows + list(extra))

    def compare_bios(self, body, interfaces=None):
        return self.compare(body, interfaces or self.interfaces(), BIOS_PREPROCESSED)

    def refused_bios(self, body, reason, interfaces=None):
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare_bios(body, interfaces)
        self.assertIn(reason, str(caught.exception))
        return str(caught.exception)


class BiosCallTests(BiosBase):
    def test_a_register_the_bios_call_does_not_read(self):
        (result,) = self.compare_bios(bios_call("08000270"))
        text = semantics.record(T.SYMBOL, [result], perturbed=True)
        self.assertIn("BIOS calls by their GBATEK interfaces: func_08000270 SWI 0x11 LZ77UnCompWram reads "
                      f"{{r0, r1}} ({semantics.BIOS_NAME}, premise: {semantics.BIOS_PREMISE})", text)

    def test_without_the_table_the_register_is_compared(self):
        # kit main: an svc wrapper's interface is unknown, so every r0-r3 is compared
        with mock.patch.object(semantics.RomInterfaces, "bios_wrapper", lambda self, address: None):
            message = self.refused_bios(bios_call("08000270"), "differ in observable behaviour")
        self.assertNotIn("BIOS call inputs", message)

    def test_a_register_the_bios_call_reads(self):
        # ObjAffineSet reads r3; the retry still compares it, and its refusal leaves the
        # first refusal's message as it was
        body = bios_call("08000274", "r3")
        real, stripped, perturbed = T.compiles(body)
        with self.assertRaises(semantics.SemanticError) as first:
            semantics._compare_bounded(real, stripped, BIOS_PREPROCESSED, T.SYMBOL, T.DECLARATION, perturbed,
                                       self.interfaces())
        message = self.refused_bios(body, "differ in observable behaviour")
        self.assertEqual(message, str(first.exception))

    def test_the_tabled_interface(self):
        # the inputs GBATEK lists are read, and no register is asserted written
        interfaces = self.interfaces().with_bios()
        self.assertEqual(interfaces("func_08000270"), (frozenset({"r0", "r1"}), frozenset()))
        self.assertEqual(interfaces.bios_used, {0x08000270: 0x11})

    def test_a_register_the_bios_call_may_leave_alone(self):
        # r3 is overwritten after the call: the load is dead, relying on the call not
        # reading r3, and asserting nothing written
        (result,) = self.compare_bios(after_bios("mov\tr3, #0"))
        text = semantics.record(T.SYMBOL, [result], perturbed=True)
        self.assertIn("callee interfaces from ROM: func_08000270 reads {r0, r1} writes {}", text)
        # r3 is read after the call: nothing says the BIOS overwrote it, so the load is used
        self.refused_bios(after_bios("mov\tr0, r3"), "might take as an argument its prototype does not name")

    def test_an_arm_row(self):
        message = self.refused_bios(bios_call("08000270"), "differ in observable behaviour",
                                    self.interfaces("arm"))
        self.assertNotIn("BIOS calls", message)

    def test_two_rows_at_the_wrapper(self):
        self.refused_bios(bios_call("08000270"), "differ in observable behaviour",
                          self.interfaces(extra=[{"rom": "0x08000270", "mode": "thumb"}]))

    def test_a_call_outside_the_table(self):
        message = self.refused_bios(bios_call("08000278"), "differ in observable behaviour")
        self.assertNotIn("BIOS call inputs", message)

    def test_not_an_exact_wrapper(self):
        message = self.refused_bios(bios_call("0800027C"), "differ in observable behaviour")
        self.assertNotIn("BIOS call inputs", message)

    def test_records_without_a_bios_call_keep_their_text(self):
        # a check that passes without the table never consults it
        (result,) = self.compare_bios(FRAME + loop("mov\tr0, r6", "mov\tr1, r7", "mov\tr2, #5",
                                                   "bl\tfunc_08000270", start="r5") + MEMBER + END)
        self.assertNotIn("BIOS calls", semantics.record(T.SYMBOL, [result], perturbed=True))

    def test_the_table_is_gbatek(self):
        self.assertEqual({n: reads for n, (_, reads) in semantics.BIOS_CALLS.items()}, {
            0x06: ("r0", "r1"), 0x08: ("r0",), 0x0A: ("r0", "r1"), 0x0B: ("r0", "r1", "r2"),
            0x0C: ("r0", "r1", "r2"), 0x0E: ("r0", "r1", "r2"), 0x0F: ("r0", "r1", "r2", "r3"),
            0x11: ("r0", "r1"), 0x12: ("r0", "r1"), 0x2A: ("r0",)})


class BiosCallMutantTests(BiosBase):
    def test_with_objaffineset_reading_two_registers(self):
        with mock.patch.dict(semantics.BIOS_CALLS, {0x0F: ("ObjAffineSet", ("r0", "r1"))}):
            (result,) = self.compare_bios(bios_call("08000274", "r3"))
        self.assertEqual(result[0], "func_08028C34")

    def test_without_the_exact_wrapper_check(self):
        original = semantics.RomInterfaces.bios_wrapper

        def loose(self, address):
            return original(self, address) or (0x11 if address == 0x0800027C else None)
        with mock.patch.object(semantics.RomInterfaces, "bios_wrapper", loose):
            (result,) = self.compare_bios(bios_call("0800027C"))
        self.assertEqual(result[0], "func_08028C34")


def through(*body, offset=4):
    """r5 holds the fixed frame address sp+offset; the loop's body stores through it"""
    return FRAME + ("add\tsp, sp, #-8", f"add\tr5, sp, #{offset}") + loop(*body, start="r6") + \
        ("ldrb\tr0, [sp, #4]", "bl\tfunc_0802A2C0") + MEMBER + ("add\tsp, sp, #8",) + END


class RegisterSlotTests(T.Base):
    def test_a_fixed_frame_slot_stored_through_a_register(self):
        body = through("strb\tr4, [r5]")
        self.bounded(body)
        (result,) = self.compare(body)
        self.assertEqual(result[-1], (5,))

    def test_the_compiles_still_compare_the_slot(self):
        self.refused(through(("real", "strb\tr4, [r5]"), ("stripped", "strb\tr7, [r5]")),
                     "back edge 1: ('slot', -24, 1) differs from the real compile's ('slot', -24, 1)")

    def test_a_variable_frame_offset(self):
        # a walk over the frame: the register holds a different address each time round
        self.refused(through("strb\tr4, [r5]", "add\tr5, r5, #1"), "r5 does not keep its value around the loop")

    def test_a_pushed_register(self):
        # sp+12 after `sub sp, #8` is the pushed r5
        self.refused(through("strb\tr4, [r5]", offset=12), "a frame store in a loop outside the slots")


class RegisterSlotMutantTests(T.Base):
    def test_with_the_switch_off(self):
        with mock.patch.object(induction.POLICY, "register_slots", False):
            self.refused(through("strb\tr4, [r5]"), "a frame store in a loop outside the slots")

    def test_without_the_marking(self):
        with mock.patch.object(induction.InductionExecutor, "mark_slots", lambda *args: None):
            self.refused(through("strb\tr4, [r5]"), "a frame store in a loop outside the slots")

    def test_with_the_push_area(self):
        # defence in depth: a slot marked over a pushed register still refuses, at the
        # partial overlap with the push (a byte) or at the return (a word)
        with mock.patch.object(induction.InductionExecutor, "in_push_area", lambda *args: False):
            self.refused(through("strb\tr4, [r5]", offset=12), "partially overlapping stack access")
            self.refused(through("str\tr4, [r5]", offset=12), "r5 does not hold its entry value at the return")


if __name__ == "__main__":
    unittest.main()
