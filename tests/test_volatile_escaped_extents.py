"""escaped-local-extents-v1: after a frame address escapes, the volatile semantic
check keeps the compiler's spill slots internal when the compile's DWARF shows
that no escaped named local reaches them."""

import contextlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import escaped_local_extents as extents
import match
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

NAME = "func_08028C34"
Local = extents.Local
FIVE = "extern void func_0802A2D0(int, int, int, int, int);\n"


def body(*lines):
    return fixtures.assembly(*lines)


def frame(*middle, size=12):
    """push {r4, lr}; a `size`-byte frame; &x (sp+0) escapes to func_0802A2C0; then middle"""
    return body("push\t{r4, lr}", f"add\tsp, sp, #-{size}", "mov\tr0, sp", "bl\tfunc_0802A2C0",
                *middle, f"add\tsp, sp, #{size}", "pop\t{r4}", "pop\t{r0}", "bx\tr0")


X = [Local("x", 0, 4, ())]


def model(label, text, locals_, objects=None):
    return extents.FrameModel(NAME, label, locals_, semantics.parse_assembly(text)[0][NAME], objects)


def check(real, stripped, real_locals=X, stripped_locals=None, preprocessed=fixtures.PREPROCESSED,
          objects=None):
    models = {("real", NAME): model("real", real, real_locals, objects),
              ("stripped", NAME): model("stripped", stripped,
                                        real_locals if stripped_locals is None else stripped_locals, objects)}
    token = semantics.FRAME_MODELS.set(models)
    try:
        return fixtures.compare(real, stripped, preprocessed), models
    finally:
        semantics.FRAME_MODELS.reset(token)


def differing(*after):
    """the same frame twice, storing 1 and 2 at sp+8 after `after`"""
    return [frame(*after, f"mov\tr1, #{value}", "str\tr1, [sp, #8]") for value in (1, 2)]


class ExecutorTests(unittest.TestCase):
    def refused(self, real, stripped, reason, **options):
        with self.assertRaises(semantics.SemanticError) as caught:
            check(real, stripped, **options)
        self.assertIn(reason, str(caught.exception))

    def test_spill_slots_outside_every_escaped_local_are_internal(self):
        real, stripped = differing()
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)          # main: every frame store is observable
        self.assertIn("differ in observable behaviour", str(caught.exception))
        results, models = check(real, stripped)
        self.assertEqual(results[0][1], 1)
        self.assertEqual(models[("real", NAME)].escaped, {X[0]})

    def test_internal_reload_crosses_calls(self):
        # a value kept in a spill slot across a call in one compile, in r4 in the other
        spilled = frame("mov\tr1, #7", "str\tr1, [sp, #8]", "mov\tr0, #0", "bl\tfunc_0802A2C0",
                        "ldr\tr0, [sp, #8]", "bl\tfunc_0802A2C0")
        kept = frame("mov\tr4, #7", "mov\tr0, #0", "bl\tfunc_0802A2C0", "mov\tr0, r4",
                     "bl\tfunc_0802A2C0")
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(spilled, kept)
        self.assertEqual(check(spilled, kept)[0][0][1], 1)
        # a different value reloaded is still a different argument
        self.refused(spilled, kept.replace("#7", "#6"), "differ in observable behaviour")

    def test_internal_slots_survive_unknown_pointers_and_later_escapes(self):
        # a store through a pointer not computed from sp cannot reach the internal slot
        def through_argument(keep):
            kept = ["mov\tr2, #7"] if keep else ["mov\tr2, #7", "str\tr2, [sp, #8]"]
            use = ["mov\tr0, #7"] if keep else ["ldr\tr0, [sp, #8]"]
            return body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr4, r1, #0", "mov\tr0, sp",
                        "bl\tfunc_0802A2C0", *kept, "mov\tr1, #9", "str\tr1, [r4]", *use,
                        "bl\tfunc_0802A2C0", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.assertEqual(check(through_argument(False), through_argument(True))[0][0][1], 1)
        # a later escape snapshots only the escaped locals, not the differing slot
        real, stripped = differing()
        again = [text.replace("\tadd\tsp, sp, #12\n", "\tmov\tr0, sp\n\tbl\tfunc_0802A2C0\n\tadd\tsp, sp, #12\n")
                 for text in (real, stripped)]
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*again)
        self.assertEqual(check(*again)[0][0][1], 1)
        # a frame address kept in an internal slot before the first escape does not escape
        def parked(value):
            return body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr1, sp, #8", "str\tr1, [sp, #4]",
                        "mov\tr1, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0", f"mov\tr1, #{value}",
                        "str\tr1, [sp, #8]", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.assertEqual(check(parked(1), parked(2))[0][0][1], 1)

    def test_stores_inside_an_escaped_local_stay_observable(self):
        real, stripped = frame("mov\tr1, #1", "str\tr1, [sp]"), frame("mov\tr1, #2", "str\tr1, [sp]")
        self.refused(real, stripped, "differ in observable behaviour")
        # a wider local reaches the slot too
        self.refused(*differing(), "differ in observable behaviour", real_locals=[Local("x", 0, 12, ())])
        # and a byte store that overlaps it
        real, stripped = frame("mov\tr1, #1", "strb\tr1, [sp, #3]"), frame("mov\tr1, #2", "strb\tr1, [sp, #3]")
        self.refused(real, stripped, "differ in observable behaviour")

    def test_escaping_address_needs_exactly_one_live_owner(self):
        real, stripped = differing()
        message = "is not inside exactly one named local in scope"
        self.refused(real, stripped, message, real_locals=[])                       # a temporary
        self.refused(real, stripped, message, real_locals=[Local("x", 4, 4, ())])   # outside x
        self.refused(real, stripped, message,                                       # two owners
                     real_locals=[Local("x", 0, 4, ()), Local("y", 0, 2, ())])
        self.refused(real, stripped, message, real_locals=[Local("x", 0, 4, ((5, 9),))])  # out of scope
        # the bl is instruction 3: a scope that covers it admits
        self.assertEqual(check(real, stripped, real_locals=[Local("x", 0, 4, ((3, 4),))])[0][0][1], 1)
        # a one-past-the-end address does not name the local before it
        past = lambda value: body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr0, sp, #4",
                                  "bl\tfunc_0802A2C0", f"mov\tr1, #{value}", "str\tr1, [sp]",
                                  "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.refused(past(1), past(2), message)
        # when it is also the start of the next one, both escape (C lets the callee read p[-1])
        self.refused(past(1), past(2), "differ in observable behaviour",
                     real_locals=[Local("x", 0, 4, ()), Local("y", 4, 4, ())])
        later = lambda value: past(value).replace("str\tr1, [sp]", "str\tr1, [sp, #8]")
        escaped = check(later(1), later(2), real_locals=[Local("x", 0, 4, ()), Local("y", 4, 4, ())])[1]
        self.assertEqual(sorted(local.name for local in escaped[("real", NAME)].escaped), ["x", "y"])

    def test_frame_addresses_stored_where_others_can_read_them_escape(self):
        locals_ = [Local("x", 0, 4, ()), Local("y", 8, 4, ())]
        # &y (sp+8) stored into x before the escape: y escapes with x
        self.refused(*[body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr1, sp, #8", "str\tr1, [sp]",
                            "mov\tr1, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0", f"mov\tr1, #{value}",
                            "str\tr1, [sp, #8]", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
                       for value in (1, 2)], "differ in observable behaviour", real_locals=locals_)
        # ... and after it
        self.refused(*differing("add\tr1, sp, #8", "str\tr1, [sp]"), "differ in observable behaviour",
                     real_locals=locals_)
        # a pointer to nothing named, stored into x, refuses
        self.refused(*differing("add\tr1, sp, #8", "str\tr1, [sp]"), "not inside exactly one named local")
        # in an unnamed argument register the ROM callee may read
        self.refused(*differing("add\tr1, sp, #8", "mov\tr0, #0", "bl\tfunc_0802A2C0"),
                     "differ in observable behaviour", real_locals=locals_)
        # in an incoming-argument word (no listed reader) before the first escape: refused
        self.refused(*[body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr1, sp, #8", "str\tr1, [sp, #24]",
                            "mov\tr1, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0", f"mov\tr1, #{value}",
                            "str\tr1, [sp, #8]", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
                       for value in (1, 1)], "a frame address is stored to a frame slot outside the named locals",
                     real_locals=locals_)
        # an internal slot may hold one: it is reloaded exactly
        self.assertEqual(check(*differing("add\tr1, sp, #4", "str\tr1, [sp, #4]"))[0][0][1], 1)

    def test_a_stored_one_past_address_escapes_the_local_before_it(self):
        # int w; int x[2]; int *z;  f(&x[1]);  z = &w + 1;  f(&z);  w = v;  f(0):
        # &w + 1 == &x[0], and f may read w through z[-1]
        def one_past(value):
            return body("push\t{r4, lr}", "add\tsp, sp, #-16", "add\tr0, sp, #8", "bl\tfunc_0802A2C0",
                        "add\tr1, sp, #4", "str\tr1, [sp, #12]", "add\tr0, sp, #12", "mov\tr1, #0",
                        "bl\tfunc_0802A2C0", f"mov\tr1, #{value}", "str\tr1, [sp]", "mov\tr0, #0",
                        "mov\tr1, #0", "bl\tfunc_0802A2C0", "add\tsp, sp, #16", "pop\t{r4}", "pop\t{r0}",
                        "bx\tr0")
        locals_ = [Local("w", 0, 4, ()), Local("x", 4, 8, ()), Local("z", 12, 4, ())]
        self.refused(one_past(1), one_past(2), "differ in observable behaviour", real_locals=locals_)
        # ... even when the local before it is out of scope there
        scoped = [Local("w", 0, 4, ((0, 1),)), Local("x", 4, 8, ()), Local("z", 12, 4, ())]
        self.refused(one_past(1), one_past(2), "differ in observable behaviour", real_locals=scoped)

    def test_frame_addresses_reach_only_ram_and_listed_consumers(self):
        # review spill4 R2: &x stored to DMA3SAD, then a 3-word DMA reads past x over the
        # internal slot; a frame address may only be stored to proven ordinary RAM
        def dma(value, pool=("0x040000d4", "data_02000000", "0x84000003")):
            text = body("push\t{r4, lr}", "add\tsp, sp, #-12", f"mov\tr1, #{value}", "str\tr1, [sp, #8]",
                        "ldr\tr2, .L3", "mov\tr0, sp", "str\tr0, [r2]", "ldr\tr0, .L3+4", "str\tr0, [r2, #4]",
                        "ldr\tr0, .L3+8", "str\tr0, [r2, #8]", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}",
                        "bx\tr0")
            return text.replace(".word\tg_control_flags_03000940\n",
                                "".join(f".word\t{word}\n" for word in pool))
        self.refused(dma(1), dma(2), "is not proven ordinary RAM")
        # an unknown pointer is not proven RAM either
        unknown = frame("mov\tr0, sp", "str\tr0, [r5]")
        self.refused(unknown, unknown, "is not proven ordinary RAM")
        # a RAM word is a premised consumer, listed with the store's instruction
        ram = lambda value: dma(value, pool=("0x03001000", "data_02000000", "0x84000003"))
        line = extents.record(check(ram(1), ram(1))[1])
        self.assertIn("premised consumers: stored to 0x3001000 at #6: x", line)
        # a data symbol is RAM only when the data symbols place it there
        named = frame("ldr\tr2, .L3", "mov\tr0, sp", "str\tr0, [r2, #4]")
        self.refused(named, named, "is not proven ordinary RAM")
        self.refused(named, named, "is not proven ordinary RAM", objects={fixtures.SYMBOL: 0x04000000})
        line = extents.record(check(named, named, objects={fixtures.SYMBOL: 0x03000940})[1])
        self.assertIn(f"premised consumers: func_0802A2C0 r0 at #3: x; stored to ({fixtures.SYMBOL} + 0x4)",
                      line)
        # callees are consumers too: listed, or proven for memcpy with a constant count
        listed = extents.record(check(*differing())[1])
        self.assertIn("premised consumers: func_0802A2C0 r0 at #3: x", listed)
        copy = lambda count: frame("add\tr0, sp, #4", "mov\tr1, #0", f"mov\tr2, #{count}", "bl\tmemcpy",
                                   "mov\tr1, #1", "str\tr1, [sp]")
        memcpy = fixtures.PREPROCESSED + "extern void *memcpy(void *, const void *, unsigned long);\n"
        locals_ = [Local("x", 0, 4, ()), Local("b", 4, 4, ())]
        proven = extents.record(check(copy(4), copy(4), real_locals=locals_, preprocessed=memcpy)[1])
        self.assertIn("proven consumers: memcpy r0 at #", proven)
        self.assertIn(": b +0x0, 4 bytes", proven)
        for count in (5, 0):                    # past b, or no count proof: premised
            self.assertIn("premised consumers: func_0802A2C0 r0 at #3: x; memcpy r0 at #",
                          extents.record(check(copy(count), copy(count), real_locals=locals_,
                                               preprocessed=memcpy)[1]))

    def test_frame_addresses_reach_hardware_by_no_other_route(self):
        def program(*lines, pool=("0x040000d4", "data_08300000", "0x84000003"), size=12):
            text = body("push\t{r4, lr}", f"add\tsp, sp, #-{size}", *lines, f"add\tsp, sp, #{size}",
                        "pop\t{r4}", "pop\t{r0}", "bx\tr0")
            return text.replace(".word\tg_control_flags_03000940\n", "".join(f".word\t{w}\n" for w in pool))
        memcpy = fixtures.PREPROCESSED + ("extern void *memcpy(void *, const void *, int);\n"
                                          "extern void func_0802A2D0(int);\n")
        # R5: memcpy returns its destination, &x, which then programs DMA3SAD
        returned = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #8]", "mov\tr0, sp",
                                         "ldr\tr1, .L3+4", "mov\tr2, #4", "bl\tmemcpy", "ldr\tr2, .L3",
                                         "str\tr0, [r2]", "ldr\tr0, .L3+8", "str\tr0, [r2, #8]")
        # (tracked: the frame-address rule, not the screen for unknown values, refuses it)
        self.refused(returned(1), returned(2), "which is not proven ordinary RAM (I/O, ROM or an unknown pointer)",
                     preprocessed=memcpy)
        # the result of any other call handed a frame address is screened the same way
        result = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #8]", "mov\tr0, sp",
                                       "bl\tfunc_0802A2F0", "ldr\tr2, .L3", "str\tr0, [r2]")
        self.refused(result(1), result(2), "a value that may be a frame address is stored to 0x40000d4",
                     preprocessed=memcpy + "extern int func_0802A2F0(int *);\n")
        # frame bytes copied after a call handed a frame address may hold one: not to I/O
        after = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #8]", "add\tr0, sp, #4",
                                      "bl\tfunc_0802A2C0", "ldr\tr0, .L3", "mov\tr1, sp", "mov\tr2, #4",
                                      "bl\tmemcpy", size=12)
        self.refused(after(1), after(2), "copies frame bytes that may hold a frame address",
                     real_locals=[Local("x", 0, 4, ()), Local("b", 4, 4, ())],
                     preprocessed=memcpy + "extern void func_0802A2C0(void *);\n")
        # R4: s.src = &y, a call, then DMA3SAD = s.src read back from the escaped s
        locals_ = [Local("s", 0, 12, ()), Local("y", 12, 4, ())]
        readback = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #16]", "mov\tr0, sp",
                                         "ldr\tr1, .L3+4", "mov\tr2, #12", "bl\tmemcpy", "add\tr1, sp, #12",
                                         "str\tr1, [sp]", "mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0",
                                         "mov\tr3, #0", "bl\tfunc_0802A2D0", "ldr\tr2, .L3", "ldr\tr0, [sp]",
                                         "str\tr0, [r2]", "ldr\tr0, [sp, #8]", "str\tr0, [r2, #8]", size=20)
        self.refused(readback(1), readback(2), "a value that may be a frame address is stored to 0x40000d4",
                     real_locals=locals_, preprocessed=memcpy)
        # R3: s holds &y, and a memcpy copies s into the DMA registers
        for call in ("memcpy", "func_0802A2C0"):
            with self.subTest(call=call):
                copied = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #16]", "add\tr1, sp, #12",
                                               "str\tr1, [sp]", "ldr\tr1, .L3+4", "str\tr1, [sp, #4]",
                                               "ldr\tr1, .L3+8", "str\tr1, [sp, #8]", "ldr\tr0, .L3",
                                               "mov\tr1, sp", "mov\tr2, #12", f"bl\t{call}", size=20,
                                               pool=("0x040000d4", "data_02000000", "0x84000002"))
                if call == "memcpy":
                    self.refused(copied(1), copied(2), "copies frame bytes that may hold a frame address",
                                 real_locals=locals_, preprocessed=memcpy + "extern void func_0802A2C0(void *);\n")
                else:                    # a premised callee: &y kept in s is listed with it
                    line = extents.record(check(copied(1), copied(1), real_locals=locals_,
                                                preprocessed=memcpy)[1])
                    self.assertIn("func_0802A2C0 r1 at #", line)
                    self.assertIn("kept in s at #", line)
                    self.assertIn(": y", line)
        # a frame copy to RAM is listed, and a copy of frame bytes with no frame address is proven
        to_ram = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #16]", "add\tr1, sp, #12",
                                       "str\tr1, [sp]", "ldr\tr0, .L3+4", "mov\tr1, sp", "mov\tr2, #12",
                                       "bl\tmemcpy", size=20, pool=("0x040000d4", "0x03001000"))
        line = extents.record(check(to_ram(1), to_ram(1), real_locals=locals_, preprocessed=memcpy)[1])
        self.assertIn("frame bytes that may hold a frame address copied by memcpy to 0x3001000", line)
        plain = lambda value: program(f"mov\tr1, #{value}", "str\tr1, [sp, #16]", "ldr\tr0, .L3",
                                      "mov\tr1, sp", "mov\tr2, #12", "bl\tmemcpy", size=20)
        line = extents.record(check(plain(1), plain(2), real_locals=locals_, preprocessed=memcpy)[1])
        self.assertIn("proven consumers: memcpy r1 at #", line)
        # without the ROM copy helper's identity no contract is used, and a source defining memcpy refuses
        unproven = extents.FrameModel(NAME, "real", locals_, semantics.parse_assembly(plain(1))[0][NAME],
                                      contracts=False)
        self.assertEqual(unproven.contracts, {})
        own = fixtures.assembly("bx\tlr", name="memcpy")
        with self.assertRaises(semantics.SemanticError) as caught:
            extents.frame_models("real", own, own)
        self.assertIn("defines its own memcpy", str(caught.exception))

    def test_frame_address_slots_and_copy_registers(self):
        preprocessed = fixtures.PREPROCESSED + FIVE + "extern void *memcpy(void *, const void *, int);\n"
        locals_ = [Local("x", 4, 4, ())]
        # &x as a stack argument word, after an escape: allowed and listed
        word = body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr0, sp, #4", "bl\tfunc_0802A2C0",
                    "add\tr1, sp, #4", "str\tr1, [sp]", "mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0",
                    "mov\tr3, #0", "bl\tfunc_0802A2D0", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        word = word.replace("\tstr\tr1, [sp]\n", "\tstr\tr1, [sp]\n", 1)
        # (the word becomes a stack argument only at the call; keep it there afterwards too)
        kept = word.replace("\tbl\tfunc_0802A2D0\n", "\tbl\tfunc_0802A2D0\n\tadd\tr1, sp, #4\n\tstr\tr1, [sp]\n")
        line = extents.record(check(kept, kept, real_locals=locals_, preprocessed=preprocessed)[1])
        self.assertIn("kept in stack word sp+0x0 at #", line)
        # ... but not in an incoming-argument word, after the escape either
        incoming = frame("add\tr1, sp, #4", "str\tr1, [sp, #24]")
        self.refused(incoming, incoming, "a frame address is stored to a frame slot outside the named locals",
                     real_locals=[Local("x", 0, 8, ())])
        # a frame address in memcpy's unnamed r3 is a premised consumer, not a contract argument
        copy = frame("add\tr0, sp, #4", "mov\tr1, #0", "mov\tr2, #4", "mov\tr3, sp", "bl\tmemcpy")
        line = extents.record(check(copy, copy, real_locals=[Local("x", 0, 4, ()), Local("b", 4, 4, ())],
                                    preprocessed=preprocessed)[1])
        self.assertIn("memcpy r3 at #", line)
        self.assertIn("proven consumers: memcpy r0 at #", line)

    def test_variable_offsets_stay_clear_of_the_saved_registers(self):
        # s = x[n & 3]; f(x): the variable read walks back over the pushes, which it cannot reach
        indexed = body("push\t{r4, lr}", "add\tsp, sp, #-12", "lsl\tr2, r4, #2", "mov\tr3, sp",
                       "add\tr3, r3, r2", "ldr\tr4, [r3]", "mov\tr3, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0",
                       "add\tr0, r4, #0", "bl\tfunc_0802A2C0", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}",
                       "bx\tr0")
        self.assertEqual(check(indexed, indexed, real_locals=[Local("x", 0, 12, ())])[0][0][1], 1)

    def test_an_escape_binds_the_order_of_variable_frame_stores(self):
        # kit #346's shape: sp+8 = 1 and a[r5] = r6 in either order, then &a[2] escapes; with
        # r5 == 2 the callee sees 1 in one order and r6 in the other
        def stores(constant_first):
            constant = ("mov\tr1, #1", "str\tr1, [sp, #8]")
            indexed = ("lsl\tr3, r5, #2", "add\tr3, sp", "str\tr6, [r3]", "mov\tr3, #0")
            return body("push\t{r4, lr}", "add\tsp, sp, #-16",
                        *(constant + indexed if constant_first else indexed + constant),
                        "mov\tr0, sp", "add\tr0, #8", "bl\tfunc_0802A2C0", "add\tsp, sp, #16", "pop\t{r4}",
                        "pop\t{r0}", "bx\tr0")
        locals_ = [Local("a", 0, 16, ())]
        self.refused(stores(True), stores(False), "differ in observable behaviour", real_locals=locals_)
        self.assertEqual(check(stores(True), stores(True), real_locals=locals_)[0][0][1], 1)

    def test_routes_past_the_screen_rest_on_the_listed_consumer(self):
        # final delta B0-B6: func_0802A2C0 gets &x (premised) and may leave &x in data_02000000;
        # the function then moves that word to DMA3SAD by various routes.  Only B0 (a word read
        # straight after the receiving call) is screened; the others are accepted with the
        # consumer listed, so they rest on premise 1 as rule 9 says
        def program(value, middle):
            text = body("push\t{r4, lr}", "add\tsp, sp, #-12", f"mov\tr1, #{value}", "str\tr1, [sp, #8]",
                        "mov\tr0, sp", "bl\tfunc_0802A2C0", *middle, "ldr\tr3, .L3", "ldr\tr0, .L3+8",
                        "str\tr0, [r3, #8]", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
            return text.replace(".word\tg_control_flags_03000940\n",
                                ".word\t0x040000d4\n.word\tdata_02000000\n.word\t0x84000003\n")
        preprocessed = fixtures.PREPROCESSED + ("extern void func_0802A2D0(int);\nextern int func_0802A2E0(void);\n"
                                                "extern void *memcpy(void *, const void *, int);\n")
        word, io = ["ldr\tr2, .L3+4"], ["ldr\tr3, .L3"]
        routes = {
            "B1": word + ["ldrh\tr0, [r2]", "ldrh\tr1, [r2, #2]", "lsl\tr1, r1, #16", "orr\tr0, r1"] + io +
                  ["str\tr0, [r3]"],
            "B1b": word + ["ldrb\tr0, [r2]", "ldrb\tr1, [r2, #1]", "lsl\tr1, r1, #8", "orr\tr0, r1",
                           "ldrb\tr1, [r2, #2]", "lsl\tr1, r1, #16", "orr\tr0, r1", "ldrb\tr1, [r2, #3]",
                           "lsl\tr1, r1, #24", "orr\tr0, r1"] + io + ["str\tr0, [r3]"],
            "B2": ["mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0", "mov\tr3, #0", "bl\tfunc_0802A2D0"] + word +
                  ["ldr\tr0, [r2]"] + io + ["str\tr0, [r3]"],
            "B3": word + ["mov\tr1, #3", "strb\tr1, [r2, #3]", "ldr\tr0, [r2]"] + io + ["str\tr0, [r3]"],
            "B4": ["bl\tfunc_0802A2E0"] + io + ["str\tr0, [r3]"],
            "B5": word + io + ["ldrh\tr0, [r2]", "strh\tr0, [r3]", "ldrh\tr0, [r2, #2]", "strh\tr0, [r3, #2]"],
            "B6": ["ldr\tr0, .L3", "ldr\tr1, .L3+4", "mov\tr2, #4", "bl\tmemcpy"],
        }
        objects = {"data_02000000": 0x02000000}
        for name, middle in routes.items():
            with self.subTest(route=name):
                line = extents.record(check(program(1, middle), program(2, middle), preprocessed=preprocessed,
                                            objects=objects)[1])
                self.assertIn("premised consumers: func_0802A2C0 r0 at #5: x", line)
                self.assertIn(extents.POLICY.premises[0], line)
        screened = word + ["ldr\tr0, [r2]"] + io + ["str\tr0, [r3]"]
        self.refused(program(1, screened), program(2, screened), "a value that may be a frame address",
                     preprocessed=preprocessed, objects=objects)

    def test_frame_contents_hidden_by_a_call_are_refused(self):
        # int x, *p[2], a; p[0] = &a; f(&x); f(0); *p[i] = 9; f(a): p[i] is read at a
        # variable offset after a call, so it would come back unknown
        def through(keep):
            kept = ["mov\tr4, #7"] if keep else ["mov\tr1, #7", "str\tr1, [sp, #12]"]
            use = ["mov\tr0, r4"] if keep else ["ldr\tr0, [sp, #12]"]
            return body("push\t{r4, lr}", "add\tsp, sp, #-16", "add\tr1, sp, #12", "str\tr1, [sp, #4]",
                        *kept, "mov\tr1, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0", "mov\tr0, #0",
                        "bl\tfunc_0802A2C0", "lsl\tr3, r5, #2", "add\tr3, sp", "ldr\tr2, [r3, #4]",
                        "mov\tr3, #0", "mov\tr1, #9", "str\tr1, [r2]", *use, "bl\tfunc_0802A2C0",
                        "add\tsp, sp, #16", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        locals_ = [Local("x", 0, 4, ()), Local("p", 4, 8, ()), Local("a", 12, 4, ())]
        self.refused(through(False), through(True), "partially overlapping stack access",
                     real_locals=locals_)
        # a frame address kept in an escaped local makes its own local escape, so reading it
        # back as an unknown value is harmless: the stores it reaches are compared
        def held(keep):
            kept = ["mov\tr4, #7"] if keep else ["mov\tr1, #7", "str\tr1, [sp, #8]"]
            use = ["mov\tr0, r4"] if keep else ["ldr\tr0, [sp, #8]"]
            return frame("add\tr1, sp, #8", "str\tr1, [sp]", *kept, "mov\tr0, #0", "bl\tfunc_0802A2C0",
                         "ldr\tr2, [sp]", "mov\tr1, #9", "str\tr1, [r2]", *use, "bl\tfunc_0802A2C0")
        self.refused(held(False), held(True), "differ in observable behaviour",
                     real_locals=[Local("x", 0, 4, ()), Local("s", 8, 4, ())])

    def test_untraced_stores_a_call_would_hide_are_refused(self):
        # review round 3, P1: an internal array a, a call, then a[i] at a variable offset
        def indexed(value):
            return frame(f"mov\tr1, #{value}", "str\tr1, [sp, #8]", "mov\tr0, #0", "mov\tr1, #0",
                         "bl\tfunc_0802A2C0", "lsl\tr3, r5, #2", "add\tr3, sp", "ldr\tr0, [r3, #8]",
                         "mov\tr3, #0", "bl\tfunc_0802A2C0", size=16)
        self.refused(indexed(1), indexed(2), "partially overlapping stack access",
                     real_locals=[Local("x", 0, 4, ()), Local("a", 8, 8, ())])
        # P2: a word load straddling an escaped short and an internal halfword, after a call
        def straddle(value):
            return body("push\t{r4, lr}", "add\tsp, sp, #-12", "mov\tr0, sp", "bl\tfunc_0802A2C0",
                        f"mov\tr1, #{value}", "strh\tr1, [sp, #2]", "mov\tr0, #0", "bl\tfunc_0802A2C0",
                        "ldr\tr0, [sp]", "bl\tfunc_0802A2C0", "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}",
                        "bx\tr0")
        self.refused(straddle(1), straddle(2), "partially overlapping stack access",
                     real_locals=[Local("s", 0, 2, ())])
        # the same reads of escaped locals alone are admitted: the call may change them
        initialised = lambda value: body("push\t{r4, lr}", "add\tsp, sp, #-12", f"mov\tr1, #{value}",
                                         "str\tr1, [sp]", "mov\tr0, sp", "bl\tfunc_0802A2C0", "ldr\tr0, [sp]",
                                         "bl\tfunc_0802A2C0", "mov\tr1, #3", "str\tr1, [sp, #8]",
                                         "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.assertEqual(check(initialised(1), initialised(1))[0][0][1], 1)

    def test_stack_argument_words_stay_observable(self):
        preprocessed = fixtures.PREPROCESSED + FIVE

        def outgoing(value):
            return body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr0, sp, #4", "bl\tfunc_0802A2C0",
                        "mov\tr1, #5", "str\tr1, [sp]", "mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0",
                        "mov\tr3, #0", "bl\tfunc_0802A2D0", f"mov\tr1, #{value}", "str\tr1, [sp]",
                        "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        locals_ = [Local("x", 4, 4, ())]
        self.refused(outgoing(1), outgoing(2), "differ in observable behaviour", real_locals=locals_,
                     preprocessed=preprocessed)
        # a second call's stack argument stored over the first one's is ordinary, even when the
        # stored value is a load (the store-time self-assignment peek must not refuse it)
        twice = body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tr0, sp, #4", "bl\tfunc_0802A2C0",
                     *[line for value in ("mov\tr1, #5", "ldr\tr1, [sp, #4]") for line in (
                         value, "str\tr1, [sp]", "mov\tr0, #0", "mov\tr1, #0", "mov\tr2, #0",
                         "mov\tr3, #0", "bl\tfunc_0802A2D0")],
                     "add\tsp, sp, #12", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        self.assertEqual(check(twice, twice, real_locals=locals_, preprocessed=preprocessed)[0][0][1], 1)
        # without the stack-argument call the same word is internal
        alone = lambda value: outgoing(value).replace("bl\tfunc_0802A2D0", "mov\tr0, #0")
        self.assertEqual(check(alone(1), alone(2), real_locals=locals_,
                               preprocessed=preprocessed)[0][0][1], 1)

    def test_internal_reload_after_a_variable_offset_store_is_refused(self):
        indexed = frame("mov\tr1, #1", "str\tr1, [sp, #8]", "lsl\tr2, r4, #2", "mov\tr3, sp",
                        "add\tr3, r3, r2", "mov\tr1, #0", "str\tr1, [r3]", "ldr\tr0, [sp, #8]",
                        "mov\tr3, #0", "bl\tfunc_0802A2C0")
        self.refused(indexed, indexed, "partially overlapping stack access")

    def test_saved_registers_incoming_words_and_below_sp_stay_observable(self):
        for slot in ("[sp, #12]", "[sp, #20]"):     # the saved r4; an incoming argument word
            with self.subTest(slot=slot):
                real = frame("mov\tr1, #1", f"str\tr1, {slot}")
                self.refused(real, real.replace("#1", "#2", 1), "differ in observable behaviour")
        # below sp no plain store is admitted at all (kit#591), even an identical one
        below = lambda value: frame("mov\tr2, sp", "sub\tr2, #4", f"mov\tr1, #{value}", "str\tr1, [r2]")
        self.refused(below(1), below(2), "a frame access below sp")
        self.refused(below(1), below(1), "a frame access below sp")

    def test_locals_must_fit_the_frame(self):
        real, stripped = differing()
        self.refused(real, stripped, "overlaps the saved registers",
                     real_locals=X + [Local("z", 10, 4, ())])
        self.refused(real, stripped, "lies below sp", real_locals=X + [Local("z", -4, 4, ())])
        # an incoming argument (above the saved registers) is a local the rule can name
        self.assertEqual(check(real, stripped, real_locals=X + [Local("a", 20, 4, ())])[0][0][1], 1)

    def test_the_stack_pointer_moves_only_in_the_prologue_and_epilogue(self):
        moved = "the stack pointer moves outside the prologue and epilogue"
        # a second decrement: the DWARF offsets are from the sp after the prologue
        twice = lambda value: body("push\t{r4, lr}", "add\tsp, sp, #-12", "add\tsp, sp, #-4",
                                   "add\tr0, sp, #4", "bl\tfunc_0802A2C0", f"mov\tr1, #{value}",
                                   "str\tr1, [sp, #8]", "add\tsp, sp, #16", "pop\t{r4}", "pop\t{r0}",
                                   "bx\tr0")
        self.refused(twice(1), twice(2), moved, real_locals=[Local("x", 0, 8, ()), Local("y", 8, 4, ())])
        # sp raised around a call (its pushes would land in the frame) or lowered around a reload
        raised = frame("mov\tr1, #1", "str\tr1, [sp, #4]", "add\tsp, sp, #8", "bl\tfunc_0802A2C0",
                       "add\tsp, sp, #-8", "ldr\tr0, [sp, #4]", "bl\tfunc_0802A2C0")
        lowered = frame("mov\tr1, #1", "str\tr1, [sp, #8]", "add\tsp, sp, #-4", "ldr\tr0, [sp, #12]",
                        "add\tsp, sp, #4", "bl\tfunc_0802A2C0")
        for shape in (raised, lowered):
            with self.subTest(shape=shape):
                self.refused(shape, shape, moved)
        # an epilogue that does more than restore, or is entered from a label
        busy = frame().replace("\tpop\t{r4}\n", "\tpop\t{r4}\n\tbl\tfunc_0802A2C0\n")
        self.refused(busy, busy, "does more than restore")
        entered = frame().replace("\tpop\t{r4}\n", ".L9:\n\tpop\t{r4}\n")
        self.refused(entered, entered, "entered from a label")
        # a function with no frame may still pop in its epilogue; a large frame uses a pool word
        leaf = body("push\t{lr}", "mov\tr0, sp", "pop\t{r0}", "bx\tr0")
        self.assertEqual(extents.frame_shape(semantics.parse_assembly(leaf)[0][NAME]), (4, 0))
        big = body("push\t{r4, lr}", "ldr\tr3, .L3", "add\tsp, sp, r3", "bx\tlr").replace(
            ".word\tg_control_flags_03000940", ".word\t-1024")
        self.assertEqual(extents.frame_shape(semantics.parse_assembly(big)[0][NAME]), (8, 1024))
        # agbcc's large-frame epilogue builds the increment with mov and lsl
        shifted = body("push\t{r4, lr}", "ldr\tr4, .L3", "add\tsp, sp, r4", "mov\tr3, #151",
                       "lsl\tr3, r3, #2", "add\tsp, sp, r3", "pop\t{r4}", "pop\t{r1}", "bx\tr1").replace(
            ".word\tg_control_flags_03000940", ".word\t-604")
        self.assertEqual(extents.frame_shape(semantics.parse_assembly(shifted)[0][NAME]), (8, 604))
        unequal = shifted.replace("#151", "#150")
        with self.assertRaises(semantics.SemanticError):
            extents.frame_shape(semantics.parse_assembly(unequal)[0][NAME])
        # an epilogue's moves restore r8-r11 only, never sp
        stacked = frame().replace("\tpop\t{r4}\n", "\tmov\tr8, r3\n\tpop\t{r4}\n")
        self.assertEqual(extents.frame_shape(semantics.parse_assembly(stacked)[0][NAME]), (8, 12))
        self.refused(frame().replace("\tpop\t{r4}\n", "\tmov\tsp, r3\n\tpop\t{r4}\n"),
                     frame(), "does more than restore")

    def test_frame_reads_before_an_escape_are_bound_not_refused(self):
        # kit#346 composed: before any escape a read the byte map cannot place (a[i & 1]) is a
        # frame-read event carrying the stores it could see, in this rule as in main; after
        # &x escapes, a spill at sp+12 that no local holds stays internal
        def program(first, spill):
            return body("push\t{r4, lr}", "add\tsp, sp, #-16", f"mov\tr1, #{first}", "str\tr1, [sp, #4]",
                        "mov\tr1, #0", "str\tr1, [sp, #8]", "mov\tr1, #1", "and\tr1, r0", "lsl\tr1, r1, #2",
                        "add\tr1, sp", "ldr\tr4, [r1, #4]", "mov\tr1, #0", "mov\tr0, sp", "bl\tfunc_0802A2C0",
                        f"mov\tr1, #{spill}", "str\tr1, [sp, #12]", "mov\tr0, r4", "bl\tfunc_0802A2C0",
                        "add\tsp, sp, #16", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        locals_ = [Local("x", 0, 4, ()), Local("a", 4, 8, ())]
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(program(1, 5), program(1, 6))     # main: the spill is observable
        self.assertIn("differ in observable behaviour", str(caught.exception))
        results, _ = check(program(1, 5), program(1, 6), real_locals=locals_)
        self.assertEqual(results[0][1], 1)
        self.assertEqual(results[0][-1], list(semantics.FRAME_READ_PREMISES))
        self.refused(program(1, 5), program(2, 5), "real frame read32", real_locals=locals_)

    def test_an_escape_carrying_the_stores_names_the_premises(self):
        # kit#346 composed: a leaf (no pushes, so no saved slot passes the store) whose a[i] = v
        # precedes the escape of &a to RAM: ordering() binds the store, and the record names the
        # frame-read premises that binding relies on
        def program(value):
            return body("add\tsp, sp, #-8", "lsl\tr3, r0, #2", "add\tr3, sp", f"mov\tr1, #{value}",
                        "str\tr1, [r3]", "ldr\tr2, .L3", "mov\tr1, sp", "str\tr1, [r2]", "add\tsp, sp, #8",
                        "bx\tlr").replace(".word\tg_control_flags_03000940\n", ".word\tdata_02000000\n")
        options = dict(real_locals=[Local("a", 0, 8, ())], objects={"data_02000000": 0x02000000})
        results, models = check(program(1), program(1), **options)
        self.assertEqual(results[0][-1], list(semantics.FRAME_READ_PREMISES))
        self.assertIn("premised consumers: stored to", extents.record(models))
        self.refused(program(1), program(2), "differ in observable behaviour", **options)

    def test_an_internal_slot_read_past_a_variable_offset_store_is_refused(self):
        # after &x escapes, a[i] = v into the internal array a, then a[1], never stored, is read:
        # an internal load must find an exact earlier store, never an overlapping traced one
        indexed = frame("lsl\tr2, r4, #2", "mov\tr3, sp", "add\tr3, r3, r2", "mov\tr1, #0", "str\tr1, [r3, #4]",
                        "ldr\tr0, [sp, #8]", "mov\tr3, #0", "bl\tfunc_0802A2C0", size=16)
        self.refused(indexed, indexed, "partially overlapping stack access",
                     real_locals=[Local("x", 0, 4, ()), Local("a", 4, 8, ())])

    def test_a_saved_slot_overwritten_by_a_plain_store_is_local(self):
        # kit#346's push area: once a store other than its push overwrites the saved r4 slot it is
        # local, so a[i] = v may reach it; the two orders of that store and a[i] = v, then a read of
        # the slot, differ (main refuses them through a frame read, and so must the frame model)
        def program(order):
            overwrite, indexed = ("mov\tr2, #1", "str\tr2, [sp, #8]"), ("lsl\tr3, r0, #2", "add\tr3, sp",
                                                                        "str\tr1, [r3]")
            return body("push\t{r4, lr}", "add\tsp, sp, #-8",
                        *(overwrite + indexed if order == "oi" else indexed + overwrite),
                        "ldr\tr0, [sp, #8]", "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r1}", "bx\tr1")
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(program("oi"), program("io"))
        self.refused(program("oi"), program("io"), "differ in observable behaviour",
                     real_locals=[Local("a", 0, 8, ())])
        self.assertEqual(check(program("oi"), program("oi"), real_locals=[Local("a", 0, 8, ())])[0][0][1], 1)

    def test_a_pushed_argument_register_is_no_saved_slot(self):
        # kit#346 (F2) makes a pushed r0-r3 data that a variable offset may reach, so the saved
        # area (saved_area, out of reach of a variable offset) may not hold one: `push {r1, r4,
        # lr}`, a[i] = v, then the r1 slot read back in either order is refused by main, and the
        # frame model must not admit it
        def body_(hoisted):
            store = ["lsl\tr3, r0, #2", "add\tr3, sp", "str\tr1, [r3]"]
            read = ["ldr\tr0, [sp, #8]"]
            return body("push\t{r1, r4, lr}", "add\tsp, sp, #-8", *(read + store if hoisted else store + read),
                        "add\tsp, sp, #8", "pop\t{r1, r4}", "pop\t{r2}", "bx\tr2")
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(body_(False), body_(True))
        self.refused(body_(False), body_(True), "the prologue pushes an argument register", real_locals=[])
        for registers in ("r0, r1, r2, r3", "r3", "r2, lr"):
            with self.subTest(registers=registers), self.assertRaises(semantics.SemanticError) as caught:
                extents.frame_shape(semantics.parse_assembly(body(f"push\t{{{registers}}}", "bx\tlr"))[0][NAME])
            self.assertIn("the prologue pushes an argument register", str(caught.exception))

    def test_frame_state_checks_the_body_sp_itself(self):
        # frame_shape already keeps sp at the body sp between prologue and epilogue; the state
        # checks it again at every call, escape and internal access (defence in depth)
        state = model("real", frame(), X).state()

        class Stub:
            pc, memory = 3, []

            def __init__(self, sp):
                self.regs = {"sp": semantics.add(semantics.SP, sp)}

            def fail(self, text, message):
                raise semantics.SemanticError(message)
        body_sp, moved = Stub(state.base), Stub(state.base + 4)
        state.escape(body_sp, [semantics.add(semantics.SP, state.base)], "")
        self.assertTrue(state.private(body_sp, semantics.add(semantics.SP, state.base + 8), 4))
        self.assertFalse(state.private(moved, semantics.add(semantics.SP, state.base + 8), 4))
        for action in (lambda: state.call(moved, 1, ""),
                       lambda: state.escape(moved, [semantics.add(semantics.SP, state.base)], "")):
            with self.assertRaises(semantics.SemanticError) as caught:
                action()
            self.assertIn("with the stack pointer away from the body's", str(caught.exception))

    def test_without_models_main_is_unchanged(self):
        real = frame("mov\tr1, #1", "str\tr1, [sp, #8]")
        self.assertIsNone(semantics.FRAME_MODELS.get())
        self.assertEqual(fixtures.compare(real, real)[0][1], 1)


def debug_info(function, locals_, frame_base=b"\x5d", blocks=(), extra=()):
    """.debug_abbrev/.debug_info text: an int and a char[5] type and `function` with
    its locals [(tag, name, type, location bytes)] and blocks [(low, high, locals)]"""
    abbreviations = {
        1: (0x11, 1, [(0x03, 0x08)]),
        2: (0x24, 0, [(0x03, 0x08), (0x0B, 0x0B)]),
        3: (0x01, 1, [(0x49, 0x13)]),
        4: (0x21, 0, [(0x2F, 0x0B)]),
        5: (0x2E, 1, [(0x03, 0x08), (0x11, 0x01), (0x12, 0x01), (0x40, 0x0A)]),
        6: (0x34, 0, [(0x03, 0x08), (0x49, 0x13), (0x02, 0x0A)]),
        7: (0x05, 0, [(0x03, 0x08), (0x49, 0x13), (0x02, 0x0A)]),
        8: (0x0B, 1, [(0x11, 0x01), (0x12, 0x01)]),
        9: (0x1D, 0, []),
        10: (0x34, 0, [(0x03, 0x08), (0x49, 0x13)]),
    }
    lines = ["\t.section\t.debug_abbrev"]
    for code, (tag, children, attributes) in abbreviations.items():
        lines += [f"\t.byte\t{code:#x}", f"\t.byte\t{tag:#x}", f"\t.byte\t{children:#x}"]
        lines += [f"\t.byte\t{name:#x}\n\t.byte\t{form:#x}" for name, form in attributes]
        lines.append("\t.byte\t0,0")
    lines.append("\t.byte\t0")
    items, size = [], 11
    # (directive, value, byte length)

    def emit(directive, value, length):
        nonlocal size
        items.append(f"\t.{directive}\t{value}")
        size += length

    def string(text):
        nonlocal size
        items.append(f'\t.ascii\t"{text}\\000"')
        size += len(text) + 1

    emit("byte", 1, 1)
    string("t.c")
    int_type = size
    emit("byte", 2, 1)
    string("int")
    emit("byte", 4, 1)
    char = size
    emit("byte", 2, 1)
    string("char")
    emit("byte", 1, 1)
    array = size
    emit("byte", 3, 1)
    emit("4byte", char, 4)
    emit("byte", 4, 1)
    emit("byte", 4, 1)                              # [0..4]
    emit("byte", 0, 1)
    types = {"int": int_type, "char5": array, "char": char}

    def local(tag, name, type_name, location):
        if location is None:
            emit("byte", 10, 1)
            string(name)
            emit("4byte", types[type_name], 4)
            return
        emit("byte", 6 if tag == "variable" else 7, 1)
        string(name)
        emit("4byte", types[type_name], 4)
        emit("byte", len(location), 1)
        for byte in location:
            emit("byte", byte, 1)

    emit("byte", 5, 1)
    string(function)
    emit("4byte", ".LFB1", 4)
    emit("4byte", ".LFE1", 4)
    emit("byte", len(frame_base), 1)
    for byte in frame_base:
        emit("byte", byte, 1)
    for entry in locals_:
        local(*entry)
    for low, high, inner in blocks:
        emit("byte", 8, 1)
        emit("4byte", low, 4)
        emit("4byte", high, 4)
        for entry in inner:
            local(*entry)
        emit("byte", 0, 1)
    for tag in extra:
        emit("byte", tag, 1)
    emit("byte", 0, 1)                              # end of the subprogram
    emit("byte", 0, 1)                              # end of the unit
    return "\n".join(lines + ["\t.section\t.debug_info", f"\t.4byte\t{size - 4:#x}", "\t.2byte\t0x2",
                              "\t.4byte\t.debug_abbrev", "\t.byte\t0x4"] + items) + "\n"


def fbreg(offset):
    return bytes([0x91, offset & 0x7F])


PLAIN = frame("mov\tr1, #1", "str\tr1, [sp, #8]")
DEBUG = PLAIN.replace("\tmov\tr0, sp\n", ".LBB2:\n\tmov\tr0, sp\n").replace(
    "\tadd\tsp, sp, #12\n", ".LBE2:\n\tadd\tsp, sp, #12\n")


class DwarfTests(unittest.TestCase):
    def models(self, plain=PLAIN, debug=DEBUG, **options):
        info = debug_info(NAME, **options)
        return extents.frame_models("real", plain, debug + info)

    def test_frame_locals_scopes_and_sizes(self):
        model = self.models(locals_=[("parameter", "a", "int", fbreg(8)), ("variable", "r", "int", b"\x54")],
                            blocks=[(".LBB2", ".LBE2", [("variable", "x", "char5", fbreg(0)),
                                                         ("variable", "gone", "int", None)])])
        locals_ = model[("real", NAME)].locals
        self.assertEqual([(l.name, l.offset, l.size, l.scope) for l in locals_],
                         [("a", 8, 4, ()), ("x", 0, 5, ((2, 6),))])

    def test_unsupported_shapes_are_refused(self):
        cases = {
            "the frame base is not sp": dict(locals_=[], frame_base=b"\x57"),
            "a local's location": dict(locals_=[("variable", "x", "int", b"\x7d\x00")]),
            "entry tag 0x1d": dict(locals_=[], extra=[9]),
            "a block's code range": dict(locals_=[], blocks=[(".LBB9", ".LBE2", [])]),
        }
        for reason, options in cases.items():
            with self.subTest(reason=reason):
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.models(**options)
                self.assertIn(reason, str(caught.exception))

    def test_code_must_be_the_checked_code(self):
        with self.assertRaises(semantics.SemanticError) as caught:
            self.models(debug=DEBUG.replace("#1", "#3", 1), locals_=[])
        self.assertIn("code differs", str(caught.exception))
        # label numbering alone may differ
        renamed = DEBUG.replace(".L3", ".L7")
        self.assertEqual(self.models(debug=renamed, locals_=[])[("real", NAME)].locals, [])

    def test_debug_compile_requires_identical_text(self):
        class Runner:
            def read_binary(self, path):
                return DEBUG.encode()
        calls = []

        def compile_object(runner, workspace, args, root, address, source, rewrite=None):
            calls.append((args.flags, rewrite))
            return b"", b"", {"text": b"\x01\x02"}
        args = match.argparse.Namespace(flags="-O2")
        with unittest.mock.patch.object(match, "compile_object", compile_object):
            self.assertEqual(match.debug_compile(Runner(), "w", args, "root", 0, "s", "decl", "real",
                                                 {"text": b"\x01\x02"}), DEBUG)
            self.assertEqual(calls[-1], ("-O2 -g", None))
            match.debug_compile(Runner(), "w", args, "root", 0, "s", "decl", "stripped", {"text": b"\x01\x02"})
            self.assertIsNotNone(calls[-1][1])
            with self.assertRaises(semantics.SemanticError) as caught:
                match.debug_compile(Runner(), "w", args, "root", 0, "s", "decl", "real", {"text": b"\x01\x03"})
        self.assertIn("code differs", str(caught.exception))

    def test_match_retries_only_outside_the_cpuset_interface_selectors(self):
        import bios_cpuset_fill_profile
        import escaped_local_extents
        import inert_spin_profile
        entry = dict(symbol=fixtures.SYMBOL, declaration=fixtures.DECLARATION)

        class Runner:
            @contextlib.contextmanager
            def workspace(self):
                yield "w"

            def read_binary(self, path):
                return b""
        refusal = semantics.SemanticError("main's reason")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "src" / "08010000.c").write_text("")
            (root / "baserom.bin").write_bytes(b"\0" * 4)
            patches = [
                unittest.mock.patch.object(match.plausibility, "allowlisted_volatile_used", return_value=[entry]),
                unittest.mock.patch.object(match, "mapping_snapshot", return_value="{}"),
                unittest.mock.patch.object(match, "report_rom_path", return_value=str(root / "baserom.bin")),
                unittest.mock.patch.object(match, "function_span", return_value=4),
                unittest.mock.patch.object(match, "data_snapshot", return_value=""),
                unittest.mock.patch.object(inert_spin_profile, "index_snapshot", return_value=""),
                unittest.mock.patch.object(bios_cpuset_fill_profile, "ConditionalVolatileInterfaces"),
                unittest.mock.patch.object(semantics, "RomInterfaces"),
                unittest.mock.patch.object(match, "compile_object", return_value=(b"", b"", {"text": b""})),
                unittest.mock.patch.object(semantics, "compare", side_effect=refusal),
                unittest.mock.patch.object(escaped_local_extents, "retry", side_effect=refusal),
            ]
            with contextlib.ExitStack() as stack:
                for patch in patches:
                    stack.enter_context(patch)
                retry = escaped_local_extents.retry
                for selector, retried in ((None, True), ("bounded-buffer-bios-fill-source-v1", False),
                                          ("bounded-buffer-bios-fill-local-source-semantics-v1", False)):
                    with self.subTest(selector=selector):
                        retry.reset_mock()
                        with self.assertRaises(semantics.SemanticError) as caught:
                            match.allowlisted_volatile_semantics(root, 0x08010000, runner=Runner(),
                                                                 owner_runtime_profile=selector)
                        self.assertIs(caught.exception, refusal)
                        self.assertEqual(retry.called, retried)

    def test_memcpy_is_proven_only_against_the_pinned_rom_helper(self):
        copy = frame("add\tr0, sp, #4", "mov\tr1, #0", "mov\tr2, #4", "bl\tmemcpy")
        info = debug_info(NAME, locals_=[("variable", "x", "int", fbreg(0)), ("variable", "b", "int", fbreg(4))])
        texts = {"real": copy, "stripped": copy}
        source = fixtures.PREPROCESSED + "extern void *memcpy(void *, const void *, unsigned long);\n"
        run = lambda: semantics._compare_compiles(copy, copy, source, fixtures.SYMBOL, fixtures.DECLARATION)
        for rom in (None, bytes(0x150000)):         # no ROM, or a ROM whose helper is not the pinned one
            _, line = extents.retry(semantics.SemanticError("main"), texts, lambda label: copy + info, run,
                                    rom=rom)
            self.assertIn("memcpy r0 at #", line)
            self.assertNotIn("proven consumers", line)

    def test_retry_keeps_the_original_refusal(self):
        refusal = semantics.SemanticError("main's reason")
        with self.assertRaises(semantics.SemanticError) as caught:
            extents.retry(refusal, {"real": PLAIN}, lambda label: "garbage", lambda: None)
        self.assertIs(caught.exception, refusal)
        extents.POLICY.enabled = False
        try:
            with self.assertRaises(semantics.SemanticError) as caught:
                extents.retry(refusal, {}, None, lambda: [("f", 1, [], [])])
            self.assertIs(caught.exception, refusal)
        finally:
            extents.POLICY.enabled = True

    def test_retry_records_the_escaped_locals_and_premises(self):
        real, stripped = frame("mov\tr1, #1", "str\tr1, [sp, #8]"), frame("mov\tr1, #2", "str\tr1, [sp, #8]")
        info = debug_info(NAME, locals_=[("variable", "x", "int", fbreg(0))])
        refusal = semantics.SemanticError("main")
        results, line = extents.retry(refusal, {"real": real, "stripped": stripped},
                                      lambda label: {"real": real, "stripped": stripped}[label] + info,
                                      lambda: fixtures.compare(real, stripped))
        self.assertEqual(results[0][1], 1)
        self.assertTrue(line.startswith("* allowlisted volatile escaped-local extents (escaped-local-extents-v1)"))
        self.assertIn("real and stripped `func_08028C34`: x@+0x0/4", line)
        for premise in extents.POLICY.premises:
            self.assertIn(premise, line)


def compile_twins(source):
    """agbcc's plain and -g compiles of a C source"""
    with tempfile.TemporaryDirectory() as directory:
        Path(directory, "t.i").write_text(source)
        outputs = {}
        for flags in ("", "-g"):
            subprocess.run([os.path.expandvars(match.DEFAULT_CC), *match.DEFAULT_FLAGS.split(),
                            *flags.split(), "t.i", "-o", f"t{flags}.s"], cwd=directory, check=True,
                           capture_output=True)
            outputs[flags] = Path(directory, f"t{flags}.s").read_text()
    return outputs[""], outputs["-g"]


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file(), "requires agbcc")
class CompilerTests(unittest.TestCase):
    def test_agbcc_dwarf_matches_the_frame(self):
        source = ("extern void f(short *, short *);\nextern int g(int);\n"
                  "int func_08000000(int a, int b)\n{\n    int r = 0;\n    if (a) {\n"
                  "        short x, y;\n        f(&x, &y);\n        r = g(x) + g(y) + b;\n    }\n"
                  "    return r;\n}\n")
        plain, debug = compile_twins(source)
        models = extents.frame_models("real", plain, debug)
        locals_ = {l.name: l for l in models[("real", "func_08000000")].locals}
        self.assertEqual(sorted(locals_), ["x", "y"])
        self.assertEqual((locals_["x"].size, locals_["y"].size), (2, 2))
        self.assertTrue(all(local.scope for local in locals_.values()))
        # the executor finds both escaping addresses (sp+0 and sp+2) inside them
        token = semantics.FRAME_MODELS.set(models)
        try:
            semantics._compare_compiles(plain, plain, source, fixtures.SYMBOL, fixtures.DECLARATION)
        finally:
            semantics.FRAME_MODELS.reset(token)
        self.assertEqual(models[("real", "func_08000000")].escaped, {locals_["x"], locals_["y"]})

    def test_a_stored_one_past_pointer_escapes_the_array_before_it(self):
        # review repro: b + 2 == &a[0]; r = b + 2 reaches f through &r, so f may write b[1]
        # through r[-1]; the closure must escape b although the stored value lies in a
        source = ("extern void func_0802A2C0(void *);\nvoid func_08000000(int v)\n{\n    int a[2];\n"
                  "    int b[2];\n    int *r;\n    r = b + 2;\n    func_0802A2C0(&a[1]);\n"
                  "    func_0802A2C0(&r);\n    b[1] = v;\n    func_0802A2C0(0);\n}\n")
        plain, debug = compile_twins(source)
        store = "\tstr\tr4, [sp, #4]\n"
        self.assertIn(store, plain)
        changed = {"real": plain, "stripped": plain.replace(store, "\tstr\tr0, [sp, #4]\n")}
        twins = {"real": debug, "stripped": debug.replace(store, "\tstr\tr0, [sp, #4]\n")}

        def run(texts=changed):
            return semantics._compare_compiles(texts["real"], texts["stripped"], source,
                                               fixtures.SYMBOL, fixtures.DECLARATION)
        refusal = semantics.SemanticError("main")
        with self.assertRaises(semantics.SemanticError) as caught:
            extents.retry(refusal, changed, twins.get, run)
        self.assertIs(caught.exception, refusal)
        # the identical pair passes, with b escaped as the local r points one past
        same = {"real": plain, "stripped": plain}
        results, line = extents.retry(refusal, same, {"real": debug, "stripped": debug}.get,
                                      lambda: run(same))
        self.assertIn("b@+0x0/8", line)

    def test_internal_array_read_after_a_call_is_refused(self):
        # review round 3, c20: a[0], a[1] internal; a call; then a[i & 1] is passed on
        source = ("extern void func_0802A2C0(void *);\nextern void func_0802A2D0(int);\n"
                  "void func_08000000(int i, int v)\n{\n    int x;\n    int a[2];\n"
                  "    func_0802A2C0(&x);\n    a[0] = v;\n    a[1] = v + 1;\n    func_0802A2D0(0);\n"
                  "    func_0802A2D0(a[i & 1]);\n}\n")
        plain, debug = compile_twins(source)
        models = extents.frame_models("real", plain, debug)
        token = semantics.FRAME_MODELS.set(models)
        try:
            with self.assertRaises(semantics.SemanticError) as caught:
                semantics._compare_compiles(plain, plain, source, fixtures.SYMBOL, fixtures.DECLARATION)
        finally:
            semantics.FRAME_MODELS.reset(token)
        self.assertIn("partially overlapping stack access", str(caught.exception))

    def test_length_taking_callee_is_a_listed_premise(self):
        # review spill4 R1: a CpuSet-shaped callee given &x and a count of 4 words reads past x
        # over named homes; the kit cannot bound it, so the report names it as a premised consumer
        source = ("typedef unsigned int u32;\nextern void func_080B0000(const void *src, void *dst, u32 control);\n"
                  "extern int func_0802A2D0(int);\nextern u32 data_02000000[4];\n"
                  "int func_08000000(int a, int b, int c, int d)\n{\n    u32 x;\n    int p, q, r, s, t, u, v, w;\n"
                  "    p = func_0802A2D0(a);\n    q = func_0802A2D0(b);\n    r = func_0802A2D0(c);\n"
                  "    s = func_0802A2D0(d);\n    t = func_0802A2D0(p);\n    u = func_0802A2D0(q);\n"
                  "    v = func_0802A2D0(r);\n    w = func_0802A2D0(s);\n    x = a;\n"
                  "    func_080B0000(&x, data_02000000, 4);\n    return p + q + r + s + t + u + v + w + x;\n}\n")
        plain, debug = compile_twins(source)
        spill, keep = "\tstr\tr0, [sp, #8]\n", "\tadd\tr7, r0, #0\n"

        def swap(text):
            self.assertTrue(text.count(spill) == 1 and text.count(keep) == 1)
            return text.replace(spill, "\x00").replace(keep, spill).replace("\x00", keep)
        texts = {"real": plain, "stripped": swap(plain)}
        twins = {"real": debug, "stripped": swap(debug)}
        results, line = extents.retry(semantics.SemanticError("main"), texts, twins.get, lambda: semantics.
                                      _compare_compiles(texts["real"], texts["stripped"], source,
                                                        fixtures.SYMBOL, fixtures.DECLARATION))
        self.assertRegex(line, r"premised consumers: func_080B0000 r0 at #\d+: x")
        self.assertIn(extents.POLICY.premises[0], line)

    def test_pointer_array_read_back_after_an_escape_is_refused(self):
        # review repro: p[i] is read at a variable offset after f(&x); the store through it
        # writes y or z, so the function returns 16 or 17, never the 15 a stripped
        # compile might fold
        source = ("extern void func_0802A2C0(int *);\nint func_08000000(int i)\n{\n"
                  "    int x, y, z;\n    int *p[2];\n    y = 7;\n    z = 8;\n    p[0] = &y;\n"
                  "    p[1] = &z;\n    func_0802A2C0(&x);\n    *p[i] = 9;\n    return y + z;\n}\n")
        plain, debug = compile_twins(source)
        reloads = "\tldr\tr0, [sp]\n\tldr\tr1, [sp, #4]\n\tadd\tr0, r0, r1\n"
        self.assertIn(reloads, plain)
        folded = {"real": plain, "stripped": plain.replace(reloads, "\tmov\tr0, #15\n")}
        twins = {"real": debug, "stripped": debug.replace(reloads, "\tmov\tr0, #15\n")}

        def run():
            return semantics._compare_compiles(folded["real"], folded["stripped"], source,
                                               fixtures.SYMBOL, fixtures.DECLARATION)
        refusal = semantics.SemanticError("main")
        with self.assertRaises(semantics.SemanticError) as caught:
            extents.retry(refusal, folded, twins.get, run)
        self.assertIs(caught.exception, refusal)

if __name__ == "__main__":
    unittest.main()
