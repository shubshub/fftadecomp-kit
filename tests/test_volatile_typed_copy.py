"""kit#375, rule T: one typed copy of the allowlisted control block in a struct member.

`state->control = symbol;` with a `__typeof__(symbol) control;` member compiles to
the compiler's memcpy (08125A5C), and the copy is later read by member
(`symbol.display = state->control.display`).  Under the copy80 route, which binds
that memcpy to func_081443FC, the save is a rule U transfer; the destination is a
typed copy whose pinned members must follow the permuted compile as the object's
do, read only, at constant offsets, never escaping; the report prints the premise
that no other function reads it.
"""
from pathlib import Path
import sys
import types
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import plausible
import volatile_semantics as semantics
import test_volatile_semantics as fixtures
import test_plausible_volatile_allowlist as allowlist
import test_volatile_whole_object as whole

SYMBOL = fixtures.SYMBOL
STATE = ("typedef struct { unsigned char unknown_00[0x64]; __typeof__(" + SYMBOL + ") control; } State;\n"
         "extern State *state;\n")
SAVE = "state->control = " + SYMBOL + ";"
BINDING = {"helper": 0x081443FC, "site": 0x08028C40, "selector": "named-data-buffer-compiler-copy80-binding-v1"}


def rules(body, declarations=STATE):
    return whole.rules(body, declarations)


class TextRuleTests(unittest.TestCase):
    def test_the_save_restore_and_member_reads_are_admitted(self):
        for body in (SAVE + " x = state->control.unknown_3C;",
                     SYMBOL + " = state->control;",
                     SAVE + " if (state->control.display & 4) y(); " + SYMBOL + ".display = state->control.display;"):
            with self.subTest(body=body):
                self.assertEqual(rules(body), [])

    def test_every_other_use_is_refused(self):
        for body, declarations in (
                (SAVE + " state->control.display = 1;", STATE),
                (SAVE + " state->control.display++;", STATE),
                (SAVE + " p = &state->control;", STATE),
                (SAVE + " p = &state->control.display;", STATE),
                (SAVE + " x = state->control.unknown_02[1];", STATE),
                (SAVE + " other = state->control;", STATE),
                ("x = (state->control = " + SYMBOL + ");", STATE),
                (SAVE + " f(state->control);", STATE),
                (SAVE + " control = 1;", STATE),
                (SAVE, STATE.replace("typedef struct {", "typedef union {")),
                (SAVE, STATE.replace("control; }", "control; __typeof__(" + SYMBOL + ") other; }")),
                ("__typeof__(" + SYMBOL + ") copy; copy = " + SYMBOL + ";", whole.COPY),
                (SAVE, STATE.replace("__typeof__(" + SYMBOL + ") control;",
                                     "const __typeof__(" + SYMBOL + ") control;"))):
            with self.subTest(body=body, declarations=declarations[:40]):
                self.assertIn("volatile-allowlist", rules(body, declarations))

    def test_sites(self):
        code = STATE + "void f(void) { " + SAVE + " x = state->control.unknown_3C; }\n"
        admitted, typeofs, findings = plausible.typed_copy_sites(code, SYMBOL, allowlist.ENTRY["declaration"])
        self.assertEqual(sorted(admitted.values()), ["the typed copy's save", "the typed copy's type"])
        self.assertEqual(typeofs, {code.index("__typeof__")})
        self.assertEqual(findings, [])

    def test_the_census_admits_the_copy_s_typeof_only(self):
        markers = {"volatile": "__mkaaaa", "__volatile__": "__mkbbbbbbbb", "__volatile": "__mkcccccc"}
        unit = "extern volatile u8 a;\ntypedef struct { __typeof__(a) c; } S;\n"
        spot = plausible.strip_comments_and_strings(unit).index("__typeof__")
        marked = unit.replace("volatile", "__mkaaaa")
        self.assertEqual(plausible.census_findings(unit, marked, markers, frozenset({spot})), [])
        self.assertTrue(plausible.census_findings(unit, marked, markers))


PREPROCESSED = ("typedef unsigned char u8;\ntypedef unsigned short u16;\nextern void func_0802A2C0(void *);\n" +
                fixtures.DECLARATION + "\n" +
                STATE.replace("extern State *state;\n", "") +
                "int func_08028C34(State *state) { " + SAVE + " return state->control.unknown_3C; }\n")


def body(*after, read="ldrb\tr0, [r4, #160]", save=True):
    """`state->control = symbol; return state->control.unknown_3C;` (the copy at state + 0x64)"""
    copy = ("mov\tr0, r4", "add\tr0, r0, #100", "ldr\tr1, .L3", "mov\tr2, #62", "bl\tmemcpy") if save else ()
    return fixtures.assembly("push\t{r4, lr}", "mov\tr4, r0", *copy, *after, read, "pop\t{r4}", "pop\t{r1}",
                             "bx\tr1")


class SemanticTests(unittest.TestCase):
    def compare(self, real, perturbed=None, binding=BINDING, stripped=None):
        token = semantics.COMPILER_COPY.set(binding)
        try:
            return semantics._compare_compiles(real, real if stripped is None else stripped, PREPROCESSED, SYMBOL,
                                               fixtures.DECLARATION,
                                               body(read="ldrb\tr0, [r4, #161]") if perturbed is None else perturbed)
        finally:
            semantics.COMPILER_COPY.reset(token)

    def refused(self, real, reason, **options):
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(real, **options)
        self.assertIn(reason, str(caught.exception))

    def test_a_copy_read_that_follows_its_member_passes_with_its_premise(self):
        self.assertEqual(semantics.perturbed_declaration(fixtures.DECLARATION)[1], {0x3C: 0x3D, 0x3D: 0x3C})
        line = semantics.record(SYMBOL, self.compare(body()), perturbed=True)
        self.assertIn("typed copies (kit#375): `" + SYMBOL + "` saved to ", line)
        self.assertIn("by the compiler's memcpy at instruction 7, bound to func_081443FC by "
                      "named-data-buffer-compiler-copy80-binding-v1; premise: the copy at", line)
        self.assertIn("is read only by member, through this function's typed declaration", line)

    def test_a_read_at_a_fixed_offset_does_not_follow(self):
        self.refused(body(), "does not follow its member", perturbed=body())

    def test_memcpy_stays_untyped_without_the_binding(self):
        self.refused(body(), "no prototype", binding=None)

    def test_the_copy_is_read_only_at_constant_offsets_by_member(self):
        self.refused(body("strb\tr2, [r4, #161]"), "writes the typed copy",
                     perturbed=body("strb\tr2, [r4, #160]", read="ldrb\tr0, [r4, #161]"))
        self.refused(body(read="ldrh\tr0, [r4, r1]"), "variable offset", perturbed=body(read="ldrh\tr0, [r4, r1]"))
        self.refused(body(read="ldrh\tr0, [r4, #160]"), "other than as one pinned member",
                     perturbed=body(read="ldrh\tr0, [r4, #160]"))

    def test_the_copy_s_address_does_not_escape(self):
        escape = ("mov\tr0, r4", "add\tr0, r0, #101", "bl\tfunc_0802A2C0")
        self.refused(body(*escape), "escapes", perturbed=body(*escape, read="ldrb\tr0, [r4, #161]"))

    def test_one_destination_per_function(self):
        record = types.SimpleNamespace
        paths = [types.SimpleNamespace(records=[record(kind="call", address=None, copy_destination=destination)],
                                       trace=[]) for destination in (("arg", "r0"), ("arg", "r1"))]
        with self.assertRaisesRegex(semantics.SemanticError, "more than one destination"):
            semantics.typed_copy("func_08028C34", paths, SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1})
        self.assertIsNone(semantics.typed_copy("func_08028C34", paths[:0], SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1}))


if __name__ == "__main__":
    unittest.main()
