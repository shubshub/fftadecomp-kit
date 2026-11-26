"""kit#375, rule P: one typed pointer to the allowlisted control block.

`__typeof__(symbol) *control; control = &symbol;` then `control->member` and the
whole-object transfer `copy(saved, control, sizeof)` (0812C2B8, 08125FA8) are the
same accesses as `symbol.member`: the pointer is the object's base with the
object's own type, so the permuted compile moves its members as it moves the
symbol's.  Exactly one such pointer, bound once, used only by member or as a
rule U argument, is admitted; anything else keeps the typeof and `&` refusals.
"""
from pathlib import Path
import sys
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
COPY = whole.COPY
TYPED = whole.TYPED
POINTER = "__typeof__(" + SYMBOL + ") *control;"
BIND = "control = &" + SYMBOL + ";"


def rules(body, declarations=COPY):
    return whole.rules(body, declarations)


class TextRuleTests(unittest.TestCase):
    def test_one_pointer_bound_once_and_used_by_member_or_as_a_transfer_is_admitted(self):
        for body in (POINTER + " " + BIND + " func_081443FC(b, control, 0x50); control->unknown_3C |= 1;",
                     "__typeof__(" + SYMBOL + ") *control = &" + SYMBOL + "; control->display = 2;",
                     "__typeof(" + SYMBOL + ") *control; x = 1; " + BIND + " if (control->display & 4) y();",
                     "typeof(" + SYMBOL + ") *control; " + BIND + " func_081443FC(control, b, sizeof " + SYMBOL +
                     ");"):
            with self.subTest(body=body):
                self.assertEqual(rules(body), [])

    def test_other_pointers_bindings_and_uses_are_refused(self):
        for body, declarations in (
                (POINTER + " __typeof__(" + SYMBOL + ") *other; " + BIND + " other = &" + SYMBOL + ";", COPY),
                (POINTER + " " + BIND + " " + BIND, COPY),
                (POINTER + " control->display = 1;", COPY),
                ("__typeof__(" + SYMBOL + ") *control = &" + SYMBOL + "; " + BIND, COPY),
                (POINTER + " " + BIND + " p = control + 1;", COPY),
                (POINTER + " " + BIND + " x = *control;", COPY),
                (POINTER + " " + BIND + " control[0].display = 1;", COPY),
                (POINTER + " " + BIND + " p = control;", COPY),
                (POINTER + " " + BIND + " control = 0;", COPY),
                (POINTER + " " + BIND + " return control;", COPY),
                (POINTER + " " + BIND + " func_081443FC(b, control, 0x50);", TYPED),
                (POINTER + " " + BIND + " unknown(b, control, 0x50);", COPY),
                (POINTER + " " + BIND + " func_081443FC(control, control, 0x50);", COPY),
                (POINTER + " " + BIND + " func_081443FC(control, &" + SYMBOL + ", 0x50);", COPY),
                (POINTER + " " + BIND + " p = &control->display;", COPY),
                (POINTER + " " + BIND + " x = control->unknown_02[1];", COPY),
                (POINTER + " " + BIND + " x = (control)->display;", COPY),
                ("static " + POINTER + " " + BIND, COPY),
                ("__typeof__(" + SYMBOL + ") copy; copy.display = 1;", COPY),
                ("__typeof__(" + SYMBOL + ") **control; " + BIND, COPY),
                ("x = sizeof(__typeof__(" + SYMBOL + "));", COPY)):
            with self.subTest(body=body):
                self.assertIn("volatile-allowlist", rules(body, declarations))

    def test_a_file_scope_pointer_is_refused(self):
        source = COPY + POINTER + "\nvoid f(void) { " + BIND + " control->display = 1; }\n"
        found = [rule for _, rule, _, _ in plausible.check_text(
            source, data_symbols=allowlist.MAPPING, relpath="src/08028C34.c", volatile_allow=[allowlist.ENTRY])]
        self.assertIn("volatile-allowlist", found)

    def test_sites(self):
        code = COPY + "void f(void) { " + POINTER + " " + BIND + " control->display = 1; }\n"
        admitted, typeofs, findings = plausible.typed_pointer_sites(code, SYMBOL, allowlist.ENTRY["declaration"],
                                                                    plausible.declaration_fragments(code))
        self.assertEqual(sorted(admitted.values()), ["the typed pointer's binding", "the typed pointer's type"])
        self.assertEqual(typeofs, {code.index("__typeof__")})
        self.assertEqual(findings, [])


class CensusTests(unittest.TestCase):
    MARKERS = {"volatile": "__mkaaaa", "__volatile__": "__mkbbbbbbbb", "__volatile": "__mkcccccc"}

    def test_only_the_admitted_typeof_passes(self):
        unit = "extern volatile u8 a;\nvoid f(void) { __typeof__(a) *p; }\n"
        marked = unit.replace("volatile", "__mkaaaa")
        spot = plausible.strip_comments_and_strings(unit).index("__typeof__")
        self.assertEqual(plausible.census_findings(unit, marked, self.MARKERS, frozenset({spot})), [])
        self.assertTrue(plausible.census_findings(unit, marked, self.MARKERS))
        self.assertTrue(plausible.census_findings(unit, marked, self.MARKERS, frozenset({spot + 1})))
        twice = unit.replace("}\n", "__typeof__(a) *q; }\n")
        self.assertTrue(plausible.census_findings(twice, twice.replace("volatile", "__mkaaaa"), self.MARKERS,
                                                  frozenset({spot})))
        quoted = unit.replace("}\n", 'char *s = "typeof"; }\n')
        self.assertTrue(plausible.census_findings(quoted, quoted.replace("volatile", "__mkaaaa"), self.MARKERS,
                                                  frozenset({spot})))


def preprocessed(body, declarations=COPY):
    return whole.preprocessed(body, declarations)


class SemanticTests(unittest.TestCase):
    def compare(self, real, body):
        return fixtures.compare(real, real, preprocessed(body))

    def test_the_pointer_s_transfer_and_member_store_pass(self):
        body = POINTER + " " + BIND + " func_081443FC(b, control, sizeof " + SYMBOL + "); control->display = 2;"
        real = fixtures.assembly("push\t{r4, lr}", "ldr\tr4, .L3", "mov\tr0, r5", "mov\tr1, r4", whole.SIZE,
                                 "bl\tfunc_081443FC", "mov\tr0, #2", "strh\tr0, [r4]", "pop\t{r4}", "pop\t{r0}",
                                 "bx\tr0")
        line = semantics.record(SYMBOL, self.compare(real, body))
        self.assertIn("as the void-pointer argument 2 of func_081443FC", line)

    def test_a_misused_pointer_is_refused_after_preprocessing(self):
        real = fixtures.assembly("bx\tlr")
        for body in (POINTER + " " + BIND + " p = control + 1;", POINTER + " " + BIND + " " + BIND,
                     POINTER + " __typeof__(" + SYMBOL + ") *other; " + BIND):
            with self.subTest(body=body), self.assertRaisesRegex(semantics.SemanticError, "after preprocessing"):
                self.compare(real, body)

    def test_the_pointer_escaping_to_another_call_is_refused_by_the_executor(self):
        # the text admits `control` at the void-pointer argument; the code must hand over the whole object
        body = POINTER + " " + BIND + " func_081443FC(b, control, 0x50);"
        real = fixtures.assembly("push\t{r4, lr}", "ldr\tr4, .L3", "mov\tr0, r5", "mov\tr1, r4", "mov\tr2, #2",
                                 "bl\tfunc_081443FC", "pop\t{r4}", "pop\t{r0}", "bx\tr0")
        with self.assertRaisesRegex(semantics.SemanticError, "without its size"):
            self.compare(real, body)


if __name__ == "__main__":
    unittest.main()
