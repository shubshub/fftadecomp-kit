"""kit#375, rule U: the allowlisted object's whole-object arguments.

`sizeof symbol` and `&symbol`, cast or not to a void pointer, as one complete
argument at a `void *` / `const void *` parameter of a prototyped callee (or of
a typed function-pointer table element) are the only whole-object uses
admitted, in plausible.py and on the preprocessed text; Executor.call admits
only the object's exact address in that argument register, and the callee's
result may not become an address, a stored value, an argument or the return
value.
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

SYMBOL = fixtures.SYMBOL
COPY = "extern void *func_081443FC(void *destination, const void *source, unsigned int size);\n"
TYPED = "extern void func_081443FC(void *destination, const unsigned char *source, unsigned int size);\n"
TABLE = ("typedef void (*Fill)(void *destination, unsigned int size);\n"
         "extern Fill const g_callbacks_0836D4B8[];\n")


def rules(body, declarations=COPY):
    """plausible.py's findings for a user of the allowlisted object"""
    return [rule for _, rule, _, _ in plausible.check_text(
        declarations + "void f(void) { " + body + " }\n", data_symbols=allowlist.MAPPING,
        relpath="src/08028C34.c", volatile_allow=[allowlist.ENTRY])]


def preprocessed(body, declarations=COPY):
    return ("void func_08028C34(void);\n" + declarations + fixtures.DECLARATION +
            "\nvoid func_08028C34(void) { " + body + " }\n")


# the fixture declaration's size, 0x3E bytes
SIZE = "mov\tr2, #62"


def copy_call(*before, source="ldr\tr1, .L3", destination="mov\tr0, r4", after=(), count=SIZE):
    """`func_081443FC(r4, <source>, sizeof sym)` with the object's literal word"""
    return fixtures.assembly("push\t{r4, lr}", *before, destination, source, count,
                             "bl\tfunc_081443FC", *after, "pop\t{r4}", "pop\t{r0}", "bx\tr0")


def restore_call(count=SIZE):
    """`func_081443FC(&sym, r4, sizeof sym)`: the copy back into the object"""
    return fixtures.assembly("push\t{r4, lr}", "ldr\tr0, .L3", "mov\tr1, r4", count, "bl\tfunc_081443FC",
                             "pop\t{r4}", "pop\t{r0}", "bx\tr0")


class TextRuleTests(unittest.TestCase):
    def test_complete_void_pointer_arguments_and_sizeof_are_admitted(self):
        for body, declarations in (
                ("func_081443FC(buffer, &" + SYMBOL + ", 0x50);", COPY),
                ("func_081443FC(buffer, (const void *)&" + SYMBOL + ", sizeof " + SYMBOL + ");", COPY),
                ("func_081443FC(&" + SYMBOL + ", buffer, sizeof(" + SYMBOL + "));", COPY),
                ("g_callbacks_0836D4B8[0](&" + SYMBOL + ", sizeof(" + SYMBOL + "));", TABLE),
                ("n = sizeof " + SYMBOL + ";", COPY)):
            with self.subTest(body=body):
                self.assertEqual(rules(body, declarations), [])

    def test_every_other_address_or_whole_object_use_is_refused(self):
        for body, declarations in (
                ("func_081443FC(buffer, &" + SYMBOL + " + 4, 0x50);", COPY),
                ("func_081443FC(buffer, (u8 *)&" + SYMBOL + " + 4, 0x50);", COPY),
                ("func_081443FC(buffer, &" + SYMBOL + ".display, 0x50);", COPY),
                ("func_081443FC(buffer, &" + SYMBOL + ", 0x50);", TYPED),
                ("unknown(buffer, &" + SYMBOL + ", 0x50);", COPY),
                ("func_081443FC(&" + SYMBOL + ", &" + SYMBOL + ", 0x50);", COPY),
                ("func_081443FC(buffer, (&" + SYMBOL + "), 0x50);", COPY),
                ("func_081443FC(buffer, c ? &" + SYMBOL + " : 0, 0x50);", COPY),
                ("p = &" + SYMBOL + ";", COPY),
                ("p = (const void *)&" + SYMBOL + "; func_081443FC(buffer, p, 0x50);", COPY),
                ("copy = " + SYMBOL + ";", COPY),
                ("x = __alignof__(" + SYMBOL + ");", COPY),
                ("g_callbacks_0836D4B8[n](&" + SYMBOL + ", 0x50);", TABLE),
                ("s.callback(&" + SYMBOL + ", 0x50);", "struct S { void (*callback)(void *, unsigned int); } s;\n")):
            with self.subTest(body=body):
                self.assertIn("volatile-allowlist", rules(body, declarations))

    def test_the_prototypes_must_agree_and_be_plain(self):
        for declarations in (COPY + TYPED, COPY.replace("void *destination", "void *destination, ..."),
                             "extern void *(*func_081443FC)(void *, const void *, unsigned int);\n",
                             "typedef void *func_081443FC(void *, const void *, unsigned int);\n"):
            with self.subTest(declarations=declarations):
                self.assertIn("volatile-allowlist",
                              rules("func_081443FC(buffer, &" + SYMBOL + ", 0x50);", declarations))

    def test_a_table_typedef_must_be_unique(self):
        twice = TABLE + "typedef void (*Fill)(const unsigned char *destination, unsigned int size);\n"
        self.assertIn("volatile-allowlist",
                      rules("g_callbacks_0836D4B8[0](&" + SYMBOL + ", sizeof(" + SYMBOL + "));", twice))
        direct = "extern void (*g_callbacks_0836D4B8[])(void *destination, unsigned int size);\n"
        self.assertEqual(rules("g_callbacks_0836D4B8[0](&" + SYMBOL + ", sizeof(" + SYMBOL + "));", direct), [])

    def test_sites_name_the_argument(self):
        code = COPY + "void f(void) { func_081443FC(b, &" + SYMBOL + ", sizeof " + SYMBOL + "); }\n"
        sites = plausible.whole_object_sites(code, SYMBOL, plausible.declaration_fragments(code))
        self.assertEqual(sorted(sites.values()), ["sizeof", "the void-pointer argument 2 of func_081443FC"])


class ExecutorTests(unittest.TestCase):
    def compare(self, real, stripped=None, body="func_081443FC(b, &" + SYMBOL + ", 0x50);", declarations=COPY):
        return fixtures.compare(real, real if stripped is None else stripped, preprocessed(body, declarations))

    def refused(self, real, reason, **options):
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(real, **options)
        self.assertIn(reason, str(caught.exception))

    def test_the_exact_address_at_a_void_pointer_parameter_is_admitted_and_recorded(self):
        results = self.compare(copy_call())
        self.assertEqual(results[0][1], 1)
        line = semantics.record(SYMBOL, results)
        self.assertIn("whole-object arguments (kit#375): `&" + SYMBOL + "` (+0x0) as the void-pointer argument 2 "
                      "of func_081443FC at instruction 5, with the object's size 0x3e in argument 3; what the "
                      "callee does with them is not checked", line)
        # and only where the rule is used: an ordinary report keeps its text
        plain = fixtures.compare(fixtures.assembly("bx\tlr"), fixtures.assembly("bx\tlr"))
        self.assertNotIn("whole-object", semantics.record(SYMBOL, plain))

    def test_a_typed_table_element_is_admitted(self):
        table = fixtures.assembly(
            "push\t{r4, lr}", "ldr\tr0, .L3", "mov\tr1, #62", "ldr\tr2, .L5", "ldr\tr2, [r2]",
            "bl\t_call_via_r2", "pop\t{r4}", "pop\t{r0}", "bx\tr0").replace(
            ".L3:\n\t.word\t" + SYMBOL + "\n", ".L3:\n\t.word\t" + SYMBOL + "\n.L5:\n\t.word\tg_callbacks_0836D4B8\n")
        results = self.compare(table, body="g_callbacks_0836D4B8[0](&" + SYMBOL + ", sizeof " + SYMBOL + ");",
                               declarations=TABLE)
        self.assertIn("(+0x0) as the void-pointer argument 1 of g_callbacks_0836D4B8[0] at instruction 6, with the "
                      "object's size 0x3e in argument 2",
                      semantics.record(SYMBOL, results))

    def test_both_directions_are_admitted(self):
        # #375 item 1: a copy back into the object takes the same rule
        body = "func_081443FC(&" + SYMBOL + ", b, sizeof " + SYMBOL + ");"
        line = semantics.record(SYMBOL, self.compare(restore_call(), body=body))
        self.assertIn("(+0x0) as the void-pointer argument 1 of func_081443FC at instruction 5, with the object's "
                      "size 0x3e in argument 3", line)

    def test_the_count_must_be_the_object_s_size(self):
        # a partial or unknown count could hand the callee a part of the object only
        for count in ("mov\tr2, #61", "mov\tr2, #80", "mov\tr2, r4"):
            with self.subTest(count=count):
                self.refused(copy_call(count=count), "without its size")
                self.refused(restore_call(count=count), "without its size",
                             body="func_081443FC(&" + SYMBOL + ", b, sizeof " + SYMBOL + ");")

    def test_an_offset_another_parameter_type_or_two_arguments_are_refused(self):
        # the text admits `&symbol`; the code must pass exactly the object's address
        self.refused(copy_call(source="ldr\tr1, .L3\n\tadd\tr1, r1, #4"), "is passed to a call")
        self.refused(copy_call(destination="ldr\tr0, .L3"), "is passed to a call")
        # a typed parameter: the text refuses first, and the executor on its own
        self.refused(copy_call(), "after preprocessing", declarations=TYPED)
        self.refused(copy_call(), "is passed to a call", declarations=TYPED, body="func_081443FC(b, s, 0x50);")

    def test_the_callees_result_may_not_reach_memory_or_escape(self):
        for after, reason in ((("ldrb\tr3, [r0]",), "used as an address"),
                              (("str\tr0, [r4]",), "stored to memory"),
                              (("bl\tfunc_081443FC",), "passed to a call")):
            with self.subTest(after=after):
                self.refused(copy_call(after=after), reason)

    def test_a_text_use_the_rule_does_not_admit_is_refused_after_preprocessing(self):
        self.refused(copy_call(), "after preprocessing", body="p = &" + SYMBOL + "; func_081443FC(b, p, 0x50);")
        self.refused(copy_call(), "after preprocessing", body="func_081443FC(b, &" + SYMBOL + " + 4, 0x50);")


if __name__ == "__main__":
    unittest.main()
