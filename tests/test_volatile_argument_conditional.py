"""An outer conditional operator in an argument list is one argument, not a refusal."""

import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_semantics as semantics


class ConditionalArgumentTests(unittest.TestCase):
    def test_a_conditional_operand_ends_at_the_next_outer_comma(self):
        for text, parts in (
                ("b > a ? a : b, 0, 2, owner", ["b > a ? a : b", "0", "2", "owner"]),
                ("x, y ? 1 : 2", ["x", "y ? 1 : 2"]),
                # the middle operand is an expression: its comma separates nothing
                ("x ? 1, 2 : 3, y", ["x ? 1, 2 : 3", "y"]),
                ("a ? b ? c : d : e, f", ["a ? b ? c : d : e", "f"]),
                ("a ? b : c ? d : e, f", ["a ? b : c ? d : e", "f"]),
                ("(a ? b, c : d), e", ["(a ? b, c : d)", "e"]),
                ("f(a ? b : c, d), e", ["f(a ? b : c, d)", "e"])):
            with self.subTest(text=text):
                self.assertEqual(semantics.parameter_parts(text), parts)

    def test_what_cannot_be_read_still_refuses(self):
        for text in ("a ? b, c", "a ? b : c :", "a ? b : , c", "? b : c", "a : b", "c ? ',' : d, e",
                     'c ? "," : d, e',
                     # a conditional cut by a bracket: its `?` and `:` must pair at one level
                     "(a ? b) : c", "a ? (b : c)", "a ? b : c : d", "a ? [b : c]", "{a ? b} : c"):
            with self.subTest(text=text), self.assertRaises(semantics.SemanticError):
                semantics.parameter_parts(text)
        # a quote beside a conditional that parentheses close is read as before
        self.assertEqual(semantics.parameter_parts("(c ? 1 : 2), 'x'"), ["(c ? 1 : 2)", "'x'"])
        # GNU C's omitted middle operand
        self.assertEqual(semantics.parameter_parts("a ?: b, c"), ["a ?: b", "c"])

    def test_literal_operands_are_read_on_the_checks_path(self):
        # translation_unit blanks every literal, so the quote refusal never fires there and
        # a literal holding `?`, `:` or a comma does not change the count
        for call, count in (("g(a ? 'x' : ',', b);", 2), ('g(a ? "?" : ":", b, c);', 3),
                            ("g(a ? ',' : 'y');", 1), ("g(a ? 'a' : (b ? ':' : 'c'), d);", 2)):
            with self.subTest(call=call):
                code = semantics.translation_unit("void f(int a, int b, int c, int d) { " + call + " }")
                self.assertNotIn("'", code)
                self.assertNotIn('"', code)
                self.assertIsNone(semantics.call_uses(code, "g", None, count))
                self.assertEqual(semantics.call_uses(code, "g", None, count + 1),
                                 f"a call through {{name}} passes {count} arguments to its "
                                 f"{count + 1}-argument prototype")

    def test_a_call_with_a_conditional_argument_is_counted(self):
        code = "void f(int a, int b, int o) { func_080D993C(b > a ? a : b, 0, 2, o); }"
        self.assertIsNone(semantics.call_uses(code, "func_080D993C", None, 4))
        self.assertEqual(semantics.call_uses(code, "func_080D993C", None, 5),
                         "a call through {name} passes 4 arguments to its 5-argument prototype")


if __name__ == "__main__":
    unittest.main()
