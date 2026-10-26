import sys
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible


class StatementMacroTests(unittest.TestCase):
    @staticmethod
    def findings(source):
        return plausible.check_text(source)

    def test_function_statement_macro(self):
        source = "#define UPDATE(x) do { \\\n    (x) += 1; \\\n} while (0)\n"
        self.assertEqual(self.findings(source), [])

    def test_object_statement_macro(self):
        self.assertEqual(self.findings("#define UPDATE do { update(); } while (0)\n"), [])

    def test_nested_blocks_comments_and_literals(self):
        source = '''#define UPDATE(x) do { \\
    if (x) { emit("} while (0)"); } /* } */ \\
    (x) += 1; \\
} /* boundary */ while (0)
'''
        self.assertEqual(self.findings(source), [])

    def test_macro_ending_is_not_a_general_dead_code_exemption(self):
        source = "#define UPDATE(x) do { (x) += 1; } while (0)\nwhile (0) update();\n"
        findings = self.findings(source)
        self.assertEqual([(line, rule) for line, rule, _, _ in findings], [(2, "dead-code")])

    def test_dead_code_inside_wrapper(self):
        for body in ("if (0) update();", "while (0) update();", "if (0) { update(); }"):
            with self.subTest(body=body):
                findings = self.findings(f"#define UPDATE do {{ {body} }} while (0)\n")
                self.assertEqual([rule for _, rule, _, _ in findings], ["dead-code"])

    def test_preprocessor_dead_code_inside_wrapper(self):
        source = "#define UPDATE do { \\\n#if 0 \\\nupdate(); \\\n#endif \\\n} while (0)\n"
        self.assertIn("dead-code", [rule for _, rule, _, _ in self.findings(source)])

    def test_standalone_constant_conditions_remain_rejected(self):
        for source in ("while (0) update();", "if (0) update();", "#if 0\nupdate();\n#endif\n"):
            with self.subTest(source=source):
                self.assertIn("dead-code", [rule for _, rule, _, _ in self.findings(source)])

    def test_nonmacro_do_wrapper_is_not_exempt(self):
        findings = self.findings("void update(void) { do { step(); } while (0); }\n")
        self.assertIn("dead-code", [rule for _, rule, _, _ in findings])

    def test_other_banned_constructs_inside_wrapper(self):
        for body, expected in (("asm(\"nop\");", "inline-asm"),
                               ("volatile int value;", "volatile"),
                               ("int value __attribute__((used));", "attribute-steering"),
                               ("_Pragma(\"GCC optimize(0)\")", "stringised-pragma")):
            with self.subTest(body=body):
                rules = [rule for _, rule, _, _ in self.findings(
                    f"#define UPDATE do {{ {body} }} while (0)\n")]
                self.assertIn(expected, rules)

    def test_line_splices_cannot_hide_forbidden_body_constructs(self):
        for body in ("if \\\n(0) update();", "whi\\\nle (0) update();", "as\\\nm(\"nop\");", "vola\\\ntile int value;"):
            with self.subTest(body=body):
                self.assertTrue(self.findings(f"#define UPDATE do {{ {body} }} while (0)\n"))

    def test_malformed_or_partial_wrappers_are_not_exempt(self):
        for replacement in ("{ update(); } while (0)",
                            "do { update(); while (0)",
                            "do { update(); } while (0); while (0)",
                            "if (ready) do { update(); } while (0)",
                            "do { } while (0)"):
            with self.subTest(replacement=replacement):
                rules = [rule for _, rule, _, _ in self.findings(f"#define UPDATE {replacement}\n")]
                self.assertIn("dead-code", rules)

    def test_comments_cannot_forge_macro_boundaries(self):
        source = "/* #define UPDATE do { */\nwhile (0) update();\n/* } while (0) */\n"
        findings = self.findings(source)
        self.assertEqual([(line, rule) for line, rule, _, _ in findings], [(2, "dead-code")])

    def test_crlf_and_multiple_definitions(self):
        source = ("#define FIRST(x) do { \\\r\n(x)++; \\\r\n} while (0)\r\n"
                  "#define SECOND do { update(); } while (0)\r\n")
        self.assertEqual(self.findings(source), [])


if __name__ == "__main__":
    unittest.main()
