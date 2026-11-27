"""plausible.py numbers a finding by the line it is on in the file, after block comments that span lines too.

strip_comments_and_strings blanks a block comment's newlines with the rest of it (cpp reads the comment as one
space, so a directive goes on past it), so a line counted in the stripped code drifts one line low for every
newline a comment holds; justified() then looks for `plausible:` on the wrong lines.
"""
import sys
from pathlib import Path
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible

TYPES = "typedef unsigned short u16;\n"
COMMENT = "/* a block comment\n   over\n   four\n   lines */\n"


def findings(source, **kwargs):
    return [(line, rule) for line, rule, _, _ in plausible.check_text(source, **kwargs)]


def line_of(source, needle):
    return source[:source.index(needle)].count("\n") + 1


class LineNumberTests(unittest.TestCase):
    def test_a_finding_after_a_multi_line_comment_is_on_its_own_line(self):
        source = TYPES + COMMENT + "u16 f(void) { return *(volatile u16 *)0x03001000; }\n"
        self.assertEqual(line_of(source, "volatile"), 6)
        self.assertIn((6, "volatile"), findings(source))

    def test_a_justification_inside_a_comment_three_lines_up_does_not_clear(self):
        source = (TYPES + "/* a block comment\n   plausible: written for something else, three lines above\n"
                  "   over\n   four lines */\nint x;\nu16 f(void) { return *(u16 *)0x08001234; }\n")
        line = line_of(source, "0x08001234")
        self.assertIn((line, "rom-address"), findings(source))

    def test_a_justification_on_the_line_above_still_clears(self):
        for comment in ("/* plausible: a ROM table */\n",
                        # a block comment over two lines, ending on the line above (the marker begins the comment)
                        "/* plausible: a ROM table,\n   read by the boot code */\n",
                        "// plausible: a ROM table\n"):
            with self.subTest(comment=comment):
                source = TYPES + COMMENT + comment + "u16 f(void) { return *(u16 *)0x08001234; }\n"
                self.assertNotIn("rom-address", [rule for _, rule in findings(source)])
        # and on the line itself, after a multi-line comment
        source = TYPES + COMMENT + "u16 f(void) { return *(u16 *)0x08001234; } /* plausible: a ROM table */\n"
        self.assertNotIn("rom-address", [rule for _, rule in findings(source)])

    def test_inert_control_flow_is_numbered_by_the_file(self):
        source = COMMENT + "void f(int c, int *x) {\n    if (c) *x = 1; else *x = 1;\n}\n"
        self.assertIn((line_of(source, "if (c)"), "inert-control-flow"), findings(source))

    def test_nul_bytes_and_preprocessor_probes_are_numbered_by_the_file(self):
        source = COMMENT + "int x;\n#if __has_include(\"a.h\")\n#endif\nint y;\0\n"
        found = findings(source)
        self.assertIn((line_of(source, "#if"), "preprocessor-probe"), found)
        self.assertIn((line_of(source, "\0"), "nul-byte"), found)

    def test_volatile_allow_list_findings_are_numbered_by_the_file(self):
        symbol = "g_control_flags_03000940"
        entry = {"symbol": symbol, "address": "0x03000940", "header": "include/control_flags.h",
                 "member_types": ["u8"], "declaration": "extern struct { u16 display; } " + symbol + ";",
                 "evidence": "#90", "reason": "test"}
        source = COMMENT + "__typeof__(" + symbol + ".display) local;\n"
        found = findings(source, data_symbols={symbol: "0x03000940"}, relpath="src/08028C34.c",
                         volatile_allow=[entry])
        self.assertIn((line_of(source, "__typeof__"), "volatile-allowlist"), found)

    def test_the_stripped_code_keeps_offsets_and_blanks_comment_newlines(self):
        # a directive goes on past a comment that spans lines, as cpp reads it
        text = "#define X /* one\n two */ 1\nint y;\n"
        code = plausible.strip_comments_and_strings(text)
        self.assertEqual(len(code), len(text))
        self.assertEqual(code.count("\n"), 2)
        self.assertEqual(plausible.DIRECTIVE.match(code)[0].split(), ["#define", "X", "1"])


if __name__ == "__main__":
    unittest.main()
