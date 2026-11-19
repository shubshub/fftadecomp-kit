"""Kit#357 item 2: every rule also reads a file with its line splices joined, as cpp does.

cpp deletes backslash-newline (and backslash, spaces or NUL, newline) before it
reads a token.  A file with a splice is checked as written and again joined;
a finding of either view is a finding.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible

S = "\\\n"
SPLICES = ("\\\n", "\\ \t\n", "\\\r\n", "\\\0\n")


def findings(source):
    return plausible.check_text(source, data_symbols={}, volatile_allow=[])


def rules(source):
    return sorted({rule for _, rule, _, _ in findings(source)})


class IssueTableTests(unittest.TestCase):
    """the issue's reproducer: one line refused, and the same split by a splice"""

    CASES = (
        ("inline-asm", 'void f(void) { asm("nop"); }', 'void f(void) { a' + S + 'sm("nop"); }'),
        ("inline-asm", 'void f(void) { __asm__("nop"); }', 'void f(void) { __a' + S + 'sm__("nop"); }'),
        ("dead-code", "void f(void) { if (0) g(); }", "void f(void) { if (" + S + "0) g(); }"),
        ("dead-code", "#if 0\nint x;\n#endif\n", "#if " + S + "0\nint x;\n#endif\n"),
        ("attribute-steering", 'int x __attribute__((section(".x")));',
         'int x __attribute__((sec' + S + 'tion(".x")));'),
        ("stringised-pragma", '_Pragma("pack(1)")\n', '_Pra' + S + 'gma("pack(1)")\n'),
        ("empty-body", "void f(void) {}", "void f(void) " + S + "{}"),
        ("volatile", "volatile int x;", "vola" + S + "tile int x;"),
    )

    def test_every_rule_sees_a_token_split_by_a_splice(self):
        for rule, plain, spliced in self.CASES:
            with self.subTest(plain=plain):
                self.assertIn(rule, rules(plain))
            for splice in SPLICES:
                with self.subTest(spliced=spliced, splice=splice):
                    self.assertIn(rule, rules(spliced.replace(S, splice)))

    def test_more_rules_and_the_earlier_reviews_cases(self):
        for rule, source in (
                ("dead-code", "void f(void) { whi" + S + "le (0) g(); }"),
                ("dead-code", "void f(void) { if" + S + " (0) g(); }"),
                ("inline-asm", "void f(void) { _" + S + "_as" + S + "m__ (\"nop\"); }"),
                ("optimize-pragma", "#pragma GCC opti" + S + "mize (\"O0\")\n"),
                ("emission-pragma", "#pra" + S + "gma weak f\n"),
                ("pragma-pack", "#pragma pa" + S + "ck(1)\n"),
                ("no-standard-errors", "#pragma GCC diag" + S + "nostic ignored \"-Wall\"\n"),
                ("placeholder", "int TO" + S + "DO;\n"),
                ("placeholder", "int x = FIX" + S + "ME;\n"),
                ("hack-vocabulary", "int x; /* this is a ha" + S + "ck */\n"),
                ("pad-named", "struct S { u8 pa" + S + "d[4]; };\n"),
                ("noinline", "static __attribute__((no" + S + "inline)) void f(void) {}\n"),
                ("rom-address", "u32 x = 0x080" + S + "12345;\n")):
            with self.subTest(source=source):
                self.assertIn(rule, rules(source))

    def test_inert_control_flow_split_by_a_splice(self):
        plain = "void f(int c) { if (c) x = 1; else x = 1; }\n"
        self.assertTrue(findings(plain))
        spliced = "void f(int c) { if (c) x = 1; el" + S + "se x = 1; }\n"
        self.assertEqual(rules(spliced), rules(plain))


class ReportingTests(unittest.TestCase):
    def test_a_joined_finding_is_on_its_logical_lines_first_line_and_says_so(self):
        found = findings("int a;\nvoid f(void) { a" + S + "sm(\"nop\"); }\nint b;\n")
        self.assertEqual([(line, rule) for line, rule, _, _ in found], [(2, "inline-asm")])
        self.assertTrue(found[0][3].endswith(plausible.JOINED))
        found = findings("#define M(x) \\\n    (x)\nint a;\nvoid f(void) { a" + S + "sm(\"nop\"); }\n")
        self.assertEqual([(line, rule) for line, rule, _, _ in found], [(4, "inline-asm")])

    def test_a_finding_both_views_make_is_reported_once_where_it_is_written(self):
        for source, expected in (
                ("#define M(x) \\\n    (x)\nvoid f(void) { asm(\"nop\"); }\n", [(3, "inline-asm")]),
                ("void f(void) { __" + S + "asm (\"nop\"); }\n", [(2, "inline-asm")]),
                ("#define M(x) do { \\\n    asm(\"nop\"); \\\n} while (0)\n", [(2, "inline-asm")]),
                ("__" + S + "volatile int x;\n", [(2, "volatile")])):
            with self.subTest(source=source):
                found = findings(source)
                self.assertEqual([(line, rule) for line, rule, _, _ in found], expected)
                self.assertFalse(found[0][3].endswith(plausible.JOINED))

    def test_two_split_tokens_on_one_logical_line_are_two_findings(self):
        found = findings("void f(void) { a" + S + "sm(\"a\"); a" + S + "sm(\"b\"); }\n")
        self.assertEqual([(line, rule) for line, rule, _, _ in found], [(1, "inline-asm"), (1, "inline-asm")])

    def test_files_without_a_splice_are_checked_once(self):
        calls = []
        real = plausible.check_view

        def spy(*args, **kwargs):
            calls.append(args[0])
            return real(*args, **kwargs)

        from unittest import mock
        with mock.patch.object(plausible, "check_view", side_effect=spy):
            plausible.check_text("int x;\n", data_symbols={})
            self.assertEqual(len(calls), 1)
            plausible.check_text("#define A \\\n 1\n", data_symbols={})
            self.assertEqual(calls[1:], ["#define A \\\n 1\n", "#define A  1\n"])

    def test_an_exemption_holds_only_where_both_views_admit_it(self):
        bound = ("typedef struct { unsigned control; } R;\nextern R data_040000D4;\nextern R ram_obj;\n"
                 "void f(void)\n{\n    /* plausible: DMA3 MMIO requires volatile writes. */\n"
                 "    volatile R *dma = &data_040000D4;\n%s\n    dma->control = 1;\n}\n")
        mapping = {"data_040000D4": "0x040000D4"}
        ok = plausible.check_text(bound % "", data_symbols=mapping, volatile_allow=[])
        self.assertEqual(ok, [])
        hidden = plausible.check_text(bound % ("    d" + S + "ma = &ram_obj;"), data_symbols=mapping,
                                      volatile_allow=[])
        self.assertEqual([rule for _, rule, _, _ in hidden], ["volatile"])
        self.assertTrue(hidden[0][3].endswith(plausible.JOINED))


if __name__ == "__main__":
    unittest.main()
