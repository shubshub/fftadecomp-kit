"""inert-control-flow is a suspect: a justification that cites the ROM clears it.

`if (c) X; else X;` has identical arms, so the test exists only for the code it makes.  Where the ROM keeps the
test's instructions (a dead load of what it reads, a frame the branch needed), the source is the original's, and
the maintainer's ruling on kit#201 admits it with a comment that cites them.  check_view used to append these
hits without any justification test, so no comment could clear one.  Now a justification (a comment that begins
`plausible:` and says why, on the `if`'s line or ending on the line before) clears one when it names a ROM
address.  The shapes a review tried against the first version (a label, a string, `implausible:`, an empty
marker, a justification admitting steering, one written for another finding) clear nothing.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import plausible

TYPES = "typedef unsigned char u8;\ntypedef unsigned short u16;\n"
BODY = ("typedef struct { u16 id; u8 unknown_02[0x1a]; u8 flag; } S;\n"
        "void f(S *p, u8 b) {\n"
        "{comment}"
        "    if (p->id){same}\n"
        "        p->flag = b;\n"
        "    else{after}\n"
        "        p->flag = b;\n"
        "{tail}"
        "}\n")
KEPT = "the ROM keeps the test's dead load at 0x08148634 and saved lr at 0x0814862C"


def source(comment="", same="", after="", tail=""):
    return TYPES + BODY.replace("{comment}", comment).replace("{same}", same).replace(
        "{after}", after).replace("{tail}", tail)


def inert(text):
    return [(line, severity) for line, rule, severity, _ in plausible.check_text(text, data_symbols={})
            if rule == "inert-control-flow"]


def findings(text):
    return [(line, rule) for line, rule, _, _ in plausible.check_text(text, data_symbols={})]


def line_of(text, needle):
    return text[:text.index(needle)].count("\n") + 1


def fn(body, before=""):
    return TYPES + before + "void f(int c, int d, int *x) {\n" + body + "}\n"


INERT = "    if (c) *x = 1; else *x = 1;\n"


class InertControlFlowJustificationTests(unittest.TestCase):
    def test_an_unjustified_inert_test_still_refuses(self):
        for text in (source(), "void f(int c, int *x) { if (c) *x = 1; else *x = 1; }\n",
                     source(comment=f"    /* {KEPT} */\n")):
            with self.subTest(text=text):
                self.assertEqual(inert(text), [(line_of(text, "if ("), "suspect")])

    def test_a_justification_that_cites_the_rom_clears_it(self):
        for text in (
                source(comment=f"    /* plausible: {KEPT} */\n"),
                source(comment=f"    // plausible: {KEPT}\n"),
                # a block comment that begins with the marker and ends on the line before the `if`, as 0814862C's
                source(comment="    /* plausible: identical arms whose test the ROM keeps: the id load is at\n"
                               "     * 0x08148634 (ldrh r0, [r2]), and push {lr} at 0x0814862C, so the\n"
                               "     * test's dead load and saved lr are in the ROM */\n"),
                source(same=f" /* plausible: {KEPT} */"),
                f"void f(int c, int *x) {{ if (c) *x = 1; else *x = 1; }} /* plausible: {KEPT} */\n"):
            with self.subTest(text=text):
                self.assertEqual(inert(text), [])

    def test_a_justification_that_cites_no_rom_address_does_not_count(self):
        for comment in ("    /* plausible: the ROM keeps the test's dead load and saved lr */\n",
                        "    /* plausible: the test reads the word at 0x03001234 */\n",
                        "    /* plausible: kept at 0x0814862 */\n"):
            with self.subTest(comment=comment):
                text = source(comment=comment)
                self.assertEqual(inert(text), [(line_of(text, "if ("), "suspect")])

    def test_an_address_run_into_a_longer_number_or_a_word_does_not_count(self):
        # a ROM address is a whole number of eight digits: one that runs on into more digits or a word cites nothing
        for comment in ("    /* plausible: the ROM keeps the test's dead load at 0x081486340 */\n",
                        "    /* plausible: the ROM keeps the test's dead load at id0x08148634 */\n",
                        "    /* plausible: the ROM keeps the test's dead load at 0x08148634_load */\n"):
            with self.subTest(comment=comment):
                text = source(comment=comment)
                self.assertEqual(inert(text), [(line_of(text, "if ("), "suspect")])

    def test_a_justification_on_another_line_does_not_count(self):
        for text in (
                # two lines above
                source(comment=f"    /* plausible: {KEPT} */\n\n"),
                source(comment=f"    /* plausible: {KEPT}\n     * and the frame */\n\n"),
                # on the arms, the else or after the statement: the hit is on the `if`'s line
                source(after=f" /* plausible: {KEPT} */"),
                source(tail=f"    /* plausible: {KEPT} */\n"),
                TYPES + f"void f(int c, int *x) {{\n    if (c) *x = 1;\n    /* plausible: {KEPT} */ else *x = 1;\n}}\n",
                # the marker on the last line of a block comment (0814862C's first draft): not where it begins
                source(comment="    /* Identical arms whose test the ROM keeps: the id load is at\n"
                               "     * 0x08148634 (ldrh r0, [r2]), and push {lr} at 0x0814862C.\n"
                               "     * plausible: the test's dead load and saved lr are in the ROM */\n")):
            with self.subTest(text=text):
                self.assertEqual(inert(text), [(line_of(text, "if ("), "suspect")])

    def test_one_justification_clears_only_its_own_test(self):
        justified = f"    /* plausible: {KEPT} */\n"
        text = (TYPES + "void f(int c, int d, int *x) {\n" + justified +
                "    if (c) *x = 1; else *x = 1;\n    *x += 2;\n    if (d) *x = 3; else *x = 3;\n}\n")
        self.assertEqual(inert(text), [(line_of(text, "if (d)"), "suspect")])

    def test_both_views_of_a_file_with_a_splice_read_the_justification(self):
        splice = "#define ONE \\\n    1\n"
        justified = splice + source(comment=f"    /* plausible: {KEPT} */\n")
        self.assertEqual(inert(justified), [])
        bare = splice + source()
        self.assertEqual(inert(bare), [(line_of(bare, "if ("), "suspect")])
        # a finding of either view is a finding: the splice puts the justification next to the test only as cpp
        # reads the file, and as written it is two lines up
        moved = source(comment=f"    /* plausible: {KEPT} */ \\\n\n")
        self.assertEqual([line for line, _ in inert(moved)], [line_of(moved, "if (")])

    def test_the_command_line_passes_a_justified_test_even_strictly(self):
        with tempfile.TemporaryDirectory() as directory:
            for name, text, status in (
                    ("justified.c", source(comment=f"    /* plausible: {KEPT} */\n"), 0),
                    ("bare.c", source(), 1)):
                path = Path(directory) / name
                path.write_text(text)
                for flags in ([], ["--strict"]):
                    with self.subTest(name=name, flags=flags):
                        run = subprocess.run([sys.executable, str(TOOLS / "plausible.py"), *flags, str(path)],
                                             capture_output=True, text=True, cwd=directory,
                                             env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
                        self.assertEqual(run.returncode, status, run.stdout + run.stderr)
                        self.assertEqual("inert-control-flow" in run.stdout, bool(status))


class ReviewControls(unittest.TestCase):
    """the review's controls: refused bare, cleared by a citing justification on the if's line or the one before"""

    def test_bare_refuses(self):
        self.assertEqual(inert(fn(INERT)), [(4, "suspect")])

    def test_a_citing_comment_on_the_line_before_or_the_same_line_clears(self):
        self.assertEqual(inert(fn("    /* plausible: dead ldrh at 0x08148634 */\n" + INERT)), [])
        self.assertEqual(inert(fn("    if (c) *x = 1; else *x = 1; /* plausible: kept test at 0x08148634 */\n")), [])

    def test_two_lines_up_or_the_line_after_does_not(self):
        self.assertEqual(inert(fn("    /* plausible: kept test at 0x08148634 */\n\n" + INERT)), [(6, "suspect")])
        self.assertEqual(inert(fn(INERT + "    /* plausible: kept test at 0x08148634 */\n")), [(4, "suspect")])

    def test_two_inert_tests_one_comment(self):
        text = fn("    /* plausible: first, at 0x08148634 */\n" + INERT + INERT.replace("c", "d"))
        self.assertEqual(inert(text), [(6, "suspect")])

    def test_errors_stay_errors_with_a_justification(self):
        for body in ("    /* plausible: kept at 0x08148634 */\n    if (0) *x = 1;\n",
                     "    /* plausible: kept at 0x08148634 */\n    while (0) *x = 1;\n",
                     "    /* plausible: kept at 0x08148634 */\n    while (c) {}\n",
                     "    /* plausible: kept at 0x08148634 */\n    asm(\"nop\");\n"):
            with self.subTest(body=body):
                self.assertTrue([f for f in plausible.check_text(fn(body), data_symbols={}) if f[2] == "error"])


class ReviewBypasses(unittest.TestCase):
    """the review's bypasses of the first version: each now leaves the finding"""

    def test_an_empty_justification(self):
        self.assertEqual(inert(fn("    /* plausible: */\n" + INERT)), [(5, "suspect")])

    def test_implausible_and_not_plausible(self):
        self.assertEqual(inert(fn("    /* implausible: this test is only steering, 0x08148634 */\n" + INERT)),
                         [(5, "suspect")])
        self.assertEqual(inert(fn("    // not plausible: steering at 0x08148634\n" + INERT)), [(5, "suspect")])

    def test_a_label(self):
        text = fn("    plausible: if (c) *x = 1; else *x = 1;\n")
        self.assertEqual(findings(text), [(4, "inert-control-flow")])

    def test_a_string_literal(self):
        text = TYPES + "extern void say(const char *);\nvoid f(int c, int *x) {\n    say(\"plausible: 0x08148634\");\n" + \
            INERT + "}\n"
        self.assertEqual(findings(text), [(line_of(text, "if (c)"), "inert-control-flow")])

    def test_steering_admitted_in_the_justification(self):
        text = fn("    /* plausible: codegen hack so the compiler will keep the frame at 0x08148634 */\n" + INERT)
        self.assertEqual(findings(text), [(4, "hack-vocabulary"), (5, "inert-control-flow")])

    def test_another_findings_justification(self):
        # a justification written for a ROM-address suspect on the line before clears that suspect, and the test
        # only if it cites a ROM address: a comment is not bound to its finding
        text = fn("    *x = *(int *)0x08001234; /* plausible: a ROM table word */\n" + INERT)
        self.assertEqual(findings(text), [(5, "inert-control-flow")])
        text = fn("    *x = *(int *)0x08001234; /* plausible: the ROM table word at 0x08001234 */\n" + INERT)
        self.assertEqual(findings(text), [])


class Shadowing(unittest.TestCase):
    def test_an_uncited_justification_does_not_hide_a_cited_one(self):
        text = fn("    /* plausible: kept */\n    if (c) *x = 1; else *x = 1; /* plausible: the load at 0x08148634 */\n")
        self.assertEqual(inert(text), [])
        self.assertEqual(plausible.justifications(text, 5), ["plausible: kept", "plausible: the load at 0x08148634"])
        self.assertEqual(inert(fn("    /* plausible: kept */\n" + INERT)), [(5, "suspect")])


if __name__ == "__main__":
    unittest.main()
