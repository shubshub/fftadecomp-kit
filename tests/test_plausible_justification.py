"""A suspect is cleared only by a comment that begins `plausible:` and says why.

justified() used to test the raw substring `plausible:` on the suspect's line or the line before, and the
hack-vocabulary scan skipped every line holding it.  So a C label `plausible:`, a string literal, `implausible:`,
`not plausible:`, an empty `/* plausible: */` and `/* plausible: codegen hack ... */` each cleared a finding with
no finding left.  Now the marker must begin a comment that lexical_spans (the scanner that strips comments for
every rule) reads as one, the rest must say something that admits no steering, and the comment must lie on the
suspect's line or end on the line before.  The hardware volatile exception reads its comment the same way.
"""
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import plausible

TYPES = "typedef unsigned char u8;\ntypedef unsigned short u16;\n"
ROM = "    *x = *(int *)0x08001234;\n"


def fn(body, before=""):
    return TYPES + before + "void f(int c, int *x) {\n" + body + "}\n"


def findings(text):
    return [(line, rule) for line, rule, _, _ in plausible.check_text(text, data_symbols={})]


def line_of(text, needle):
    return text[:text.index(needle)].count("\n") + 1


def rom(text):
    return [(line_of(text, "*x = *(int *)0x08"), "rom-address")]


class JustificationTests(unittest.TestCase):
    def test_a_comment_that_begins_plausible_and_says_why_clears_a_suspect(self):
        for text in (
                fn("    /* plausible: the word at 0x08001234 is a ROM table entry */\n" + ROM),
                fn("    // plausible: a ROM table entry\n" + ROM),
                fn("    /*plausible:a ROM table entry*/\n" + ROM),
                fn(ROM.rstrip("\n") + " /* plausible: a ROM table entry */\n"),
                # a block comment that begins with the marker counts by its last line, and one that starts on the
                # suspect's line counts however far it runs
                fn("    /* plausible: a ROM table entry,\n     * read once at boot\n     */\n" + ROM),
                fn(ROM.rstrip("\n") + " /* plausible: a ROM table\n       entry */\n")):
            with self.subTest(text=text):
                self.assertEqual(findings(text), [])
        for rule, statement in (("pad-named", "    u8 pad[4];\n"), ("noinline", "    int noinline;\n")):
            with self.subTest(rule=rule):
                self.assertEqual(findings(fn("    /* plausible: the member is unknown */\n" + statement)), [])
                bare = fn(statement)
                self.assertEqual(findings(bare), [(line_of(bare, statement.strip()), rule)])

    def test_nothing_else_spelling_the_marker_clears_one(self):
        for text in (
                fn(ROM),
                # a C label named plausible on the suspect's line, and one on the line before
                fn("    plausible: " + ROM.lstrip()),
                fn("plausible:\n" + ROM),
                # a string literal on the line before, and a comment inside one
                fn("    say(\"plausible: \");\n" + ROM, before="extern void say(const char *);\n"),
                fn("    say(\"/* plausible: a ROM table entry */\");\n" + ROM,
                   before="extern void say(const char *);\n"),
                # comments that say something else
                fn("    /* implausible: this is only steering */\n" + ROM),
                fn("    // not plausible: steering\n" + ROM),
                fn("    /* a ROM table entry; plausible: yes */\n" + ROM),
                fn("    /* a ROM table entry read once at boot,\n     * plausible: so it is a value */\n" + ROM),
                # a marker with nothing after it
                fn("    /* plausible: */\n" + ROM),
                fn("    /* plausible:\n     *\n     */\n" + ROM),
                fn("    // plausible:\n" + ROM),
                fn("    /* plausible: -- */\n" + ROM),
                # a comment two lines up, or after the suspect
                fn("    /* plausible: a ROM table entry */\n\n" + ROM),
                fn(ROM + "    /* plausible: a ROM table entry */\n")):
            with self.subTest(text=text):
                self.assertEqual(findings(text), rom(text))
        # a block comment that is never closed carries none
        text = TYPES + "void f(int c, int *x) {\n" + ROM.rstrip("\n") + " /* plausible: a ROM table entry\n}\n"
        self.assertIn((line_of(text, "*x = *(int *)0x08"), "rom-address"), findings(text))

    def test_a_justification_that_admits_steering_clears_nothing_and_is_found(self):
        for comment in ("    /* plausible: codegen hack so the compiler will keep the frame */\n",
                        "    // plausible: a workaround for the ROM table\n"):
            with self.subTest(comment=comment):
                text = fn(comment + ROM)
                self.assertEqual(findings(text), sorted([(line_of(text, "plausible:"), "hack-vocabulary")] +
                                                        rom(text)))
        # hack vocabulary on a marker line is read like any other line
        text = fn("    /* plausible: a ROM table entry */ /* hack */\n" + ROM)
        self.assertIn((line_of(text, "/* hack */"), "hack-vocabulary"), findings(text))

    def test_the_justification_is_the_comment_text(self):
        text = fn("    /* plausible: a ROM table\n     *   entry read at boot */\n" + ROM)
        line = line_of(text, "*x = *(int *)0x08")
        self.assertEqual(plausible.justification(text, line), "plausible: a ROM table entry read at boot")
        self.assertTrue(plausible.justified(text, line))
        both = fn("    /* implausible: no */ /* plausible: first */ // plausible: second\n" +
                  ROM.rstrip("\n") + " /* plausible: third */\n")
        self.assertEqual(plausible.justification(both, line_of(both, "*x = *(int *)0x08")), "plausible: first")
        self.assertIsNone(plausible.justification(fn(ROM), line))
        self.assertFalse(plausible.justified(fn(ROM), line))

    def test_the_hardware_exception_reads_its_comment_the_same_way(self):
        access = "*(volatile u16 *)0x04000000 = value;"
        rules = lambda source: [rule for _, rule, _, _ in plausible.check_text(source, data_symbols={})]
        self.assertEqual(rules("/* plausible: DISPCNT */\n" + access), [])
        self.assertEqual(rules(access + " // plausible: DISPCNT\n"), [])
        for prefix in ("/* implausible: DISPCNT */\n", "/* plausible: */\n", "// not plausible: DISPCNT\n",
                       "/* DISPCNT; plausible: yes */\n", 'const char *s = "/* plausible: DISPCNT */";\n'):
            with self.subTest(prefix=prefix):
                self.assertIn("volatile", rules(prefix + access))

    def test_a_suspect_and_the_hardware_exception_read_the_same_justifications(self):
        # (text before the statement, text after it on its line), each placed before a ROM-address suspect and
        # before a direct register access: the one justification rule decides both
        shapes = [("/* plausible: kept */\n", ""), ("// plausible: kept\n", ""), ("", " /* plausible: kept */"),
                  ("", " // plausible: kept"), ("/* plausible: kept,\n   over two lines */\n", ""),
                  ("", " /* plausible: kept,\n   running on */"), ("/* plausible: kept */\n\n", ""),
                  ("/* implausible: kept */\n", ""), ("// not plausible: kept\n", ""), ("/* plausible: */\n", ""),
                  ("/* kept; plausible: yes */\n", ""), ("/* kept,\n   plausible: yes */\n", ""),
                  ("plausible:\n", ""), ('say("plausible: kept");\n', ""), ('say("/* plausible: kept */");\n', ""),
                  ("/* plausible: a hack */\n", "")]
        cleared = []
        for before, after in shapes:
            suspect = (TYPES + "extern void say(const char *);\nvoid f(int *x) {\n" + before +
                       "*x = *(int *)0x08001234;" + after + "\n}\n")
            access = (TYPES + "extern void say(const char *);\nvoid g(u16 value) {\n" + before +
                      "*(volatile u16 *)0x04000000 = value;" + after + "\n}\n")
            with self.subTest(before=before, after=after):
                by_suspect = "rom-address" not in [rule for _, rule in findings(suspect)]
                by_access = "volatile" not in [rule for _, rule in findings(access)]
                self.assertEqual(by_suspect, by_access)
                cleared.append(by_suspect)
        self.assertEqual(cleared, [True] * 6 + [False] * 10)

    def test_the_command_line_refuses_a_label_even_without_strict(self):
        with tempfile.TemporaryDirectory() as directory:
            for name, text, status in (("justified.c", fn("    /* plausible: a ROM table entry */\n" + ROM), 0),
                                       ("label.c", fn("    plausible: " + ROM.lstrip()), 1)):
                path = Path(directory) / name
                path.write_text(text)
                for flags in ([], ["--strict"]):
                    with self.subTest(name=name, flags=flags):
                        run = subprocess.run([sys.executable, str(TOOLS / "plausible.py"), *flags, str(path)],
                                             capture_output=True, text=True, cwd=directory,
                                             env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
                        self.assertEqual(run.returncode, status, run.stdout + run.stderr)


def reference_strip(text):
    """strip_comments_and_strings as it was before lexical_spans: the scanner must blank the same characters"""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            while i < n and not (text[i] == "*" and i + 1 < n and text[i + 1] == "/"):
                out[i] = " "
                i += 1
            for k in range(i, min(i + 2, n)):
                out[k] = " "
            i += 2
        elif c in "\"'":
            q = c
            out[i] = " "
            i += 1
            while i < n and text[i] != q:
                if text[i] == "\\":
                    out[i] = " "
                    if i + 1 < n:
                        out[i + 1] = " "
                    i += 2
                    continue
                out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


class LexicalSpanTests(unittest.TestCase):
    def test_the_spans_blank_exactly_what_the_stripper_blanked(self):
        cases = ["", "/", "/*", "/**/", "/*/", "/*/ x */", "//", "a // b\nc", '"', "'", '"\\', "'\\'",
                 '"a\\"b" /* "c */ d', "/* a */ \"/* b */\" // c\n'/'", "x /* never closed", '"never closed',
                 "/* plausible: a */ *x = *(int *)0x08001234;"]
        rng = random.Random(201)
        cases += ["".join(rng.choice('/*"\'\\\n ab') for _ in range(rng.randrange(1, 24))) for _ in range(20000)]
        for text in cases:
            spans = list(plausible.lexical_spans(text))
            self.assertEqual(plausible.strip_comments_and_strings(text), reference_strip(text), text)
            self.assertEqual(reference_strip(text), "".join(
                " " if any(start <= i < end for _, start, end in spans) else c for i, c in enumerate(text)), text)
            self.assertTrue(all(0 <= start < end <= len(text) for _, start, end in spans), text)
            self.assertTrue(all(text.startswith(("//", "/*"), start) == (kind == "comment")
                                for kind, start, _ in spans), text)


if __name__ == "__main__":
    unittest.main()
