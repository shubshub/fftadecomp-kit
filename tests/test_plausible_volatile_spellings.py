"""Kit#93: every spelling of the volatile qualifier, in the lint and in the translation unit.

agbcc's keyword table (gcc/c-parse.gperf) maps `volatile`, `__volatile__` and
`__volatile` to the same qualifier.  The lint refuses all three and its
exceptions accept only the plain spelling; the census checks cpp's output.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parents[1] / "tools"
sys.path.insert(0, str(TOOLS))
import plausible
import volatile_semantics


SPELLINGS = ("volatile", "__volatile__", "__volatile")
GNU = SPELLINGS[1:]
HAVE_CPP = shutil.which("cpp") is not None
COMMENT = "/* plausible: hardware register, volatile is required here */\n"
SYMBOL = "g_control_flags_03000940"
DECLARATION = ("extern struct {\n    u16 display;\n    u8 unknown_02[0x3A];\n"
               "    volatile u8 unknown_3C : 8;\n    volatile u8 unknown_3D : 8;\n"
               "} " + SYMBOL + ";\n")
ENTRY = {"symbol": SYMBOL, "address": "0x03000940", "header": "include/control_flags.h",
         "member_types": ["u8"], "declaration": " ".join(DECLARATION.split()),
         "evidence": "#90", "reason": "test"}


def rules(source, relpath=None, mapping=None, entries=()):
    return [rule for _, rule, _, _ in plausible.check_text(
        source, data_symbols=mapping or {}, relpath=relpath, volatile_allow=list(entries))]


class SpellingTests(unittest.TestCase):
    def test_spellings_are_agbcc_keywords(self):
        self.assertEqual(plausible.VOLATILE_SPELLINGS, SPELLINGS)
        for spelling in SPELLINGS:
            self.assertEqual(plausible.VOLATILE_QUALIFIER.findall(f"x {spelling} y"), [spelling])

    def test_issue_repro_is_refused_in_every_spelling(self):
        for spelling in SPELLINGS:
            with self.subTest(spelling=spelling):
                self.assertEqual(rules(f"{spelling} int x = 0; x = 1;"), ["volatile"])

    def test_every_form_in_sources_and_headers(self):
        forms = ("{q} int x;", "*({q} u16 *)p = 1;", "typedef {q} struct {{ u8 a; }} T;",
                 "struct S {{ {q} u8 a; }};", "void f({q} u8 *p);", "#define V {q}\nV u8 x;",
                 "#define R(a) (*({q} u8 *)(a))", "const {q} u8 x;", "u8 * {q} p;",
                 "u32 n = sizeof({q} u8);", "extern {q}\nu8 x;")
        for spelling in SPELLINGS:
            for form in forms:
                for relpath in (None, "src/08000000.c", "include/x.h"):
                    with self.subTest(spelling=spelling, form=form, relpath=relpath):
                        found = rules(form.format(q=spelling), relpath)
                        self.assertEqual(found.count("volatile"), 1, found)

    def test_gnu_findings_name_the_spelling(self):
        for spelling in GNU:
            with self.subTest(spelling=spelling):
                (finding,) = plausible.check_text(f"{spelling} int x;", data_symbols={})
                self.assertEqual(finding[1], "volatile")
                self.assertIn(f"`{spelling}`", finding[3])
                self.assertIn("only the plain spelling", finding[3])
        (finding,) = plausible.check_text("volatile int x;", data_symbols={})
        self.assertNotIn("GNU", finding[3])
        found = plausible.check_text("__volatile__ int x;\nvolatile int y;\n", data_symbols={})
        self.assertIn("GNU", found[0][3])
        self.assertNotIn("GNU", found[1][3])

    def test_identifiers_that_contain_a_spelling_are_not_qualifiers(self):
        for word in ("is_volatile_flag", "__volatile_x", "volatile__", "my__volatile", "volatile_",
                     "x__volatile__y", "__volatile___", "___volatile", "nonvolatile", "volatile2"):
            with self.subTest(word=word):
                self.assertEqual(rules(f"u8 {word};"), [])

    def test_comments_and_literals_are_not_code(self):
        for source in ("/* __volatile__ */ int x;", "// __volatile\nint x;",
                       'char *s = "__volatile__ volatile";', "char c = '__volatile';"):
            with self.subTest(source=source):
                self.assertEqual(rules(source), [])

    def test_hardware_exception_accepts_only_the_plain_spelling(self):
        direct = COMMENT + "*({q} u16 *)0x04000000 = value;"
        bound = ("typedef struct {{ void *source; void *destination; u32 control; }} DmaRegisters;\n"
                 "extern DmaRegisters dma3;\n" + COMMENT + "{q} DmaRegisters *dma = &dma3;\n"
                 "dma->control = value;\n")
        polling = COMMENT + "#define STATUS (*({q} u16 *)0x04000004)\nvoid w(void) {{ while (STATUS & 1) {{}} }}"
        mapping = {"dma3": "0x040000D4"}
        for form in (direct, bound, polling):
            with self.subTest(form=form):
                self.assertEqual(rules(form.format(q="volatile"), mapping=mapping), [])
            for spelling in GNU:
                with self.subTest(form=form, spelling=spelling):
                    self.assertIn("volatile", rules(form.format(q=spelling), mapping=mapping))

    def test_listed_header_with_a_respelt_qualifier_is_refused(self):
        mapping = {SYMBOL: "0x03000940"}
        self.assertEqual(rules(DECLARATION, ENTRY["header"], mapping, [ENTRY]), [])
        for spelling in GNU:
            with self.subTest(spelling=spelling):
                for count in (1, -1):
                    found = rules(DECLARATION.replace("volatile", spelling, count), ENTRY["header"],
                                  mapping, [ENTRY])
                    self.assertIn("volatile-allowlist", found)
                    self.assertIn("volatile", found)

    def test_every_asm_keyword_spelling_is_inline_asm(self):
        # c-parse.gperf: asm, __asm and __asm__ are ASM_KEYWORD; the grammar is
        # ASM_KEYWORD maybe_type_qual '(' (review-93 M2, and the 2026-11-13 review)
        for keyword in ("asm", "__asm", "__asm__"):
            for qualifier in SPELLINGS + ("const", "__const", "__const__", "__restrict__", ""):
                with self.subTest(keyword=keyword, qualifier=qualifier):
                    self.assertIn("inline-asm", rules(f'void f(void) {{ {keyword} {qualifier} ("nop"); }}'))
        for code in ('void f(void) { __asm("nop"); }', 'void f(void) { x = 1; __asm ("" ::: "memory"); x = 2; }',
                     'void f(void) { __asm("mov r8, r8"); }', 'void f(void) { register int r __asm("r4"); }',
                     'int x __asm("y");', 'int x asm("y");', 'int x __asm__("y");',
                     '#define A asm\nvoid f(void) { A ("nop"); }', '#define A __asm\nvoid f(void) { A ("nop"); }',
                     '__asm (".global x");', 'void f(void) { __\\\nasm ("nop"); }'):
            for relpath in ("src/08000000.c", "include/x.h"):
                with self.subTest(code=code, relpath=relpath):
                    self.assertIn("inline-asm", rules(code + "\n", relpath))

    def test_words_that_only_contain_asm_are_not_inline_asm(self):
        for code in ("int asmx;", "int x_asm;", "int __asmx;", "int __asm_y;", "int hand_asm_count;",
                     "int x__asm__y;", "int __asm__x;", "int x__asm__;", "/* __asm (\"nop\") */ int x;",
                     'const char *s = "asm(nop)";'):
            with self.subTest(code=code):
                self.assertEqual(rules(code + "\n"), [])

    def test_member_provenance_skips_every_qualifier_spelling(self):
        entry = {"symbol": "s", "declaration": "extern struct { u8 a; } s;"}
        qualifiers = ("const", "__const", "__const__") + SPELLINGS + (
            "restrict", "__restrict", "__restrict__", "signed", "__signed", "__signed__", "unsigned")
        for qualifier in qualifiers:
            for cast in ("x = (%s struct { u8 a; } *)p;", "x = (u8 (* %s)[4])p;",
                         "x = (%s union { u8 a; } *)p;"):
                with self.subTest(qualifier=qualifier, cast=cast):
                    self.assertTrue(plausible.member_provenance(cast % qualifier, entry))
        self.assertEqual(plausible.member_provenance("x = (u8)s.a; y = (const u8 *)p;", entry), [])

    def test_strip_removes_every_spelling_from_the_pinned_declaration_only(self):
        for spelling in SPELLINGS:
            declaration = ENTRY["declaration"].replace("volatile", spelling)
            text = f"{spelling} int other;\n" + declaration.replace("; ", ";\n") + "\n"
            with self.subTest(spelling=spelling):
                stripped = volatile_semantics.strip_pinned_volatile(text, declaration)
                self.assertEqual(len(stripped), len(text))
                self.assertEqual(plausible.VOLATILE_QUALIFIER.findall(stripped), [spelling])
                self.assertTrue(stripped.startswith(f"{spelling} int other;"))


MARKERS = {"volatile": "__mkaaaa", "__volatile__": "__mkbbbbbbbb", "__volatile": "__mkcccccc"}


class CensusFindingTests(unittest.TestCase):
    def test_markers_are_fresh_reserved_and_as_long_as_their_spelling(self):
        seen = set()
        for _ in range(20):
            markers = plausible.census_markers(["text"])
            self.assertEqual(set(markers), set(SPELLINGS) | {plausible.HARDWARE})
            values = list(markers.values())
            self.assertEqual(len(set(values)), 4)
            for spelling, marker in markers.items():
                self.assertEqual(len(marker), len(spelling if spelling in SPELLINGS else "volatile"))
                self.assertRegex(marker, r"^__[A-Za-z0-9]+$")
                self.assertFalse(any(other in marker for other in values if other != marker))
            seen.add(tuple(values))
        self.assertGreater(len(seen), 15)
        # drawn from letters of both cases and digits (62 symbols), not lower case alone
        drawn = "".join(marker[2:] for values in seen for marker in values)
        self.assertTrue(any(char.isupper() for char in drawn) and any(char.isdigit() for char in drawn))

    def test_markers_avoid_every_forbidden_text_and_each_other(self):
        # the first draw is distinct but forbidden, so it is drawn again
        draws = iter("a" * 6 + "b" * 10 + "c" * 8 + "g" * 6 + "d" * 6 + "e" * 10 + "f" * 8 + "h" * 6)
        markers = plausible.census_markers(["int __aaaaaa;"], choice=lambda letters: next(draws))
        self.assertEqual(markers, {"volatile": "__dddddd", "__volatile__": "__eeeeeeeeee",
                                   "__volatile": "__ffffffff", plausible.HARDWARE: "__hhhhhh"})
        # a draw where one marker would sit inside another is drawn again
        draws = iter("a" * 6 + "a" * 10 + "a" * 8 + "x" * 6 + "b" * 6 + "c" * 10 + "d" * 8 + "y" * 6)
        markers = plausible.census_markers([], choice=lambda letters: next(draws))
        self.assertEqual(markers, {"volatile": "__bbbbbb", "__volatile__": "__cccccccccc",
                                   "__volatile": "__dddddddd", plausible.HARDWARE: "__yyyyyy"})

    def test_marking_follows_the_lint_code_view(self):
        text = ('/* volatile */ volatile u8 a; // __volatile\n"__volatile__" __volatile__ u8 b;\n'
                "__volatile u8 c; is_volatile d;\n")
        marked = plausible.census_marked(text, MARKERS)
        self.assertEqual(len(marked), len(text))
        self.assertEqual(marked, text.replace(" volatile u8", " __mkaaaa u8")
                         .replace("\" __volatile__ u8", "\" __mkbbbbbbbb u8")
                         .replace("__volatile u8 c", "__mkcccccc u8 c"))

    def test_unit_without_a_qualifier_needs_nothing(self):
        self.assertEqual(plausible.census_findings("int x;\n", "anything", MARKERS), [])
        self.assertEqual(plausible.census_findings('typeof(x) y; char *s = "volatil";\n', "", MARKERS), [])

    def test_lexical_qualifiers_pass(self):
        real = 'extern volatile u8 a;\n# 1 "include/x.h" 1\n__volatile__ u8 b; char *s = "q";\n'
        marked = real.replace("volatile u8 a", "__mkaaaa u8 a").replace("__volatile__", "__mkbbbbbbbb")
        self.assertEqual(plausible.census_findings(real, marked, MARKERS), [])

    def test_each_obligation_is_refused_alone(self):
        real = "extern volatile u8 a;\nint z;\n"
        self.assertEqual(plausible.census_findings(real, "extern __mkaaaa u8 a;\nint z;\n", MARKERS), [])
        cases = (
            ("where no linted file", "extern volatile u8 a;\nvolatile int z;\n",
             "extern __mkaaaa u8 a;\nvolatile int z;\n"),
            ("pasted into a longer token", "extern volatile u8 a;\nint volatilex;\n",
             "extern __mkaaaa u8 a;\nint __mkaaaax;\n"),
            ("pasted into a longer token", "extern volatile u8 a;\nint x$volatile;\n",
             "extern __mkaaaa u8 a;\nint x$__mkaaaa;\n"),
            ("changes when only its linted qualifiers", real, "extern __mkaaaa u8 a;\nint y;\n"),
        )
        for message, unit, marked in cases:
            with self.subTest(message=message):
                found = plausible.census_findings(unit, marked, MARKERS)
                self.assertEqual(len(found), 1, found)
                self.assertIn(message, found[0])
        for spelling in ("typeof", "__typeof__", "__typeof"):
            with self.subTest(typeof=spelling):
                text = f"extern volatile u8 a;\n{spelling}(a) b;\n"
                found = plausible.census_findings(text, text.replace("volatile", "__mkaaaa"), MARKERS)
                self.assertEqual(len(found), 1, found)
                self.assertIn("typeof", found[0])

    def test_markers_spelt_by_the_source_are_refused(self):
        real = "extern volatile u8 a; int __mkaaaa;\n"
        marked = "extern __mkaaaa u8 a; int __mkaaaa;\n"
        self.assertTrue(plausible.census_findings(real, marked, MARKERS))


class ProbeTests(unittest.TestCase):
    """cpp's queries about the files could tell the census copy from the tree (review-93 C1).

    Defence in depth only: CensusDetectionTests shows a pasted query, which no
    scan of the text sees, refused by the census's random markers.
    """

    def test_every_probe_is_refused_however_it_is_spelt(self):
        for source in ('#if __has_include("x.h")\n#endif\n', '#if __has_include(<x.h>)\n#endif\n',
                       '#if __has_include_next("x.h")\n#endif\n', '#if __has_embed("x.h")\n#endif\n',
                       'int a[] = {\n#embed "x.bin"\n};\n', 'int a[] = {\n# /* c */ embed "x.bin"\n};\n',
                       'int a[] = {\n%:embed "x.bin"\n};\n', 'const char *t = __TIMESTAMP__;\n',
                       '#if __has_inc\\\nlude("x.h")\n#endif\n', '#if __has_\\ \t\ninclude("x.h")\n#endif\n',
                       '#ifdef NEVER\n\'\n#endif\n#if __has_include("x.h")\n#endif\n/* \' */\n',
                       '/* __has_include */ int x;\n',
                       # review-93's GCC 15 probes: a macro alias, pasting, a macro operand, every
                       # #embed spelling (also as a token emitter) and __has_embed's limit(0)
                       '#define H __has_include\n#if H("x.h")\n#endif\n',
                       '#define P(a) __has_##a\n#if P(include)("x.h")\n#endif\n',
                       '#define E(a) __has_##a\n#if E(embed)("x.h")\n#endif\n',
                       '#define C(a, b) a##b\n#if C(__has_, include)("x.h")\n#endif\n',
                       '#define F "x.h"\n#if __has_include(F)\n#endif\n',
                       '#embed "x.h" if_empty(was_empty) limit(0)\n',
                       '#/**/embed "x.h" prefix(sep_) limit(1)\n', '%:embed "x.h" prefix(digraph_) limit(1)\n',
                       '# \\\nembed "x.h" prefix(splice_) limit(1)\n', '#/*a*/ /*b*/ embed "x.h"\n',
                       '# /\\\n* c *\\\n/ embed "x.h"\n', '# /* c\n */ embed "x.h"\n',
                       '#if __has_embed("x.h" limit(0)) == 2\n#endif\n',
                       '#if defined(__has_builtin)\n#endif\n', 'int __has_inc;\n'):
            for relpath in ("src/08000000.c", "include/x.h"):
                with self.subTest(source=source, relpath=relpath):
                    self.assertIn("preprocessor-probe", rules(source, relpath))

    def test_probe_findings_are_on_their_line(self):
        found = plausible.check_text('int a;\n\n#if __has_inc\\\nlude("x.h")\n#endif\n', data_symbols={})
        self.assertEqual([(line, rule) for line, rule, _, _ in found], [(3, "preprocessor-probe")])

    def test_words_near_a_probe_are_not_probes(self):
        for source in ("int has_include;", "int _has_include;", "int embedded;", "#define EMBED 1",
                       "int x; /* embed */", "const char *s = \"#include\";"):
            with self.subTest(source=source):
                self.assertEqual(rules(source), [])


class CensusTree:
    """a scratch decomp tree, and plausible.py --addr on it as match.py runs it"""
    ADDRESS = 0x08000000

    def setUp(self):
        self.tree = Path(tempfile.mkdtemp(prefix="ffta_census_test_"))
        self.addCleanup(shutil.rmtree, self.tree, ignore_errors=True)
        (self.tree / "include").mkdir()
        (self.tree / "src").mkdir()
        (self.tree / "config").mkdir()
        (self.tree / "config" / "data_symbols.json").write_text("{}")
        (self.tree / "include" / "ffta.h").write_text(
            "typedef unsigned char u8;\ntypedef unsigned short u16;\ntypedef unsigned int u32;\n")

    def write(self, source, name=None, headers=None):
        for header, text in (headers or {}).items():
            (self.tree / "include" / header).write_text(text)
        path = self.tree / "src" / (name or f"{self.ADDRESS:08X}.c")
        path.write_bytes(source.encode("utf-8") if isinstance(source, str) else source)
        return path

    def linted(self):
        return sorted(str(path) for top in ("src", "include")
                      for path in (self.tree / top).rglob("*") if path.is_file())

    def run_checker(self, paths=None, addr=None):
        command = [sys.executable, str(TOOLS / "plausible.py"), "--quiet", "--addr",
                   addr or f"0x{self.ADDRESS:08X}", "--json"] + (paths or self.linted())
        result = subprocess.run(command, capture_output=True, text=True, cwd=self.tree)
        return result, json.loads(result.stdout)

    def census(self, paths=None):
        return [message for _, _, message in plausible.volatile_census(self.ADDRESS, paths or self.linted())]

    def census_rules(self, paths=None):
        return [(rule, message) for _, rule, message in
                plausible.volatile_census(self.ADDRESS, paths or self.linted())]

    def cpp_takes(self, condition):
        """does the host cpp, run as the census runs it, evaluate this #if condition as true?"""
        probe = self.tree / "src" / "cpp_probe.c"
        probe.write_text(f"#define CAT(a, b) a##b\n#if {condition}\nTAKEN\n#endif\n")
        try:
            result = subprocess.run(["cpp", "-nostdinc", "-undef", "-I", "include", "src/cpp_probe.c"],
                                    cwd=self.tree, capture_output=True, text=True)
        finally:
            probe.unlink()
        return result.returncode == 0 and "TAKEN" in result.stdout

    def refused(self, source, needle="no linted file spells", **write):
        self.write(source, **write)
        found = self.census()
        self.assertTrue(any(needle in message for message in found), found)
        return found


@unittest.skipUnless(HAVE_CPP, "the census runs cpp")
class CensusTests(CensusTree, unittest.TestCase):
    def test_lexical_qualifier_passes_and_the_contract_holds(self):
        self.write('#include "ffta.h"\nvoid f(u16 v)\n{\n    ' + COMMENT +
                   "    *(volatile u16 *)0x04000000 = v;\n}\n")
        self.assertEqual(self.census(), [])
        result, document = self.run_checker()
        self.assertEqual((result.returncode, document["total"]), (0, 0))

    def test_listed_qualifiers_in_an_included_header_pass(self):
        header = '#include "ffta.h"\n' + COMMENT + "#define STATUS (*(volatile u16 *)0x04000004)\n"
        self.write('#include "hw.h"\nvoid f(void) { while (STATUS & 1) ; }\n', headers={"hw.h": header})
        self.assertEqual(self.census(), [])

    def test_qualifiers_the_lint_cannot_read_are_refused(self):
        sources = {
            "splice": "extern vola\\\ntile u8 x;\n",
            "splice-spaces": "extern vola\\ \t\ntile u8 x;\n",
            "splice-crlf": "extern __vola\\\r\ntile__ u8 x;\n",
            "paste": "#define C(a, b) a##b\nextern C(vola, tile) u8 x;\n",
            "paste-gnu": "#define C(a, b) a##b\nextern C(__vola, tile__) u8 x;\n",
            "digraph-paste": "#define C(a, b) a%:%:b\nextern C(__vola, tile) u8 x;\n",
            "desync": "#ifdef NEVER\n'\n#endif\nextern volatile u8 x;\n/* ' */\n",
            "desync-gnu": "#ifdef NEVER\n'\n#endif\nextern __volatile__ u8 x;\n/* ' */\n",
        }
        for name, body in sources.items():
            with self.subTest(name=name):
                self.write('#include "ffta.h"\n' + body + "void f(void) { x = 1; }\n")
                found = self.census()
                self.assertTrue(any("no linted file spells" in message for message in found), found)
                result, document = self.run_checker()
                self.assertEqual(result.returncode, 1)
                self.assertIn("volatile-census", [f["rule"] for f in document["findings"]])

    def test_a_pasted_lexical_qualifier_is_refused(self):
        self.write('#include "ffta.h"\n#define P(a) a##_x\nint P(volatile);\n'
                   "extern volatile u8 y;\n")
        self.assertTrue(any("pasted" in message for message in self.census()))

    def test_a_unit_that_reads_beyond_its_text_is_refused(self):
        (self.tree / "outside.txt").write_text("")
        self.write('#include "ffta.h"\n#if __has_include("../outside.txt")\n#define Q vola##tile\n'
                   "#else\n#define Q\n#endif\nextern Q u8 x;\n")
        found = self.census()
        self.assertTrue(any("preprocessor query" in message for message in found), found)

    def test_a_typed_pointer_s_typeof_passes_only_when_its_text_check_does(self):
        # kit#375, rule P: the census admits the one typed pointer's typeof only where the pointer's
        # own text check (typed_pointer_sites) finds no problem with it
        import test_volatile_semantics as fixtures
        entry = plausible.volatile_allow_entries()[0]
        (self.tree / entry["header"]).write_text(
            fixtures.HEADER.format(declaration=entry["declaration"].replace("; ", ";\n    ")))
        symbol, header = entry["symbol"], Path(entry["header"]).name

        def typeofs(early):
            self.write(f'#include "{header}"\nvoid f(void)\n{{\n    __typeof__({symbol}) *control;\n' + early +
                       f"    control = &{symbol};\n    control->display = 1;\n}}\n")
            return [message for message in self.census() if "typeof" in message]
        self.assertEqual(typeofs(""), [])
        # used before its binding: the text check has a problem, so the census reports the typeof
        self.assertTrue(typeofs("    (void)control->display;\n"))

    def test_typeof_in_a_qualified_unit_is_refused(self):
        # `__typeof__` written out is refused by the lint's address walk (kit#357); through a macro
        # the lint reads a call, and the census sees the typeof
        self.write('#include "ffta.h"\nvoid f(void)\n{\n' + COMMENT +
                   "    __typeof__(*(volatile u16 *)0x04000000) copy = 0;\n    copy = 1;\n}\n")
        self.assertEqual([rule for _, rule, _, _ in plausible.check_file(self.tree / "src" / "08000000.c")],
                         ["volatile"])
        self.write('#include "ffta.h"\n#define TYPE_OF(x) __typeof__(x)\nvoid f(void)\n{\n' + COMMENT +
                   "    TYPE_OF(*(volatile u16 *)0x04000000) copy = 0;\n    copy = 1;\n}\n")
        self.assertEqual(plausible.check_file(self.tree / "src" / "08000000.c"), [])
        self.assertTrue(any("typeof" in message for message in self.census()))
        self.write('#include "ffta.h"\ntypeof(1) x;\n')
        self.assertEqual(self.census(), [])

    def test_unit_must_read_only_linted_files(self):
        self.write('#include "hw.h"\n', headers={"hw.h": "extern volatile unsigned char x;\n"})
        source = str(self.tree / "src" / "08000000.c")
        found = self.census([source])
        self.assertTrue(any("does not lint" in message for message in found), found)
        self.assertEqual(self.census([source, str(self.tree / "include" / "hw.h")]), [])

    def test_census_is_skipped_when_no_input_could_hold_a_qualifier(self):
        self.write('#include "ffta.h"\nint f(void) { return 1; }\n')
        with mock.patch.object(plausible, "census_run", side_effect=RuntimeError("cpp ran")):
            self.assertEqual(self.census(), [])
        (self.tree / "include" / "other.h").write_text("/* vola\\\ntile */\n")
        with mock.patch.object(plausible, "census_run", side_effect=RuntimeError("cpp ran")):
            self.assertTrue(any("could not preprocess" in message for message in self.census()))

    def test_inputs_the_run_does_not_lint_still_start_the_census(self):
        (self.tree / "src" / "local.h").write_text("extern volatile unsigned char x;\n")
        source = self.write('#include "local.h"\n')
        found = self.census([str(source)])
        self.assertTrue(any("does not lint" in message for message in found), found)
        (self.tree / "src" / "local.h").unlink()
        (self.tree / "include" / "gone.h").symlink_to(self.tree / "missing.h")
        self.write('#include "ffta.h"\nint f(void) { return 1; }\n')
        with mock.patch.object(plausible, "census_run", side_effect=RuntimeError("cpp ran")):
            self.assertTrue(any("could not read an input" in message for message in self.census([str(source)])))

    def test_the_copy_keeps_text_outside_the_qualifiers(self):
        self.write('#include "ffta.h"\nconst char *name = "caf\u00e9 \u30a2";\nvoid f(u16 v)\n{\n' + COMMENT +
                   "    *(volatile u16 *)0x04000000 = v;\n}\n")
        self.assertEqual(self.census(), [])

    def test_lone_carriage_returns_end_lines_as_cpp_ends_them(self):
        self.write('#include "ffta.h"\nvoid f(u16 v)\n{\n    // plausible: hardware register\r'
                   "    *(volatile u16 *)0x04000000 = v;\r}\r")
        self.assertEqual(plausible.check_file(self.tree / "src" / "08000000.c"), [])
        self.assertEqual(self.census(), [])

    def test_every_hint_starts_the_census(self):
        for hint in ("volatile", "__volatile", "a ## b", "%:", "??=", "??/", "vo\\\nlatile"):
            with self.subTest(hint=hint):
                self.write('#include "ffta.h"\n/* ' + hint + ' */\nint f(void) { return 1; }\n')
                with mock.patch.object(plausible, "census_run", side_effect=RuntimeError("cpp ran")):
                    self.assertTrue(self.census())

    def test_the_census_runs_match_cpp_without_importing_match(self):
        import match
        self.assertEqual(plausible.CENSUS_CPP, match.DEFAULT_CPP)
        self.write('#include "ffta.h"\nvoid f(u16 v)\n{\n' + COMMENT + "    *(volatile u16 *)0x04000000 = v;\n}\n")
        probe = ("import sys; sys.path.insert(0, sys.argv[1]); import plausible; "
                 "print(plausible.volatile_census(0x08000000, sys.argv[2:]), 'match' in sys.modules)")
        result = subprocess.run([sys.executable, "-c", probe, str(TOOLS)] + self.linted(),
                                capture_output=True, text=True, cwd=self.tree)
        self.assertEqual(result.stdout.split(), ["[]", "False"], result.stderr)
        self.write('#include "ffta.h"\nextern vola\\\ntile u8 x;\n')
        with mock.patch.dict(sys.modules, {"match": None}):
            self.assertTrue(any("no linted file spells" in message for message in self.census()))

    def test_on_windows_the_census_runs_through_match_runner(self):
        self.write('#include "ffta.h"\nextern vola\\\ntile u8 x;\n')
        calls = []

        class Runner:
            def __init__(self, cc, root=None):
                self.cc, self.root = cc, root

            def sh(self, command):
                calls.append((self.cc, Path(self.root), command))
                result = subprocess.run(command, shell=True, capture_output=True, text=True, cwd=self.root)
                if result.returncode:
                    raise RuntimeError(result.stderr)
                return result.stdout

        fake = mock.Mock(DEFAULT_CC="agbcc-for-test", Runner=Runner)
        with mock.patch.object(plausible.platform, "system", return_value="Windows"):
            with mock.patch.dict(sys.modules, {"match": fake}):
                found = self.census()
            with mock.patch.dict(sys.modules, {"match": None}):
                self.assertTrue(any("could not preprocess" in message for message in self.census()))
        self.assertTrue(any("no linted file spells" in message for message in found), found)
        self.assertEqual(len(calls), 2)
        self.assertEqual({cc for cc, _, _ in calls}, {"agbcc-for-test"})
        self.assertEqual(calls[0][1], self.tree.resolve())
        self.assertEqual(calls[1][1].name, "copy")
        self.assertTrue(all(command.startswith("cpp -nostdinc -undef -I include src/08000000.c -o ")
                            for _, _, command in calls), calls)

    def test_a_census_that_cannot_run_is_a_finding(self):
        self.write('#include "missing.h"\nextern volatile u8 x;\n')
        self.assertTrue(any("could not preprocess" in message for message in self.census()))
        # cpp reports an #error, still writes its output, and fails
        self.write('#include "ffta.h"\n#error not this one\nextern volatile u8 x;\n')
        found = self.census()
        self.assertEqual(len(found), 1, found)
        self.assertIn("could not preprocess", found[0])
        self.assertIn("not this one", found[0])

    def test_one_addressed_source_under_src(self):
        self.write("extern volatile unsigned char x;\n")
        (self.tree / "src" / "copy").mkdir()
        self.write("extern volatile unsigned char x;\n", name="copy/08000000.c")
        self.assertTrue(any("exactly one" in message for message in self.census()))
        self.assertEqual(plausible.volatile_census(self.ADDRESS, [str(self.tree / "include" / "ffta.h")]), [])
        loose = self.tree / "08000000.c"
        loose.write_text("extern vola\\\ntile unsigned char x;\n")
        self.assertEqual(plausible.volatile_census(self.ADDRESS, [str(loose)]), [])

    def test_strings_naming_the_qualifier_are_refused(self):
        # documented over-refusal: a word `volatile` the copy keeps is refused wherever it is
        self.write('#include "ffta.h"\nconst char *s = "volatile";\n')
        self.assertTrue(self.census())

    def test_checker_output_satisfies_match_plausibility_contract(self):
        import match
        self.write('#include "ffta.h"\nextern vola\\\ntile u8 x;\n')
        result, _ = self.run_checker()
        findings, allowed = match.plausibility_result(result, self.ADDRESS)
        # the rules see the split qualifier in the joined view (kit#357), the census in cpp's output
        self.assertEqual(findings, ["08000000.c:2: ERROR: volatile", "08000000.c:0: ERROR: volatile-census"])
        self.assertIsNone(allowed)
        result, document = self.run_checker(addr="zz")
        self.assertEqual(result.returncode, 1)
        self.assertEqual([f["rule"] for f in document["findings"]], ["volatile", "volatile-census"])
        self.assertIn("hexadecimal --addr", document["findings"][-1]["message"])

    def test_relative_paths_from_a_capture_directory(self):
        self.write('#include "ffta.h"\nextern vola\\\ntile u8 x;\n')
        result, document = self.run_checker(paths=["src/08000000.c", "include/ffta.h"])
        self.assertIn("volatile-census", [f["rule"] for f in document["findings"]])
        self.write('#include "ffta.h"\nvoid f(u16 v)\n{\n' + COMMENT + "    *(volatile u16 *)0x04000000 = v;\n}\n")
        result, document = self.run_checker(paths=["src/08000000.c", "include/ffta.h"])
        self.assertEqual((result.returncode, document["findings"]), (0, []))

    def test_the_copy_keeps_directories_that_hold_no_input(self):
        (self.tree / "include" / "empty").mkdir()
        (self.tree / "src" / "20101").mkdir()
        self.write('#include "../../include/empty/../ffta.h"\n' + COMMENT +
                   "#define STATUS (*(volatile u16 *)0x04000004)\nvoid w(void) { while (STATUS & 1) ; }\n",
                   name="20101/08000000.c")
        self.assertEqual(self.census(), [])


def split(word, at, splice="\\\n"):
    return word[:at] + splice + word[at:]


@unittest.skipUnless(HAVE_CPP, "the census runs cpp")
class CensusDetectionTests(CensusTree, unittest.TestCase):
    """review-93 C1: a source must not be able to tell the census copy from the tree."""

    REPROS = {
        # r1: a header the unit does not read is not in the copy
        "unread-header": ('#include "ffta.h"\n#if __has_include("other.h")\n#define FLAG_QUAL vola\\\ntile\n'
                          "#else\n#define FLAG_QUAL {marker}\n#endif\nextern FLAG_QUAL u8 gFlag;\n"
                          "void f(void)\n{{\n    gFlag = 1;\n    gFlag = 2;\n}}\n"),
        # r2: the copy sits beside the real unit's output
        "workdir": ('#include "ffta.h"\n#if __has_include("../../real.i")\n#define FLAG_QUAL {marker}\n'
                    "#else\n#define FLAG_QUAL vola\\\ntile\n#endif\nextern FLAG_QUAL u8 gFlag;\n"
                    "void f(void) {{ gFlag = 1; gFlag = 2; }}\n"),
        # r3: the real branch's plain qualifier hidden by the #129 desync
        "desync": ('#include "ffta.h"\n#ifdef NEVER_DEFINED\n\'\n#endif\n#if __has_include("other.h")\n'
                   "#define FLAG_QUAL volatile\n#else\n#define FLAG_QUAL {marker}\n#endif\n/* ' */\n"
                   "extern FLAG_QUAL u8 gFlag;\nvoid f(void) {{ gFlag = 1; gFlag = 2; }}\n"),
        # the end-to-end 080ED308 header
        "listed-header": ('#include "ffta.h"\n#if __has_include("control_flags.h")\n#define BLEND_QUAL vola\\\n'
                          "tile\n#else\n#define BLEND_QUAL {marker}\n#endif\n"
                          "typedef struct __attribute__((packed)) {{ BLEND_QUAL u8 eva : 8; BLEND_QUAL u8 evb : 8; }}"
                          " BlendLine;\nvoid f(BlendLine *l) {{ l->eva = 0; l->evb = 16; }}\n"),
        # the copy branch pastes the marker (`__q0##____`)
        "pasted-marker": ('#include "ffta.h"\n#define CAT(a, b) a##b\n#if __has_include("other.h")\n'
                          "#define FLAG_QUAL vola\\\ntile\n#else\n#define FLAG_QUAL CAT(__q0, ____)\n#endif\n"
                          "extern FLAG_QUAL u8 gFlag;\n"),
    }

    def setUp(self):
        super().setUp()
        (self.tree / "include" / "other.h").write_text("/* not read by the unit */\n")
        (self.tree / "include" / "control_flags.h").write_text("extern volatile unsigned char cf;\n")

    def test_the_review_repros_are_refused(self):
        # the markers the source guesses: review-93's fixed one, and a random draw
        for marker in ("__q0____", plausible.census_markers([])["volatile"]):
            for name, source in self.REPROS.items():
                with self.subTest(name=name, marker=marker):
                    found = self.refused(source.format(marker=marker), "preprocessor query")
                    result, document = self.run_checker()
                    self.assertEqual(result.returncode, 1)
                    rules_found = {f["rule"] for f in document["findings"]}
                    self.assertIn("preprocessor-probe", rules_found)
                    self.assertIn("volatile-census", rules_found)

    def test_the_random_markers_refuse_a_probe_no_scan_can_see(self):
        # review-93 delta: pasting builds a query the probe rule cannot see; the
        # copy takes the other branch, and cannot spell the marker the census draws
        probes = ("CAT(__ha, s_include)(\"other.h\")", "CAT(__h, as_include)(\"control_flags.h\")")
        for probe in probes:
            if not self.cpp_takes(probe):
                self.skipTest("the host cpp does not evaluate a pasted __has_include")
        guesses = ("", "__q0____", "CAT(__q0, ____)", plausible.census_markers([])["volatile"])
        for paste in ("a##b", "a %:%: b"):
            for probe in probes:
                for guess in guesses:
                    source = (f'#include "ffta.h"\n#define CAT(a, b) {paste}\n#if {probe}\n'
                              "#define FLAG_QUAL vola\\\ntile\n#else\n"
                              f"#define FLAG_QUAL {guess}\n#endif\nextern FLAG_QUAL u8 gFlag;\n"
                              "void f(void) { gFlag = 1; gFlag = 2; }\n")
                    with self.subTest(paste=paste, probe=probe, guess=guess):
                        self.write(source)
                        result, document = self.run_checker()
                        found = {(f["rule"], f["message"]) for f in document["findings"]}
                        self.assertEqual(result.returncode, 1)
                        self.assertNotIn("preprocessor-probe", {rule for rule, _ in found})
                        self.assertTrue(any(rule == "volatile-census" and "changes when only its linted "
                                            "qualifiers are renamed" in message for rule, message in found),
                                        found)

    def test_the_review_repros_are_refused_by_the_markers_alone(self):
        # with the probe rule switched off, the census still refuses every repro
        with mock.patch.object(plausible, "preprocessor_probes", return_value=[]):
            for marker in ("__q0____", plausible.census_markers([])["volatile"]):
                for name, source in self.REPROS.items():
                    with self.subTest(name=name, marker=marker):
                        self.refused(source.format(marker=marker), "changes when only its linted qualifiers")

    def test_a_guessed_marker_cannot_stand_in_for_a_hidden_qualifier(self):
        # without a probe both runs take the same branch: the hidden qualifier is
        # in the real unit and the copy alike, and no guess maps back to it
        for marker in ("__q0____", "__mkaaaa"):
            with self.subTest(marker=marker):
                self.refused('#include "ffta.h"\nextern vola\\\ntile u8 a;\nextern ' + marker + " u8 b;\n")

    def test_one_file_under_two_names_is_refused(self):
        (self.tree / "include" / "alias.h").symlink_to(self.tree / "include" / "control_flags.h")
        self.refused('#include "control_flags.h"\n#include "alias.h"\n', "one file under two names")
        (self.tree / "include" / "alias.h").unlink()
        os.link(self.tree / "include" / "control_flags.h", self.tree / "include" / "alias.h")
        self.refused('#include "control_flags.h"\n#include "alias.h"\n', "one file under two names")

    def test_a_header_read_through_a_symlink_keeps_its_name(self):
        (self.tree / "include" / "real_hw.h").write_text(
            COMMENT + "#define STATUS (*(volatile u16 *)0x04000004)\n")
        (self.tree / "include" / "hw.h").symlink_to(self.tree / "include" / "real_hw.h")
        self.write('#include "ffta.h"\n#include "hw.h"\nvoid w(void) { while (STATUS & 1) ; }\n')
        self.assertEqual(self.census(), [])

    def test_markers_avoid_every_input_and_the_real_unit(self):
        self.write('#include "ffta.h"\n/* sp\\\nlit */ extern volatile u8 x;\n',
                   headers={"extra.h": "int unused;\n"})
        seen = []
        real = plausible.census_markers
        with mock.patch.object(plausible, "census_markers",
                               side_effect=lambda forbidden: seen.append(forbidden) or real(forbidden)):
            self.assertEqual(self.census(), [])
        (forbidden,) = seen
        self.assertTrue(any("/* sp\\\nlit */" in text for text in forbidden))
        self.assertTrue(any("/*split*/" in text for text in forbidden))
        self.assertTrue(any("int unused;" in text for text in forbidden))
        self.assertTrue(any(text.startswith("# 0 ") and "extern volatile" in text for text in forbidden))

    def test_a_linted_file_outside_the_tree_is_refused_and_left_alone(self):
        outside = Path(tempfile.mkdtemp(prefix="ffta_census_outside_"))
        self.addCleanup(shutil.rmtree, outside, ignore_errors=True)
        header = outside / "outside.h"
        header.write_text("extern volatile unsigned char x;\n")
        for include in (str(header), os.path.relpath(header, self.tree / "src")):
            with self.subTest(include=include):
                self.write('#include "' + include + '"\n')
                found = self.census(self.linted() + [str(header)])
                self.assertTrue(any("outside its tree" in message for message in found), found)
                self.assertEqual(header.read_text(), "extern volatile unsigned char x;\n")

    def test_the_copy_keeps_each_name_the_unit_reads(self):
        (self.tree / "include" / "sub").mkdir()
        (self.tree / "include" / "sub" / "hw.h").write_text(
            COMMENT + "#define STATUS (*(volatile u16 *)0x04000004)\n")
        self.write('#include "ffta.h"\n#include "../include/sub/../sub/hw.h"\n'
                   "void w(void) { while (STATUS & 1) ; }\n")
        self.assertEqual(self.census(), [])


@unittest.skipUnless(HAVE_CPP, "the census runs cpp")
class CensusSpliceTests(CensusTree, unittest.TestCase):
    """the 2026-11-13 reviews' splice and NUL cases, refused through the census"""

    def test_issue_repros_are_refused(self):
        for source in ("vola\\\ntile int x;\nvoid f(void){ x = 1; }\n",
                       "__vola\\\ntile__ int x;\nvoid f(void){ x = 1; }\n",
                       "#define V __vola\\\ntile\nV int x;\nvoid f(void){ x = 1; }\n",
                       "/* x *\\\n/ volatile int y; /* */\n"):
            with self.subTest(source=source):
                self.refused(source)

    def test_every_spelling_split_anywhere_is_refused(self):
        for spelling in SPELLINGS:
            for at in range(1, len(spelling)):
                for splice in ("\\\n", "\\ \t\n", "\\\r\n", "\\\0\n"):
                    with self.subTest(spelling=spelling, at=at, splice=splice):
                        # a split that leaves a shorter spelling whole (`__volatile` then
                        # `__`) is a lint-visible qualifier, renamed, and pasted by cpp
                        self.refused("extern " + split(spelling, at, splice) + " unsigned char g;\n",
                                     "" if spelling[:at] in SPELLINGS or spelling[at:] in SPELLINGS
                                     else "no linted file spells")

    def test_every_form_in_a_source_and_a_header_is_refused(self):
        forms = ("{w} unsigned char local;", "extern {w} unsigned char g;",
                 "unsigned char *p = ({w} unsigned char *)0x02000000;", "#define V {w}\nV unsigned char x;",
                 "typedef {w} unsigned char vu8;", "struct S {{ {w} unsigned char a; }};")
        for spelling in SPELLINGS:
            for form in forms:
                text = form.format(w=split(spelling, 4)) + "\n"
                with self.subTest(spelling=spelling, form=form, where="source"):
                    self.refused(text)
                with self.subTest(spelling=spelling, form=form, where="header"):
                    self.refused('#include "spliced.h"\n', headers={"spliced.h": text})

    def test_nul_splices_are_refused(self):
        for spelling in SPELLINGS:
            for splice in ("\\\0\n", "\\ \0\n", "\\\0 \n", "\\\0\0\n", "\\\t\0\f\n", "\\\0\r\n"):
                word = split(spelling, 4, splice)
                self.assertRegex(plausible.join_splices(word), r"^" + plausible.VOLATILE + r"$")
                with self.subTest(spelling=spelling, splice=splice):
                    self.refused("extern " + word + " unsigned char g;\n")
        self.refused("/* x *\\\0\n/ volatile int y; /* */\n")

    def test_the_shipped_entry_respelt_or_spliced_is_refused_through_the_cli(self):
        # review repro: src/08028C34.c declares the allowlisted object itself,
        # each qualifier respelt or split, and does not include the header
        shipped = plausible.volatile_allow_entries()[0]
        (self.tree / "config" / "data_symbols.json").write_text(
            json.dumps({shipped["symbol"]: shipped["address"]}))
        header = self.tree / shipped["header"]
        header.write_text(shipped["declaration"] + "\n")
        self.assertEqual(plausible.check_file(header), [])
        body = ("\nvoid func_08028C34(void)\n{\n    " + shipped["symbol"] + ".winin_hi = 0x13;\n"
                "    " + shipped["symbol"] + ".display |= 0x4000;\n}\n")
        cases = [(spelling, "") for spelling in GNU] + [(spelling, splice) for spelling in SPELLINGS
                                                       for splice in ("\\\n", "\\\0\n")]
        for spelling, splice in cases:
            word = split(spelling, 4, splice) if splice else spelling
            respelt = shipped["declaration"].replace("volatile", word)
            source = self.tree / "src" / "08028C34.c"
            source.write_text("#include \"ffta.h\"\n" + respelt.replace("; ", ";\n") + "\n" + body)
            with self.subTest(spelling=spelling, splice=splice):
                command = [sys.executable, str(TOOLS / "plausible.py"), "--quiet", "--addr", "0x08028C34",
                           "--json"] + self.linted()
                result = subprocess.run(command, capture_output=True, text=True, cwd=self.tree)
                found = {f["rule"] for f in json.loads(result.stdout)["findings"]}
                self.assertEqual(result.returncode, 1)
                self.assertIn("volatile" if not splice else "volatile-census", found)
                header.write_text(respelt + "\n")
                header_rules = [rule for _, rule, _, _ in plausible.check_file(header)]
                self.assertIn("volatile-allowlist", header_rules)
                if not splice:
                    self.assertIn("volatile", header_rules)
                header.write_text(shipped["declaration"] + "\n")


@unittest.skipUnless(HAVE_CPP, "the census runs cpp")
class CensusAsmTests(CensusTree, unittest.TestCase):
    """an asm keyword anywhere in the unit's code is inline asm, however cpp made it (review-93 delta)"""

    HIDDEN = ('void f(void) { __a\\\nsm("nop"); }\n', 'void f(void) { a\\\nsm ("nop"); }\n',
              'void f(void) { x = 1; __as\\ \t\nm__ ("" ::: "memory"); x = 2; }\n',
              '#define CAT(a, b) a##b\nvoid f(void) { CAT(__as, m)("nop"); }\n',
              '#define CAT(a, b) a %:%: b\nvoid f(void) { CAT(__as, m__) ("nop"); }\n',
              '#define CAT(a, b) a##b\nvoid f(void) { register int r CAT(a, sm)("r4"); }\n')

    def test_asm_the_rules_cannot_read_is_refused(self):
        for source in self.HIDDEN:
            with self.subTest(source=source):
                # since kit#357 the rules see a spliced keyword in the joined view; a pasted one
                # only the census can see
                self.assertEqual(rules(source), ["inline-asm"] if "##" not in source and "%:" not in source
                                 else [])
                self.write(source)
                found = self.census_rules()
                self.assertEqual(len(found), 1, found)
                self.assertEqual(found[0][0], "inline-asm")
                self.assertIn("inline asm", found[0][1])

    def test_asm_hidden_in_a_header_is_refused_through_the_cli(self):
        self.write('#include "ffta.h"\n#include "barrier.h"\nvoid f(int *x) { *x = 1; BARRIER(); *x = 2; }\n',
                   headers={"barrier.h": '#define BARRIER() __a\\\nsm volatile ("" ::: "memory")\n'})
        result, document = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertIn(("inline-asm", 0), {(f["rule"], f["line"]) for f in document["findings"]})

    def test_a_literal_that_runs_past_its_line_is_refused(self):
        # review-93 delta 2 (r7): cpp ends an unterminated literal at the newline and only
        # warns, but cc1 reads on, so `"); a\sm(...)` is code to agbcc
        for quote in ('"', "'"):
            source = ('#include "ffta.h"\nextern u8 gFlag;\nvoid f(void)\n{\n    gFlag = 1;\n'
                      f"    (void)sizeof({quote}x\n{quote}); a\\\nsm(\"\" ::: \"memory\");\n"
                      "    gFlag = 2;\n}\n")
            with self.subTest(quote=quote):
                self.write(source)
                found = self.census_rules()
                self.assertEqual(len(found), 1, found)
                self.assertEqual(found[0][0], "multiline-literal")
                self.assertIn("runs past the end of its line", found[0][1])
                result, document = self.run_checker()
                self.assertEqual(result.returncode, 1)
                self.assertIn(("multiline-literal", 0), [(f["rule"], f["line"]) for f in document["findings"]])
        for text in ('const char *s = "x\\\" asm";\n', "char c = '\\'', d = '\\\\';\n",
                     'const char *t = "a\\\\";\n'):
            with self.subTest(text=text):
                self.write('#include "ffta.h"\n#define CAT(a, b) a##b\n' + text)
                self.assertEqual(self.census_rules(), [])

    def test_the_080318d0_barrier_behind_a_multiline_literal_is_refused(self):
        # review-93's end-to-end case: a matched function with a compiler barrier hidden
        # behind a literal that runs past its line, checked as match.py checks it
        self.ADDRESS = 0x080318D0
        barrier = '    (void)sizeof("x\n"); a\\\nsm("" ::: "memory");\n'
        source = ('#include "ffta.h"\n\nextern void func_08031708(u8 value);\n\nvoid func_080318D0(void)\n{\n'
                  "%s    func_08031708(0x50);\n}\n")
        self.write(source % "")
        result, document = self.run_checker()
        self.assertEqual((result.returncode, document["findings"]), (0, []))
        self.write(source % barrier)
        result, document = self.run_checker()
        self.assertEqual(result.returncode, 1)
        self.assertIn("multiline-literal", [f["rule"] for f in document["findings"]])
        self.write(source % '    a\\\nsm("" ::: "memory");\n')
        result, document = self.run_checker()
        self.assertIn(("inline-asm", 0), [(f["rule"], f["line"]) for f in document["findings"]])

    def test_words_and_literals_are_not_asm(self):
        self.write('#include "ffta.h"\n#define CAT(a, b) a##b\nconst char *s = "asm";\n'
                   "const char *t = \"as\\\nm __asm__\";\nchar c = 'a';\nint hand_asm_count, __asm_y, x$asm;\n"
                   "int CAT(as, my);\nconst char *u = \"q\\\" asm\";\nchar d = '\\'', e = 'asm';\n")
        self.assertEqual(self.census_rules(), [])

    def test_lint_visible_asm_is_refused_by_both(self):
        self.write('void f(void) { __asm("nop"); }\n')
        result, document = self.run_checker()
        self.assertEqual({f["rule"] for f in document["findings"]}, {"inline-asm"})
        self.assertEqual(sorted(f["line"] for f in document["findings"]), [0, 1])


class NulByteTests(unittest.TestCase):
    """cpp reads NUL as whitespace, also between a backslash and the newline."""

    def test_a_nul_byte_is_refused_anywhere(self):
        for source in ("int x;\0\n", "int\0x;\n", "/* \0 */ int x;\n", "// \0\nint x;\n",
                       'const char *s = "\0";\n', "#define A \0\n"):
            for relpath in ("src/08000000.c", "include/x.h"):
                with self.subTest(source=source, relpath=relpath):
                    self.assertEqual(rules(source, relpath), ["nul-byte"])
        self.assertEqual([(line, rule) for line, rule, _, _ in plausible.check_text(
            "int a;\nint b;\0\n", data_symbols={})], [(2, "nul-byte")])

    def test_a_nul_byte_splices_like_whitespace(self):
        for splice in ("\\\0\n", "\\ \0\n", "\\\0 \n", "\\\0\0\n", "\\\t\0\f\n", "\\\0\r\n"):
            with self.subTest(splice=splice):
                self.assertEqual(plausible.join_splices("a" + splice + "b"), "ab")

    def test_the_allowlist_refuses_nul_with_the_other_control_characters(self):
        findings = plausible.check_text('#include "control_flags.h"\nint x;\0\n', data_symbols={SYMBOL: "0x03000940"},
                                        relpath="src/08000000.c", volatile_allow=[ENTRY])
        self.assertTrue(any(rule == "volatile-allowlist" and "NUL" in message
                            for _, rule, _, message in findings), findings)
        self.assertIn("nul-byte", [rule for _, rule, _, _ in findings])


class SpliceExemptionTests(unittest.TestCase):
    """an exemption holds only where it holds both as written and as cpp reads it"""

    DMA = {"data_040000D4": "0x040000D4"}
    BOUND = ("typedef struct { unsigned control; } R;\nextern R data_040000D4;\nextern R ram_obj;\n"
             "void f(void)\n{\n    /* plausible: DMA3 MMIO requires volatile writes. */\n"
             "    volatile R *dma = &data_040000D4;\n%s\n    dma->control = 1;\n"
             "    dma->control = 2;\n}\n")

    def test_a_spliced_retarget_or_escape_of_a_bound_pointer_is_refused(self):
        self.assertEqual(rules(self.BOUND % "", mapping=self.DMA), [])
        for body in ("    dma = &ram_obj;", "    d\\\nma = &ram_obj;", "    g(d\\\nma);",
                     "    d\\\nma++;", "    d\\\nma = d\\\nma;", "    dm\\\0\na = &ram_obj;",
                     # cpp ends the comment at `*\<newline>/`, so the retarget is code
                     "    /* note *\\\n/ dma = &ram_obj; /* end */",
                     # cpp continues the `//` comment over the binding's tail
                     "    // x \\\n    ; dma = &ram_obj;"):
            with self.subTest(body=body):
                self.assertIn("volatile", rules(self.BOUND % body, mapping=self.DMA))
        hidden = self.BOUND.replace("    volatile R *dma = &data_040000D4;\n",
                                    "    volatile R *dma = &data_040000D4; // x \\\n    ; dma = &ram_obj;\n")
        self.assertIn("volatile", rules(hidden % "", mapping=self.DMA))

    def test_an_exemption_both_views_see_is_kept(self):
        macro = "#define M(x) \\\n    ((x) + 1)\n"
        self.assertEqual(rules(macro + COMMENT + "*(volatile u16 *)0x04000000 = v;\n"), [])
        self.assertEqual(rules(macro + "volatile int x;\n"), ["volatile"])
        self.assertEqual(rules("#define M(x) do { \\\n    f(x); \\\n} while (0)\n"), [])

    def test_a_statement_macro_exemption_needs_both_views(self):
        # `/\<newline>*` opens a comment only for cpp: the `#define` the
        # unjoined scan sees is inside it, and the do/while(0) is a statement
        statement = ("extern int y;\nvoid f(void)\n{\n    do {\n/\\\n*\n"
                     "#define M do { */ y = 1; } while (0);\n}\n")
        self.assertEqual(rules(statement), ["dead-code"])
        macro = "#define SET(p, v) do { \\\n    (p)->control = (v); \\\n} while (0)\n"
        self.assertEqual(rules(macro + self.BOUND % "", mapping=self.DMA), [])
        self.assertEqual(rules(macro + "void g(R *r) { SET(r, 3); }\n"), [])

    def test_a_splice_anywhere_ends_the_polling_exemption(self):
        polling = (COMMENT + "#define STATUS (*(volatile u16 *)0x04000004)\n%s"
                   "void wait(void) { while (STATUS & 1) {} }\n")
        self.assertEqual(rules(polling % ""), [])
        for extra in ("// note \\\n\n", "/* \\\n */\n", "#define M(x) \\\n    (x)\n"):
            with self.subTest(extra=extra):
                self.assertIn("empty-body", rules(polling % extra))
        text = polling % "// note \\\n\n"
        code = plausible.strip_comments_and_strings(text)
        self.assertTrue(plausible.hardware_polling_bodies(code, set(range(len(code)))))
        self.assertEqual(plausible.hardware_polling_bodies(code, set(range(len(code))), text), set())

    def test_one_token_split_by_a_splice_is_one_finding(self):
        for source, rule in (('void f(void) { __\\\nasm ("nop"); }\n', "inline-asm"),
                             ("__\\\nvolatile int x;\n", "volatile")):
            with self.subTest(source=source):
                self.assertEqual(rules(source), [rule])


class ProvenanceShapeTests(unittest.TestCase):
    """the 2026-11-13 second review: bodies after attributes or a tag, nested abstract pointers"""
    QUALIFIERS = ("const", "__const", "__const__") + SPELLINGS + (
        "restrict", "__restrict", "__restrict__", "signed", "__signed", "__signed__", "unsigned", "__extension__")

    def provenance(self, code):
        return plausible.member_provenance("void f(void) { " + code + " x = " + SYMBOL + ".unknown_3C; }", ENTRY)

    def test_every_qualifier_spelling_is_skipped(self):
        for qualifier in self.QUALIFIERS:
            for code in ("q = (" + qualifier + " struct { u8 b[2]; } *)p;",
                         "q = (" + qualifier + " union { u8 b[2]; } *)p;",
                         "q = (const " + qualifier + " struct { u8 b[2]; } *)p;",
                         "f = (void (* " + qualifier + ")(void))p;",
                         "f = (void (* const " + qualifier + ")(void))p;"):
                with self.subTest(code=code):
                    self.assertTrue(self.provenance(code))

    def test_plain_casts_are_not_provenance_findings(self):
        for qualifier in self.QUALIFIERS:
            with self.subTest(qualifier=qualifier):
                self.assertEqual(self.provenance("q = (" + qualifier + " u8 *)p;"), [])
        for code in ("q = (struct T *)p;", "n = sizeof (struct T);", "t = (struct T){ 0 };", "q = (union U *)p;"):
            with self.subTest(code=code):
                self.assertEqual(self.provenance(code), [])
        self.assertEqual(plausible.member_provenance("void g(struct T *t) { x = " + SYMBOL + ".unknown_3C; }",
                                                     ENTRY), [])

    def test_attributed_bodies_and_nested_pointers_are_provenance_findings(self):
        for code in ("q = (struct __attribute__((packed)) { u8 b[2]; } *)p;",
                     "q = (struct __attribute__((packed)) T { u8 b[2]; } *)p;",
                     "q = (union __attribute ((aligned(4))) { u8 b[2]; } *)p;",
                     "q = (const struct __attribute__((packed)) { u8 b[2]; } *)p;",
                     "x = (**(u8 (**)[4])p)[1];", "x = (**(u8 (* const *)[4])p)[1];",
                     "f = (void (**)(void))p;"):
            with self.subTest(code=code):
                self.assertTrue(self.provenance(code))



class SharedCppOptionsTests(CensusTree, unittest.TestCase):
    """every compile match.py runs for a report preprocesses with the census's options (plausible.CPP_OPTIONS)"""
    SOURCE = "src/08000000.c"
    OAM_OWNER = 0x08001244
    # the ordered OAM list context reads its predecessors first, the census does not: the one known difference
    OAM_INCLUDES = {(0x0800105C, 0x08001194): "-include src/0800105C.c -include src/08001194.c ",
                    (0x08001194,): "-include src/08001194.c "}

    class Stop(Exception):
        pass

    def first_command(self, compile_object, address, source, **options):
        """the first command compile_object hands its runner, without TMPDIR and the output"""
        import match
        commands = []

        def sh(command):
            commands.append(command)
            raise self.Stop

        with self.assertRaises(self.Stop):
            compile_object(mock.Mock(sh=sh), "build/work", mock.Mock(cpp=match.DEFAULT_CPP), self.tree,
                           address, source, **options)
        self.assertEqual(len(commands), 1)
        prefix, suffix = "export TMPDIR=build/work; ", " -o build/work/f.i"
        self.assertTrue(commands[0].startswith(prefix) and commands[0].endswith(suffix), commands)
        return commands[0][len(prefix):-len(suffix)]

    def compile_commands(self):
        """{context: (address, cpp command)} for every compile of a report, less the OAM -include options"""
        import match
        import switch_placement
        commands = {}
        for thumb in (True, False):
            commands[f"match.compile_object thumb={thumb}"] = (
                self.ADDRESS, self.first_command(match.compile_object, self.ADDRESS, self.SOURCE, thumb=thumb))
        commands["switch_placement.compile_object"] = (
            self.ADDRESS, self.first_command(switch_placement.compile_object, self.ADDRESS, self.SOURCE))
        for prefix, includes in self.OAM_INCLUDES.items():
            command = self.first_command(match.compile_object, self.OAM_OWNER, f"src/{self.OAM_OWNER:08X}.c",
                                         oam_prefix=prefix)
            before, found, after = command.partition(includes)
            self.assertEqual(found, includes, command)
            label = " ".join(f"{member:08X}" for member in prefix)
            commands[f"match.compile_object oam_prefix={label}"] = (self.OAM_OWNER, before + after)
        return commands

    def census_command(self, address):
        """the preprocessor command the census runs on the addressed source, without the output"""
        self.write('#include "ffta.h"\nextern volatile u8 x;\n', name=f"{address:08X}.c")
        commands = []

        def run(command, root):
            commands.append(command)
            raise RuntimeError("stopped before cpp")

        with mock.patch.object(plausible, "census_run", side_effect=run):
            found = [message for _, _, message in plausible.volatile_census(address, self.linted())]
        self.assertTrue(any("could not preprocess" in message for message in found), found)
        self.assertEqual(len(commands), 1)
        command, output = commands[0].rsplit(" -o ", 1)
        self.assertRegex(output, r"\Abuild/ffta_census_[^/ ]+/real\.i\Z")
        return command

    def test_every_compile_and_the_census_run_the_same_command(self):
        for context, (address, command) in self.compile_commands().items():
            with self.subTest(context=context):
                self.assertEqual(command, f"cpp -nostdinc -undef -I include src/{address:08X}.c")
                self.assertEqual(self.census_command(address), command)

    def test_an_option_added_to_the_shared_string_reaches_every_command(self):
        self.compile_commands()  # match.py and switch_placement.py are imported before the string changes
        options = plausible.CPP_OPTIONS + " -DADDED_OPTION"
        with mock.patch.object(plausible, "CPP_OPTIONS", options):
            for context, (address, command) in self.compile_commands().items():
                with self.subTest(context=context):
                    self.assertEqual(command, f"cpp {options} src/{address:08X}.c")
                    self.assertEqual(self.census_command(address), command)


if __name__ == "__main__":
    unittest.main()
