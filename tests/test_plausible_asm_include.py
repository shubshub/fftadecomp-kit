"""The asm-include rule refuses an included assembly file.

It used to match the code view, where string literals are blanked, so the
quoted file name never reached it and the rule never fired.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible


def rules(source, relpath=None):
    return [rule for _, rule, _, _ in plausible.check_text(source, data_symbols={}, relpath=relpath,
                                                           volatile_allow=[])]


class AsmIncludeTests(unittest.TestCase):
    def test_an_included_assembly_file_is_refused(self):
        for source in ('#include "x.s"\n', '#include "x.S"\n', '#  include "sub/x.s"\n', '  #include<x.s>\n',
                       '#include <sub/x.S>\n', 'int a;\n#include "x.s" /* note */\nint b;\n',
                       'void f(void)\n{\n#include "body.s"\n}\n'):
            for relpath in ("src/08000000.c", "include/x.h"):
                with self.subTest(source=source, relpath=relpath):
                    self.assertEqual(rules(source, relpath), ["asm-include"])

    def test_the_finding_is_on_the_directive_line(self):
        found = plausible.check_text('int a;\n\n#include "x.s"\n', data_symbols={}, volatile_allow=[])
        self.assertEqual([(line, rule) for line, rule, _, _ in found], [(3, "asm-include")])

    def test_other_includes_and_text_are_not_refused(self):
        for source in ('#include "x.h"\n', '#include <ffta.h>\n', '#include "x.sh"\n', '#include "x.c"\n',
                       '/* #include "x.s" */\nint a;\n', '// #include "x.s"\nint a;\n',
                       'const char *s = "#include \\"x.s\\"";\n', 'const char *s = "#include <x.s>";\n',
                       '#define NAME "x.s"\n'):
            with self.subTest(source=source):
                self.assertEqual(rules(source), [])

    def test_a_directive_split_by_a_splice_is_refused(self):
        self.assertEqual(rules('#include "x.\\\ns"\n'), ["asm-include"])
        self.assertEqual(rules('#inc\\\nlude "x.s"\n'), ["asm-include"])


if __name__ == "__main__":
    unittest.main()
