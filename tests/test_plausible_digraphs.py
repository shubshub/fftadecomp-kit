"""Kit#408: a directive spelt with the `%:` digraph meets every rule its `#` spelling meets.

cpp and agbcc read the C94 digraphs: `%:` is `#`, `%:%:` is `##`, `<%` `%>`
are braces and `<:` `:>` are brackets.  The rules read the code with each
digraph spelt as the token it stands for, keeping offsets, and leave literals
as they are.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import plausible


def rules(source):
    return [(line, rule) for line, rule, _, _ in plausible.check_text(source, data_symbols={}, volatile_allow=[])]


class DigraphDirectiveTests(unittest.TestCase):
    # the issue's table: each directive refused in its `#` spelling, and now in its `%:` spelling
    TABLE = (
        ("%:if 0\nint dead;\n%:endif\n", "dead-code"),
        ('%:pragma GCC diagnostic ignored "-Wall"\n', "no-standard-errors"),
        ("%:pragma pack(1)\n", "pragma-pack"),
        ('%:include "x.s"\n', "asm-include"),
    )

    def test_each_directive_meets_its_rule(self):
        for source, rule in self.TABLE:
            with self.subTest(source=source):
                self.assertIn((1, rule), rules(source))
                self.assertIn((1, rule), rules(source.replace("%:", "#")))

    def test_spacing_and_splices(self):
        for source, rule in (("  %:  if 0\nint dead;\n%:endif\n", "dead-code"),
                             ("%\\\n:if 0\nint dead;\n%:endif\n", "dead-code"),
                             ("%:\\\ninclude <x.S>\n", "asm-include")):
            with self.subTest(source=source):
                self.assertIn(rule, [found for _, found in rules(source)])

    def test_brackets_are_read_as_brackets(self):
        self.assertIn("empty-body", [rule for _, rule in rules("void f(void) <% %>\n")])
        self.assertEqual(plausible.spell_digraphs("a<:1:> <%b%> %:%:%:"), "a[ 1 ] { b } ##  # ")

    def test_literals_and_comments_are_left_alone(self):
        for source in ('const char *s = "%:include \\"x.s\\"";\n', "/* %:if 0 */\nint x;\n",
                       "char c = '%'; int x = c<:0:>;\n", '#include "a%:b.h"\n'):
            with self.subTest(source=source):
                self.assertEqual(rules(source), [])
        code = plausible.strip_comments_and_strings('x = "<%"; y <: 0 :>;\n')
        literals = plausible.spell_digraphs(code, plausible.strip_comments_and_strings_keep_strings(
            'x = "<%"; y <: 0 :>;\n'))
        self.assertEqual(literals, 'x = "<%"; y [  0  ];\n')


if __name__ == "__main__":
    unittest.main()
