"""Calls through typed function-pointer objects (`bl _call_via_rN`) in the
allowlisted volatile semantic check: the prototype is the pointer object's
declared type, and the call stays an opaque ordered barrier."""
import os
import shutil
import sys
import tempfile
import json
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import plausible
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

SYMBOL = fixtures.SYMBOL
TYPEDEF = 'typedef void (*Callback)(void *, u32);\nextern Callback g_cb[];\n'


def source(declarations=TYPEDEF, call='g_cb[0](0, 5);'):
    return declarations + 'void func_08028C34(void)\n{\n    ' + call + '\n}\n'


def assembly(*body):
    """agbcc-shaped output whose pool holds the object and the pointer table"""
    return fixtures.assembly(*body).replace(
        f'.word\t{SYMBOL}\n', f'.word\t{SYMBOL}\n\t.word\tg_cb\n')


# `sym.unknown_3C = 0; g_cb[0](0, 5);` with its dead read-modify-write load
STORE = ('ldr\tr3, .L3', 'add\tr3, r3, #60', 'ldrb\tr1, [r3]', 'mov\tr1, #0', 'strb\tr1, [r3]')
CALL = ('ldr\tr2, .L3+4', 'ldr\tr2, [r2]', 'mov\tr0, #0', 'mov\tr1, #5', 'bl\t_call_via_r2')
REAL = assembly('push\t{lr}', *STORE, *CALL, 'pop\t{r0}', 'bx\tr0')
STRIPPED = REAL.replace('ldrb\tr1, [r3]\n\t', '')


def compare(real=REAL, stripped=STRIPPED, preprocessed=None):
    return semantics._compare_compiles(real, stripped, preprocessed or source(), SYMBOL,
                                       fixtures.DECLARATION)


class SignatureTests(unittest.TestCase):
    def signature(self, text):
        code = plausible.strip_comments_and_strings(text)
        return semantics.indirect_signature(code, semantics.file_scope(text), 'g_cb')

    def test_declared_prototypes_are_read(self):
        for declarations, call, expected in (
                (TYPEDEF, 'g_cb[0](0, 5);', (False, 2, 0)),
                ('typedef void (*Callback)(void *, u32);\nextern Callback const g_cb[4];\n',
                 'g_cb[3](0, 5);', (False, 2, 4)),
                ('extern void (*g_cb[])(void *, u32);\n', 'g_cb[0x0](0, 5);', (False, 2, 0)),
                ('extern int (*const g_cb[2])(void);\n', 'g_cb[1]();', (True, 0, 2)),
                ('extern void (*g_cb)(u8 *, u16, int);\n', 'g_cb(0, 1, (2, 3));', (False, 3, None)),
                ('typedef u32 (*Callback)(void *, u32, u32, u32, u32);\nextern Callback g_cb[];\n',
                 'g_cb[0](0, 1, 2, 3, 4);', (True, 5, 0))):
            with self.subTest(declarations=declarations):
                self.assertEqual(self.signature(source(declarations, call)), expected)

    def test_unprototyped_and_variadic_pointers_are_refused(self):
        for declarations, call in (
                ('typedef void (*Callback)();\nextern Callback g_cb[];\n', 'g_cb[0](0, 5);'),
                ('extern void (*g_cb[])();\n', 'g_cb[0](0, 5);'),
                ('typedef void (*Callback)(void *, ...);\nextern Callback g_cb[];\n', 'g_cb[0](0, 5);'),
                ('extern void (*g_cb[])(void *, ...);\n', 'g_cb[0](0, 5);'),
                ('typedef void (*Callback)(long long);\nextern Callback g_cb[];\n', 'g_cb[0](0);'),
                ('extern void *g_cb[];\n', 'g_cb[0](0, 5);'),
                ('', 'g_cb[0](0, 5);')):
            with self.subTest(declarations=declarations):
                self.assertIsInstance(self.signature(source(declarations, call)), str)

    def test_every_use_must_be_a_direct_call_through_the_declared_type(self):
        for call, reason in (
                ('((void (*)(int, int, int))g_cb[0])(0, 5, 6);', 'other than as a direct call'),
                ('(*g_cb[0])(0, 5);', 'other than as a direct call'),
                ('{ Callback f = g_cb[0]; f(0, 5); }', 'other than as a direct call'),
                ('g_cb[n](0, 5);', 'other than as a direct call'),
                ('g_cb[0](0);', 'passes 1 arguments to its 2-argument prototype'),
                ('g_cb[0](0, 5, 6);', 'passes 3 arguments to its 2-argument prototype'),
                ('s.g_cb[0](0, 5);', 'a member named g_cb')):
            with self.subTest(call=call):
                self.assertIn(reason, self.signature(source(call=call)))
        sized = 'typedef void (*Callback)(void *, u32);\nextern Callback g_cb[2];\n'
        self.assertIn('outside the array', self.signature(source(sized, 'g_cb[2](0, 5);')))
        disagree = TYPEDEF + 'extern void (*g_cb[])(void *, u32, u32);\n'
        self.assertIn('disagree', self.signature(source(disagree)))


class IndirectCallTests(unittest.TestCase):
    def refused(self, reason, real=REAL, stripped=STRIPPED, preprocessed=None):
        with self.assertRaises(semantics.SemanticError) as caught:
            compare(real, stripped, preprocessed)
        self.assertIn(reason, str(caught.exception))

    def test_a_typed_pointer_call_is_an_opaque_call(self):
        (result,) = compare()
        self.assertEqual(result[1:3], (1, [3]))
        self.assertEqual(result[-1], ['g_cb as 2 arguments'])
        self.assertIn('indirect calls typed by declaration: g_cb as 2 arguments',
                      semantics.record(SYMBOL, [result]))
        # a report without one keeps its text
        self.assertNotIn('indirect', semantics.record(SYMBOL, [result[:5]]))

    def test_arguments_are_compared(self):
        self.refused('differ in observable behaviour',
                     stripped=STRIPPED.replace('mov\tr1, #5', 'mov\tr1, #6'))

    def test_the_unprototyped_and_variadic_pointers_are_refused(self):
        for declarations in ('typedef void (*Callback)();\nextern Callback g_cb[];\n',
                             'typedef void (*Callback)(void *, ...);\nextern Callback g_cb[];\n'):
            with self.subTest(declarations=declarations):
                self.refused('not a prototyped function pointer', preprocessed=source(declarations))

    def test_volatile_accesses_may_not_move_across_the_call(self):
        after = assembly('push\t{lr}', *CALL, *STORE, 'pop\t{r0}', 'bx\tr0')
        # the qualified store on the other side of the call in one compile
        self.refused('differ in observable behaviour', stripped=after.replace('ldrb\tr1, [r3]\n\t', ''))
        self.refused('differ in observable behaviour', real=after)
        # the read-modify-write load and its store split by the call
        split = assembly('push\t{lr}', *STORE[:3], *CALL, *STORE[3:], 'pop\t{r0}', 'bx\tr0')
        with self.assertRaisesRegex(semantics.SemanticError, 'not directly followed by a store'):
            compare(split, after.replace('ldrb\tr1, [r3]\n\t', ''))

    def test_a_mismatched_argument_count_is_refused(self):
        three = 'typedef void (*Callback)(void *, u32, u32);\nextern Callback g_cb[];\n'
        # the pointer sits in an argument register of the declared prototype
        self.refused('an argument register of the 3-argument prototype of g_cb',
                     preprocessed=source(three, 'g_cb[0](0, 5, 6);'))
        self.refused('passes 1 arguments to its 2-argument prototype',
                     preprocessed=source(call='g_cb[0](0);'))

    def test_the_thunk_register_must_hold_the_pointer_value(self):
        for replacement in ('ldr\tr2, .L3+4\n\tadd\tr2, r2, #0',      # the table address itself
                            'ldr\tr2, .L3+4\n\tldrh\tr2, [r2]',      # not a word
                            'ldr\tr2, .L3+4\n\tldr\tr2, [r2, #2]',   # not an element
                            'ldr\tr2, .L3\n\tldr\tr2, [r2]',         # another object
                            'mov\tr2, r0'):                          # an argument
            with self.subTest(replacement=replacement):
                real = REAL.replace('ldr\tr2, .L3+4\n\tldr\tr2, [r2]', replacement)
                with self.assertRaisesRegex(semantics.SemanticError,
                                            'not a word loaded from a typed|not an element'):
                    compare(real, real.replace('ldrb\tr1, [r3]\n\t', ''))
        # a pointer forwarded from a store is not the object's value
        stored = REAL.replace('ldr\tr2, .L3+4\n\tldr\tr2, [r2]',
                              'ldr\tr2, .L3+4\n\tstr\tr0, [r2]\n\tldr\tr2, [r2]')
        with self.assertRaisesRegex(semantics.SemanticError, 'not a word loaded from a typed'):
            compare(stored, stored.replace('ldrb\tr1, [r3]\n\t', ''))
        unsized = REAL.replace('ldr\tr2, [r2]', 'ldr\tr2, [r2, #8]')
        self.assertEqual(compare(unsized, unsized.replace('ldrb\tr1, [r3]\n\t', ''))[0][1], 1)
        sized = 'typedef void (*Callback)(void *, u32);\nextern Callback g_cb[2];\n'
        self.refused('is not an element of its declaration', unsized,
                     unsized.replace('ldrb\tr1, [r3]\n\t', ''), source(sized))


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('cpp') and shutil.which('arm-none-eabi-as') and
                     shutil.which('arm-none-eabi-objcopy'), 'fixed compiler required')
class CompiledIndirectCallTests(unittest.TestCase):
    """through agbcc: the recovered 0x0802F400 shape passes, the untyped ones do not"""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        entry = plausible.volatile_allow_entries()[0]
        for name in ('config', 'src', 'include'):
            (cls.root / name).mkdir()
        (cls.root / 'config' / 'data_symbols.json').write_text(
            json.dumps({entry['symbol']: entry['address']}))
        declaration = entry['declaration'].replace('; ', ';\n    ')
        (cls.root / entry['header']).write_text(fixtures.HEADER.format(declaration=declaration))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def check(self, declarations, body):
        (self.root / 'src' / '08028C34.c').write_text(
            '#include "control_flags.h"\ntypedef unsigned int u32;\n' + declarations +
            'extern u8 g_buffer[];\nvoid func_08028C34(void)\n{\n' + body + '\n}\n')
        with mock.patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return match.allowlisted_volatile_semantics(self.root, 0x08028C34)

    def test_typed_callback_tables(self):
        s = SYMBOL
        body = (f'{s}.bldcnt_lo = ({s}.bldcnt_hi = 0); g_cb[0](g_buffer, 0x1258); '
                f'{s}.bldy_lo = 0x10;')
        for declarations in (TYPEDEF, 'extern void (*const g_cb[])(void *, u32);\n'):
            with self.subTest(declarations=declarations):
                (record,) = self.check(declarations, body)
                self.assertIn('indirect calls typed by declaration: g_cb as 2 arguments', record)
        for declarations, call, reason in (
                ('typedef void (*Callback)();\nextern Callback g_cb[];\n', 'g_cb[0](g_buffer, 8);',
                 'not a prototyped function pointer'),
                ('typedef void (*Callback)(void *, ...);\nextern Callback g_cb[];\n',
                 'g_cb[0](g_buffer, 8);', 'not a prototyped function pointer'),
                (TYPEDEF + 'typedef void (*Three)(void *, u32, u32);\n',
                 '((Three)g_cb[0])(g_buffer, 8, 1);',
                 'other than as a direct call')):
            with self.subTest(declarations=declarations, call=call):
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.check(declarations, f'{s}.bldy_lo = 0x10; {call}')
                self.assertIn(reason, str(caught.exception))


if __name__ == '__main__':
    unittest.main()
