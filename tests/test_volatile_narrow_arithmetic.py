"""Narrow affine stores retain value and live member-read provenance."""
import os
from pathlib import Path
import shutil
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class NarrowArithmeticTests(unittest.TestCase):
    def test_forwarded_narrow_values_have_the_same_low_affine_bits(self):
        value = ('ret', 0)
        for bits in (8, 16):
            for inner in (bits, 32):
                for coefficient in (-3, -1, 1, 5):
                    with self.subTest(bits=bits, inner=inner, coefficient=coefficient):
                        narrow = semantics.scale(semantics.truncate(value, inner), coefficient)
                        wide = semantics.scale(value, coefficient)
                        self.assertEqual(
                            semantics.truncate(semantics.add(16, narrow), bits),
                            semantics.truncate(semantics.add(16, wide), bits))

    def test_narrower_values_and_shifted_high_bits_stay_distinct(self):
        value = ('ret', 0)
        narrow = semantics.truncate(value, 8)
        self.assertNotEqual(semantics.truncate(semantics.add(16, narrow, -1), 16),
                            semantics.truncate(semantics.add(16, value, -1), 16))
        for shift in ('lsr', 'asr', 'ror'):
            self.assertNotEqual(
                semantics.truncate(semantics.shift(shift, narrow, 4), 8),
                semantics.truncate(semantics.shift(shift, value, 4), 8))

    def test_different_low_values_are_not_equated(self):
        value = ('ret', 0)
        for bits in (8, 16):
            expected = semantics.truncate(semantics.add(16, value, -1), bits)
            for altered in (semantics.add(17, value, -1), semantics.add(16, value),
                            semantics.add(16, ('ret', 1), -1)):
                self.assertNotEqual(expected, semantics.truncate(altered, bits))

    def test_nested_affine_truncations_and_cancelled_coefficients(self):
        value = ('arg', 0)
        for bits in (8, 16):
            mask = (1 << bits) - 1
            inner = semantics.truncate(semantics.add(value, mask + 2), bits)
            nested = semantics.truncate(semantics.add(16, inner, -1), bits)
            self.assertEqual(nested, semantics.truncate(semantics.add(15, value, -1), bits))
            self.assertEqual(semantics.truncate(semantics.scale(value, mask + 1), bits), 0)

    def test_normalization_preserves_concrete_low_bits(self):
        def evaluate(expression, value):
            if isinstance(expression, int):
                return expression
            if expression[0] == 'arg':
                return value
            if expression[0] == 'trunc':
                return evaluate(expression[2], value) % (1 << expression[1])
            if expression[0] == 'lin':
                return (expression[1] + sum(evaluate(term, value) * coefficient
                                           for term, coefficient in expression[2])) % (1 << 32)
            self.fail(f'unexpected expression {expression!r}')

        atom = ('arg', 0)
        values = list(range(512)) + [65535, 65536, 65537, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]
        for bits in (8, 16):
            for inner in (8, 16, 32):
                for coefficient in (-3, -1, 0, 1, 5, 1 << bits):
                    expression = ('lin', 17, ((('trunc', inner, atom), coefficient), (atom, 3)))
                    normalized = semantics.truncate(expression, bits)
                    for value in values:
                        self.assertEqual(evaluate(expression, value) % (1 << bits),
                                         evaluate(normalized, value))


class ForwardedArithmeticTests(unittest.TestCase):
    def test_unused_or_interrupted_arithmetic_is_not_a_chain(self):
        real = fixtures.assembly(
            'ldr\tr1, .L3', 'add\tr1, r1, #60', 'ldrb\tr2, [r1]',
            'strb\tr0, [r1]', 'ldrb\tr2, [r1]', 'mov\tr0, #16',
            'sub\tr0, r0, r2', 'ldrb\tr3, [r1, #1]',
            'strb\tr0, [r1, #1]', 'bx\tlr')
        stripped = fixtures.assembly(
            'ldr\tr1, .L3', 'add\tr1, r1, #60', 'strb\tr0, [r1]',
            'mov\tr2, #16', 'sub\tr0, r2, r0', 'strb\tr0, [r1, #1]', 'bx\tlr')
        self.assertEqual(fixtures.compare(real, stripped)[0][3], [4])
        for extra in ('add\tr2, r2, #1', 'ldr\tr3, [r1, #-4]',
                      'cmp\tr2, #0'):
            altered = real.replace('ldrb\tr3, [r1, #1]', extra + '\n\tldrb\tr3, [r1, #1]')
            with self.subTest(extra=extra), self.assertRaises(semantics.SemanticError):
                fixtures.compare(altered, stripped)

    def test_cross_width_arithmetic_needs_a_stripped_counterpart(self):
        # A real compile may reload the byte before a halfword store, but
        # this is not the same-width forwarding exception. The compiler
        # test below checks its independently emitted stripped counterpart.
        real = fixtures.assembly(
            'ldr\tr1, .L3', 'ldrb\tr2, [r1, #58]', 'strb\tr0, [r1, #58]',
            'ldrb\tr2, [r1, #58]', 'mov\tr0, #16', 'sub\tr0, r0, r2',
            'ldrh\tr3, [r1, #2]', 'strh\tr0, [r1, #2]', 'bx\tlr')
        name = 'func_08028C34'
        functions, _ = semantics.parse_assembly(real)
        size, pinned = semantics.pinned_members(fixtures.DECLARATION16)
        path, = semantics.explore(name, functions[name], {name: (False, 0)},
                                  'real', (fixtures.SYMBOL, size, pinned))
        def pinned_width(address):
            return pinned.get(semantics.object_offset(address, fixtures.SYMBOL, size))
        self.assertTrue(path.records[3].forwarded)
        self.assertFalse(semantics.chained_reread(path.records, 3, pinned_width))

    def test_flags_from_forwarded_arithmetic_cannot_feed_a_later_branch(self):
        real = fixtures.assembly(
            'ldr\tr1, .L3', 'add\tr1, r1, #60', 'ldrb\tr2, [r1]',
            'strb\tr0, [r1]', 'ldrb\tr2, [r1]', 'mov\tr0, #16',
            'sub\tr0, r0, r2', 'ldrb\tr3, [r1, #1]',
            'strb\tr0, [r1, #1]', 'ldr\tr0, .L3', 'ldr\tr2, .L3',
            'beq\t.L5', 'mov\tr3, #1', '.L5:', 'bx\tlr')
        name = 'func_08028C34'
        functions, _ = semantics.parse_assembly(real)
        size, pinned = semantics.pinned_members(fixtures.DECLARATION)
        paths = semantics.explore(name, functions[name], {name: (False, 0)},
                                  'real', (fixtures.SYMBOL, size, pinned))
        def pinned_width(address):
            return pinned.get(semantics.object_offset(address, fixtures.SYMBOL, size))
        self.assertEqual(len(paths), 2)
        for path in paths:
            self.assertFalse(semantics.chained_reread(path.records, 4, pinned_width))


@unittest.skipUnless(Path(os.path.expandvars(fixtures.match.DEFAULT_CC)).is_file()
                     and shutil.which('cpp') and shutil.which('arm-none-eabi-as')
                     and shutil.which('arm-none-eabi-objcopy'), 'fixed compiler required')
class CompiledNarrowArithmeticTests(unittest.TestCase):
    setUpClass = classmethod(fixtures.CompiledSemanticTests.setUpClass.__func__)
    tearDownClass = classmethod(fixtures.CompiledSemanticTests.tearDownClass.__func__)
    check = fixtures.CompiledSemanticTests.check

    def test_unknown_byte_complement_preserves_every_member_access(self):
        symbol = fixtures.SYMBOL
        for expression in (f'16 - {symbol}.bldalpha_lo',
                           f'{symbol}.bldalpha_lo + 3',
                           f'-{symbol}.bldalpha_lo'):
            with self.subTest(expression=expression):
                records = self.check(f'{symbol}.bldalpha_lo = value; '
                                     f'{symbol}.bldalpha_hi = {expression};', 'int value')
                self.assertEqual(len(records), 1)
                self.assertIn('pinned bytes moved follows every pinned access', records[0])

    def test_compiler_division_then_complement_is_checked(self):
        symbol = fixtures.SYMBOL
        records = self.check(
            f'if (first >= second) {{ {symbol}.bldalpha_lo = 16; '
            f'{symbol}.bldalpha_hi = 0; }} else {{ '
            f'{symbol}.bldalpha_lo = (second * 16) / first; '
            f'{symbol}.bldalpha_hi = 16 - {symbol}.bldalpha_lo; }}',
            'u16 first, u16 second')
        self.assertIn('agrees on 2 paths', records[0])

    def test_cross_width_read_has_its_ordinary_compiler_counterpart(self):
        symbol = fixtures.SYMBOL
        records = self.check(f'{symbol}.bldalpha_lo = value; '
                             f'{symbol}.bg0cnt = 16 - {symbol}.bldalpha_lo;', 'int value')
        self.assertIn('chained re-reads at []', records[0])

    def test_constant_cancelled_and_unused_reads_stay_refused(self):
        symbol = fixtures.SYMBOL
        for body in (
            f'{symbol}.bldalpha_lo = 0; {symbol}.bldalpha_hi = {symbol}.bldalpha_lo + 1;',
            f'{symbol}.bldalpha_lo = value; '
            f'{symbol}.bldalpha_hi = {symbol}.bldalpha_lo - {symbol}.bldalpha_lo;',
            f'(void){symbol}.bldalpha_lo; {symbol}.bldalpha_hi = value;',
            f'{symbol}.bldalpha_lo = value; '
            f'func_0802A2C0({symbol}.bldalpha_lo + 1, 0, 0, 0);',
            f'{symbol}.bldalpha_lo = value; '
            f'{symbol}.bldalpha_hi = {symbol}.bldalpha_lo & 15;',
            f'{symbol}.bldalpha_lo = value; '
            f'(void)({symbol}.bldalpha_lo + 3); {symbol}.bldalpha_hi = 16;',
        ):
            with self.subTest(body=body), self.assertRaises(semantics.SemanticError):
                self.check(body, 'int value')


if __name__ == '__main__':
    unittest.main()
