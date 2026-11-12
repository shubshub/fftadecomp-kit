"""Cancellation of a left/right shift is valid only inside surviving low bits."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class ShiftTruncationTests(unittest.TestCase):
    atom = ('arg', 0)

    def test_shift_pairs_cancel_only_within_surviving_bits(self):
        for amount in range(1, 32):
            for bits in range(1, 33 - amount):
                for right in ('lsr', 'asr'):
                    with self.subTest(amount=amount, bits=bits, right=right):
                        pair = semantics.shift(right, semantics.shift('lsl', self.atom, amount), amount)
                        self.assertEqual(semantics.truncate(pair, bits),
                                         semantics.truncate(self.atom, bits))

    def test_aligned_affine_values_preserve_modular_low_bits(self):
        for amount in (1, 8, 16, 24, 31):
            bits = 32 - amount
            for coefficient in (-3, -1, 1, 5):
                for constant in (-1, 0, 17):
                    inner = semantics.add(semantics.scale(self.atom, coefficient), constant)
                    pair = semantics.shift('lsr', semantics.shift('lsl', inner, amount), amount)
                    self.assertEqual(semantics.truncate(pair, bits),
                                     semantics.truncate(inner, bits))

    def test_high_bits_mismatched_shifts_and_unaligned_values_stay_distinct(self):
        for right in ('lsr', 'asr'):
            shifted = semantics.shift('lsl', self.atom, 24)
            for amount in (0, 23, 25, 31, 32, 33, 255, ('arg', 1)):
                self.assertNotEqual(semantics.truncate(semantics.shift(right, shifted, amount), 8),
                                    semantics.truncate(self.atom, 8))
            pair = semantics.shift(right, shifted, 24)
            for bits in (9, 16, 32):
                self.assertNotEqual(semantics.truncate(pair, bits),
                                    semantics.truncate(self.atom, bits))
            for inner in (semantics.add(shifted, 1),
                          semantics.add(shifted, self.atom),
                          semantics.scale(self.atom, (1 << 24) + 1)):
                self.assertNotEqual(semantics.truncate(semantics.shift(right, inner, 24), 8),
                                    semantics.truncate(self.atom, 8))
        self.assertNotEqual(semantics.truncate(semantics.shift('ror', shifted, 24), 8),
                            semantics.truncate(self.atom, 8))

    def test_normalization_preserves_concrete_32_bit_values(self):
        def evaluate(expression, value):
            if isinstance(expression, int):
                return expression
            op = expression[0]
            if op == 'arg':
                return value
            if op == 'lin':
                return (expression[1] + sum(evaluate(term, value) * coefficient
                                           for term, coefficient in expression[2])) & semantics.MASK
            if op == 'trunc':
                return evaluate(expression[2], value) & ((1 << expression[1]) - 1)
            source = evaluate(expression[1], value)
            if op == 'lsr':
                return source >> expression[2]
            if op == 'asr':
                signed = source - (1 << 32) if source & (1 << 31) else source
                return (signed >> expression[2]) & semantics.MASK
            self.fail(f'unexpected expression {expression!r}')

        values = list(range(256)) + [0x7fffffff, 0x80000000, 0xffffff80, 0xffffffff]
        for amount in (1, 7, 8, 16, 24, 31):
            for bits in {1, 32 - amount, min(31, 33 - amount)}:
                for right in ('lsr', 'asr'):
                    for coefficient, constant in ((1, 0), (-1, 17), (3, -1)):
                        inner = semantics.add(semantics.scale(self.atom, coefficient), constant)
                        pair = semantics.shift(right, semantics.shift('lsl', inner, amount), amount)
                        normalized = semantics.truncate(pair, bits)
                        for value in values:
                            self.assertEqual(evaluate(pair, value) & ((1 << bits) - 1),
                                             evaluate(normalized, value))


class ShiftObservationTests(unittest.TestCase):
    def bodies(self, extra=()):
        prefix = ('lsl\tr0, r0, #24', 'lsr\tr0, r0, #24')
        real = fixtures.assembly(*prefix, 'ldr\tr1, .L3', 'add\tr1, r1, #60',
                                 'ldrb\tr2, [r1]', 'strb\tr0, [r1]', *extra, 'bx\tlr')
        stripped = fixtures.assembly('ldr\tr1, .L3', 'add\tr1, r1, #60',
                                     'strb\tr0, [r1]', *extra, 'bx\tlr')
        return real, stripped

    def test_byte_store_accepts_cancellation(self):
        real, stripped = self.bodies()
        self.assertEqual(fixtures.compare(real, stripped)[0][1], 1)

    def test_untruncated_return_and_branch_still_refuse(self):
        real, stripped = self.bodies()
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped, 'u32 func_08028C34(void);')
        real, stripped = self.bodies(('cmp\tr0, #0', 'beq\t.L9', 'mov\tr3, #1', '.L9:'))
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_shift_flags_reaching_control_flow_stay_distinct(self):
        real = fixtures.assembly('lsl\tr0, r0, #24', 'lsr\tr0, r0, #24', 'beq\t.L9',
                                 'ldr\tr1, .L3', 'add\tr1, r1, #60',
                                 'ldrb\tr2, [r1]', 'strb\tr0, [r1]', '.L9:', 'bx\tlr')
        stripped = fixtures.assembly('add\tr0, r0, #0', 'beq\t.L9',
                                     'ldr\tr1, .L3', 'add\tr1, r1, #60',
                                     'strb\tr0, [r1]', '.L9:', 'bx\tlr')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_unused_load_and_changed_store_order_still_refuse(self):
        real, stripped = self.bodies(('ldrb\tr3, [r1, #1]',))
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)
        real, stripped = self.bodies(('ldrb\tr2, [r1, #1]', 'mov\tr0, #19', 'strb\tr0, [r1, #1]'))
        stripped = stripped.replace('strb\tr0, [r1]\n', '')
        stripped = stripped.replace('strb\tr0, [r1, #1]', 'strb\tr0, [r1, #1]\n\tstrb\tr0, [r1]')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)


class UnequalShiftTruncationTests(unittest.TestCase):
    atom = ('arg', 0)

    def test_loaded_halfword_high_byte_matches_08087F0C(self):
        value = ('load', 2, ('sym', 'data_030027F0'), 'entry')
        for right in ('lsr', 'asr'):
            pair = semantics.shift(right, semantics.shift('lsl', value, 16), 24)
            self.assertEqual(semantics.truncate(pair, 8),
                             semantics.truncate(semantics.shift('lsr', value, 8), 8))

    def test_partial_cancellation_only_observes_surviving_bits(self):
        for left in range(1, 31):
            for amount in range(left + 1, 32):
                for bits in {1, 32 - amount}:
                    for right in ('lsr', 'asr'):
                        with self.subTest(left=left, right=right, amount=amount, bits=bits):
                            pair = semantics.shift(right, semantics.shift('lsl', self.atom, left), amount)
                            expected = semantics.shift('lsr', self.atom, amount - left)
                            self.assertEqual(semantics.truncate(pair, bits),
                                             semantics.truncate(expected, bits))

    def test_overflow_sign_fill_and_changed_values_stay_distinct(self):
        expected = semantics.shift('lsr', self.atom, 8)
        for right in ('lsr', 'asr'):
            pair = semantics.shift(right, semantics.shift('lsl', self.atom, 16), 24)
            for bits in (9, 16, 32):
                self.assertNotEqual(semantics.truncate(pair, bits),
                                    semantics.truncate(expected, bits))
            for inner in (semantics.add(semantics.shift('lsl', self.atom, 16), 1 << 24),
                          semantics.shift('lsl', self.atom, 15),
                          semantics.shift('lsl', ('arg', 1), 16)):
                changed = semantics.shift(right, inner, 24)
                self.assertNotEqual(semantics.truncate(changed, 8),
                                    semantics.truncate(expected, 8))
        # All but the input's low bit were lost before the right shift.
        overflow = semantics.shift('lsr', semantics.shift('lsl', self.atom, 31), 31)
        self.assertNotEqual(semantics.truncate(overflow, 8),
                            semantics.truncate(self.atom, 8))

    def test_concrete_32_bit_affine_overflow_and_sign_fill(self):
        def evaluate(expression, value):
            if isinstance(expression, int):
                return expression
            op = expression[0]
            if op == 'arg':
                return value
            if op == 'lin':
                return (expression[1] + sum(evaluate(term, value) * coefficient
                                           for term, coefficient in expression[2])) & semantics.MASK
            if op == 'trunc':
                return evaluate(expression[2], value) & ((1 << expression[1]) - 1)
            source = evaluate(expression[1], value)
            if op == 'lsr':
                return source >> expression[2]
            if op == 'asr':
                signed = source - (1 << 32) if source & (1 << 31) else source
                return (signed >> expression[2]) & semantics.MASK
            self.fail(f'unexpected expression {expression!r}')

        values = [0, 1, 0x7f, 0x80, 0x7fff, 0x8000, 0xffff, 0x10000,
                  0x7fffffff, 0x80000000, 0xffffffff]
        for left in (1, 7, 8, 16, 24, 30):
            for amount in {left + 1, 31}:
                for bits in {1, 32 - amount, 33 - amount, 32}:
                    for right in ('lsr', 'asr'):
                        for coefficient, constant in ((1, 0), (-1, 17), (3, -1)):
                            inner = semantics.add(semantics.scale(self.atom, coefficient), constant)
                            pair = semantics.shift(right, semantics.shift('lsl', inner, left), amount)
                            normalized = semantics.truncate(pair, bits)
                            for value in values:
                                source = ((((coefficient * value + constant) & semantics.MASK)
                                           << left) & semantics.MASK)
                                if right == 'asr' and source & (1 << 31):
                                    source -= 1 << 32
                                expected = (source >> amount) & ((1 << bits) - 1)
                                self.assertEqual(evaluate(normalized, value), expected)

    def test_byte_observation_accepts_but_wider_return_and_changed_byte_refuse(self):
        real = fixtures.assembly('lsl\tr0, r0, #16', 'lsr\tr0, r0, #24',
                                 'ldr\tr1, .L3', 'add\tr1, r1, #60',
                                 'ldrb\tr2, [r1]', 'strb\tr0, [r1]', 'bx\tlr')
        stripped = fixtures.assembly('lsr\tr0, r0, #8', 'ldr\tr1, .L3',
                                     'add\tr1, r1, #60', 'strb\tr0, [r1]', 'bx\tlr')
        self.assertEqual(fixtures.compare(real, stripped)[0][1], 1)
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped, 'u32 func_08028C34(void);')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped.replace('r0, r0, #8', 'r0, r0, #7'))


if __name__ == '__main__':
    unittest.main()
