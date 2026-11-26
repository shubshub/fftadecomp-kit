"""kit#375, rule N: lsr(2**24 * B mod 2**32, 24) normalises to trunc8(B), exactly.

08057578's `bldy_lo--` compiles to `sub r0, #1; strb` in the real compile (the
member's value is `trunc8(x + 0xFF)`) and to `lsl #24; lsr #24` of the same sum
in the stripped one (`lsr(x * 2**24 + 0xFF000000, 24)`).  Both are the same
byte, so they must print alike; only that one shift, and only when the constant
and every coefficient are divisible by 2**24, so no carry or remainder is assumed.
"""
from pathlib import Path
import random
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_semantics as semantics

MASK = 0xFFFFFFFF
X = ("load", 1, "x")              # an atom: a byte the executor read
Y = ("arg", "r1")                 # an atom: a full word


def evaluate(value, env):
    """the 32-bit number a normalised value denotes, for atom values env"""
    if isinstance(value, int):
        return value & MASK
    if value[0] == "lin":
        return (value[1] + sum(c * evaluate(term, env) for term, c in value[2])) & MASK
    if value[0] == "trunc":
        return evaluate(value[2], env) & ((1 << value[1]) - 1)
    if value[0] == "lsr":
        return evaluate(value[1], env) >> value[2]
    if value[0] == "asr":
        word = evaluate(value[1], env)
        return (((word - (1 << 32)) if word & 0x80000000 else word) >> value[2]) & MASK
    return env[value]


def narrowed(value):
    """`lsl #24; lsr #24` of value, as the executor builds it"""
    return semantics.shift("lsr", semantics.shift("lsl", value, 24), 24)


class ShiftIdentityTests(unittest.TestCase):
    def test_the_measured_conditions_print_alike(self):
        decremented = semantics.add(X, 0xFF)                       # x - 1, as `sub r0, #1` leaves it
        real = semantics.truncate(decremented, 8)
        stripped = semantics.shift("lsr", semantics.make_linear(0xFF000000, {X: 1 << 24}), 24)
        self.assertEqual(stripped, real)
        self.assertEqual(narrowed(decremented), real)

    def test_exhaustively_over_the_byte_domain(self):
        # every byte x and every constant K: the normalised form denotes the shift's value
        for constant in range(256):
            value = semantics.add(X, constant)
            form = narrowed(value)
            self.assertEqual(form, semantics.truncate(value, 8))
            for x in range(256):
                word = ((x + constant) << 24) & MASK
                self.assertEqual(evaluate(form, {X: x}), word >> 24, (constant, x))

    def test_affine_values_over_random_words(self):
        generator = random.Random(375)
        for _ in range(2000):
            constant, a, b = (generator.randrange(1 << 32) for _ in range(3))
            value = semantics.make_linear(constant, {X: a, Y: b})
            form = narrowed(value)
            for _ in range(4):
                env = {X: generator.randrange(256), Y: generator.randrange(1 << 32)}
                exact = ((evaluate(value, env) << 24) & MASK) >> 24
                self.assertEqual(evaluate(form, env), exact)
            self.assertNotEqual(form[0] if isinstance(form, tuple) else None, "lsr")

    def test_near_misses_stay_opaque(self):
        for value, amount in ((semantics.make_linear(0xFF000001, {X: 1 << 24}), 24),   # a remainder
                              (semantics.make_linear(0x00800000, {X: 1 << 24}), 24),
                              (semantics.make_linear(0xFF000000, {X: 1 << 23}), 24),   # a coefficient
                              (semantics.make_linear(0xFF000000, {X: 1 << 24, Y: 3}), 24),
                              (semantics.make_linear(0xFF000000, {X: 1 << 24}), 23),   # another shift
                              (semantics.make_linear(0xFF000000, {X: 1 << 24}), 25),
                              (semantics.make_linear(0xFFFF0000, {X: 1 << 16}), 16),
                              (semantics.make_linear(0xFF000000, {X: 1 << 24}), 8),
                              (X, 24), (("trunc", 8, X), 24)):
            with self.subTest(value=value, amount=amount):
                self.assertEqual(semantics.shift("lsr", value, amount), ("lsr", value, amount))
        signed = semantics.make_linear(0xFF000000, {X: 1 << 24})
        self.assertEqual(semantics.shift("asr", signed, 24), ("asr", signed, 24))

    def test_the_near_misses_differ_in_value(self):
        # what the refused forms would have claimed is false for some byte
        remainder = semantics.make_linear(0xFF800000, {X: 1 << 24})
        claimed = semantics.truncate(semantics.add(X, 0xFF), 8)
        self.assertTrue(any(evaluate(semantics.shift("lsr", remainder, 23), {X: x}) != evaluate(claimed, {X: x})
                            for x in range(256)))
        self.assertTrue(any(evaluate(semantics.shift("asr", semantics.make_linear(0xFF000000, {X: 1 << 24}), 24),
                                     {X: x}) != evaluate(claimed, {X: x}) for x in range(256)))


if __name__ == "__main__":
    unittest.main()
