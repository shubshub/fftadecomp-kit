"""A complete executed path may jump unconditionally to its member store."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class SharedStoreTests(unittest.TestCase):
    def bodies(self, between=(), store='strb\tr0, [r1]'):
        real = fixtures.assembly(
            'ldr\tr1, .L3', 'add\tr1, r1, #60', 'ldrb\tr0, [r1]',
            'mov\tr0, #19', 'b\t.L5', '.L5:', *between, store, 'bx\tlr')
        stripped = fixtures.assembly(
            'ldr\tr1, .L3', 'add\tr1, r1, #60', 'mov\tr0, #19',
            *between, store, 'bx\tlr')
        return real, stripped

    def test_unconditional_jump_to_same_member_store(self):
        real, stripped = self.bodies()
        result, = fixtures.compare(real, stripped)
        self.assertEqual(result[2], [2])

    def test_multiple_jumps_preserve_same_executed_store(self):
        real, stripped = self.bodies()
        real = real.replace('.L5:\n', '.L5:\n\tb\t.L6\n.L6:\n')
        self.assertEqual(fixtures.compare(real, stripped)[0][2], [2])

    def test_conditional_jump_still_refuses(self):
        real, stripped = self.bodies()
        real = real.replace('b\t.L5', 'beq\t.L5')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_intervening_effects_still_refuse(self):
        for between in [('ldrb\tr3, [r1, #1]',),
                        ('strb\tr2, [r1, #1]',),
                        ('bl\tfunc_0802A2C0',),
                        ('add\tr1, r1, r2',)]:
            with self.subTest(between=between), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*self.bodies(between))

    def test_load_independent_value_arithmetic_after_the_jump(self):
        # kit#165: arithmetic that finishes only the stored value is admitted
        # on the shared store's side of the jump as well
        self.assertEqual(fixtures.compare(*self.bodies(('add\tr0, r0, r2',)))[0][2], [2])

    def test_different_member_width_or_missing_store_still_refuses(self):
        for store in ('strb\tr0, [r1, #1]', 'strh\tr0, [r1]', 'bx\tlr'):
            with self.subTest(store=store), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*self.bodies(store=store))

    def test_store_value_and_order_remain_checked(self):
        real, stripped = self.bodies()
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped.replace('#19', '#20'))
        real = real.replace('b\t.L5', 'strb\tr2, [r1, #1]\n\tb\t.L5')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_nonterminating_or_missing_target_is_not_a_store(self):
        real, stripped = self.bodies()
        for broken in (real.replace('.L5:\n', '.L5:\n\tb\t.L5\n'),
                       real.replace('b\t.L5', 'b\t.Lmissing')):
            with self.subTest(broken=broken), self.assertRaises(semantics.SemanticError):
                fixtures.compare(broken, stripped)


if __name__ == '__main__':
    unittest.main()
