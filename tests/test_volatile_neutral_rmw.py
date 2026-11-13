"""Only path-proven neutral register OR may feed a volatile member store."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class NeutralRmwTests(unittest.TestCase):
    def bodies(self, *, zero='mov\tr3, #0', operation='orr\tr0, r3',
               suffix=(), target='strb\tr0, [r1]', stripped_suffix=()):
        prefix = ('ldr\tr1, .L3', 'add\tr1, r1, #60', zero)
        real = fixtures.assembly(*prefix, 'ldrb\tr2, [r1]', operation,
                                 target, *suffix, 'bx\tlr')
        stripped = fixtures.assembly(*prefix, target, *stripped_suffix, 'bx\tlr')
        return real, stripped

    def test_neutral_register_or_feeds_unknown_store_value(self):
        report, = fixtures.compare(*self.bodies())
        self.assertEqual(report[2], [3])

    def test_three_operand_neutral_or_and_zero_first(self):
        for operation in ('orrs\tr0, r0, r3', 'orr\tr0, r3, r0'):
            with self.subTest(operation=operation):
                self.assertEqual(fixtures.compare(*self.bodies(operation=operation))[0][2], [3])

    def test_path_constant_zero_can_be_computed(self):
        self.assertEqual(fixtures.compare(*self.bodies(zero='mov\tr3, #1\n\tsub\tr3, r3, #1'))[0][2], [4])

    def test_unknown_and_nonzero_or_operand_refused(self):
        for zero in ('mov\tr3, r4', 'mov\tr3, #1'):
            with self.subTest(zero=zero), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*self.bodies(zero=zero))

    def test_unrelated_neutral_copy_not_feeding_store_refused(self):
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(operation='orr\tr4, r3'))

    def test_unrelated_neutral_copy_with_a_dead_reader_refused(self):
        # liveness of scheduled-in work is transitive: a dead copy after the
        # store, or a push popped straight back, does not make the OR live
        for suffix in (('mov\tr5, r4',), ('push\t{r4}', 'pop\t{r4}')):
            with self.subTest(suffix=suffix), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*self.bodies(operation='orr\tr4, r3', suffix=suffix,
                                              stripped_suffix=suffix))
        # nor does a call register the prototype does not name, or a frame
        # slot that is never read back or escaped
        for operation, suffix in (
                ('orr\tr0, r3\n\tmov\tr3, r5', ('mov\tr2, #0', 'push\t{lr}', 'bl\tfunc_0802A2C0',
                                                 'pop\t{r2}', 'mov\tlr, r2')),
                ('orr\tr0, r3\n\tmov\tr4, r5', ('sub\tsp, #4', 'str\tr4, [sp]', 'add\tsp, #4'))):
            with self.subTest(operation=operation), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*self.bodies(operation=operation, suffix=suffix,
                                              stripped_suffix=suffix))

    def test_dead_loaded_value_cannot_be_or_source(self):
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(operation='orr\tr0, r2'))

    def test_changed_store_value_refused(self):
        real, stripped = self.bodies()
        stripped = stripped.replace('strb\tr0, [r1]', 'strb\tr4, [r1]')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_changed_live_value_after_store_refused(self):
        real, stripped = self.bodies(suffix=('str\tr0, [r5]',),
                                     stripped_suffix=('str\tr4, [r5]',))
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_store_address_neutral_copy_is_admitted(self):
        real = fixtures.assembly('ldr\tr1, .L3', 'add\tr1, r1, #60',
            'mov\tr3, #0', 'ldrb\tr2, [r1]', 'orr\tr1, r3', 'strb\tr0, [r1]', 'bx\tlr')
        stripped = fixtures.assembly('ldr\tr1, .L3', 'add\tr1, r1, #60',
            'strb\tr0, [r1]', 'bx\tlr')
        self.assertEqual(fixtures.compare(real, stripped)[0][2], [3])

    def test_nonzero_or_cannot_change_store_address(self):
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(zero='mov\tr3, #1', operation='orr\tr1, r3'))

    def test_flags_after_store_are_not_discarded(self):
        suffix = ('beq\t.Lzero', 'mov\tr0, #1', 'b\t.Ldone',
                  '.Lzero:', 'mov\tr0, #2', '.Ldone:', 'str\tr0, [r5]')
        # Real OR sets N/Z from unknown R0; stripped MOV sets them from zero.
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(suffix=suffix, stripped_suffix=suffix))

    def test_flags_may_be_overwritten_before_branch(self):
        suffix = ('cmp\tr4, #0', 'beq\t.Lzero', 'mov\tr0, #1', 'b\t.Ldone',
                  '.Lzero:', 'mov\tr0, #2', '.Ldone:', 'str\tr0, [r5]')
        self.assertTrue(fixtures.compare(*self.bodies(suffix=suffix, stripped_suffix=suffix)))


if __name__ == '__main__':
    unittest.main()
