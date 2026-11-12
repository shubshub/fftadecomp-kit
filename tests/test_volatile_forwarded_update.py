"""Bounded same-member constant updates preserve live value and flag roles."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class ForwardedUpdateTests(unittest.TestCase):
    def bodies(self, *, initial='mov\tr0, #63', middle=(), before=(),
               update='orr\tr0, r1', after=(), suffix=(), mask=128,
               load='ldrb\tr0, [r2]', store='strb\tr0, [r2]'):
        prefix = ('ldr\tr2, .L3', 'add\tr2, r2, #60')
        ordinary = ('mov\tr0, #5', 'ldrsb\tr0, [r6, r0]', 'cmp\tr0, #0',
                    'bge\t.Lpositive', 'neg\tr0, r0', '.Lpositive:',
                    'cmp\tr0, #1', 'bgt\t.Llarge')
        real = fixtures.assembly(*prefix, 'ldrb\tr0, [r2]', initial,
            'strb\tr0, [r2]', *middle, *ordinary, load, f'mov\tr1, #{mask}',
            'b\t.Lupdate', '.Llarge:', load, 'mov\tr1, #192', '.Lupdate:',
            *before, update, 'ldrb\tr1, [r2]', *after, store, *suffix,
            'mov\tr0, #0', 'mov\tr1, #0', 'cmp\tr4, #0', 'bx\tlr')
        stripped = fixtures.assembly(*prefix, initial, 'strb\tr0, [r2]',
            *middle, *ordinary, f'mov\tr0, #{63 | mask}', 'b\t.Lstore',
            '.Llarge:', 'mov\tr0, #255', '.Lstore:', store, *suffix,
            'mov\tr0, #0', 'mov\tr1, #0', 'cmp\tr4, #0', 'bx\tlr')
        return real, stripped

    def refused(self, **kwargs):
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(**kwargs))

    def test_actual_shaped_constant_update_with_ordinary_signed_load_and_branches(self):
        report, = fixtures.compare(*self.bodies())
        self.assertGreater(report[1], 1)
        self.assertTrue(report[-1])
        self.assertEqual(report[3], [])
        self.assertIn("same-member constant update re-reads", semantics.record(fixtures.SYMBOL, [report]))

    def test_neutral_rmw_copy_can_follow_actual_update(self):
        real, stripped = self.bodies(after=('mov\tr3, #0', 'orr\tr0, r3'))
        self.assertTrue(fixtures.compare(real, stripped))

    def test_unrelated_read_between_forwarded_read_and_store_refused(self):
        self.refused(before=('ldrb\tr5, [r6]',))

    def test_unrelated_consumer_of_forwarded_read_refused(self):
        self.refused(before=('mov\tr5, r0',), suffix=('str\tr5, [r6]',))

    def test_overlapping_store_refused(self):
        self.refused(middle=('strh\tr0, [r2]',))

    def test_width_mismatch_refused(self):
        self.refused(load='ldrh\tr0, [r2]')

    def test_unknown_or_changed_forwarded_value_refused(self):
        for initial in ('mov\tr0, r4', 'mov\tr0, #62'):
            with self.subTest(initial=initial):
                self.refused(initial=initial)

    def test_unknown_update_mask_refused(self):
        self.refused(before=('mov\tr1, r4',))

    def test_non_or_value_change_refused(self):
        self.refused(update='add\tr0, r0, r1')

    def test_address_consumer_refused(self):
        self.refused(before=('ldrb\tr5, [r6, r0]',))

    def test_prior_address_register_mutation_refused(self):
        self.refused(middle=('mov\tr3, r2', 'mov\tr2, r3'))

    def test_intervening_call_refused(self):
        self.refused(middle=('bl\tfunc_0802A2C0',))

    def test_call_after_forwarded_read_refused(self):
        self.refused(before=('bl\tfunc_0802A2C0',))

    def test_nonzero_or_after_update_refused(self):
        self.refused(after=('mov\tr3, #1', 'orr\tr0, r3'))

    def test_update_branch_consumer_refused(self):
        self.refused(after=('beq\t.Lsame', '.Lsame:'))

    def test_self_assignment_refused(self):
        self.refused(mask=0)

    def test_live_flags_after_update_refused(self):
        self.refused(suffix=('beq\t.Lsame', '.Lsame:'))

    def test_unpaired_dead_ordinary_load_is_not_skipped(self):
        real, stripped = self.bodies(middle=('ldrb\tr5, [r6]',))
        stripped = stripped.replace('\tldrb\tr5, [r6]\n', '')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)

    def test_flag_consumer_of_live_source_refused(self):
        self.refused(before=('cmp\tr0, #0',))

    def test_changed_ordinary_load_provenance_refused(self):
        real, stripped = self.bodies()
        stripped = stripped.replace('ldrsb\tr0, [r6, r0]', 'ldrsb\tr0, [r5, r0]')
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped)


if __name__ == '__main__':
    unittest.main()
