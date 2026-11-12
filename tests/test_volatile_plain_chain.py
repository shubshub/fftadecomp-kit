"""An unchanged pinned reread may feed exactly one ordinary same-width store."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class PlainChainTests(unittest.TestCase):
    def bodies(self, *, halfword=False, prefix=(), between=(), suffix=(),
               load=None, store=None, copied=False):
        width = 'h' if halfword else 'b'
        offset = 2 if halfword else 60
        base = ('ldr\tr2, .L3', f'add\tr2, r2, #{offset}')
        original = ('mov\tr3, r4', f'str{width}\tr3, [r2]')
        real = fixtures.assembly(*base, f'ldr{width}\tr0, [r2]', *original,
            *prefix, load or f'ldr{width}\tr0, [r2]', *between,
            *(( 'mov\tr1, r0',) if copied else ()),
            store or f'str{width}\t{"r1" if copied else "r0"}, [r6, #6]',
            *suffix, 'mov\tr0, #0', 'mov\tr1, #0', 'cmp\tr5, #0', 'bx\tlr')
        stripped = fixtures.assembly(*base, *original, *prefix,
            f'str{width}\tr3, [r6, #6]', *suffix,
            'mov\tr0, #0', 'mov\tr1, #0', 'cmp\tr5, #0', 'bx\tlr')
        return real, stripped

    def compare(self, real, stripped, halfword=False):
        if halfword:
            return semantics._compare_compiles(real, stripped, fixtures.PREPROCESSED,
                                               fixtures.SYMBOL, fixtures.DECLARATION16)
        return fixtures.compare(real, stripped)

    def refused(self, **kwargs):
        with self.assertRaises(semantics.SemanticError):
            self.compare(*self.bodies(**kwargs), halfword=kwargs.get('halfword', False))

    def test_byte_and_halfword_plain_assignment(self):
        for halfword in (False, True):
            for copied in (False, True):
                with self.subTest(halfword=halfword, copied=copied):
                    report, = self.compare(*self.bodies(halfword=halfword, copied=copied), halfword)
                    self.assertTrue(report[-1])
                    self.assertEqual(report[3], [])
                    self.assertIn('ordinary-store chained re-reads', semantics.record(fixtures.SYMBOL, [report]))

    def test_wrong_width_refused(self):
        self.refused(store='strh\tr0, [r6, #6]')
        self.refused(halfword=True, store='strb\tr0, [r6, #6]')

    def test_value_arithmetic_and_self_copy_refused(self):
        for operation in ('add\tr0, r0, #1', 'eor\tr0, r0', 'orr\tr0, r0'):
            with self.subTest(operation=operation):
                self.refused(between=(operation,))

    def test_changed_value_refused(self):
        self.refused(store='strb\tr5, [r6, #6]')

    def test_changed_address_refused_by_trace(self):
        real, stripped = self.bodies()
        stripped = stripped.replace('[r6, #6]', '[r6, #7]')
        with self.assertRaises(semantics.SemanticError):
            self.compare(real, stripped)

    def test_value_used_as_address_refused(self):
        self.refused(store='strb\tr0, [r6, r0]')

    def test_extra_consumer_before_and_after_store_refused(self):
        self.refused(between=('mov\tr5, r0',), suffix=('strb\tr5, [r6]',))
        self.refused(suffix=('strb\tr0, [r6]',))

    def test_call_and_branch_before_reread_refused(self):
        for prefix in (('bl\tfunc_0802A2C0',), ('cmp\tr4, #0', 'beq\t.Lnext', '.Lnext:')):
            with self.subTest(prefix=prefix):
                self.refused(prefix=prefix)

    def test_call_branch_and_load_between_reread_and_store_refused(self):
        for operation in ('bl\tfunc_0802A2C0', 'b\t.Lnext\n.Lnext:', 'ldrb\tr5, [r6]'):
            with self.subTest(operation=operation):
                self.refused(between=(operation,))

    def test_alias_write_before_reread_refused(self):
        self.refused(prefix=('strb\tr3, [r6]',))

    def test_prior_member_width_mismatch_refused(self):
        self.refused(load='ldrh\tr0, [r2]')

    def test_address_register_mutation_refused(self):
        self.refused(prefix=('mov\tr1, r2', 'mov\tr2, r1'))

    def test_copied_value_flags_cannot_feed_branch(self):
        self.refused(copied=True, suffix=('beq\t.Lnext', '.Lnext:'))

    def test_independent_flags_before_branch_allowed(self):
        suffix = ('cmp\tr5, #0', 'beq\t.Lnext', '.Lnext:')
        self.assertTrue(self.compare(*self.bodies(copied=True, suffix=suffix)))


if __name__ == '__main__':
    unittest.main()
