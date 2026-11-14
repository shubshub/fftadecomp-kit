"""A separated insertion read permits only a same-member live OR store."""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures


class SeparatedRmwTests(unittest.TestCase):
    def bodies(self, *, prior='ldrb\tr1, [r4]', mask='mov\tr0, #4',
               insertion='ldrb\tr2, [r4]', middle=(), operation='orr\tr0, r1',
               store='strb\tr0, [r4]', suffix=()):
        prefix = ('ldr\tr4, .L3', 'add\tr4, r4, #60')
        real = fixtures.assembly(*prefix, prior, mask, insertion, *middle,
                                 operation, store, *suffix, 'bx\tlr')
        stripped = fixtures.assembly(*prefix, prior, mask, *middle,
                                     operation, store, *suffix, 'bx\tlr')
        return real, stripped

    def refused(self, **kwargs):
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*self.bodies(**kwargs))

    def not_this_shape(self, **kwargs):
        """separated_or_store itself refuses the insertion read, but since
        kit#165 the plain window explains it: the OR (or other arithmetic)
        reads a live counterpart read or a known value, never the dead load,
        and the stripped comparison still checks the stored value"""
        real, stripped = self.bodies(**kwargs)
        size, pinned = semantics.pinned_members(fixtures.DECLARATION)
        (name, function), = semantics.parse_assembly(real)[0].items()
        signatures = {name: (False, 0), 'func_0802A2C0': (False, 1)}
        for path in semantics.explore(name, function, signatures, 'real',
                                      (fixtures.SYMBOL, size, pinned)):
            loads = [i for i, r in enumerate(path.records)
                     if r.kind == 'load' and r.text.startswith('ldrb\tr2')]
            self.assertTrue(loads)
            for position in loads:
                record = path.records[position]
                self.assertIsNone(semantics.separated_or_store(
                    path.records, position, record.address, record.width))
        self.assertTrue(fixtures.compare(real, stripped))

    def test_byte_or_update(self):
        self.assertEqual(fixtures.compare(*self.bodies())[0][2], [4])

    def test_three_operand_or_update(self):
        self.assertTrue(fixtures.compare(*self.bodies(operation='orrs\tr0, r0, r1')))

    def test_halfword_or_update(self):
        real, stripped = self.bodies(prior='ldrh\tr1, [r4]',
                                    insertion='ldrh\tr2, [r4]', store='strh\tr0, [r4]')
        real, stripped = (text.replace('r4, #60', 'r4, #2') for text in (real, stripped))
        self.assertTrue(semantics._compare_compiles(real, stripped, fixtures.PREPROCESSED,
                                                  fixtures.SYMBOL, fixtures.DECLARATION16))

    def test_other_prior_member_is_an_ordinary_read(self):
        # not this bounded shape, but since kit#165 the plain window admits
        # it: `sym.unknown_3C = sym.unknown_3D | 4`, the OR reading only the
        # other member's live counterpart read, never the dead load
        self.not_this_shape(prior='ldrb\tr1, [r4, #1]')
        self.refused(prior='ldrb\tr1, [r4, #1]', operation='orr\tr0, r2')

    def test_wrong_store_member_refused(self):
        self.refused(store='strb\tr0, [r4, #1]')

    def test_prior_width_mismatch_refused(self):
        self.refused(prior='ldrh\tr1, [r4]')

    def test_insertion_value_use_refused(self):
        self.refused(operation='orr\tr0, r2')

    def test_unknown_mask_is_ordinary_value_arithmetic(self):
        # `sym.x |= v` with an unknown v: since kit#165 the plain window
        # admits the OR, which reads the live prior read, not the dead load
        self.not_this_shape(mask='mov\tr0, r5')
        self.refused(mask='mov\tr0, r5', operation='orr\tr0, r2')

    def test_other_arithmetic_is_not_the_bounded_shape(self):
        self.not_this_shape(operation='add\tr0, r0, r1')

    def test_nonfeeding_result_refused(self):
        self.refused(operation='orr\tr3, r1')

    def test_prior_value_replaced_refused(self):
        self.refused(mask='mov\tr1, #4')

    def test_unrelated_memory_refused(self):
        self.refused(middle=('ldrb\tr3, [r6]',))

    def test_unrelated_store_refused(self):
        self.refused(middle=('str\tr3, [r6]',))

    def test_call_refused(self):
        self.refused(middle=('bl\tfunc_0802A2C0',))

    def test_control_flow_is_not_the_bounded_shape(self):
        self.not_this_shape(middle=('b\t.Lnext', '.Lnext:'))

    def test_flag_consumer_refused(self):
        self.refused(suffix=('beq\t.Lnext', '.Lnext:'))

    def test_independent_flag_overwrite(self):
        self.assertTrue(fixtures.compare(*self.bodies(
            suffix=('cmp\tr6, #0', 'beq\t.Lnext', '.Lnext:'))))

    def test_extra_value_consumer_is_not_the_bounded_shape(self):
        self.not_this_shape(suffix=('str\tr0, [r6]',))

    def test_extra_prior_value_consumer_is_not_the_bounded_shape(self):
        self.not_this_shape(suffix=('str\tr1, [r6]',))

    def test_extra_dead_load_consumer_refused(self):
        self.refused(suffix=('str\tr2, [r6]',))

    def test_zero_mask_refused(self):
        self.refused(mask='mov\tr0, #0')

    def test_mask_outside_member_is_not_the_bounded_shape(self):
        self.not_this_shape(mask='mov\tr0, #256')

    def test_signed_prior_is_not_the_bounded_shape(self):
        self.not_this_shape(prior='ldrsb\tr1, [r4]')

    def test_missing_prior_is_not_the_bounded_shape(self):
        self.not_this_shape(prior='mov\tr1, r5')

    def test_unrelated_arithmetic_refused(self):
        self.refused(middle=('add\tr3, r3, #1',))

    def test_dead_read_flag_use_refused(self):
        self.refused(middle=('cmp\tr2, #0',))

    def test_address_register_mutation_is_not_the_bounded_shape(self):
        self.not_this_shape(middle=('mov\tr5, r4', 'mov\tr4, r5'))

    def test_only_one_access_following_permutation_refused(self):
        real, stripped = self.bodies()
        permuted = real.replace('ldrb\tr1, [r4]', 'ldrb\tr1, [r4, #1]')
        with self.assertRaises(semantics.SemanticError):
            semantics.compare(real, stripped, fixtures.PREPROCESSED,
                              fixtures.SYMBOL, fixtures.DECLARATION, permuted)

    def test_changed_stripped_store_refused(self):
        real, stripped = self.bodies()
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(real, stripped.replace('strb\tr0, [r4]', 'strb\tr3, [r4]'))

    def test_member_permutation_required(self):
        real, stripped = self.bodies()
        permuted = real.replace('r4, #60', 'r4, #61')
        self.assertTrue(semantics.compare(real, stripped, fixtures.PREPROCESSED,
                                         fixtures.SYMBOL, fixtures.DECLARATION, permuted))
        with self.assertRaises(semantics.SemanticError):
            semantics.compare(real, stripped, fixtures.PREPROCESSED,
                              fixtures.SYMBOL, fixtures.DECLARATION, real)


if __name__ == '__main__':
    unittest.main()
