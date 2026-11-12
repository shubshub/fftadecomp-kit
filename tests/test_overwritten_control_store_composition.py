"""Classifier composition retains independent member permutation and refusals."""
import unittest
from test_volatile_semantics import assembly, DECLARATION, SYMBOL
import volatile_semantics as v
import overwritten_control_store_composition as c


class Tests(unittest.TestCase):
    def setUp(self):
        self.real = assembly('ldr r2, .L3', 'ldrb r0, [r2, #60]', 'mov r0, #0',
            'strb r0, [r2, #60]', 'ldrb r0, [r2, #60]', 'mov r0, #19',
            'strb r0, [r2, #60]', 'bx lr')
        self.stripped = assembly('ldr r2, .L3', 'mov r0, #19', 'strb r0, [r2, #60]', 'bx lr')
        self.permuted = self.real.replace('#60', '#61')

    def compare(self, real=None, stripped=None, permuted=None, manifest=None):
        functions = [v.parse_assembly(a)[0]['func_08028C34'] for a in
                     (real or self.real, stripped or self.stripped, permuted or self.permuted)]
        size, pinned = v.pinned_members(DECLARATION)
        _, mapping, _ = v.perturbed_declaration(DECLARATION)
        return c.compare_function('func_08028C34', *functions,
            {'func_08028C34': (False, ())}, SYMBOL, size, pinned, mapping,
            selector=c.SELECTOR, premise=c.PREMISE, manifest=manifest)

    def test_actual_executor_classifier_composition(self):
        proof = self.compare()
        self.assertTrue(proof['volatile_classification_complete'])
        self.assertTrue(proof['independent_permutation_complete'])
        self.assertEqual(len(proof['paths'][0]['real_removed']), 1)
        self.compare(manifest=proof)
        with self.assertRaisesRegex(v.SemanticError, 'manifest is stale'):
            self.compare(manifest={})

    def test_permutation_cannot_be_excused(self):
        with self.assertRaises(v.SemanticError): self.compare(permuted=self.real)

    def test_legacy_still_refuses(self):
        real = v.parse_assembly(self.real)[0]['func_08028C34']
        stripped = v.parse_assembly(self.stripped)[0]['func_08028C34']
        size, pinned = v.pinned_members(DECLARATION)
        with self.assertRaises(v.SemanticError):
            v.compare_function('func_08028C34', real, stripped,
                {'func_08028C34': (False, ())}, SYMBOL, size, pinned)

    def test_live_read_and_changed_return_refuse(self):
        for tail in ('add r1, r0, #1', 'mov r1, r0'):
            changed = self.real.replace('ldrb r0, [r2, #60]\n\tmov r0, #19',
                'ldrb r0, [r2, #60]\n\t' + tail + '\n\tmov r0, #19')
            changed = changed.replace('bx lr', 'mov r0, r1\n\tbx lr')
            with self.assertRaises(v.SemanticError):
                self.compare(real=changed, permuted=changed.replace('#60','#61'))


if __name__ == '__main__': unittest.main()
