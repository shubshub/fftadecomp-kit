"""Load-time capture, conservative aliasing, and typed event correspondence."""
import unittest
from test_volatile_semantics import assembly, DECLARATION, SYMBOL
import volatile_semantics as v
import overwritten_control_store_composition as c


def execute(body, capture=True):
    function = v.parse_assembly(assembly(*body))[0]['func_08028C34']
    size, pinned = v.pinned_members(DECLARATION)
    return v.explore('func_08028C34', function,
        {'func_08028C34': (True, 2), 'f': (False, 0)}, 'synthetic',
        (SYMBOL, size, pinned), _capture_load_provenance=capture)[0]


def compare(a, b, removed=(), other=(), **kwargs):
    return c.compare_survivors(a, b, removed, other, load_time_provenance=True, **kwargs)


class Tests(unittest.TestCase):
    def body(self, *, extra=False, width='ldr', offset=0, value=7, repeated=False):
        prefix = ['push {r4,r5,r6,lr}', 'mov r4, r0', 'mov r5, r1', 'ldr r2, .L3']
        if extra:
            prefix += ['mov r0, #0', 'strb r0, [r2, #60]']
        return prefix + ['mov r0, #19', 'strb r0, [r2, #60]', 'bl f'] + (
            ['bl f'] if repeated else []) + [
            'ldr r6, [r4]', 'mov r1, #' + str(value), 'str r1, [r5]',
            width + ' r0, [r6, #' + str(offset) + ']',
            # The pointer loaded before the may-alias write remains captured.
            'str r1, [r5, #4]', 'pop {r4,r5,r6}', 'pop {r1}', 'bx r1']

    def pair(self, **kwargs):
        return execute(self.body(extra=True, **kwargs)), execute(self.body(**kwargs))

    def test_legacy_default_has_no_capture(self):
        path = execute(self.body(), capture=False)
        self.assertFalse(hasattr(path, '_load_provenance'))

    def test_captured_pointer_and_may_alias_store_versions(self):
        a, b = self.pair()
        proof = compare(a, b, [{'event': 0}])
        self.assertEqual(proof['real'], proof['stripped'])
        compare(a, b, [{'event': 0}], manifest=proof)
        self.assertTrue(any(capture[0][3][0] == 'store'
            for capture in a._load_provenance.captures if isinstance(capture[0][3], tuple)))
        # The legacy bare-trace subset retains its conservative refusal.
        with self.assertRaises(v.SemanticError):
            c.compare_survivors(a, b, [{'event': 0}], [])

    def test_repeated_calls_have_distinct_typed_identities(self):
        a, b = self.pair(repeated=True)
        compare(a, b, [{'event': 0}])
        with self.assertRaises(v.SemanticError):
            compare(a, execute(self.body()), [{'event': 0}])

    def test_changed_width_address_and_store_value_refuse(self):
        a, b = self.pair()
        for kwargs in ({'width': 'ldrh'}, {'offset': 4}, {'value': 8}):
            with self.subTest(kwargs=kwargs), self.assertRaises(v.SemanticError):
                compare(a, execute(self.body(**kwargs)), [{'event': 0}])

    def test_stale_and_forged_provenance_refuse(self):
        a, b = self.pair()
        with self.assertRaises(v.SemanticError):
            v.LoadProvenance(a, a._load_provenance.captures)
        old = a._load_provenance
        a._load_provenance = b._load_provenance
        with self.assertRaises(v.SemanticError): compare(a, b, [{'event': 0}])
        a._load_provenance = old
        a.records[0].text += ' forged'
        with self.assertRaises(v.SemanticError): compare(a, b, [{'event': 0}])

    def test_missing_capture_removed_wrong_kind_and_forward_refuse(self):
        for mutation in ('missing', 'removed', 'wrong-kind', 'forward', 'entry'):
            a, b = self.pair()
            if mutation == 'missing':
                del a._load_provenance
            else:
                version = {'removed': ('store', 0), 'wrong-kind': ('call', 1),
                           'forward': ('store', len(a.trace)), 'entry': 'entry'}[mutation]
                a.trace[-1] = ('return', ('load', 4, ('arg', 0), version))
            with self.subTest(mutation=mutation), self.assertRaises(v.SemanticError):
                compare(a, b, [{'event': 0}])
        a, b = self.pair()
        with self.assertRaises(v.SemanticError): compare(a, b, [{'event': 0}], manifest={})


if __name__ == '__main__': unittest.main()
