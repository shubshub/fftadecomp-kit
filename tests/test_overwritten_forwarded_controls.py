"""Forwarded constant control reads retain their complete ordered effects."""
import unittest
import test_overwritten_control_store_composition as composition_tests
from test_volatile_semantics import assembly
import volatile_semantics as v


class ForwardedTests(composition_tests.Tests):
    def setUp(self):
        self.real = assembly('ldr r2, .L3', 'ldrb r0, [r2, #60]', 'mov r0, #0',
            'strb r0, [r2, #60]', 'ldrb r0, [r2, #60]',
            'ldrb r1, [r2, #61]', 'strb r0, [r2, #61]',
            'ldrb r0, [r2, #60]', 'mov r0, #19', 'strb r0, [r2, #60]', 'bx lr')
        self.stripped = assembly('ldr r2, .L3', 'mov r0, #0', 'strb r0, [r2, #61]',
            'mov r0, #19', 'strb r0, [r2, #60]', 'bx lr')
        self.permuted = self.real.replace('#60', '#TEMP').replace('#61', '#60').replace('#TEMP', '#61')

    def test_forwarded_constant_crossing(self):
        proof = self.compare()
        self.assertEqual(len(proof['paths'][0]['real_removed']), 1)
        self.assertEqual([e[3] for e in proof['paths'][0]['correspondence']['real'] if e[0]=='store'], [0,19])

    def test_default_and_hostile_read_barriers(self):
        import copy
        import overwritten_control_store_prerequisite as rule
        from test_volatile_semantics import DECLARATION, SYMBOL
        size, pinned = v.pinned_members(DECLARATION)
        function = v.parse_assembly(self.real)[0]['func_08028C34']
        original = v.explore('func_08028C34', function, {'func_08028C34': (False, ())},
            'real', (SYMBOL,size,pinned))[0]
        # Use the same dead-read view as the independently checked composition.
        original.records = [r for i,r in enumerate(original.records) if r.kind != 'load' or
            (r.forwarded and type(r.value) is int and v.chained_reread(original.records,i,
                lambda address: pinned.get(v.object_offset(address,SYMBOL,size))))]
        args = (SYMBOL,size,pinned)
        self.assertEqual(rule.normalise(original,*args,_typed_correspondence=True)[1], [])
        with self.assertRaises(v.SemanticError):
            rule.normalise(original,*args,_forwarded_constant_controls=True)
        self.assertEqual(len(rule.normalise(original,*args,_typed_correspondence=True,
            _forwarded_constant_controls=True)[1]), 1)
        for field, value in (('signed',True),('forwarded',False),('value',('arg',0)),
                             ('width',2),('address',('arg',0))):
            candidate = copy.deepcopy(original)
            load = next(r for r in candidate.records if r.kind == 'load')
            setattr(load,field,value)
            with self.subTest(field=field):
                self.assertEqual(rule.normalise(candidate,*args,_typed_correspondence=True,
                    _forwarded_constant_controls=True)[1], [])
        for kind in ('call','branch','return','load'):
            candidate = copy.deepcopy(original)
            position = next(i for i,r in enumerate(candidate.records) if r.kind == 'load')
            candidate.records.insert(position, v.Record(999,'barrier',kind,
                address=('arg',0),width=1,value=0))
            with self.subTest(kind=kind):
                self.assertEqual(rule.normalise(candidate,*args,_typed_correspondence=True,
                    _forwarded_constant_controls=True)[1], [])

    def test_surviving_effect_order_and_values(self):
        for changed in (
            self.stripped.replace('mov r0, #0', 'mov r0, #1'),
            assembly('ldr r2, .L3', 'mov r0, #19', 'strb r0, [r2, #60]',
                'mov r0, #0', 'strb r0, [r2, #61]', 'bx lr')):
            with self.assertRaises(v.SemanticError): self.compare(stripped=changed)


if __name__ == '__main__': unittest.main()
