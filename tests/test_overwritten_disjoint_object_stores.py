"""Forwarded constant control reads retain their complete ordered effects."""
import unittest
import test_overwritten_control_store_composition as composition_tests
from test_volatile_semantics import assembly
import volatile_semantics as v


class DisjointTests(composition_tests.Tests):
    def setUp(self):
        self.real = assembly('ldr r2, .L3', 'ldrb r0, [r2, #60]', 'mov r0, #0',
            'strb r0, [r2, #60]', 'ldrb r0, [r2, #60]',
            'ldrb r1, [r2, #61]', 'strb r0, [r2, #61]',
            'mov r1, #31', 'strh r1, [r2]', 'ldrb r0, [r2, #60]', 'mov r0, #19', 'strb r0, [r2, #60]', 'bx lr')
        self.stripped = assembly('ldr r2, .L3', 'mov r0, #0', 'strb r0, [r2, #61]',
            'mov r1, #31', 'strh r1, [r2]', 'mov r0, #19', 'strb r0, [r2, #60]', 'bx lr')
        self.permuted = self.real.replace('#60', '#TEMP').replace('#61', '#60').replace('#TEMP', '#61')

    def compare(self, real=None, stripped=None, permuted=None, manifest=None):
        import plausible
        import overwritten_control_store_composition as c
        from test_volatile_semantics import SYMBOL
        declaration=next(e['declaration'] for e in plausible.volatile_allow_entries() if e['symbol']==SYMBOL)
        size,pinned=v.pinned_members(declaration)
        _,mapping,_=v.perturbed_declaration(declaration)
        if permuted is None:
            permuted=(real or self.real).replace('#60','#TEMP').replace('#61',f'#{mapping[61]}').replace('#TEMP',f'#{mapping[60]}')
        functions=[v.parse_assembly(a)[0]['func_08028C34'] for a in
            (real or self.real,stripped or self.stripped,permuted)]
        return c.compare_function('func_08028C34',*functions,{'func_08028C34':(False,())},
            SYMBOL,size,pinned,mapping,selector=c.SELECTOR,premise=c.PREMISE,manifest=manifest)

    def test_forwarded_constant_crossing(self):
        proof = self.compare()
        self.assertEqual(len(proof['paths'][0]['real_removed']), 1)
        self.assertEqual([e[3] for e in proof['paths'][0]['correspondence']['real'] if e[0]=='store'], [0,31,19])


    def test_changed_and_reordered_effects_refuse(self):
        for stripped in (self.stripped.replace('#31','#30'),
            self.stripped.replace("strh r1, [r2]", "strh r1, [r2, #2]"),
            assembly('ldr r2, .L3','mov r1, #31','strh r1, [r2]',
                'mov r0, #0','strb r0, [r2, #61]',
                'mov r0, #19','strb r0, [r2, #60]','bx lr')):
            with self.subTest(stripped=stripped),self.assertRaises(v.SemanticError):
                self.compare(stripped=stripped)

    def test_exact_declaration_ranges_and_barriers(self):
        import copy
        import plausible
        import overwritten_control_store_prerequisite as rule
        from test_volatile_semantics import SYMBOL
        declaration=next(e['declaration'] for e in plausible.volatile_allow_entries() if e['symbol']==SYMBOL)
        size,pinned=v.pinned_members(declaration)
        address=v.add(('sym',SYMBOL),60)
        ordinary=('sym',SYMBOL)
        def store(index,address,value,width):
            return v.Record(index,'synthetic store','store',address=address,value=value,width=width)
        def path(rows):
            return v.Path([],[],[('store',r.width,r.address,r.value) for r in rows if r.kind=='store'],rows)
        options=dict(_typed_correspondence=True,_disjoint_ordinary_stores=True)
        real=path([store(0,address,0,1),store(1,ordinary,31,2),store(2,address,19,1)])
        self.assertEqual(rule.normalise(real,SYMBOL,size,pinned,_typed_correspondence=True)[1],[])
        removed=rule.normalise(real,SYMBOL,size,pinned,**options)[1]
        self.assertEqual(removed[0]['crossed_disjoint_ordinary_stores'],[1])
        for changed,width in ((v.add(ordinary,59),2),(v.add(ordinary,60),2),
            (v.add(ordinary,79),2),(v.add(ordinary,80),2),(('arg',0),2),
            (('sym','unrelated'),2),(ordinary,1),(ordinary,4),(ordinary,8)):
            rows=[store(0,address,0,1),store(1,changed,31,width),store(2,address,19,1)]
            with self.subTest(address=changed,width=width):
                self.assertEqual(rule.normalise(path(rows),SYMBOL,size,pinned,**options)[1],[])
        for kind in ('load','call','branch','return'):
            rows=[store(0,address,0,1),v.Record(9,'barrier',kind,address=ordinary,width=2),
                  store(1,ordinary,31,2),store(2,address,19,1)]
            self.assertEqual(rule.normalise(path(rows),SYMBOL,size,pinned,**options)[1],[])
        self.assertEqual(rule.normalise(real,'unregistered',size,pinned,**options)[1],[])
        for args in ((SYMBOL,size-1,pinned),(SYMBOL,size,{60:1})):
            with self.assertRaises(v.SemanticError):rule.normalise(real,*args,**options)
        with self.assertRaises(v.SemanticError):
            rule.normalise(real,SYMBOL,size,pinned,_disjoint_ordinary_stores=True)

    def test_stale_producer_and_value_address_consumers(self):
        from unittest.mock import patch
        import overwritten_control_store_composition as c
        original=c.compare_survivors
        def stale(real,*args,**kwargs):
            real.records[0].text+=' changed'
            return original(real,*args,**kwargs)
        with patch.object(c,'compare_survivors',stale),self.assertRaises(v.SemanticError):
            self.compare()
        # Live reads that reach ordinary values or addresses cannot be erased
        # merely because a later pinned constant overwrites their source.
        for use in ('strh r0, [r2]', 'strh r1, [r0]'):
            changed=self.real.replace('mov r1, #31\n\tstrh r1, [r2]',
                'ldrb r0, [r2, #60]\n\t'+use)
            with self.subTest(use=use),self.assertRaises(v.SemanticError):self.compare(real=changed)

if __name__ == '__main__': unittest.main()
