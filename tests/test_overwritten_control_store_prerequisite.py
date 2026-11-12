"""Bounded conditional prerequisite retains ordered events and opaque versions."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import volatile_semantics as v
import overwritten_control_store_prerequisite as rule

SYMBOL='control'
ADDRESS=('sym',SYMBOL)
OTHER=v.add(ADDRESS,1)


def store(index,address,value,width=1):
    return v.Record(index,'synthetic store','store',address=address,width=width,value=value)


def path(records,extra=(),conditions=()):
    events=[('store',row.width,row.address,row.value) for row in records if row.kind=='store']
    return v.Path([],list(conditions),events+list(extra),records)


def compare(real,stripped,**changes):
    arguments=dict(symbol=SYMBOL,size=4,pinned={0:1,1:1},selector=rule.SELECTOR,premise=rule.PREMISE)
    arguments.update(changes)
    return rule.compare_paths(real,stripped,**arguments)


class Tests(unittest.TestCase):
    def test_exact_overwritten_constants_and_ordered_survivors(self):
        real=path([store(0,ADDRESS,0),store(1,OTHER,3),store(2,ADDRESS,7)])
        stripped=path([store(0,OTHER,3),store(1,ADDRESS,7)])
        proof=compare(real,stripped)
        self.assertEqual(proof['real_removed'][0]['instruction'],0)
        self.assertEqual(proof['surviving_events'],2)
        self.assertFalse(proof['native_admission'])
        self.assertFalse(proof['volatile_classification_complete'])
        compare(real,stripped,manifest=proof)

    def test_observer_alias_load_unknown_access_and_call_are_barriers(self):
        for kind,address in (('load',ADDRESS),('load',('arg',0)),('load',OTHER),
                             ('call',None),('branch',None),('return',None),
                             ('store',('arg',0))):
            barrier=v.Record(1,'barrier',kind,address=address,width=1,value=0)
            real=path([store(0,ADDRESS,0),barrier,store(2,ADDRESS,7)])
            stripped=path([store(0,ADDRESS,7)])
            with self.subTest(kind=kind,address=address),self.assertRaises(v.SemanticError):
                compare(real,stripped)

    def test_partial_overwrites_and_nonconstant_values_refuse(self):
        for replacement in (store(1,ADDRESS,7,2),store(1,ADDRESS,('arg',0))):
            with self.assertRaises(v.SemanticError):
                compare(path([store(0,ADDRESS,0),replacement]),path([replacement]))

    def test_surviving_order_is_not_sorted(self):
        with self.assertRaisesRegex(v.SemanticError,'ordered events'):
            compare(path([store(0,ADDRESS,0),store(1,OTHER,3),store(2,ADDRESS,7)]),
                    path([store(0,ADDRESS,7),store(1,OTHER,3)]))

    def test_return_control_and_address_effects_remain_observable(self):
        real_records=[store(0,ADDRESS,0),store(1,ADDRESS,7)]
        stripped_records=[store(0,ADDRESS,7)]
        with self.assertRaises(v.SemanticError):
            compare(path(real_records,[('return',0)]),path(stripped_records,[('return',7)]))
        with self.assertRaises(v.SemanticError):
            compare(path(real_records,conditions=[('cmp',0,1)]),
                    path(stripped_records,conditions=[('cmp',7,1)]))
        with self.assertRaises(v.SemanticError):
            compare(path(real_records+[store(2,OTHER,3)]),
                    path(stripped_records+[store(1,v.add(ADDRESS,2),3)]))

    def test_opaque_memory_and_call_versions_refuse_without_reindexing(self):
        for value in (('load',1,OTHER,('store',0)),('ret',1),('clobber',1,'r0'),
                      ('ret',('raw-call',1,0))):
            with self.subTest(value=value),self.assertRaisesRegex(v.SemanticError,'version expressions'):
                compare(path([store(0,ADDRESS,0),store(1,ADDRESS,7)],[('return',value)]),
                        path([store(0,ADDRESS,7)],[('return',value)]))

    def test_explicit_scope_and_stale_manifest(self):
        real=path([store(0,ADDRESS,0),store(1,ADDRESS,7)]);other=path([store(0,ADDRESS,7)])
        for change in (dict(selector='ordinary'),dict(premise=''),dict(pinned={0:2,1:1}),dict(manifest={})):
            with self.subTest(change=change),self.assertRaises(v.SemanticError):compare(real,other,**change)

    def test_self_assignment_is_never_discharged(self):
        first=store(0,ADDRESS,0);first.self_assignment=True
        with self.assertRaisesRegex(v.SemanticError,'self-assignment'):
            compare(path([first,store(1,ADDRESS,7)]),path([store(0,ADDRESS,7)]))

    def test_real_executor_paths_and_independent_permutation(self):
        from test_volatile_semantics import assembly,DECLARATION,SYMBOL as real_symbol
        real=assembly('ldr r2, .L3','mov r1, #0','strb r1, [r2, #60]',
                      'mov r1, #255','strb r1, [r2, #60]','bx lr')
        stripped=assembly('ldr r2, .L3','mov r1, #255','strb r1, [r2, #60]','bx lr')
        permuted=real.replace('[r2, #60]','[r2, #61]')
        rf,_=v.parse_assembly(real);sf,_=v.parse_assembly(stripped);pf,_=v.parse_assembly(permuted)
        size,pinned=v.pinned_members(DECLARATION);_,mapping,_=v.perturbed_declaration(DECLARATION)
        signatures={'func_08028C34':(False,())}
        args=('func_08028C34',rf['func_08028C34'],signatures,'real',(real_symbol,size,pinned))
        original=v.explore(*args)[0]
        counterpart=v.replay('func_08028C34',sf['func_08028C34'],signatures,'stripped',
            original.decisions,(real_symbol,size,pinned))
        proof=compare(original,counterpart,symbol=real_symbol,size=size,pinned=pinned)
        self.assertEqual(len(proof['real_removed']),1)
        self.assertEqual(v.perturbation_check('func_08028C34',rf['func_08028C34'],pf['func_08028C34'],
            signatures,real_symbol,size,pinned,mapping),1)

    def test_unchanged_legacy_order_and_permutation_remain_strict(self):
        # Independently check real/permuted accesses through the existing API.
        # A fixed-slot store cannot pass merely because it is overwritten.
        from test_volatile_semantics import assembly,DECLARATION,PREPROCESSED,SYMBOL as real_symbol
        real=assembly('ldr r2, .L3','mov r1, #0','strb r1, [r2, #60]',
                      'mov r1, #255','strb r1, [r2, #60]','bx lr')
        functions,_=v.parse_assembly(real)
        size,pinned=v.pinned_members(DECLARATION)
        _,mapping,_=v.perturbed_declaration(DECLARATION)
        signatures={'func_08028C34':(False,())}
        with self.assertRaises(v.SemanticError):
            v.perturbation_check('func_08028C34',functions['func_08028C34'],
                functions['func_08028C34'],signatures,real_symbol,size,pinned,mapping)
        with self.assertRaises(v.SemanticError):
            v._compare_compiles(real,assembly('ldr r2, .L3','mov r1, #255',
                'strb r1, [r2, #60]','bx lr'),PREPROCESSED,real_symbol,DECLARATION)


if __name__=='__main__':unittest.main()
