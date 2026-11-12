"""Typed event identity tests retain ordering and fail closed provenance."""
import unittest
import volatile_semantics as v
import overwritten_control_store_composition as c


def path(trace): return v.Path([], [], trace, [])


class Tests(unittest.TestCase):
    def positive(self):
        real=path([('store',1,('sym','control'),0),('store',1,('sym','control'),7),
                   ('call','f',()),('return',('load',1,('sym','other'),('call',2)))])
        stripped=path(real.trace[1:3]+[('return',('load',1,('sym','other'),('call',1)))])
        return real,stripped

    def test_later_memory_versions_and_replay(self):
        a,b=self.positive(); proof=c.compare_survivors(a,b,[{'event':0}],[])
        c.compare_survivors(a,b,[{'event':0}],[],manifest=proof)
        with self.assertRaises(v.SemanticError):
            c.compare_survivors(a,b,[{'event':0}],[],manifest={})

    def test_actual_executor_later_call_return(self):
        from test_volatile_semantics import assembly, DECLARATION, SYMBOL
        real = assembly('push {lr}', 'ldr r2, .L3', 'mov r0, #0',
            'strb r0, [r2, #60]', 'mov r0, #19', 'strb r0, [r2, #60]',
            'bl f', 'pop {r1}', 'bx r1')
        stripped = real.replace('\tmov r0, #0\n\tstrb r0, [r2, #60]\n','')
        size,pinned=v.pinned_members(DECLARATION)
        signatures={'func_08028C34':(True,0),'f':(True,0)}
        def execute(text):
            function=v.parse_assembly(text)[0]['func_08028C34']
            return v.explore('func_08028C34',function,signatures,'real',(SYMBOL,size,pinned))[0]
        a,b=execute(real),execute(stripped)
        proof=c.compare_survivors(a,b,[{'event':0}],[])
        self.assertEqual(proof['real'][-1], ('return',('ret',1)))

    def test_removed_forward_foreign_wrong_kind_and_superseded(self):
        for reference in (-1,0,1,3,99):
            a,b=self.positive()
            a.trace[-1]=('return',('ret',reference))
            with self.subTest(reference=reference),self.assertRaises(v.SemanticError):
                c.compare_survivors(a,b,[{'event':0}],[])
        a,b=self.positive(); a.trace.insert(3,('call','g',()))
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,b,[{'event':0}],[])

    def test_distinct_repeated_calls_and_integer_values(self):
        a=path([('call','f',()),('call','f',()),('return',('ret',0))])
        b=path([('call','f',()),('call','f',()),('return',('ret',1))])
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,b,[],[])
        a.trace[-1]=('return',123); b.trace[-1]=('return',124)
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,b,[],[])

    def test_cross_instance_call_provenance_and_tainted_address(self):
        a=path([('call','f',()),('return',('ret',0))])
        b=path([('call','g',()),('return',('ret',0))])
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,b,[],[])
        a=path([('call','f',()),('store',1,('ret',0),7),('return',)])
        b=path([('call','f',()),('store',1,('sym','control'),7),('return',)])
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,b,[],[])

    def test_unknown_raw_conditions_escape_and_overlap_provenance(self):
        for expression in (('unknown',0),('ret',('raw-call',0)),
                           ('load',1,('sym','other'),('store',0))):
            a=path([('store',1,('sym','control'),1),('return',expression)])
            with self.assertRaises(v.SemanticError): c.compare_survivors(a,a,[],[])
        a=path([('call','f',()),('return',0)]); a.conditions=[('ret',0)]
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,a,[],[])
        a=path([('escape',())])
        with self.assertRaises(v.SemanticError): c.compare_survivors(a,a,[],[])


if __name__=='__main__':unittest.main()
