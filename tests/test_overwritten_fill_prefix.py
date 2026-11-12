"""Exact conditional CpuSet prefix composed with classified dead stores."""
import unittest
import test_volatile_cpuset_local_source as local
import test_volatile_semantics as fixtures
import volatile_semantics as v
import overwritten_control_store_composition as c
import bios_cpuset_fill_profile as bios


class Tests(unittest.TestCase):
    def setUp(self):
        self.fixture=local.LocalSourceTests('runTest'); self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.interface=self.fixture.interface()
        suffix=('ldr r2, .L3','ldrb r0, [r2, #60]','mov r0, #0','strb r0, [r2, #60]',
                'ldrb r0, [r2, #60]','mov r0, #19','strb r0, [r2, #60]')
        self.real=self.fixture.body(second=2,suffix=suffix)
        self.stripped=self.fixture.body(second=2,suffix=('ldr r2, .L3','mov r0, #19','strb r0, [r2, #60]'))

    def compare(self, stripped=None, interface=True, manifest=None, real=None):
        a=real or self.real; b=stripped or self.stripped
        functions=[v.parse_assembly(text)[0]['func_08028C34'] for text in (a,b,a.replace('#60','#61'))]
        size,pinned=v.pinned_members(fixtures.DECLARATION)
        _,mapping,_=v.perturbed_declaration(fixtures.DECLARATION)
        return c.compare_function('func_08028C34',*functions,
            {'func_08028C34':(False,0),bios.NAME:(False,3)},fixtures.SYMBOL,size,pinned,mapping,
            selector=c.SELECTOR,premise=c.PREMISE,interfaces=self.interface if interface else None,
            manifest=manifest)

    def test_actual_two_fill_prefix_and_manifest(self):
        proof=self.compare()
        self.assertEqual(len(proof['paths'][0]['unchanged_fill_prefix']),5)
        self.compare(manifest=proof)
        with self.assertRaises(v.SemanticError):self.compare(manifest={})

    def test_changed_content_offset_control_destination_and_provider(self):
        for old,new in (('mov\tr3, #0','mov\tr3, #1'),('add\tr0, r0, #2','add\tr0, r0, #4'),
                        ('.word\t16777472','.word\t16777473'),('.word\tdestination','.word\tother'),
                        ('strh\tr3, [r0]','str\tr3, [r0]')):
            with self.subTest(new=new),self.assertRaises(v.SemanticError):
                self.compare(stripped=self.stripped.replace(old,new))
        with self.assertRaises(v.SemanticError):self.compare(interface=False)

    def test_record_provenance_stack_mismatch_and_raw_dependency(self):
        import copy
        size,pinned=v.pinned_members(fixtures.DECLARATION)
        function=v.parse_assembly(self.real)[0]['func_08028C34']
        original=v.explore('func_08028C34',function,
            {'func_08028C34':(False,0),bios.NAME:(False,3)},'real',
            (fixtures.SYMBOL,size,pinned),self.interface)[0]
        for mutation in ('premise','stack','raw'):
            changed=copy.deepcopy(original)
            if mutation == 'premise':
                next(row for row in changed.records if row.kind=='call').local_fill_premise='forged'
            elif mutation == 'stack':
                rows=[row for row in changed.records if row.kind=='store' and type(row.value) is int]
                rows[1].width=1
            else:
                changed.trace[-1]=('return',('ret',('raw-call',4,('frame',2))))
            with self.subTest(mutation=mutation),self.assertRaises(v.SemanticError):
                c.unchanged_fill_prefix(original,changed,self.interface)

    def test_no_global_deletion_before_prefix_or_later_stack_effect(self):
        for changed in (self.real.replace('ldr\tr1, .Ldestination',
                'ldr r2, .L3\n\tmov r3, #0\n\tstrb r3, [r2, #60]\n\tldr\tr1, .Ldestination',1),
                self.real.replace('add\tsp, sp, #8','strh r0, [sp]\n\tadd\tsp, sp, #8')):
            with self.assertRaises(v.SemanticError):self.compare(real=changed)


if __name__=='__main__':unittest.main()
