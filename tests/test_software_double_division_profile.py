"""Exact target-state DIV composition; constant quotient policy stays isolated."""
import copy
import json
import struct
import unittest
import test_software_double_profile as fixture
import test_software_double_mod_profile as remainder_fixture
BASE,match,profile=fixture.BASE,fixture.match,fixture.profile
SOURCE='''double func_08000000(double value, int numerator, int denominator)
{
    return value + (double)(numerator / denominator);
}
'''

class SoftwareDoubleDivisionTests(fixture.SoftwareDoubleTests):
    def indexes(self,size,count):
        super().indexes(size,count)
        entries=json.loads(self.mapping)
        entries.extend(dict(rom=f'0x{a:08X}',end=f'0x{b:08X}',mode='thumb',instrs=n)
                       for a,b,n,_ in profile.DIVISION_IDENTITIES)
        self.mapping=json.dumps(entries).encode()
        self.index=''.join(f"{int(e['rom'],16):08X} {int(e['end'],16):08X} "
                           f"{int(e['end'],16)-int(e['rom'],16)} {e['instrs']} return\n"
                           for e in entries).encode()

    def test_natural_dynamic_original_elf_complete_native_and_fresh_replay(self):
        self.fixture(SOURCE)
        self.assertEqual(set(self.bindings.values()),{'__adddf3','__floatsidf','__divsi3'})
        self.assertEqual({s['name'] for s in self.original['symbols'] if s['name'] and not s['section']},
                         {'__adddf3','__floatsidf','__divsi3'})
        self.assertEqual(self.manifest['signed_division']['operands'],'entry-register-state')
        self.assertEqual(self.manifest['signed_division']['semantics'],'target-machine-state-v1')
        self.assertEqual(len(self.verify()),len(self.instructions))
        report=self.native_report()
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
            path=self.root/'src/08000000.c'
            path.write_text(SOURCE.replace('numerator / denominator','numerator / 7'))
            self.assertFalse(profile.report_matches(report,self.root,BASE))

    def test_original_elf_alias_addend_and_wrong_link_refused(self):
        self.fixture(SOURCE)
        for name in ('func_081426B8','func_081426B9','__div0','__udivsi3','__divsi3_alias'):
            original=copy.deepcopy(self.original)
            for s in original['symbols']:
                if s['name']=='__divsi3': s['name']=name
            runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
            with self.subTest(name=name),runner.workspace() as workspace,self.assertRaises(ValueError):
                profile.object_bytes(runner,workspace,self.args,original,BASE,self.mapping,self.rom,self.index)
        with self.assertRaisesRegex(ValueError,'noncanonical addend'):
            self.fixture(assembly='push {lr}\nbl __divsi3+2\nbl __floatsidf\nbl __adddf3\npop {r1}\nbx r1')
        self.fixture(SOURCE)
        site=next(s for s,n in self.bindings.items() if n=='__divsi3')
        for wrong in (0x081426BA,0x0814274C,0x08142950):
            altered=copy.deepcopy(self.linked)
            raw=bytearray(altered['text']);d=wrong-site-4
            struct.pack_into('<HH',raw,site-BASE,0xF000|((d>>12)&0x7ff),0xF800|((d>>1)&0x7ff))
            altered['text']=bytes(raw)
            next(s for s in altered['symbols'] if s['name']=='__divsi3')['value']=wrong|1
            with self.subTest(wrong=wrong),self.assertRaises(ValueError):
                match.linked_function_bytes(self.original,altered,'func_08000000',BASE,self.calls,
                    {name:profile.call_target(name) for name in self.bindings.values()},
                    double_bindings=self.bindings)
            calls=dict(self.calls);calls[site]=wrong
            with self.assertRaises(ValueError):
                match.verify_leaf_instructions(bytes(raw[:len(self.body)]),BASE,True,calls,
                    double_context=(self.rom,self.mapping,self.index,self.bindings))
        bindings={s:n for s,n in self.bindings.items() if n!='__divsi3'}
        with self.assertRaises(ValueError):
            profile.verify_context(self.body,BASE,self.calls,(self.rom,self.mapping,self.index,bindings))

    def test_manifest_exact_version_dependencies_sites_and_semantics(self):
        self.fixture(SOURCE)
        for kind in ('missing','runtime','semantics','operands','body','count','site','extra'):
            m=copy.deepcopy(self.manifest)
            if kind=='missing': del m['signed_division']
            elif kind in ('runtime','semantics','operands'): m['signed_division'][kind]='unproved'
            elif kind=='body': m['signed_division']['dependencies'][0][3]='0'*64
            elif kind=='count': m['signed_division']['dependencies'][0][2]=73
            elif kind=='site': m['signed_division']['calls'][0]+=2
            else: m['signed_division']['extra']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError): self.verify(m)

    def test_complete_runtime_and_dual_index_are_strict(self):
        self.fixture(SOURCE)
        for start,end,_,_ in profile.DIVISION_IDENTITIES:
            rom=bytearray(self.rom);rom[start-BASE]^=1
            with self.subTest(start=start),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,bytes(rom),self.mapping,self.index,self.manifest)
        entries=json.loads(self.mapping)
        for kind in ('missing','duplicate','odd','mode','span','overlap','count'):
            changed=copy.deepcopy(entries)
            row=next(r for r in changed if r['rom']=='0x081426B8')
            if kind=='missing': changed.remove(row)
            elif kind=='duplicate': changed.append(copy.deepcopy(row))
            elif kind=='odd': row['rom']='0x081426B9'
            elif kind=='mode': row['mode']='arm'
            elif kind=='span': row['end']='0x08142748'
            elif kind=='count': row['instrs']=73
            else: changed.append(dict(rom='0x081426BA',end='0x081426BC',mode='thumb',instrs=1))
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,self.rom,json.dumps(changed).encode(),self.index,self.manifest)
        with self.assertRaises(ValueError):
            profile.verify(self.body,BASE,self.rom,self.mapping,
                           self.index.replace(b'081426B8 0814274A 146 72',b'081426B8 0814274A 146 73'),self.manifest)

    def test_unproved_returns_writes_and_zero_callee_refused(self):
        self.fixture(SOURCE)
        import software_float_profile as floating
        entries=json.loads(self.mapping);zero=0x0814274C;start=0x081426B8
        proofs=profile.prove_division_closure(self.rom,self.mapping,self.index)
        self.assertEqual(set(proofs),{start,zero})
        self.assertEqual(set(proofs[start]['returns']),{0x0814273E,0x08142748})
        self.assertFalse(proofs[start]['writes']);self.assertFalse(proofs[start]['stack_reads'])
        kwargs=dict(call_edges=((0x08142742,zero),),scalar_entries=(start,),allowed_writes=())
        for sites in ((),(0x0814273E,),(0x0814273C,0x08142748),(0x0814273E,0x08142748,start)):
            with self.subTest(sites=sites),self.assertRaises(ValueError):
                floating.prove_runtime(self.rom,entries,start,0x0814274A,72,{zero:proofs[zero]},
                                       thumb_pc_returns=sites,**kwargs)
        with self.assertRaises(ValueError):
            floating.prove_runtime(self.rom,entries,start,0x0814274A,72,{},
                                   thumb_pc_returns=(0x0814273E,0x08142748),**kwargs)
        for site,word in ((0x0814273E,0x46A7),(0x0814273C,0xBC20),(0x08142748,0xBC01),
                          (0x081426BE,0x6008)):
            rom=bytearray(self.rom);struct.pack_into('<H',rom,site-BASE,word)
            with self.subTest(site=site),self.assertRaises(ValueError):
                floating.prove_runtime(bytes(rom),entries,start,0x0814274A,72,{zero:proofs[zero]},
                                       thumb_pc_returns=(0x0814273E,0x08142748),**kwargs)

    def test_standalone_constant_policy_not_widened(self):
        for denominator,accepted in (('7',True),('denominator',False),('-7',False)):
            source='int func_08000000(int numerator,int denominator) {return numerator/'+denominator+';}\n'
            (self.root/'src/08000000.c').write_text(source)
            runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
            with runner.workspace() as workspace:
                _,_,original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
                symbol,_=match.function_record(original,'func_08000000',BASE,True)
                self.indexes(symbol['size'],1);bindings={}
                body,calls,_=match.link_calls(runner,workspace,self.args,original,BASE,self.mapping,
                    len(self.runtime_rom),self.runtime_rom,divsi3_bindings=bindings)
            rom=bytearray(self.runtime_rom);rom[:len(body)]=body;observed={}
            if accepted:
                match.verify_leaf_instructions(body,BASE,True,calls,
                    divsi3_context=(bytes(rom),self.mapping,bindings,observed))
                self.assertEqual(list(observed.values()),[7])
            else:
                with self.assertRaisesRegex(ValueError,'CFG-proven positive signed32 constant'):
                    match.verify_leaf_instructions(body,BASE,True,calls,
                        divsi3_context=(bytes(rom),self.mapping,bindings,observed))
            with runner.workspace() as workspace,self.assertRaises(ValueError):
                profile.object_bytes(runner,workspace,self.args,original,BASE,self.mapping,bytes(rom),self.index)

class SoftwareDoubleDivisionModTests(SoftwareDoubleDivisionTests):
    def indexes(self,size,count):
        super().indexes(size,count)
        entries=json.loads(self.mapping)
        entries.append(dict(rom='0x08142950',end='0x08142A1E',mode='thumb',instrs=102))
        self.mapping=json.dumps(entries).encode()
        self.index=''.join(f"{int(e['rom'],16):08X} {int(e['end'],16):08X} "
                           f"{int(e['end'],16)-int(e['rom'],16)} {e['instrs']} return\n" for e in entries).encode()

    def test_dynamic_division_and_bounded_remainder_compose(self):
        source='int func_08000000(double v,int n,int d) { return (short)(int)(v+(double)(n/d))%7; }\n'
        self.fixture(source)
        self.assertIn('signed_division',self.manifest);self.assertIn('remainder',self.manifest)
        self.assertEqual(self.manifest['remainder']['dividend'],'signed16')
        self.verify()
        self.native_report()
        for unsafe in (source.replace('(short)(int)','(int)'),source.replace('%7','%d')):
            with self.subTest(source=unsafe),self.assertRaisesRegex(ValueError,'signed16 r0 and nonzero r1'):
                self.fixture(unsafe)

def load_tests(loader, tests, pattern):
    # Base suites run separately; exercise each new behavior once here.
    suite=unittest.TestSuite()
    for cls in (SoftwareDoubleDivisionTests,SoftwareDoubleDivisionModTests):
        for name in sorted(vars(cls)):
            if name.startswith('test_'): suite.addTest(cls(name))
    return suite

if __name__=='__main__': unittest.main()
