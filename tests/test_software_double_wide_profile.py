"""Exact target-state wide multiplication/division composition; no other wide runtime."""
import copy
import report_fixtures
import hashlib
import itertools
import json
import os
from pathlib import Path
import struct
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import test_software_double_profile as fixture
BASE,match,profile=fixture.BASE,fixture.match,fixture.profile
SOURCE='''typedef long long s64;

s64 func_08000000(s64 left, s64 right)
{
    return (left * right >> 16) / (left - right);
}
'''
DIV,MUL,UDIV,UMOD,ZERO=0x08142280,0x08142A20,0x08142AB0,0x08142B28,0x0814274C
# Local agbcc libgcc selections, their entry symbols and typed Thumb bindings.
# __divdi3's only literal object is the leading-zero table at 0836CF98.
LIBGCC=(('L_dvmd_tls','lib1thumb.asm',ZERO,'__div0',{}),
        ('L_udivsi3','lib1thumb.asm',UDIV,'__udivsi3',{'__div0':ZERO}),
        ('L_umodsi3','lib1thumb.asm',UMOD,'__umodsi3',{'__div0':ZERO}),
        ('L_muldi3','libgcc2.c',MUL,'__muldi3',{}),
        ('L_divdi3','libgcc2.c',DIV,'__divdi3',{'__udivsi3':UDIV,'__umodsi3':UMOD}))

class SoftwareDoubleWideTests(fixture.SoftwareDoubleTests):
    def indexes(self,size,count):
        super().indexes(size,count)
        entries=json.loads(self.mapping)
        present={e['rom'] for e in entries}
        entries.extend(dict(rom=f'0x{a:08X}',end=f'0x{b:08X}',mode='thumb',instrs=n)
                       for a,b,n,_ in profile.WIDE_IDENTITIES if f'0x{a:08X}' not in present)
        self.mapping=json.dumps(entries).encode()
        self.index=''.join(f"{int(e['rom'],16):08X} {int(e['end'],16):08X} "
                           f"{int(e['end'],16)-int(e['rom'],16)} {e['instrs']} return\n"
                           for e in entries).encode()

    def refused(self,source,link):
        # Compile and link in one workspace, so refusal is the profile's, not a missing object.
        (self.root/'src/08000000.c').write_text(source)
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            _,_,original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
            symbol,_=match.function_record(original,'func_08000000',BASE,True)
            self.indexes(symbol['size'],1)
            with self.assertRaises(ValueError) as caught:
                link(runner,workspace,original)
        return str(caught.exception)

    def test_natural_original_elf_complete_native_and_fresh_replay(self):
        self.fixture(SOURCE)
        self.assertEqual(set(self.bindings.values()),{'__muldi3','__divdi3'})
        self.assertEqual({s['name'] for s in self.original['symbols'] if s['name'] and not s['section']},
                         {'__muldi3','__divdi3'})
        record=self.manifest['wide_integer']
        self.assertEqual(record['operands'],'entry-register-state')
        self.assertEqual(record['semantics'],'target-machine-state-v1')
        self.assertEqual(record['runtime'],profile.WIDE_RUNTIME)
        self.assertEqual([name for _,name in record['calls']],['__muldi3','__divdi3'])
        self.assertNotIn('signed_division',self.manifest)
        self.assertEqual(len(self.verify()),len(self.instructions))
        self.assertIn('wide multiplication and signed wide division',profile.summary(self.manifest))
        report=self.native_report()
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report_fixtures.uncarried(report),self.root,BASE))
            self.assertFalse(profile.report_matches(
                report.replace('"__divdi3"]','"__muldi3"]'),self.root,BASE))
            path=self.root/'src/08000000.c'
            path.write_text(SOURCE.replace('/ (left - right)','* (left - right)'))
            self.assertFalse(profile.report_matches(report,self.root,BASE))

    def test_bindings_require_the_explicit_software_double_profile(self):
        error=self.refused(SOURCE,lambda runner,workspace,original: match.link_calls(
            runner,workspace,self.args,original,BASE,self.mapping,len(self.runtime_rom),self.runtime_rom))
        self.assertIn('undefined addressed function',error)
        self.assertNotIn('__muldi3',profile.OPERATIONS)
        self.assertFalse(profile.reserved(DIV))
        self.assertEqual([(n,t) for n in ('__muldi3','__divdi3','func_08142A20','__moddi3')
                          for t in (MUL,DIV,MUL|1,UDIV) if profile.wide_call(n,t)],
                         [('__muldi3',MUL),('__divdi3',DIV)])
        with self.assertRaises(ValueError):
            match.parse_data_symbols(json.dumps({'__divdi3':'0x02000000'}).encode())

    def test_other_wide_runtimes_and_aliases_refused(self):
        explicit=('typedef long long s64;\nextern s64 func_08142280(s64, s64);\n'
                  's64 func_08000000(s64 left, s64 right)\n'
                  '{\n    return func_08142280(left * right >> 16, left - right);\n}\n')
        for source,reason in ((SOURCE.replace('/ (left - right)','% (left - right)'),'canonical addressed'),
                              (SOURCE.replace('typedef long long','typedef unsigned long long'),'canonical addressed'),
                              (explicit,'incomplete or mixed')):
            with self.subTest(source=source):
                self.assertIn(reason,self.refused(source,lambda runner,workspace,original: profile.object_bytes(
                    runner,workspace,self.args,original,BASE,self.mapping,self.runtime_rom,self.index)))
        self.fixture(SOURCE)
        for name in ('func_08142A20','func_08142281','__udivdi3','__moddi3','__divdi3_alias'):
            original=copy.deepcopy(self.original)
            for s in original['symbols']:
                if s['name']=='__divdi3': s['name']=name
            runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
            with self.subTest(name=name),runner.workspace() as workspace,self.assertRaises(ValueError):
                profile.object_bytes(runner,workspace,self.args,original,BASE,self.mapping,self.rom,self.index)

    def test_authored_runtime_address_calls_are_refused_on_both_paths(self):
        # Naming either runtime by address is not the compiler's own call.
        authored=('typedef long long s64;\nextern s64 func_08142A20(s64, s64);\n'
                  's64 func_08000000(s64 left, s64 right)\n'
                  '{\n    return func_08142A20(left, right) / (left - right);\n}\n')
        mixed=authored.replace('func_08142A20','func_08142280').replace(
            'func_08142280(left, right) / (left - right)','func_08142280(left * right, left - right)')
        default=lambda runner,workspace,original: match.link_calls(
            runner,workspace,self.args,original,BASE,self.mapping,len(self.runtime_rom),self.runtime_rom)
        selected=lambda runner,workspace,original: profile.object_bytes(
            runner,workspace,self.args,original,BASE,self.mapping,self.runtime_rom,self.index)
        for source,link,reason in ((authored,default,'canonical compiler alias'),
                                   (authored,selected,'canonical versioned proof'),
                                   (mixed,default,'undefined addressed function'),
                                   (mixed,selected,'incomplete or mixed')):
            with self.subTest(source=source,selector=link is selected):
                self.assertIn(reason,self.refused(source,link))

    def test_composes_with_binary64_operations(self):
        self.fixture('typedef long long s64;\ndouble func_08000000(s64 left, s64 right)\n'
                     '{\n    return (double)(left * right) - (double)(left / right);\n}\n')
        self.assertEqual(sorted(self.bindings.values()),
                         ['__divdi3','__floatdidf','__floatdidf','__muldi3','__subdf3'])
        self.assertEqual([name for _,name in self.manifest['wide_integer']['calls']],['__muldi3','__divdi3'])
        self.assertEqual(len(self.verify()),len(self.instructions))
        # A mixed caller still pins the closure: bytes inside __divdi3, __udivsi3 and __umodsi3.
        for address in (0x08142400,0x08142B00,0x08142B80):
            rom=bytearray(self.rom);rom[address-BASE]^=0x10
            with self.subTest(address=hex(address)),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,bytes(rom),self.mapping,self.index,self.manifest)
        del self.manifest['wide_integer']
        with self.assertRaisesRegex(ValueError,'wide-integer target-state evidence differs'):
            self.verify()

    def test_changed_caller_bytes_are_refused(self):
        self.fixture(SOURCE)
        site=next(s for s,n in self.bindings.items() if n=='__divdi3')-BASE
        for offset in (0,site,site+3,len(self.body)-1):
            rom=bytearray(self.rom);rom[offset]^=1
            with self.subTest(offset=offset),self.assertRaisesRegex(ValueError,'caller differs from mapped ROM'):
                profile.verify(self.body,BASE,bytes(rom),self.mapping,self.index,self.manifest)

    def test_wrong_link_and_incomplete_bindings_refused(self):
        self.fixture(SOURCE)
        for alias,wrongs in (('__divdi3',(DIV+2,UDIV,MUL)),('__muldi3',(MUL+2,DIV,0x081430F0))):
            site=next(s for s,n in self.bindings.items() if n==alias)
            for wrong in wrongs:
                altered=copy.deepcopy(self.linked)
                raw=bytearray(altered['text']);d=wrong-site-4
                struct.pack_into('<HH',raw,site-BASE,0xF000|((d>>12)&0x7ff),0xF800|((d>>1)&0x7ff))
                altered['text']=bytes(raw)
                next(s for s in altered['symbols'] if s['name']==alias)['value']=wrong|1
                with self.subTest(alias=alias,wrong=wrong),self.assertRaises(ValueError):
                    match.linked_function_bytes(self.original,altered,'func_08000000',BASE,self.calls,
                        {name:profile.call_target(name) for name in self.bindings.values()},
                        double_bindings=self.bindings)
                calls=dict(self.calls);calls[site]=wrong
                with self.subTest(alias=alias,wrong=wrong,verifier=True),self.assertRaises(ValueError):
                    match.verify_leaf_instructions(bytes(raw[:len(self.body)]),BASE,True,calls,
                        double_context=(self.rom,self.mapping,self.index,self.bindings))
        for alias in ('__muldi3','__divdi3'):
            bindings={s:n for s,n in self.bindings.items() if n!=alias}
            with self.subTest(missing=alias),self.assertRaises(ValueError):
                profile.verify_context(self.body,BASE,self.calls,(self.rom,self.mapping,self.index,bindings))
        bindings=dict(self.bindings)
        site=next(s for s,n in bindings.items() if n=='__divdi3');bindings[site]='__muldi3'
        with self.assertRaises(ValueError):
            profile.verify_context(self.body,BASE,self.calls,(self.rom,self.mapping,self.index,bindings))

    def test_manifest_exact_version_dependencies_sites_and_semantics(self):
        self.fixture(SOURCE)
        for kind in ('missing','runtime','semantics','operands','body','count','end','site','name','extra'):
            m=copy.deepcopy(self.manifest)
            record=m['wide_integer']
            if kind=='missing': del m['wide_integer']
            elif kind in ('runtime','semantics','operands'): record[kind]='unproved'
            elif kind=='body': record['dependencies'][-1][3]='0'*64
            elif kind=='count': record['dependencies'][-1][2]=538
            elif kind=='end': record['dependencies'][-1][1]=0x081426B4
            elif kind=='site': record['calls'][0][0]+=2
            elif kind=='name': record['calls'][0][1]='__divdi3'
            else: record['extra']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError): self.verify(m)

    def test_complete_runtime_and_dual_index_are_strict(self):
        self.fixture(SOURCE)
        for start,end,_,_ in profile.WIDE_IDENTITIES:
            for address in (start,end-2):
                rom=bytearray(self.rom);rom[address-BASE]^=1
                with self.subTest(address=address),self.assertRaises(ValueError):
                    profile.verify(self.body,BASE,bytes(rom),self.mapping,self.index,self.manifest)
        entries=json.loads(self.mapping)
        for kind in ('missing','duplicate','odd','mode','analyzer_span','count','overlap'):
            changed=copy.deepcopy(entries)
            row=next(r for r in changed if r['rom']=='0x08142280')
            if kind=='missing': changed.remove(row)
            elif kind=='duplicate': changed.append(copy.deepcopy(row))
            elif kind=='odd': row['rom']='0x08142281'
            elif kind=='mode': row['mode']='arm'
            elif kind=='analyzer_span': row['end'],row['instrs']='0x081426B4',538
            elif kind=='count': row['instrs']=497
            else: changed.append(dict(rom='0x081426B4',end='0x081426B8',mode='thumb',instrs=2))
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,self.rom,json.dumps(changed).encode(),self.index,self.manifest)
        for old,new in ((b'08142280 081426B8 1080 496',b'08142280 081426B8 1080 497'),
                        (b'08142B28 08142BE8 192 95',b'08142B28 08142BE8 192 96')):
            with self.subTest(index=new),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,self.rom,self.mapping,self.index.replace(old,new),self.manifest)
        # Both indexes agreeing on a wrong count is refused too: the pinned count binds them.
        for (start,end,count,_),delta in itertools.product(profile.WIDE_IDENTITIES,(1,-1)):
            changed=copy.deepcopy(entries)
            next(r for r in changed if r['rom']==f'0x{start:08X}')['instrs']=count+delta
            row=f'{start:08X} {end:08X} {end-start} '.encode()
            with self.subTest(both=hex(start),delta=delta),self.assertRaises(ValueError):
                profile.verify(self.body,BASE,self.rom,json.dumps(changed).encode(),
                               self.index.replace(row+b'%d '%count,row+b'%d '%(count+delta)),self.manifest)

    def test_unproved_returns_writes_and_dependencies_refused(self):
        self.fixture(SOURCE)
        import software_float_profile as floating
        proofs=profile.prove_wide_closure(self.rom,self.mapping,self.index)
        self.assertEqual(set(proofs),{DIV,MUL,UDIV,UMOD,ZERO})
        for start,proof in proofs.items():
            self.assertFalse(proof['writes']);self.assertFalse(proof['stack_reads'])
            self.assertTrue(proof['returns'])
        self.assertEqual(proofs[DIV]['returns'],[0x081426B2])
        entries=json.loads(self.mapping)
        kwargs=dict(scalar_entries=(DIV,),allowed_writes=(),stack_load_widths=(1,4))
        children={key:proofs[key] for key in (UDIV,UMOD,ZERO)}
        for missing in (UDIV,UMOD):
            partial={key:value for key,value in children.items() if key!=missing}
            with self.subTest(missing=missing),self.assertRaisesRegex(ValueError,'no native dependency proof'):
                floating.prove_runtime(self.rom,entries,DIV,0x081426B8,496,partial,
                                       call_edges=profile.WIDE_EDGES,**kwargs)
        with self.assertRaisesRegex(ValueError,'local CFG/closure differs'):
            floating.prove_runtime(self.rom,entries,DIV,0x081426B8,496,children,
                                   call_edges=profile.WIDE_EDGES[1:],**kwargs)
        # A caller-memory store, str r4,[r1]; bx r1, which the native CFG refuses
        # before any return-register check; str r4,[sp,#0x50] over the saved LR
        # and add sp,#0x30, both with the CFG intact; pop {r4-r6} for r4-r7.
        for site,word,reason in ((0x0814228E,0x600C,'unbounded external write'),
                                 (0x081426B2,0x4708,'local CFG/closure differs'),
                                 (0x0814228E,0x9414,'overwrites a saved register'),
                                 (0x081426A4,0xB00C,'pops outside its saved frame'),
                                 (0x081426AE,0xBC70,'return/register restoration is unproved')):
            rom=bytearray(self.rom);struct.pack_into('<H',rom,site-BASE,word)
            with self.subTest(site=site,word=word),self.assertRaisesRegex(ValueError,reason):
                floating.prove_runtime(bytes(rom),entries,DIV,0x081426B8,496,children,
                                       call_edges=profile.WIDE_EDGES,**kwargs)
        # The closure refuses a body that reads its caller's stack even when its
        # digest is re-pinned: ldr r5,[sp,#0x24] in __muldi3 reads at entry SP.
        rom=bytearray(self.rom);struct.pack_into('<H',rom,0x08142A7C-BASE,0x9D09)
        identities=tuple((s,e,n,hashlib.sha256(rom[s-BASE:e-BASE]).hexdigest())
                         for s,e,n,_ in profile.WIDE_IDENTITIES)
        with patch.object(profile,'WIDE_IDENTITIES',identities), \
                self.assertRaisesRegex(ValueError,'stack access exceeds its frame'):
            profile.prove_wide_closure(bytes(rom),self.mapping,self.index)

    SPIN_SOURCE=('typedef long long s64;\ns64 func_08000000(int count, s64 left, s64 right)\n{\n'
                 '    if (count <= 2)\n        for (;;)\n            ;\n    return left OPERATOR right;\n}\n')

    def spin_object(self,operator,source=None):
        """(body, calls, bindings, rom) of a spin-guarded caller of one wide runtime, in this root."""
        (self.root/'src/08000000.c').write_text((source or self.SPIN_SOURCE).replace('OPERATOR',operator))
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            _,_,original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
            symbol,_=match.function_record(original,'func_08000000',BASE,True)
            self.indexes(symbol['size'],1)
            body,calls,bindings=profile.object_bytes(runner,workspace,self.args,original,BASE,
                                                     self.mapping,self.runtime_rom,self.index)
        rom=bytearray(self.runtime_rom);rom[:len(body)]=body
        return body,calls,bindings,bytes(rom)

    def test_inert_spins_compose_with_bound_wide_runtimes(self):
        for operator,name,target in (('*','__muldi3',MUL),('/','__divdi3',DIV)):
            with self.subTest(name=name):
                body,calls,bindings,rom=self.spin_object(operator)
                self.assertEqual(set(bindings.values()),{name})
                self.assertEqual(set(calls.values()),{target})
                context=(rom,self.mapping,self.index,bindings)
                # Without the spin record the self-branch still has no verified return.
                with self.assertRaisesRegex(ValueError,'no path to a verified return'):
                    match.verify_leaf_instructions(body,BASE,True,calls,double_context=context)
                spin={}
                instructions=match.verify_leaf_instructions(body,BASE,True,calls,double_context=context,
                                                            inert_spin_context=spin)
                self.assertEqual(len(spin['spins']),1)
                self.indexes(len(body),len(instructions))
                manifest=profile.make_manifest(calls,BASE,bindings,instructions,spins=spin['spins'])
                self.assertEqual(manifest['inert_spin'],{'schema':profile.INERT_SPIN_SCHEMA,'spins':spin['spins']})
                self.assertEqual([row[1] for row in manifest['wide_integer']['calls']],[name])
                self.assertEqual(len(profile.verify(body,BASE,rom,self.mapping,self.index,manifest)),len(instructions))
                # The spin record is still checked against the converged CFG.
                for spins in ([],[spin['spins'][0]+2],spin['spins']+[0]):
                    altered=copy.deepcopy(manifest);altered['inert_spin']['spins']=spins
                    with self.assertRaises(ValueError):
                        profile.verify(body,BASE,rom,self.mapping,self.index,altered)
                # The exemption is the context's own canonical binding at that exact site.
                site=next(iter(calls))
                other='__divdi3' if name=='__muldi3' else '__muldi3'
                for forged in ({site:other},{},{site+2:name},{**bindings,site+4:name}):
                    with self.assertRaises(ValueError):
                        match.verify_leaf_instructions(body,BASE,True,calls,inert_spin_context={},
                                                       double_context=(rom,self.mapping,self.index,forged))
                # One line restores the refusal, in the walk and in replay.
                with patch.object(profile.WIDE_SPINS,'enabled',False):
                    with self.assertRaisesRegex(ValueError,'inert spins exclude unproved arithmetic runtimes'):
                        match.verify_leaf_instructions(body,BASE,True,calls,double_context=context,
                                                       inert_spin_context={})
                    with self.assertRaisesRegex(ValueError,'inert spins exclude unproved arithmetic runtimes'):
                        profile.verify(body,BASE,rom,self.mapping,self.index,manifest)

    def test_a_wide_call_inside_the_nonreturning_region_refuses(self):
        # The quotient is computed only on the path that ends in the spin. That region must hold
        # nothing but the inert self-branch, so the exemption never admits a wide call inside it.
        source=('typedef long long s64;\ns64 func_08000000(int count, s64 *p)\n{\n'
                '    if (count <= 2) {\n        p[0] = p[1] OPERATOR p[2];\n        for (;;)\n            ;\n    }\n'
                '    return p[1] * p[2];\n}\n')
        body,calls,bindings,rom=self.spin_object('/',source)
        self.assertIn('__divdi3',bindings.values())
        context=(rom,self.mapping,self.index,bindings)
        with self.assertRaisesRegex(ValueError,'no path to a verified return'):
            match.verify_leaf_instructions(body,BASE,True,calls,double_context=context)
        with self.assertRaisesRegex(ValueError,'non-return-reaching node must itself be an inert'):
            match.verify_leaf_instructions(body,BASE,True,calls,double_context=context,inert_spin_context={})

    def test_match_py_issues_and_rechecks_a_spin_guarded_wide_report(self):
        # match.py runs as __main__ when it issues a report: run it as a separate process, as the
        # decomp's tools do, so the rule is exercised where reports are written.
        import sys
        body,calls,bindings,rom=self.spin_object('/')
        instructions=match.verify_leaf_instructions(body,BASE,True,calls,inert_spin_context={},
                                                    double_context=(rom,self.mapping,self.index,bindings))
        self.indexes(len(body),len(instructions))
        (self.root/'config/functions.json').write_bytes(self.mapping)
        (self.root/'symbols/functions.txt').write_bytes(self.index)
        (self.root/'config/data_symbols.json').write_text('{}')
        (self.root/'baserom.bin').write_bytes(rom)
        tool=Path(match.__file__).resolve()
        environment=dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin'),PYTHONDONTWRITEBYTECODE='1')
        def run(*options):
            return subprocess.run([sys.executable,str(tool),'--root',str(self.root),'--software-double-profile',
                                   profile.SELECTOR,*options,'0x08000000'],capture_output=True,text=True,
                                  env=environment,timeout=600)
        result=run()
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('verdict MATCH - byte identical',result.stdout)
        report=(self.root/'docs/match/08000000.md').read_text()
        self.assertIn('software-double-inert-self-spin-v1',report)
        self.assertIn('__divdi3',report)
        result=run('--check-report','--no-write')
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        self.assertIn('report  identical to the saved docs/match/08000000.md',result.stdout)

    def test_wide_spin_exemption_stays_inside_the_selector(self):
        # Outside the software-double context nothing changed: 08142A20 is a reserved body and
        # still refuses beside a spin; 08142280 stays an ordinary entry-only call, as before.
        body,calls,bindings,rom=self.spin_object('*')
        with self.assertRaisesRegex(ValueError,'inert spins exclude unproved arithmetic runtimes'):
            match.verify_leaf_instructions(body,BASE,True,calls,inert_spin_context={})
        body,calls,bindings,rom=self.spin_object('/')
        spin={}
        instructions=match.verify_leaf_instructions(body,BASE,True,calls,inert_spin_context=spin)
        self.assertEqual(len(spin['spins']),1)
        self.assertEqual(set(calls.values()),{DIV})
        self.assertTrue(instructions)

    def test_spin_wide_call_binds_only_the_canonical_site(self):
        bindings={BASE+8:'__muldi3',BASE+16:'__divdi3',BASE+24:'__modsi3'}
        context=(b'',b'',b'',bindings)
        self.assertTrue(profile.spin_wide_call(context,BASE+8,MUL))
        self.assertTrue(profile.spin_wide_call(context,BASE+16,DIV))
        for site,target in ((BASE+8,DIV),(BASE+16,MUL),(BASE+8,MUL+2),(BASE+24,0x08142950),
                            (BASE+12,MUL),('0x08000008',MUL),(None,MUL)):
            with self.subTest(site=site,target=target):
                self.assertFalse(profile.spin_wide_call(context,site,target))
        self.assertFalse(profile.spin_wide_call(None,BASE+8,MUL))
        self.assertFalse(profile.spin_wide_call((b'',b'',b'',[(BASE+8,'__muldi3')]),BASE+8,MUL))
        with patch.object(profile.WIDE_SPINS,'enabled',False):
            self.assertFalse(profile.spin_wide_call(context,BASE+8,MUL))

    def test_other_runtimes_beside_a_spin_still_refuse(self):
        # A spin beside a wide runtime and a call thunk, or beside an unbound wide runtime.
        sources=(
            'typedef long long s64;\ns64 func_08000000(int count, s64 left, s64 (*f)(s64))\n{\n'
            '    if (count <= 2)\n        for (;;)\n            ;\n    return f(left * left);\n}\n',
            'typedef long long s64;\ns64 func_08000000(int count, s64 left, s64 right)\n{\n'
            '    if (count <= 2)\n        for (;;)\n            ;\n    return left % right;\n}\n')
        for source in sources:
            with self.subTest(source=source.splitlines()[-2]):
                (self.root/'src/08000000.c').write_text(source)
                runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
                with runner.workspace() as workspace:
                    _,_,original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
                    symbol,_=match.function_record(original,'func_08000000',BASE,True)
                    self.indexes(symbol['size'],1)
                    with self.assertRaises(ValueError):
                        body,calls,bindings=profile.object_bytes(runner,workspace,self.args,original,BASE,
                                                                 self.mapping,self.runtime_rom,self.index)
                        rom=bytearray(self.runtime_rom);rom[:len(body)]=body
                        match.verify_leaf_instructions(body,BASE,True,calls,inert_spin_context={},
                            double_context=(bytes(rom),self.mapping,self.index,bindings))

class WideLibgccProvenanceTests(unittest.TestCase):
    """Every pinned closure body is a local agbcc libgcc selection, not a hand fixture."""
    def build(self,work,selection,source,start,entry,bindings,flags):
        agbcc=Path(os.path.expandvars(match.DEFAULT_CC)).parents[1]
        stem=work/f'{selection}{len(flags)}'
        def run(*command):
            subprocess.run([str(part) for part in command],check=True,capture_output=True)
        if source.endswith('.c'):
            run(match.DEFAULT_CPP,'-undef','-I',agbcc/'ginclude','-nostdinc',f'-D{selection}',
                '-o',stem.with_suffix('.i'),agbcc/'libgcc'/source)
            run(os.path.expandvars(match.DEFAULT_CC),*flags,stem.with_suffix('.i'),'-o',stem.with_suffix('.s'))
        else:
            run(match.DEFAULT_CPP,'-undef','-nostdinc',f'-D{selection}','-x','assembler-with-cpp',
                '-o',stem.with_suffix('.s'),agbcc/'libgcc'/source)
        with stem.with_suffix('.s').open('a') as stream:
            stream.write('.text\n\t.align\t2, 0\n')
        run(match.DEFAULT_AS,'-mcpu=arm7tdmi','-o',stem.with_suffix('.o'),stem.with_suffix('.s'))
        objects=[stem.with_suffix('.o')]
        if bindings:
            typed=work/f'{selection}-bindings.s'
            typed.write_text('.syntax unified\n.thumb\n'+''.join(
                f'.global {name}\n.type {name}, %function\n.thumb_set {name}, 0x{value|1:08X}\n'
                for name,value in bindings.items()))
            run(match.DEFAULT_AS,'-mthumb-interwork','-o',typed.with_suffix('.o'),typed)
            objects.append(typed.with_suffix('.o'))
        run(match.DEFAULT_LD,'-o',stem.with_suffix('.elf'),'-e',entry,f'-Ttext=0x{start:08X}',
            '--section-start=.rodata=0x0836CF98',*objects)
        run(match.DEFAULT_OBJCOPY,'-O','binary','-j','.text',stem.with_suffix('.elf'),stem.with_suffix('.bin'))
        return stem.with_suffix('.bin').read_bytes()

    def test_local_agbcc_libgcc_selections_rebuild_every_pinned_body(self):
        agbcc=Path(os.path.expandvars(match.DEFAULT_CC)).parents[1]
        if not all((agbcc/'libgcc'/name).is_file() for name in ('libgcc2.c','lib1thumb.asm')) or \
                not (agbcc/'ginclude').is_dir():
            # A local audit; FFTA_REQUIRE_LIBGCC=1 makes absent sources a failure.
            if os.environ.get('FFTA_REQUIRE_LIBGCC')=='1':
                self.fail(f'FFTA_REQUIRE_LIBGCC=1 but {agbcc} lacks libgcc2.c, lib1thumb.asm or ginclude')
            self.skipTest('the local agbcc libgcc sources are unavailable')
        pinned={start:(end,digest) for start,end,_,digest in profile.WIDE_IDENTITIES}
        self.assertEqual(set(pinned),{start for _,_,start,_,_ in LIBGCC})
        scratch=Path(os.environ.get('FFTA_TEST_SCRATCH',fixture.ROOT/'build'));scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='wide_libgcc_',dir=scratch) as work:
            for selection,source,start,entry,bindings in LIBGCC:
                end,digest=pinned[start]
                with self.subTest(selection=selection):
                    text=self.build(Path(work),selection,source,start,entry,bindings,match.DEFAULT_FLAGS.split())
                    self.assertEqual(hashlib.sha256(text[:end-start]).hexdigest(),digest)
                    self.assertEqual(text[end-start:].strip(b'\0'),b'')
            # The fixed interworking flags are part of the identity.
            for selection,source,start,entry,bindings in LIBGCC[3:]:
                end,digest=pinned[start]
                with self.subTest(selection=selection,flags='-O2'):
                    text=self.build(Path(work),selection,source,start,entry,bindings,['-O2'])
                    self.assertNotEqual(hashlib.sha256(text[:end-start]).hexdigest(),digest)

    def test_required_libgcc_sources_turn_the_skip_into_a_failure(self):
        audit='test_local_agbcc_libgcc_selections_rebuild_every_pinned_body'
        with tempfile.TemporaryDirectory() as empty:
            for value,expected in (('',(1,0)),('1',(0,1))):
                result=unittest.TestResult()
                with self.subTest(value=value),patch.object(match,'DEFAULT_CC',f'{empty}/bin/agbcc'), \
                        patch.dict(os.environ,{'FFTA_REQUIRE_LIBGCC':value}):
                    WideLibgccProvenanceTests(audit).run(result)
                    self.assertEqual((len(result.skipped),len(result.failures)),expected)

def load_tests(loader, tests, pattern):
    # The base suite runs separately; exercise each new behavior once here.
    suite=unittest.TestSuite()
    for case in (SoftwareDoubleWideTests,WideLibgccProvenanceTests):
        for name in sorted(vars(case)):
            if name.startswith('test_'): suite.addTest(case(name))
    return suite

if __name__=='__main__': unittest.main()
