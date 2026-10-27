"""Native canonical double arithmetic and bounded signed remainder composition."""
import copy
import json
import unittest
from unittest.mock import patch
import test_software_double_profile as fixture
BASE, match, profile = fixture.BASE, fixture.match, fixture.profile

SOURCE = """int func_08000000(double value)
{
    return (short)(int)(value + 1.0) % 7;
}
"""

class SoftwareDoubleModTests(fixture.SoftwareDoubleTests):
    def indexes(self, size, count):
        super().indexes(size, count)
        entries = json.loads(self.mapping)
        entries.extend({"rom": f"0x{a:08X}", "end": f"0x{b:08X}",
                        "mode": "thumb", "instrs": 102 if a == match.modsi3.ADDRESS else 1}
                       for a, b, _ in match.modsi3.IDENTITIES)
        self.mapping = json.dumps(entries).encode()
        self.index = "".join(f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} "
                             f"{int(e['end'], 16)-int(e['rom'], 16)} {e['instrs']} return\n"
                             for e in entries).encode()

    def test_canonical_native_natural_composition_and_replay(self):
        self.fixture(SOURCE)
        self.assertEqual(set(self.bindings.values()), {"__adddf3", "__fixdfsi", "__modsi3"})
        self.assertEqual(self.manifest['remainder']['dividend'], 'signed16')
        self.assertEqual(len(self.verify()), len(self.instructions))
        self.assertEqual({s['name'] for s in self.original['symbols'] if not s['section'] and s['name']},
                         {"__adddf3", "__fixdfsi", "__modsi3"})
        report = self.native_report()
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            (self.root/'src/08000000.c').write_text(SOURCE.replace('% 7', '% 9'))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_remainder_domain_and_divisor_are_not_assumed(self):
        for source in (SOURCE.replace('(short)(int)', '(int)'),
                       SOURCE.replace('(double value)', '(double value, int divisor)').replace('% 7', '% divisor')):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
                self.fixture(source)

    def test_natural_fixed_frame_keeps_complete_stack_proof_and_replay(self):
        source = """extern double func_08000200(double);
int func_08000000(double value) {
    double a=func_08000200(value), b=func_08000200(value+1.0);
    double c=func_08000200(value+2.0), d=func_08000200(value+3.0);
    return (short)(int)(a+b+c+d+value)%7;
}
"""
        self.fixture(source)
        self.assertTrue(self.manifest['frame'])
        self.assertEqual(len(self.verify()),len(self.instructions))
        report=self.native_report()
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
        for assembly in (
            "push {lr}\nsub sp,#4\nbl __adddf3\nbl __fixdfsi\n"
            "lsls r0,r0,#16\nasrs r0,r0,#16\nmovs r1,#7\nbl __modsi3\npop {r1}\nbx r1",
            "push {lr}\nsub sp,#4\nbl __adddf3\nbl __fixdfsi\n"
            "lsls r0,r0,#16\nasrs r0,r0,#16\nldr r1,[sp]\nbl __modsi3\nadd sp,#4\npop {r1}\nbx r1",
            "push {lr}\nsub sp,#4\nstr r0,[sp,#4]\nbl __adddf3\nbl __fixdfsi\n"
            "lsls r0,r0,#16\nasrs r0,r0,#16\nmovs r1,#7\nbl __modsi3\nadd sp,#4\npop {r1}\nbx r1",
            "push {lr}\nsub sp,#4\nmov r4,sp\nbl __adddf3\nbl __fixdfsi\n"
            "lsls r0,r0,#16\nasrs r0,r0,#16\nldr r1,[r4]\nbl __modsi3\nadd sp,#4\npop {r1}\nbx r1"):
            with self.subTest(assembly=assembly),self.assertRaises(ValueError):
                self.fixture(assembly=assembly)

    def test_standalone_remainder_keeps_its_frameless_boundary(self):
        source="int func_08000000(int value,int a,int b,int c,int count) { return (short)value%7+count; }\n"
        (self.root/'src/08000000.c').write_text(source)
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            _,_,original=match.compile_object(runner,workspace,self.args,self.root,BASE,'src/08000000.c')
            symbol,_=match.function_record(original,'func_08000000',BASE,True)
            self.indexes(symbol['size'],1)
            bindings={}
            body,calls,_=match.link_calls(runner,workspace,self.args,original,BASE,self.mapping,
                len(self.runtime_rom),self.runtime_rom,modsi3_bindings=bindings)
        rom=bytearray(self.runtime_rom);rom[:len(body)]=body
        with self.assertRaisesRegex(ValueError,'frameless caller'):
            match.verify_leaf_instructions(body,BASE,True,calls,
                modsi3_context=(bytes(rom),self.mapping,bindings))

    def test_exact_remainder_runtime_abi_and_pc_return_opt_in(self):
        self.fixture(SOURCE)
        import software_float_profile as floating
        entries=json.loads(self.mapping)
        proofs=profile.prove_remainder_closure(self.rom,self.mapping,self.index)
        self.assertEqual(set(proofs),{0x08142950,0x0814274C})
        self.assertFalse(proofs[0x08142950]['writes'])
        self.assertEqual(set(proofs[0x08142950]['returns']),{0x08142A12,0x08142A1C})
        kwargs=dict(call_edges=((0x08142A16,0x0814274C),),scalar_entries=(0x08142950,),allowed_writes=())
        with self.assertRaises(ValueError):
            floating.prove_runtime(self.rom,entries,0x08142950,0x08142A1E,102,
                                   {0x0814274C:proofs[0x0814274C]},**kwargs)
        for sites in ((0x08142A12,), (0x08142A10,0x08142A1C), (0x08142A12,0x08142A1C,0x08142950)):
            with self.subTest(sites=sites),self.assertRaises(ValueError):
                floating.prove_runtime(self.rom,entries,0x08142950,0x08142A1E,102,
                    {0x0814274C:proofs[0x0814274C]},thumb_pc_returns=sites,**kwargs)
        import struct
        for address,word in ((0x08142A12,0x46A7), # MOV PC,R4 is not LR return
                             (0x08142A10,0xBC20), # restore wrong callee register
                             (0x08142A1C,0xBC01)):# lose saved LR/return
            rom=bytearray(self.rom);struct.pack_into('<H',rom,address-BASE,word)
            with self.subTest(address=address),self.assertRaises(ValueError):
                floating.prove_runtime(bytes(rom),entries,0x08142950,0x08142A1E,102,
                    {0x0814274C:proofs[0x0814274C]},thumb_pc_returns=(0x08142A12,0x08142A1C),**kwargs)

    def test_manifest_requires_exact_remainder_policy_and_closure(self):
        self.fixture(SOURCE)
        for change in ('missing', 'domain', 'divisor', 'runtime', 'dependency', 'site', 'extra'):
            manifest = copy.deepcopy(self.manifest)
            if change == 'missing': del manifest['remainder']
            elif change == 'domain': manifest['remainder']['dividend'] = 'signed32'
            elif change == 'divisor': manifest['remainder']['divisor'] = 'unknown'
            elif change == 'runtime': manifest['remainder']['runtime'] = 'other'
            elif change == 'dependency': manifest['remainder']['dependencies'][0][2] = '0'*64
            elif change == 'site': manifest['remainder']['calls'][0] += 2
            else: manifest['remainder']['extra'] = True
            with self.subTest(change=change), self.assertRaises(ValueError): self.verify(manifest)

    def test_remainder_runtime_and_dual_index_fail_closed(self):
        self.fixture(SOURCE)
        for a, b, _ in match.modsi3.IDENTITIES:
            changed = bytearray(self.rom); changed[a-BASE] ^= 1
            with self.subTest(address=a), self.assertRaises(ValueError):
                profile.verify(self.body, BASE, bytes(changed), self.mapping, self.index, self.manifest)
        entries = json.loads(self.mapping)
        row = next(r for r in entries if int(r['rom'],16)==match.modsi3.ADDRESS)
        for kind in ('missing','duplicate','mode','odd','extent','overlap'):
            modified = copy.deepcopy(entries)
            picked = next(r for r in modified if r['rom']==row['rom'])
            if kind == 'missing': modified.remove(picked)
            elif kind == 'duplicate': modified.append(copy.deepcopy(picked))
            elif kind == 'mode': picked['mode']='arm'
            elif kind == 'odd': picked['rom']='0x08142951'
            elif kind == 'extent': picked['end']='0x08142A1C'
            else: modified.append(dict(rom='0x08142952',end='0x08142954',mode='thumb',instrs=1))
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.verify(self.body, BASE, self.rom, json.dumps(modified).encode(), self.index, self.manifest)
        with self.assertRaises(ValueError):
            profile.verify(self.body, BASE, self.rom, self.mapping,
                           self.index.replace(b'08142950 08142A1E', b'08142950 08142A1C'), self.manifest)

    def test_original_elf_alias_and_other_runtime_refusals(self):
        self.fixture(SOURCE)
        for name in ('func_08142950', 'func_08142951', '__modsi3_alias', '__divsi3', '__umodsi3'):
            altered=copy.deepcopy(self.original)
            for symbol in altered['symbols']:
                if symbol['name']=='__modsi3': symbol['name']=name
            runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
            with self.subTest(name=name), runner.workspace() as workspace, self.assertRaises(ValueError):
                profile.object_bytes(runner,workspace,self.args,altered,BASE,self.mapping,self.rom,self.index)
        with self.assertRaisesRegex(ValueError,'noncanonical addend'):
            self.fixture(assembly='push {lr}\nbl __adddf3\nbl __fixdfsi\nbl __modsi3+2\npop {r1}\nbx r1')
        self.fixture(SOURCE)
        bindings = {site:name for site,name in self.bindings.items() if name!='__modsi3'}
        with self.assertRaises(ValueError):
            profile.verify_context(self.body,BASE,self.calls,(self.rom,self.mapping,self.index,bindings))
        with self.assertRaisesRegex(ValueError,'isolated direct-call'):
            match.verify_leaf_instructions(self.body,BASE,True,self.calls,
                double_context=(self.rom,self.mapping,self.index,self.bindings),
                modsi3_context=(self.rom,self.mapping,{site:'__modsi3' for site,name in self.bindings.items() if name=='__modsi3'}))

import test_software_double_data_profile as data_fixture

class SoftwareDoubleModDataTests(data_fixture.SoftwareDoubleDataTests):
    def indexes(self, size, count):
        super().indexes(size, count)
        entries=json.loads(self.mapping)
        entries.extend({"rom":f"0x{a:08X}","end":f"0x{b:08X}","mode":"thumb",
                        "instrs":102 if a==match.modsi3.ADDRESS else 1}
                       for a,b,_ in match.modsi3.IDENTITIES)
        self.mapping=json.dumps(entries).encode()
        self.index="".join(f"{int(e['rom'],16):08X} {int(e['end'],16):08X} "
                           f"{int(e['end'],16)-int(e['rom'],16)} {e['instrs']} return\n"
                           for e in entries).encode()

    def test_natural_typed_data_cast_add_remainder_keeps_fresh_provenance(self):
        source='''#include "objects.h"
int func_08000000(double value) { return (short)(int)(value+(double)samples[1])%7; }
'''
        self.fixture(source=source,object_address=0x08394350)
        self.assertEqual(set(self.bindings.values()),{'__floatsidf','__adddf3','__fixdfsi','__modsi3'})
        self.assertEqual(len(self.literals),1)
        self.verify()
        report=self.native_report()
        opening,reading=self.patched_rom()
        with opening,reading:
            self.assertTrue(profile.report_matches(report,self.root,BASE))
            path=self.root/'config/data_symbols.json'
            raw=path.read_bytes()
            path.write_text('{"samples":"0x08394354"}')
            self.assertFalse(profile.report_matches(report,self.root,BASE))
            path.write_bytes(raw)
            path=self.root/'include/objects.h'
            path.write_text('extern const unsigned short samples[];\n')
            self.assertFalse(profile.report_matches(report,self.root,BASE))
        for field in ('data','remainder'):
            manifest=copy.deepcopy(self.manifest)
            del manifest[field]
            with self.subTest(field=field),self.assertRaises(ValueError): self.verify(manifest)

if __name__ == '__main__': unittest.main()

