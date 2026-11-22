"""Canonical external Thumb alignment remains outside the guarded-switch FUNC."""
import copy
import json
from pathlib import Path
import subprocess
import unittest
from test_switch_constants import assemble,fixture_assembly,ordinary_link,fixed_args
import test_descriptor_cursor_value as fixtures
match=fixtures.match
owner=fixtures.owner
profile=owner
A=0x08010000

class RestoringAlignmentTests(unittest.TestCase):
    def setUp(self):
        import tempfile,os
        from pathlib import Path
        self.scratch=tempfile.TemporaryDirectory(prefix='restoring_alignment_')
        self.root=Path(self.scratch.name)
        self.addCleanup(self.scratch.cleanup)

    def switch(self):
        assembly=fixture_assembly(call=True,prefix='sub sp,#8',first='',second='')
        assembly=assembly.replace('.Lconstant0:\n.word 0xFF00FF00\n.Lconstant1:\n.word 0x0F0F0F0F\n','')
        assembly=assembly.replace('bl func_08001000\npop {r1}',
            'str r3,[sp]\nbl func_08001000\nadd sp,#8\npop {r1}')
        assembly=assembly.replace('func_08000000','func_08010000')+'\n.balign 4\n'
        original=assemble(self.root,assembly)
        linked,data=ordinary_link(self.root,original,A)
        rows=[dict(rom=f'0x{A:08X}',end=f'0x{A+len(data):08X}',mode='thumb',instrs=0),
              dict(rom='0x08001000',end='0x08001002',mode='thumb',instrs=1)]
        mapping=json.dumps(rows).encode()
        rows[0]['instrs']=owner.refine(data,A,mapping)['instrs']
        mapping=json.dumps(rows).encode()
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode()
        rom=bytearray(A-match.ROM_BASE+len(data))
        rom[A-match.ROM_BASE:]=data
        rom[0x1000:0x1002]=b'\x70\x47'
        inputs=dict(data=data,address=A,rom=bytes(rom),mapping=mapping,index=index,
            objects=b'{}',selector=owner.ALIGNED_SELECTOR)
        return original,linked,inputs

    def test_actual_switch_original_link_and_report_identity(self):
        original,linked,f=self.switch()
        bindings,_=owner.original_bindings(match.elf_image(original),A,f['rom'],
            f['mapping'],f['objects'],selector=owner.ALIGNED_SELECTOR,index=f['index'])
        manifest,ins=owner.verify(**f,bindings=bindings)
        self.assertEqual(manifest['profile'],owner.ALIGNED_SCHEMA)
        self.assertTrue(manifest['proof']['ordinary_switch_inventory']['inventory_only'])
        self.assertFalse(manifest['proof']['ordinary_switch_inventory']['ordinary_callee_native_proof'])
        report=owner.render(A,(f['data'],manifest,'synthetic-source',f['mapping'],
            f['index'],f['objects'],f['rom'],len(ins),original))
        self.assertIn('* owner runtime: '+owner.ALIGNED_SELECTOR,report)
        self.assertIn('original_elf_sha256',report)
        self.assertIn(owner.ALIGNED_CONTROL_FLOW,report)
        runner=match.Runner(match.DEFAULT_CC,root=self.root,timeout=120)
        with runner.workspace() as workspace:
            Path(workspace+'/f.o').write_bytes(original)
            runner.write_text(workspace+'/f.i','')
            data,actual=owner.object_bytes(runner,workspace,fixed_args(),
                match.elf_image(original),A,f['rom'],f['mapping'],f['objects'],
                selector=owner.ALIGNED_SELECTOR,index=f['index'])
            self.assertEqual(data,f['data'])
            self.assertEqual(actual,bindings)
            self.assertEqual(match.elf_image(runner.read_binary(workspace+'/f.elf'))['text'],
                match.elf_image(linked)['text'])

    def test_switch_binding_count_guard_and_manifest_tampering_reject(self):
        original,_,f=self.switch()
        bindings,_=owner.original_bindings(match.elf_image(original),A,f['rom'],
            f['mapping'],f['objects'],selector=owner.ALIGNED_SELECTOR,index=f['index'])
        manifest,_=owner.verify(**f,bindings=bindings)
        for field in ('calls','switches'):
            altered=copy.deepcopy(bindings);altered[field]=[]
            with self.subTest(field=field),self.assertRaises(ValueError):owner.verify(**f,bindings=altered)
        altered=copy.deepcopy(manifest);altered['proof']['terminal_alignment_policy']['producer_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):owner.verify(**f,bindings=bindings,manifest=altered)
        rows=json.loads(f['mapping']);rows[0]['instrs']+=1
        with self.assertRaises(ValueError):owner.verify(**dict(f,mapping=json.dumps(rows).encode()),bindings=bindings)
        switch=owner.refine(f['data'],A,f['mapping'])['word_switches'][0]
        body=bytearray(f['data']);body[switch['guard']:switch['guard']+2]=b'\xc0\x46'
        rom=bytearray(f['rom']);rom[A-match.ROM_BASE:]=body
        with self.assertRaises(ValueError):owner.verify(**dict(f,data=bytes(body),rom=bytes(rom)),bindings=bindings)

    def test_original_alignment_and_ELF_fingerprint_are_bound(self):
        source=self.root/'envelope.s'
        source.write_text('.syntax unified\n.thumb\n.global func_08010000\n.type func_08010000,%function\n.thumb_func\nfunc_08010000:\nbx lr\n.size func_08010000,.-func_08010000\n.balign 4\n')
        subprocess.run(['arm-none-eabi-as','-mthumb-interwork',str(source),'-o',str(self.root/'envelope.o')],check=True,capture_output=True)
        image=match.elf_image((self.root/'envelope.o').read_bytes())
        mapping=json.dumps([dict(rom=f'0x{A:08X}',end=f'0x{A+2:08X}',mode='thumb',instrs=1)]).encode()
        self.assertEqual(image['text'],b'\x70\x47\xc0\x46')
        bindings,_=owner.original_bindings(image,A,b'',mapping,b'{}',selector=profile.ALIGNED_SELECTOR)
        self.assertEqual(bindings,dict(calls=[],data=[],functions=[],switches=[]))
        with self.assertRaisesRegex(ValueError,'sole complete Thumb ELF'):
            owner.original_bindings(image,A,b'',mapping,b'{}',selector=owner.ACYCLIC_SELECTOR)
        marker=f'* verification: `{owner.ALIGNED_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),owner.ALIGNED_SELECTOR)
        with self.assertRaises(ValueError):owner.selected(marker*2)
        missing=copy.deepcopy(image);missing['text']=missing['text'][:2]
        with self.assertRaises(ValueError):owner.original_bindings(missing,A,b'',mapping,b'{}',selector=owner.ALIGNED_SELECTOR)
        for kind in ('padding','extra-symbol','alignment'):
            altered=copy.deepcopy(image)
            if kind=='padding':altered['text']=altered['text'][:2]+b'\0\0'
            elif kind=='extra-symbol':altered['symbols'].append(dict(name='owned_tail',value=3,size=2,type=0,bind=1,section=altered['text_index']))
            else:
                section=list(altered['sections'][altered['text_index']]);section[8]=2;altered['sections'][altered['text_index']]=section
            with self.subTest(kind=kind),self.assertRaises(ValueError):owner.original_bindings(altered,A,b'',mapping,b'{}',selector=profile.ALIGNED_SELECTOR)
        args=(A,b'\x70\x47',{'profile':profile.ALIGNED_SCHEMA},'source',mapping,b'index',b'{}',b'rom')
        with self.assertRaisesRegex(ValueError,'original ELF'):owner.fingerprint(*args)
        self.assertNotEqual(owner.fingerprint(*args,original_elf=b'original1'),owner.fingerprint(*args,original_elf=b'original2'))

if __name__=='__main__':unittest.main(verbosity=2)
