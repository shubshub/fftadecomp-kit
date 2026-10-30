"""Explicit discarded-r2/r3 return contract and unchanged local frame boundaries."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import canonical_integer_discarded_scratch_alias_inventory as profile
import local_long_branch_profile as frame
import owner_admission_profile as owner
import owner_graph_profile as graph
import match

A,B=0x08010000,0x08020000

class DiscardedScratchAliasTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows,indent=2)+'\n').encode(),''.join(
            f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
            for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        cls.rom=Path(os.environ['FFTA_ROM']).read_bytes()
        assert profile.sha(cls.rom)=='43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        cls.retained=Path(os.environ['FFTA_SCRATCH_ALIAS_RETAIN']);cls.retained.mkdir(exist_ok=True)
        cls.rows=[{'rom':f'0x{A:08X}','end':f'0x{A+2:08X}','mode':'thumb','instrs':1},
            {'rom':f'0x{B:08X}','end':f'0x{B+2:08X}','mode':'thumb','instrs':1},
            {'rom':'0x081426B8','end':'0x0814274A','mode':'thumb','instrs':72},
            {'rom':'0x08142950','end':'0x08142A1E','mode':'thumb','instrs':102},
            {'rom':'0x08142AB0','end':'0x08142B28','mode':'thumb','instrs':59},
            {'rom':'0x08142B28','end':'0x08142BE8','mode':'thumb','instrs':95},
            {'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1}]
        cls.temporary=tempfile.TemporaryDirectory(dir=os.environ['FFTA_TEST_SCRATCH'],prefix='discarded_scratch_')
        cls.addClassCleanup(cls.temporary.cleanup);cls.root=Path(cls.temporary.name)
        cls.values=cls.case([0xB510,0xB081,'__divsi3',0x466A,0x2000,0x7010,0x5610,
            0x2800,0xD1FA,0xB001,0xBC10,0xBC01,0x4700])
        if (cls.retained/'decoded-native-inventory.json').exists():
            cls.manifest=json.loads((cls.retained/'decoded-native-inventory.json').read_text())
            assert cls.manifest['producer_source_sha256'][Path(profile.__file__).name]==profile.sha(Path(profile.__file__).read_bytes())
        else:
            cls.manifest,_=profile.verify(**cls.values)
            (cls.retained/'decoded-native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
        for name,key in (('decoded-body.bin','data'),('functions.json','mapping'),('functions.txt','index')):
            (cls.retained/name).write_bytes(cls.values[key])
        for name,key in (('rom.bin','rom'),('functions.json','mapping'),('functions.txt','index')):
            (cls.root/name).write_bytes(cls.values[key])

    @classmethod
    def case(cls,sequence,**changes):
        data=bytearray()
        for value in sequence:
            if type(value)is int:data+=struct.pack('<H',value)
            else:
                target=profile.OPERATIONS[value] if value in profile.OPERATIONS else B if value=='ordinary' else value[1]
                delta=target-(A+len(data))-4
                data+=struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
        data=bytes(data);rows=copy.deepcopy(cls.rows)
        rows[0]['end']=f'0x{A+len(data):08X}';mapping,_=cls.indexes(rows)
        rows[0]['instrs']=owner.refine(data,A,mapping)['instrs'];mapping,index=cls.indexes(rows)
        _,_,_,calls,_=graph.graph(data,A,owner.refine(data,A,mapping))
        bindings=profile.bind_calls(calls,mapping,A,len(data),len(cls.rom))
        rom=bytearray(cls.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        values=dict(data=data,address=A,rom=bytes(rom),mapping=mapping,index=index,calls=calls,bindings=bindings,
            selector=profile.SELECTOR,discarded_exit_scratch=copy.deepcopy(profile.POLICY))
        values.update(changes);return values

    def machine(self,sequence,**changes):return profile.verify(**self.case(sequence,**changes))
    def native(self,**changes):
        values=dict(self.values);values.update(changes);return profile.verify(**values)

    def test_explicit_r2_r3_and_both_residual_aliases_record_exact_offsets(self):
        self.assertEqual(self.manifest['discarded_scratch_ABI_premise'],frame.DISCARDED_SCRATCH_CONTRACT)
        self.assertFalse(self.manifest['native_nonescape_proof'])
        self.assertTrue(self.manifest['backward_edges'])
        for middle,registers in (([0x466B,0x2000,0x7018],[3]),
                                 ([0x466A,0x466B,0x2000,0x7010],[2,3])):
            with self.subTest(registers=registers):
                observed,_=self.machine([0xB510,0xB081,'__divsi3',*middle,0xB001,0xBC10,0xBC01,0x4700])
                residual=observed['frame']['discarded_exit_scratch']['residual_aliases']
                self.assertEqual([row[1] for row in residual],registers)
                self.assertTrue(all(row[2:]==[-12,False] for row in residual))
        residual=self.manifest['frame']['discarded_exit_scratch']['residual_aliases']
        self.assertEqual([row[1:] for row in residual],[[2,-12,False]])

    def test_old_default_alias_refusal_and_default_output_exact_on_retained_proofs(self):
        ins,edges,branches,calls,_=graph.graph(self.values['data'],A,owner.refine(self.values['data'],A,self.values['mapping']))
        with self.assertRaisesRegex(ValueError,'local alias escapes through an exit register'):
            frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,zero_index_profile=profile.zero_index.SELECTOR)
        values=self.case([0xB510,0xB081,'__divsi3',0x466A,0x2000,0x7010,0x5610,
            0x2800,0xD1FA,0x2200,0xB001,0xBC10,0xBC01,0x4700])
        ins,edges,branches,calls,_=graph.graph(values['data'],A,owner.refine(values['data'],A,values['mapping']))
        actual=frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,zero_index_profile=profile.zero_index.SELECTOR)
        expected={'schema': 'thumb-same-owner-long-bl-restoring-frame-v1', 'instructions': 14, 'maximum_frame_bytes': 12, 'returns': [134283292], 'preserved': 'r4-r11,sp,entry-lr', 'external_calls': 'existing-direct-call-ABI-summary', 'local_aliases': {'schema': 'thumb-same-owner-long-bl-local-alias-frame-v1', 'assignments': [134283272], 'accesses': [134283276, 134283278], 'buffer_calls': [], 'buffer_fingerprint': None}, 'zero_index_profile': 'zero-register-index-local-signed-loads-v1', 'zero_index_signed_loads': [[134283278, 68, 66, 1, [134283274]]]}
        self.assertEqual(profile.text(actual),profile.text(expected))
        values=self.case([0xB510,'__divsi3',0xBC10,0xBC01,0x4700])
        ins,edges,branches,calls,_=graph.graph(values['data'],A,owner.refine(values['data'],A,values['mapping']))
        actual=frame.prove_frame(ins,edges,A,branches,calls)
        self.assertEqual(actual,{'schema':frame.SCHEMA,'instructions':5,'maximum_frame_bytes':8,
            'returns':[A+10],'preserved':'r4-r11,sp,entry-lr','external_calls':'existing-direct-call-ABI-summary'})

    def test_r0_r1_preserved_and_nonpermitted_scratch_aliases_refused(self):
        for middle in ([0x4668,0x7001],[0x4669,0x7008],[0x466C,0x7020],[0x46EC]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):
                self.machine([0xB510,0xB081,'__divsi3',*middle,0xB001,0xBC10,0xBC08,0x4718])

    def test_policy_is_exact_strict_and_required_by_API_and_CLI(self):
        valid=profile.POLICY
        invalid=[None,False,{},dict(valid,extra=0),dict(valid,schema='unknown'),dict(valid,registers=(2,3)),
            dict(valid,registers=[2]),dict(valid,registers=[3,2]),dict(valid,registers=[2,2,3]),
            dict(valid,registers=[True,3]),dict(valid,registers=[2.0,3]),dict(valid,registers=[0,1,2,3])]
        class Policy(dict):pass
        invalid.append(Policy(valid))
        for policy in invalid:
            with self.subTest(policy=policy),self.assertRaises(ValueError):self.native(discarded_exit_scratch=policy)
        values=dict(self.values);values.pop('discarded_exit_scratch')
        with self.assertRaises(TypeError):profile.verify(**values)
        command=[sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--discarded-exit-scratch','r2,r3','--rom',str(self.root/'rom.bin'),
            '--mapping',str(self.root/'functions.json'),'--index',str(self.root/'functions.txt'),f'{A:08X}']
        completed=subprocess.run(command,capture_output=True,text=True)
        (self.retained/'cli.stdout').write_text(completed.stdout);(self.retained/'cli.stderr').write_text(completed.stderr)
        self.assertEqual(completed.returncode,0,completed.stderr);self.assertEqual(json.loads(completed.stdout),self.manifest)
        absent=subprocess.run(command[:4]+command[6:],capture_output=True,text=True)
        self.assertEqual(absent.returncode,2)

    def test_policy_cannot_compose_with_entry_slots_buffers_or_nonalias_frames(self):
        ins,edges,branches,calls,_=graph.graph(self.values['data'],A,owner.refine(self.values['data'],A,self.values['mapping']))
        for changed in ({'stack_aliases':False},{'entry_stack_policy':{'schema':'thumb-readonly-entry-stack-v1','words':[0]}},
            {'local_alias_slot_policy':{}},{'finite_stack_index_policy':{}},{'runtime_calls':{}},{'call_preservation':{}}):
            kwargs=dict(stack_aliases=True,zero_index_profile=profile.zero_index.SELECTOR,discarded_exit_scratch=profile.POLICY)
            kwargs.update(changed)
            with self.subTest(changed=changed),self.assertRaises(ValueError):frame.prove_frame(ins,edges,A,branches,calls,**kwargs)

    def test_call_arguments_SP_exports_spills_and_dangling_dereference_still_refused(self):
        for middle in ([0x466A,'ordinary'],[0x4668,'__divsi3'],[0x466A,0x9200],
            [0x466A,0x601A],[0x466A,0xB001,0xB081,0x7010]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):
                self.machine([0xB510,0xB081,'__divsi3',*middle,0xB001,0xBC10,0xBC01,0x4700])

    def test_new_policy_rejects_callee_saved_alias_at_call_before_any_discard(self):
        with self.assertRaisesRegex(ValueError,'discarded scratch local aliases cannot cross calls'):
            self.machine([0xB510,0xB081,'__divsi3',0x466C,0x2000,0x7020,'ordinary',
                0x466A,0x2000,0x7010,0xB001,0xBC10,0xBC01,0x4700])

    def test_saved_slot_entry_variable_index_and_block_transfer_still_refused(self):
        for middle in ([0xAA01,0x7010],[0x9803],[0x466A,0x2001,0x5610],[0x466A,0x5610],
            [0x466A,0xC201],[0x466A,0xCA01],[0x466A,0x3201,0x8010]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):
                self.machine([0xB510,0xB081,'__divsi3',*middle,0xB001,0xBC10,0xBC01,0x4700])

    def test_restoration_and_unambiguous_local_provenance_required_before_contract(self):
        for suffix in ([0xBC10,0xBC01,0x4700],[0xB001,0xBC20,0xBC01,0x4700],[0xB001,0xBC10,0xBC01,0x4708]):
            with self.subTest(suffix=suffix),self.assertRaises(ValueError):
                self.machine([0xB510,0xB081,'__divsi3',0x466A,0x7010,*suffix])
        with self.assertRaises(ValueError):
            self.machine([0xB510,0xB081,'__divsi3',0x2800,0xD001,0x466A,0xE000,0x2200,
                0xB001,0xBC10,0xBC01,0x4700])

    def test_only_actual_families_and_ordinary_conditional_ABI(self):
        for family in profile.OPERATIONS:
            with self.subTest(family=family):
                observed,_=self.machine([0xB510,0xB081,'ordinary',family,0x466A,0x2000,0x7010,0x5610,
                    0xB001,0xBC10,0xBC01,0x4700])
                self.assertEqual(observed['runtime_families'],[family])
                self.assertIn('conditional',observed['ordinary_call_premise'])
                self.assertEqual(set(dict(observed['native_runtime_closure'])),{profile.ZERO,profile.OPERATIONS[family]})
                self.assertEqual(observed['numeric_input_preconditions'],[])
                self.assertFalse(observed['native_nonescape_proof'])

    def test_actual_residual_required_and_selector_types_calls_maps_manifest_fail_closed(self):
        with self.assertRaisesRegex(ValueError,'actual residual'):
            self.machine([0xB510,0xB081,'__divsi3',0x466A,0x2000,0x7010,0x2200,0xB001,0xBC10,0xBC01,0x4700])
        for selector in (None,True,'canonical-integer-local-alias-inventory-v1'):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        for changed in ({'data':bytearray(self.values['data'])},{'calls':{}},{'bindings':{}},{'address':True}):
            with self.subTest(changed=changed),self.assertRaises(ValueError):self.native(**changed)
        for target in (profile.ZERO,profile.OPERATIONS['__divsi3']+2,0x081442A0,B+2):
            with self.subTest(target=target),self.assertRaises(ValueError):
                self.machine([0xB510,0xB081,'__divsi3',('call',target),0x466A,0x7010,0xB001,0xBC10,0xBC01,0x4700])
        rows=copy.deepcopy(self.rows);rows[0]['end']=f'0x{A+len(self.values["data"]):08X}';rows[0]['instrs']=0
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        wrong=copy.deepcopy(self.manifest);wrong['discarded_scratch_ABI_premise']='omitted'
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=wrong)

if __name__=='__main__':unittest.main()
