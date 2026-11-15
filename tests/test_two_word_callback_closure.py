"""Synthetic complete caller/iterator/adapter closure and native routing."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import named_data_buffer_profile as named
import function_thunk_profile as thunk
import two_word_callback_closure_profile as closure

A,W,C,G=0x08001000,0x08002000,0x08003000,0x08004000


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))


def fixture(changes=None):
    root=bytes.fromhex('00b582b000920191006903496a46')+bl(A+14,W)+bytes.fromhex('02b001bc0047')+struct.pack('<I',C+1)
    worker=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')+bl(W+20,thunk.ALIASES['_call_via_r6'])+bytes.fromhex('0028f6d170bc01bc0047')
    callback=bytes.fromhex('10b50c1c')+bl(C+4,G)+bytes.fromhex('21686268')+bl(C+12,thunk.ALIASES['_call_via_r2'])+bytes.fromhex('10bc02bc0847')
    bodies={A:root,W:worker,C:callback,G:bytes.fromhex('00687047')}
    counts={A:11,W:16,C:9,G:2}
    rom=bytearray(thunk.END-match.ROM_BASE)
    for number,target in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,target-match.ROM_BASE,0x4700+(number<<3),0x46C0)
    for target in (thunk.ALIASES['_call_via_r6'],thunk.ALIASES['_call_via_r2']):
        bodies[target]=bytes(rom[target-match.ROM_BASE:target-match.ROM_BASE+2]);counts[target]=1
    for (target,offset),value in (changes or {}).items():
        code=bytearray(bodies[target]);struct.pack_into('<H',code,offset,value);bodies[target]=bytes(code)
    rows=[]
    for target,body in bodies.items():
        rom[target-match.ROM_BASE:target-match.ROM_BASE+len(body)]=body
        rows.append(dict(rom=f'0x{target:08X}',end=f'0x{target+len(body):08X}',mode='thumb',instrs=counts[target]))
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'for row in rows).encode()
    return dict(data=bodies[A],address=A,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,objects=b'{}',selector=closure.SELECTOR,
        bindings=dict(calls=[[14,f'func_{W:08X}']],data=[],functions=[[24,f'func_{C:08X}']],switches=[]))


class ClosureTests(unittest.TestCase):
    def test_complete_initialized_read_only_closure(self):
        manifest,ins=owner.verify(**fixture())
        self.assertEqual(manifest['profile'],closure.SCHEMA)
        self.assertEqual(len(ins),11)
        proof=manifest['proof']['callback_closure']
        self.assertEqual(proof['root_descriptor']['initialized_words'],[
            dict(site=A+4,offset=0,entry_register=2),dict(site=A+6,offset=4,entry_register=1)])
        self.assertFalse(proof['iterator']['iteration_bound_assumed'])
        self.assertFalse(proof['termination_proved'])
        self.assertFalse(proof['actual_callback_ABI_established'])
        self.assertFalse(proof['physical_memory_permission'])
        self.assertEqual(proof['source_sha256']['two_word_callback_closure_profile.py'],hashlib.sha256(Path(closure.__file__).read_bytes()).hexdigest())

    def test_native_report_selector_and_original_elf_binding(self):
        values=fixture();manifest,ins=owner.verify(**values)
        result=(values['data'],manifest,'a'*64,values['mapping'],values['index'],values['objects'],values['rom'],len(ins),b'synthetic-original-ELF')
        report=owner.render(A,result)
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report),closure.SELECTOR)
        self.assertIn('* owner runtime: '+closure.SELECTOR,report)
        with self.assertRaisesRegex(ValueError,'original ELF identity'):
            owner.fingerprint(A,values['data'],manifest,'a'*64,values['mapping'],values['index'],values['objects'],values['rom'])

    def test_default_and_prior_selectors_do_not_gain_permission(self):
        for selector in (owner.SELECTOR,named.DATAFREE_SELECTOR):
            values=fixture();values['selector']=selector
            with self.subTest(selector=selector),self.assertRaises(ValueError):owner.verify(**values)

    def test_missing_initializing_store_refuses(self):
        for offset in(4,6):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture({(A,offset):0x46C0}))

    def test_saved_return_or_extra_pointer_field_refuses(self):
        for value in(0x0090,0x0093,0x009C):
            with self.subTest(value=value),self.assertRaises(ValueError):
                owner.verify(**fixture({(A,4):value}))

    def test_wrong_descriptor_address_or_frame_size_refuses(self):
        for offset,value in((12,0x4669),(2,0xB081),(18,0xB001)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture({(A,offset):value}))

    def test_external_node_write_refuses(self):
        with self.assertRaisesRegex(ValueError,'read-only node iterator'):
            owner.verify(**fixture({(W,10):0x60A4}))

    def test_callback_descriptor_escape_refuses(self):
        with self.assertRaisesRegex(ValueError,'argument word zero'):
            owner.verify(**fixture({(C,8):0x1C21}))

    def test_callback_target_and_return_damage_refuse(self):
        for offset,value in((10,0x68A2),(16,0xBC20),(18,0xBC01),(20,0x4700)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture({(C,offset):value}))

    def test_changed_iterator_guard_or_update_refuses(self):
        for offset,value in((10,0x6864),(12,0x2C01),(26,0xD0F6)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                owner.verify(**fixture({(W,offset):value}))

    def test_dependency_body_or_count_refuses(self):
        for target in(W,C,G,thunk.ALIASES['_call_via_r6']):
            values=fixture();rows=json.loads(values['mapping'])
            next(row for row in rows if int(row['rom'],16)==target)['instrs']+=1
            values['mapping']=json.dumps(rows).encode()
            with self.subTest(target=target),self.assertRaises(ValueError):owner.verify(**values)

    def test_inexact_callback_binding_or_even_target_refuses(self):
        values=fixture();values['bindings']['functions']=[[24,f'func_{G:08X}']]
        with self.assertRaises(ValueError):owner.verify(**values)
        values=fixture();body=bytearray(values['data']);struct.pack_into('<I',body,24,C);values['data']=bytes(body)
        rom=bytearray(values['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body;values['rom']=bytes(rom)
        with self.assertRaisesRegex(ValueError,'odd Thumb pointer'):owner.verify(**values)

    def test_manifest_change_refuses(self):
        values=fixture();report,_=owner.verify(**values)
        changed=copy.deepcopy(report);changed['proof']['callback_closure']['actual_callback_ABI_established']=True
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            owner.verify(**values,manifest=changed)

    def test_exact_policy_and_immutable_input_contract(self):
        values=fixture()
        for key in('objects','bindings'):values.pop(key)
        for key,value in(('selector',''),('address',True),('data',bytearray(values['data']))):
            changed=dict(values);changed[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):closure.prove(**changed)

    def test_frame_hook_rejects_unbound_context_and_subclass(self):
        values=fixture();data,ins,edges,calls,partition=closure.complete(A,28,11,values['rom'],values['mapping'],values['index'])
        class Other(closure._ContextRead):pass
        for kind,error in((closure._ContextRead,'exact complete root'),(Other,'native buffer proof')):
            proof=kind(values['rom'],values['mapping'],A+14,W,{}, {}, {})
            with self.subTest(kind=kind),self.assertRaisesRegex(ValueError,error):
                closure.frame.prove_frame(ins,edges,A,{},calls,stack_aliases=True,
                    buffer_proof=proof,call_preservation={A+14:closure.PRESERVED})

    def test_both_descriptor_words_must_be_allocated_locals(self):
        values=fixture();proof=closure._ContextRead(values['rom'],values['mapping'],A+14,W,{}, {}, {})
        for forbidden in(0,1):
            stack=[(False,False,True),(False,False,True),(True,True,False)]
            stack[forbidden]=(False,True,False)
            with self.subTest(forbidden=forbidden),self.assertRaisesRegex(ValueError,'allocated local'):
                proof.check_call(W,{match.ARM_REG_R0+2:-12},stack,site=A+14)

    def test_native_cli_dispatches_only_explicit_new_selector(self):
        with patch.object(sys,'argv',['match.py',f'{A:08X}','--owner-runtime-profile',closure.SELECTOR]), \
                patch.object(match,'repo_root',return_value='/synthetic/root'), \
                patch.object(match,'ROOT',match.ROOT),patch.object(owner,'issue',return_value='selected')as issue:
            self.assertEqual(match.main(),'selected')
            self.assertEqual(issue.call_count,1)
            self.assertEqual(issue.call_args.args[1],A)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,closure.SELECTOR)

    def test_binding_decoder_pair_is_rejected_before_effect_proof(self):
        values=fixture();values['bindings']=(values['bindings'],{'synthetic':(W,False)})
        with patch.object(closure,'prove',side_effect=AssertionError('must not execute'))as effect:
            with self.assertRaisesRegex(ValueError,'typed bindings before effect proof'):
                owner.verify(**values)
            effect.assert_not_called()

    def test_unpacked_binding_dictionary_reaches_complete_effect_proof(self):
        values=fixture();decoded=(values['bindings'],{'synthetic':(W,False)})
        values['bindings'],targets=decoded
        with patch.object(closure,'prove',wraps=closure.prove)as effect:
            result,_=owner.verify(**values)
            self.assertEqual(result['profile'],closure.SCHEMA)
            effect.assert_called_once()
