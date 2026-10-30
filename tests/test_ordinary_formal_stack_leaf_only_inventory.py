"""Focused decoded cases for the explicit leaf-only exact MOVS10 composition."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R0
import ordinary_formal_stack_leaf_only_inventory as profile
parent = profile.parent
A, L, O = 0x08010000, 0x08020000, 0x08022000
LEAF_WORDS = [0xB530,0x9C03,0x9D04,0x0400,0x12C0,0x3010,0x8018,
    0x0109,0x8021,0x0412,0x12D2,0x3210,0x802A,0xBC30,0xBC01,0x4700]
HEAD = [0xB570,0xB084,'ordinary']
CONSTRUCTOR = [0x200A,0x4468]
ARGUMENTS = [0x4604,0x9000,0xAE03,0x9601,0x2001,0x2102,0x2203,0xAB02]
TAIL = [0xA802,0x2200,0x5E81,0x4622,0x2300,0x5ED2,0x2300,0x5EF3,
    0x2015,0x9000,0x2000,'ordinary',0xB004,0xBC70,0xBC02,0x4708]
SEQUENCE = HEAD+CONSTRUCTOR+ARGUMENTS+['leaf']+TAIL


def machine(sequence, address=A):
    data = bytearray()
    for value in sequence:
        if type(value) is int:
            data += struct.pack('<H',value)
        else:
            target = {'ordinary':O,'leaf':L}[value]
            delta=target-(address+len(data))-4
            data+=struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
    return bytes(data)


def fixture(sequence=SEQUENCE):
    body, leaf = machine(sequence), machine(LEAF_WORDS,L)
    rows=[{'rom':f'0x{address:08X}','end':f'0x{address+len(data):08X}',
        'mode':'thumb','instrs':len(list(Cs(CS_ARCH_ARM,CS_MODE_THUMB).disasm(data,address)))}
        for address,data in ((A,body),(L,leaf),(O,b'\x70\x47'))]
    mapping=(json.dumps(rows,indent=2)+'\n').encode()
    index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    rom=bytearray(O-parent.match.ROM_BASE+2)
    for address,data in ((A,body),(L,leaf),(O,b'\x70\x47')):
        rom[address-parent.match.ROM_BASE:address-parent.match.ROM_BASE+len(data)]=data
    decoded=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoded.detail=True
    calls={i.address:i.operands[0].imm for i in decoded.disasm(body,A) if i.mnemonic=='bl'}
    return dict(data=body,address=A,rom=bytes(rom),mapping=mapping,index=index,calls=calls,
        bindings={site:f'func_{target:08X}' for site,target in calls.items()},selector=profile.SELECTOR)


class LeafOnlyMOVS10Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.leaf=machine(LEAF_WORDS,L)
        cls.identity=patch.object(profile,'LEAF',(L,L+len(cls.leaf),16,profile.sha(cls.leaf)))
        cls.identity.start();cls.addClassCleanup(cls.identity.stop)

    def native(self,sequence=SEQUENCE,**changes):
        values=fixture(sequence);values.update(changes)
        return profile.verify(**values)

    def components(self,values):
        return parent.FormalStackCalleeProof(self.leaf,L,values['rom'],values['mapping'],values['index'],
            {site:target for site,target in values['calls'].items() if target==L})

    def test_complete_fresh_leaf_only_and_exact_constructor_effects(self):
        result,instructions=self.native()
        self.assertEqual(result['component_accounting'],{'fresh_formal_leaf_workflows':1,
            'fresh_leaf_frames':1,'fresh_caller_frames':1,'noop_workflows':0})
        self.assertNotIn('exact_noop',result)
        frame=result['frame'];self.assertEqual(frame['maximum_frame_bytes'],32)
        proof=frame['formal_stack_callee']
        self.assertEqual(proof['native_leaf']['effects']['writes'],[[3,0,2],[4,0,2],[5,0,2]])
        self.assertEqual(proof['native_leaf']['effects']['reads'],[])
        self.assertEqual(proof['calls'][0]['writes_entry_SP_offsets'],[[-24,2],[-22,2],[-20,2]])
        self.assertEqual(frame['local_alias_slots']['allowed_MOVS_constants'],[1,2,3,10])
        self.assertEqual(result['exact_MOVS10_SP_constructors'][0][2],10)
        self.assertEqual(result['instructions'],len(instructions))
        self.assertTrue(result['complete_native_structural_proof'])
        self.assertFalse(result['source_or_ELF_admission'] or result['physical_memory_claim'])

    def test_missing_other_arithmetic_overwritten_and_call_killed_constructor(self):
        for constructor in ([],[0x200B,0x4468],[0x2009,0x3001,0x4468],
                [0x200A,0x2001,0x4468],[0x200A,'ordinary',0x4468]):
            with self.subTest(constructor=constructor),self.assertRaises(ValueError):
                self.native(HEAD+constructor+ARGUMENTS+['leaf']+TAIL)

    def test_join_requires_every_incoming_exact10(self):
        constructor=[0x200A,0x2900,0xD000,0x200B,0x4468]
        with self.assertRaises(ValueError):self.native(HEAD+constructor+ARGUMENTS+['leaf']+TAIL)
        constructor=[0x200A,0x2900,0xD000,0x200A,0x4468]
        result,_=self.native(HEAD+constructor+ARGUMENTS+['leaf']+TAIL)
        self.assertEqual(len(result['exact_MOVS10_SP_constructors'][0][3]),2)

    def test_constant_domain_validation_and_unchanged_default_outputs(self):
        decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
        body=machine([0x200A,0x2101,0x4770])
        instructions={i.address:i for i in decoder.disasm(body,A)}
        edges={A:(A+2,),A+2:(A+4,),A+4:()}
        default=parent.slots.prove_constants(instructions,edges,A)
        self.assertEqual(default,{A:{},A+2:{},A+4:{ARM_REG_R0+1:(1,frozenset((A+2,)))}})
        self.assertEqual(default,parent.slots.prove_constants(instructions,edges,A,constant_domain=None))
        extended=parent.slots.prove_constants(instructions,edges,A,constant_domain=(1,2,3,10))
        self.assertEqual(extended[A+2][ARM_REG_R0],(10,frozenset((A,))))
        for domain in ([1,2,3,10],(1,2,3),(True,2,3,10),(1,2,3,11)):
            with self.subTest(domain=domain),self.assertRaises(ValueError):
                parent.slots.prove_constants(instructions,edges,A,constant_domain=domain)
        body=machine([0xB500,0xB081,0x2001,0x9000,0xB001,0xBC02,0x4708])
        instructions={i.address:i for i in decoder.disasm(body,A)}
        edges={site:((site+i.size,) if site+i.size<A+len(body) else ()) for site,i in instructions.items()}
        expected={'schema':parent.frame.SCHEMA,'instructions':7,'maximum_frame_bytes':8,
            'returns':[A+12],'preserved':'r4-r11,sp,entry-lr','external_calls':'existing-direct-call-ABI-summary'}
        self.assertEqual(parent.frame.prove_frame(instructions,edges,A,{},{}),expected)
        self.assertEqual(parent.frame.prove_frame(instructions,edges,A,{}, {},formal_stack_alias_constant_policy=None),expected)

    def test_policy_requires_fresh_formal_proof_and_leaves_default_refusal(self):
        values=fixture();ins,edges,calls,_=parent.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        args=dict(stack_aliases=True,local_alias_slot_policy=parent.slots.SELECTOR,
            zero_index_profile=parent.zero_index.SELECTOR)
        with self.assertRaises(ValueError):parent.frame.prove_frame(ins,edges,A,{},calls,**args,
            formal_stack_callee_proof=self.components(values))
        for proof in (None,{},object()):
            with self.subTest(proof=type(proof).__name__),self.assertRaises(ValueError):
                parent.frame.prove_frame(ins,edges,A,{},calls,**args,
                    formal_stack_callee_proof=proof,formal_stack_alias_constant_policy=parent.slots.FORMAL_MOVS10_POLICY)
        for policy in (True,{},'other'):
            with self.subTest(policy=policy),self.assertRaises(ValueError):
                parent.frame.prove_frame(ins,edges,A,{},calls,**args,
                    formal_stack_callee_proof=self.components(values),formal_stack_alias_constant_policy=policy)

    def test_unmarked_ordinary_alias_and_wrong_leaf_callshape(self):
        with self.assertRaises(ValueError):self.native(HEAD+CONSTRUCTOR+ARGUMENTS+['ordinary','leaf']+TAIL)
        with self.assertRaises(ValueError):self.native(HEAD+CONSTRUCTOR+ARGUMENTS+['leaf','leaf']+TAIL)
        values=fixture();calls=dict(values['calls']);calls[next(iter(calls))]=parent.NOOP[0]
        with self.assertRaises(ValueError):profile.bind_calls(calls,values['mapping'],A,len(values['data']),len(values['rom']))

    def test_outgoing_missing_misaligned_saved_and_overlapping_output_refused(self):
        for position,replacement in ((1,0x2000),(1,0x9001),(3,0x9600),(7,0x466B),
                (7,0xAB04),(7,0xAB01),(2,0xAE02)):
            arguments=list(ARGUMENTS);arguments[position]=replacement
            with self.subTest(position=position,replacement=replacement),self.assertRaises(ValueError):
                self.native(HEAD+CONSTRUCTOR+arguments+['leaf']+TAIL)

    def test_body_index_bindings_and_complete_manifest_provenance(self):
        values=fixture();rom=bytearray(values['rom']);rom[L-parent.match.ROM_BASE]^=1
        with self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for key in ('calls','bindings'):
            changed=dict(values[key]);changed.pop(next(iter(changed)))
            with self.subTest(key=key),self.assertRaises(ValueError):self.native(**{key:changed})
        rows=json.loads(values['mapping']);rows[1]['instrs']=15
        with self.assertRaises(ValueError):self.native(mapping=json.dumps(rows).encode())
        rows=json.loads(values['mapping']);rows.append(copy.deepcopy(rows[1]))
        with self.assertRaises(ValueError):self.native(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):self.native(manifest={})
        for selector in (None,True,'default'):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)


if __name__=='__main__':unittest.main()
