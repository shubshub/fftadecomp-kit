"""Natural original O2 signed locals with exact-zero native index evidence."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import test_bounded_stack_output_inventory as fixture
import bounded_stack_output_inventory as prior
import bounded_output_zero_index_inventory as profile
import zero_index_stack_profile as zero
import local_long_branch_profile as frame
import owner_admission_profile as owner
import owner_graph_profile as graph
import match
from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
from capstone.arm_const import ARM_REG_R0,ARM_REG_R1,ARM_REG_R2,ARM_REG_R3

A,W,L=fixture.A,fixture.W,fixture.L


class ZeroIndexOutputTests(unittest.TestCase):
    indexes=staticmethod(fixture.BoundedOutputTests.indexes)

    @classmethod
    def setUpClass(cls):
        sources={address:source.replace('unsigned char','signed char') for address,source in fixture.SOURCES.items()}
        sources[A]='''extern void func_08020000(int, int, signed char *, signed char *);
int func_08010000(int value, int divisor)
{
    signed char outputs[2];
    signed char *last = &outputs[1];
    func_08020000(value, divisor, &outputs[0], last);
    return (short)value % divisor + outputs[0] + *last;
}
'''
        with patch.dict(fixture.SOURCES,sources):
            fixture.BoundedOutputTests.setUpClass.__func__(cls)
        cls.signed=[item for item in cls.instructions if zero.signed_load(item) is not None]
        assert cls.signed,'natural signed-char fixture must emit real register-index LDRSB'

    @classmethod
    def native(cls,**changes):
        values=dict(data=cls.body,address=A,rom=cls.rom,mapping=cls.mapping,index=cls.index,
            calls=cls.calls[A],bindings=cls.bindings,selector=profile.SELECTOR,
            output_calls=cls.outputs,operand_selector=fixture.shift.SELECTOR)
        values.update(changes);return profile.verify(**values)

    def changed(self,site,encoded):
        body=bytearray(self.body);body[site-A:site-A+2]=encoded.to_bytes(2,'little')
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        return bytes(body),bytes(rom)

    def test_natural_signed_local_original_O2_API_CLI_and_old_refusal(self):
        self.assertTrue(self.manifest['complete_native_proof'])
        self.assertTrue(self.manifest['inventory_only']);self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertEqual(self.manifest['selector'],profile.SELECTOR)
        accesses=self.manifest['frame']['zero_index_signed_loads']
        self.assertTrue(accesses)
        self.assertTrue(all(width==1 and origins for _,_,_,width,origins in accesses))
        self.assertTrue(all(struct.unpack_from('<H',raw,16)[0]==1 for raw in self.raw.values()))
        for row in self.manifest['bounded_output']['dependencies']:
            self.assertFalse(row['conditional_internal_ABI'])
            self.assertFalse(row['frame_memory_separation_contract']['arbitrary_pointer_ABI_claim'])
        for item in self.signed:
            self.assertEqual(item.mnemonic,'ldrsb')
            self.assertEqual(int.from_bytes(item.bytes,'little') & 0xFE00,0x5600)
        with self.assertRaisesRegex(ValueError,'constant-offset memory access'):
            prior.verify(self.body,A,self.rom,self.mapping,self.index,self.calls[A],self.bindings,
                selector=prior.SELECTOR,output_calls=self.outputs,operand_selector=fixture.shift.SELECTOR)
        command=[sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--operand-profile',fixture.shift.SELECTOR,'--rom',str(self.root/'baserom.bin'),
            '--mapping',str(self.root/'config/functions.json'),'--index',str(self.root/'symbols/functions.txt')]
        for site,target in self.outputs.items():command+=['--output-call',f'{site:08X}:{target:08X}']
        run=subprocess.run(command+[f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-cli.json').write_text(run.stdout)

    def test_nonzero_and_unknown_index_refused_in_native_owner(self):
        instructions,edges,_,_,_=graph.graph(self.body,A,owner.refine(self.body,A,self.mapping))
        states=zero.prove_zeros(instructions,edges,A)
        load=self.signed[0];index=zero.signed_load(load)[1];origins=states[load.address][index]
        self.assertEqual(len(origins),1);origin=next(iter(origins))
        encoded=int.from_bytes(instructions[origin].bytes,'little')
        body,rom=self.changed(origin,encoded|1)
        with self.assertRaisesRegex(ValueError,'constant-offset|outside|out-of-frame|tracked'):
            self.native(data=body,rom=rom)
        # Replace the same emitted MOVS with a copy of an unknown scratch value.
        destination=index-ARM_REG_R0;unknown=next(r for r in range(4) if ARM_REG_R0+r!=index)
        body,rom=self.changed(origin,0x4600|(unknown<<3)|destination)
        with self.assertRaises(ValueError):self.native(data=body,rom=rom)

    @staticmethod
    def decode(values,address=A):
        cs=Cs(CS_ARCH_ARM,CS_MODE_THUMB);cs.detail=True
        data=b''.join(value.to_bytes(2,'little') for value in values)
        return {item.address:item for item in cs.disasm(data,address)}

    def test_zero_copies_writes_and_call_kills_are_exact(self):
        # Mutation-sized instruction samples authenticate zero transfers only;
        # the positive full-owner evidence comes from original agbcc output.
        instructions=self.decode([0x2000,0x1C01,0x460A,0x2301,0x0013,0xF000,0xF800,0x560A])
        sites=sorted(instructions);edges={site:(sites[k+1],) if k+1<len(sites) else () for k,site in enumerate(sites)}
        states=zero.prove_zeros(instructions,edges,A)
        self.assertIn(ARM_REG_R0,states[A+2]);self.assertIn(ARM_REG_R1,states[A+4]);self.assertIn(ARM_REG_R2,states[A+6])
        self.assertNotIn(ARM_REG_R3,states[A+10])
        self.assertFalse(set(range(ARM_REG_R0,ARM_REG_R3+1)) & states[A+14].keys())
        self.assertIsNotNone(zero.signed_load(instructions[A+14]))
        self.assertNotIn(zero.signed_load(instructions[A+14])[1],states[A+14])

    def test_branch_bypass_and_unknown_join_do_not_create_zero(self):
        instructions=self.decode([0x2000,0x2100,0x460A,0x2201,0x5642])
        # One predecessor skips the only zero producer for r1. Every node is
        # retained; an invented branch condition supplies no numeric fact.
        edges={A:(A+2,A+4),A+2:(A+4,),A+4:(A+6,),A+6:(A+8,),A+8:()}
        states=zero.prove_zeros(instructions,edges,A)
        self.assertNotIn(ARM_REG_R1,states[A+4]);self.assertNotIn(ARM_REG_R2,states[A+6])
        # A later nonzero write also kills an earlier exact zero.
        self.assertNotIn(ARM_REG_R2,states[A+8])
        self.assertIsNotNone(zero.signed_load(instructions[A+8]))
        self.assertNotIn(zero.signed_load(instructions[A+8])[1],states[A+8])

    def test_exact_signed_load_encodings_and_width_saved_slot_bounds(self):
        instructions=self.decode([0x5608,0x5E08,0x5C08,0x5A08])
        self.assertEqual(zero.signed_load(instructions[A]),(ARM_REG_R1,ARM_REG_R0,1))
        self.assertEqual(zero.signed_load(instructions[A+2]),(ARM_REG_R1,ARM_REG_R0,2))
        self.assertIsNone(zero.signed_load(instructions[A+4]));self.assertIsNone(zero.signed_load(instructions[A+6]))
        # Change one natural LDRSB into LDRSH. The byte local at SP+1 is
        # misaligned for a halfword, which must still fail allocated-local bounds.
        item=next(item for item in self.signed if self.instructions.index(item)>0)
        body,rom=self.changed(item.address,int.from_bytes(item.bytes,'little')|0x800)
        with self.assertRaisesRegex(ValueError,'aligned|unaligned|local words|outside|constant-offset'):
            self.native(data=body,rom=rom)
        # Change a natural local base materialization from SP to SP+4, the
        # caller's saved-register slots. This cannot gain admission from zero.
        candidates=[item for item in self.instructions if item.mnemonic=='mov' and item.op_str.endswith(', sp')]
        self.assertTrue(candidates)
        item=candidates[-1];destination=item.operands[0].reg-ARM_REG_R0
        body,rom=self.changed(item.address,0xA800|(destination<<8)|1)
        with self.assertRaisesRegex(ValueError,'local|saved|outside'):
            self.native(data=body,rom=rom)

    def test_selector_context_and_manifest_are_isolated(self):
        with self.assertRaisesRegex(ValueError,'explicit inventory-only'):
            self.native(selector=prior.SELECTOR)
        with self.assertRaisesRegex(ValueError,'cannot be combined'):
            match.verify_leaf_instructions(self.body,A,True,self.calls[A],
                bounded_stack_output_inventory_context=(),bounded_stack_output_zero_index_inventory_context=())
        observed=copy.deepcopy(self.manifest);observed['frame']['zero_index_signed_loads']=[]
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.native(manifest=observed)
        instructions,edges,branches,calls,_=graph.graph(self.body,A,owner.refine(self.body,A,self.mapping))
        with self.assertRaisesRegex(ValueError,'explicit native alias policy'):
            frame.prove_frame(instructions,edges,A,branches,calls,stack_aliases=True,zero_index_profile='guess')


if __name__=='__main__':unittest.main()
