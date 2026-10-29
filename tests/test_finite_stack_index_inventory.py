"""Finite local-word alternatives preserve every path and strict frame gate."""
import argparse
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
import match
import owner_admission_profile as owner
import local_long_branch_profile as frame
import finite_stack_index_profile as finite
import finite_stack_index_inventory as profile

A,ORDINARY=0x08010000,0x08020000
SOURCE='''extern int func_08020000(int value);
int func_08010000(int first, int second, int condition)
{
    int pair[2];
    unsigned index = 0;
    pair[0] = first;
    pair[1] = second;
    if (func_08020000(condition)) {
        index = 1;
        func_08020000(second);
    } else {
        func_08020000(first);
    }
    return pair[index];
}
'''


class FiniteStackIndexInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows,indent=2)+'\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('FFTA_TEST_SCRATCH',Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='finite_indices_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root=Path(cls.temporary.name)
        for directory in ('src','include','config','symbols','build'):(cls.root/directory).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained=Path(os.environ['FFTA_FINITE_RETAIN']) if os.environ.get('FFTA_FINITE_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True,exist_ok=True)
            (cls.retained/'caller.c').write_text(SOURCE)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        runner=match.Runner(match.DEFAULT_CC,root=cls.root,timeout=120)
        with runner.workspace() as workspace:
            cls.raw,_,original=match.compile_object(runner,workspace,args,cls.root,A,'src/08010000.c')
            if cls.retained:
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
            cls.rows=[{'rom':f'0x{A:08X}','end':f'0x{A+len(original["text"]):08X}','mode':'thumb','instrs':0},
                {'rom':f'0x{ORDINARY:08X}','end':f'0x{ORDINARY+2:08X}','mode':'thumb','instrs':1}]
            mapping,_=cls.indexes(cls.rows)
            cls.body,cls.calls,literals=match.link_calls(runner,workspace,args,original,A,mapping,ORDINARY+2-match.ROM_BASE)
            assert not literals
            if cls.retained:(cls.retained/'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
        cls.rows[0]['end']=f'0x{A+len(cls.body):08X}'
        mapping,_=cls.indexes(cls.rows)
        cls.rows[0]['instrs']=owner.refine(cls.body,A,mapping)['instrs']
        cls.mapping,cls.index=cls.indexes(cls.rows)
        rom=bytearray(ORDINARY+2-match.ROM_BASE)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)]=cls.body
        rom[ORDINARY-match.ROM_BASE:]=bytes.fromhex('7047')
        cls.rom=bytes(rom)
        cls.bindings=profile.bind_calls(cls.calls,cls.mapping,A,len(cls.body),len(cls.rom))
        for name,data in [('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),('baserom.bin',cls.rom)]:
            (cls.root/name).write_bytes(data)
        cls.manifest,cls.instructions=profile.verify(cls.body,A,cls.rom,cls.mapping,cls.index,
            cls.calls,cls.bindings,selector=profile.SELECTOR)
        if cls.retained:
            for name,data in [('body.bin',cls.body),('baserom.bin',cls.rom),('functions.json',cls.mapping),('functions.txt',cls.index)]:
                (cls.retained/name).write_bytes(data)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
            (cls.retained/'fixture.json').write_text(json.dumps({'ELF_type':original['type'],
                'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS],'synthetic_only':True,
                'source_or_ELF_admission':False,'calls':cls.calls},indent=2)+'\n')

    def native(self,**changes):
        values=dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
            calls=self.calls,bindings=self.bindings,selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    HEAD=[0xB510,0xB082]
    INIT=[0x2000,0x9000,0x2001,0x9001]
    BOOL=[0x2400,0x2900,0xD000,0x2401]
    INDEX=[0x00A0,0x4468]
    TAIL=[0xB002,0xBC10,0xBC02,0x4708]

    def local(self,sequence,policy=finite.SELECTOR):
        data=bytearray()
        for value in sequence:
            if type(value) is int:data+=struct.pack('<H',value)
            else:
                displacement=ORDINARY-(A+len(data))-4
                data+=struct.pack('<HH',0xF000|((displacement>>12)&0x7FF),0xF800|((displacement>>1)&0x7FF))
        md=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);md.detail=True
        instructions={i.address:i for i in md.disasm(bytes(data),A)}
        edges={};calls={}
        for site,i in instructions.items():
            if i.mnemonic=='bx':edges[site]=()
            elif i.mnemonic=='bl':calls[site]=i.operands[0].imm;edges[site]=(site+i.size,)
            elif i.mnemonic=='b':edges[site]=(i.operands[0].imm,)
            elif i.mnemonic.startswith('b'):edges[site]=(i.operands[0].imm,site+i.size)
            else:edges[site]=(site+i.size,)
        return frame.prove_frame(instructions,edges,A,{},calls,stack_aliases=True,finite_stack_index_policy=policy)

    def test_natural_O2_API_CLI_and_source_admission_boundary(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        proof=self.manifest['frame']['finite_stack_indices']
        self.assertTrue(any([value for value,_ in row[2]]==[0,4] for row in proof['SP_additions']))
        self.assertTrue(any(len(row[2])==2 for row in proof['reads']))
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertFalse(self.manifest['source_or_ELF_admission'] or self.manifest['arithmetic_C_equivalence'] or self.manifest['termination_claim'])
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        run=subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_two_alternatives_and_conditional_callee_saved_facts(self):
        sequence=self.HEAD+self.INIT+self.BOOL+['ordinary']+self.INDEX+[0x6800]+self.TAIL
        proof=self.local(sequence)['finite_stack_indices']
        self.assertEqual(proof['SP_additions'][0][2][0][0],0)
        self.assertEqual(proof['SP_additions'][0][2][1][0],4)
        self.assertEqual(proof['reads'][0][2],[-16,-12])
        with self.assertRaises(ValueError):self.local(sequence,None)
        with self.assertRaisesRegex(ValueError,'versioned policy'):self.local(sequence,'other')

    def test_missing_arm_unknown_write_shift_and_caller_saved_call_kill(self):
        variants=[self.HEAD+self.INIT+[0x2900,0xD000,0x2401]+self.INDEX+[0x6800]+self.TAIL,
            self.HEAD+self.INIT+self.BOOL+[0x3400]+self.INDEX+[0x6800]+self.TAIL,
            self.HEAD+self.INIT+self.BOOL+[0x0060,0x4468,0x6800]+self.TAIL,
            self.HEAD+self.INIT+self.BOOL+[0x40A0,0x4468,0x6800]+self.TAIL,
            self.HEAD+self.INIT+[0x2400,0x2900,0xD003,0x2401,0x2A00,0xD000,0x00A4]+self.INDEX+[0x6800]+self.TAIL,
            self.HEAD+self.INIT+[0x2200,0x2900,0xD000,0x2201,'ordinary',0x0090,0x4468,0x6800]+self.TAIL]
        for sequence in variants:
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.local(sequence)

    def test_saved_outside_uninitialized_and_one_uninitialized_arm(self):
        variants=[self.HEAD+self.INIT+self.BOOL+self.INDEX+[0x3008,0x6800]+self.TAIL,
            self.HEAD+self.INIT+self.BOOL+self.INDEX+[0x3020,0x6800]+self.TAIL,
            self.HEAD+[0x2000,0x9000]+self.BOOL+self.INDEX+[0x6800]+self.TAIL,
            self.HEAD+[0x2000,0x9000,0x2900,0xD000,0x9001]+self.BOOL+self.INDEX+[0x6800]+self.TAIL,
            self.HEAD+self.INIT+[0x9002]+self.BOOL+self.INDEX+[0x6800]+self.TAIL]
        for sequence in variants:
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.local(sequence)

    def test_alias_partial_write_spill_call_escape_and_released_lifetime(self):
        variants=[[0x7001,0x6800],[0x6001,0x6800],[0x9000,0x6800],['ordinary',0x6800],
            [0xB002,0xB082,0x6800],[]]
        for middle in variants:
            with self.subTest(middle=middle),self.assertRaises(ValueError):
                self.local(self.HEAD+self.INIT+self.BOOL+self.INDEX+middle+self.TAIL)

    def test_tainted_alias_join_and_control_or_saved_restore_failure(self):
        for sequence in [self.HEAD+self.INIT+self.BOOL+[0x00A0,0x2900,0xD000,0x4468,0x6800]+self.TAIL,
                self.HEAD+self.INIT+self.BOOL+self.INDEX+[0x4685,0x6800]+self.TAIL,
                self.HEAD+self.INIT+self.BOOL+self.INDEX+[0x6800,'ordinary']+self.TAIL[:-1]+[0x4770]]:
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.local(sequence)

    def test_central_runtime_thunk_unknown_overlap_and_forged_evidence_gates(self):
        for target in [0x081426B8,0x08142950,0x08142244,0x08142246,ORDINARY+2,A+2]:
            calls=dict(self.calls);calls[next(iter(calls))]=target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))
        rows=copy.deepcopy(self.rows);rows.append(dict(rows[1]))
        with self.assertRaises(ValueError):profile.bind_calls(self.calls,self.indexes(rows)[0],A,len(self.body),len(self.rom))
        with self.assertRaises(ValueError):self.native(bindings={})
        with self.assertRaises(ValueError):self.native(selector='other')
        manifest=copy.deepcopy(self.manifest);manifest['frame']['finite_stack_indices']['reads'][0][2].pop()
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=manifest)
        altered=bytearray(self.rom);altered[A-match.ROM_BASE]^=1
        with self.assertRaises(ValueError):self.native(rom=bytes(altered))


if __name__=='__main__':unittest.main()
