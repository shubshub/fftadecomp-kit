"""Original agbcc O2 evidence for explicit independently proved output calls."""
import argparse
import copy
import hashlib
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
import owner_graph_profile as graph
import bounded_stack_output_profile as effects
import bounded_stack_output_inventory as profile
import zero_aware_remainder_framed_inventory as framed
import zero_aware_remainder_shift_inventory as shift
from capstone.arm_const import ARM_REG_R2,ARM_REG_R3

A,W,L=0x08010000,0x08020000,0x08030000
SOURCES={A:'''extern void func_08020000(int, int, unsigned char *, unsigned char *);
int func_08010000(int value, int divisor)
{
    unsigned char outputs[2];
    func_08020000(value, divisor, &outputs[0], &outputs[1]);
    return (short)value % divisor + outputs[0] + outputs[1];
}
''',W:'''extern void func_08030000(int, int, unsigned char *, unsigned char *);
void func_08020000(signed char x, signed char y, unsigned char *a, unsigned char *b)
{
    func_08030000(x, y, a, b);
}
''',L:'''void func_08030000(int x, int y, unsigned char *a, unsigned char *b)
{
    *a = 0;
    *b = 0;
    if (x == y) *a = 1;
    else if (x > y) *b = 1;
}
'''}


class BoundedOutputTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows,indent=2)+'\n').encode(), ''.join(
            f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
            for row in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected=os.environ.get('FFTA_ROM')
        if not selected:raise unittest.SkipTest('FFTA_ROM must reference approved ROM')
        approved=Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest()=='43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch=Path(os.environ.get('FFTA_TEST_SCRATCH',Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='bounded_output_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup);cls.root=Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):(cls.root/name).mkdir()
        cls.retained=Path(os.environ['FFTA_BOUNDED_OUTPUT_RETAIN']) if os.environ.get('FFTA_BOUNDED_OUTPUT_RETAIN') else None
        if cls.retained:cls.retained.mkdir(parents=True,exist_ok=True)
        cls.args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        cls.runner=match.Runner(match.DEFAULT_CC,root=cls.root,timeout=120)
        cls.originals={};cls.raw={}
        for address,source in SOURCES.items():
            (cls.root/f'src/{address:08X}.c').write_text(source)
            with cls.runner.workspace() as workspace:
                raw,_,original=match.compile_object(cls.runner,workspace,cls.args,cls.root,address,f'src/{address:08X}.c')
                cls.originals[address]=original;cls.raw[address]=raw
                if cls.retained:
                    (cls.retained/f'{address:08X}.c').write_text(source)
                    (cls.retained/f'{address:08X}.o').write_bytes(raw)
                    (cls.retained/f'{address:08X}.s').write_bytes(cls.runner.read_binary(f'{workspace}/f.s'))
        cls.rows=[{'rom':f'0x{address:08X}','end':f'0x{address+len(original["text"]):08X}',
            'mode':'thumb','instrs':0} for address,original in cls.originals.items()]
        cls.rows += [{'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1},
            {'rom':'0x08142950','end':'0x08142A1E','mode':'thumb','instrs':102}]
        mapping,_=cls.indexes(cls.rows)
        cls.bodies={};cls.calls={}
        for address,original in cls.originals.items():
            with cls.runner.workspace() as workspace:
                Path(workspace,'f.o').write_bytes(cls.raw[address])
                runtime={}
                if original['relocations']:
                    data,calls,literals=match.link_calls(cls.runner,workspace,cls.args,original,address,
                        mapping,len(approved),approved,modsi3_bindings=runtime)
                else:data,calls,literals=match.function_bytes(cls.raw[address],original['text'],f'func_{address:08X}',address,True),{},{}
                assert not literals
                cls.bodies[address]=data;cls.calls[address]=calls
                if cls.retained:
                    if original['relocations']:
                        (cls.retained/f'{address:08X}.elf').write_bytes(cls.runner.read_binary(f'{workspace}/f.elf'))
                    (cls.retained/f'{address:08X}.bin').write_bytes(data)
        rom=bytearray(approved)
        for address,data in cls.bodies.items():rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)]=data
        cls.rom=bytes(rom);cls.body=cls.bodies[A]
        for row in cls.rows:
            address=int(row['rom'],16)
            if address in cls.bodies:
                row['end']=f'0x{address+len(cls.bodies[address]):08X}'
                row['instrs']=owner.refine(cls.bodies[address],address,mapping)['instrs']
        cls.mapping,cls.index=cls.indexes(cls.rows)
        cls.bindings=profile.bind_calls(cls.calls[A],cls.mapping,A,len(cls.body),len(cls.rom))
        cls.outputs={site:target for site,target in cls.calls[A].items() if target==W}
        cls.manifest,cls.instructions=cls.native()
        for name,data in (('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),('baserom.bin',cls.rom)):
            (cls.root/name).write_bytes(data)
        if cls.retained:
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
            (cls.retained/'functions.json').write_bytes(cls.mapping);(cls.retained/'functions.txt').write_bytes(cls.index)
            (cls.retained/'fixture.json').write_text(json.dumps({'ELF_types':{f'{a:08X}':struct.unpack_from('<H',raw,16)[0]
                for a,raw in cls.raw.items()},'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS],
                'source_or_ELF_admission':False,'synthetic_fixture_only':True},indent=2)+'\n')

    @classmethod
    def native(cls,**changes):
        values=dict(data=cls.body,address=A,rom=cls.rom,mapping=cls.mapping,index=cls.index,
            calls=cls.calls[A],bindings=cls.bindings,selector=profile.SELECTOR,output_calls=cls.outputs,
            operand_selector=shift.SELECTOR)
        values.update(changes);return profile.verify(**values)

    def proof(self,rom=None,mapping=None,index=None):
        return effects.BoundedOutputProof(rom or self.rom,mapping or self.mapping,index or self.index,self.outputs)

    def test_natural_original_O2_API_and_CLI(self):
        self.assertTrue(self.manifest['complete_native_proof'])
        self.assertTrue(self.manifest['inventory_only']);self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertEqual(set(self.manifest['divisor_partition']),{'r1 == 0','r1 != 0'})
        dependencies=self.manifest['bounded_output']['dependencies']
        self.assertEqual({row['address'] for row in dependencies},{W,L})
        for row in dependencies:
            self.assertFalse(row['conditional_internal_ABI'])
            self.assertFalse(row['frame_memory_separation_contract']['arbitrary_pointer_ABI_claim'])
            self.assertEqual(row['frame_memory_separation_contract']['argument_effect_windows'],
                'entirely at or above callee entry SP')
            self.assertEqual(row['frame']['external_calls'],'complete-native-callee-preservation-v1')
            self.assertEqual(row['effects'],[['write',ARM_REG_R2,0,1],['write',ARM_REG_R3,0,1]])
        self.assertTrue(all(struct.unpack_from('<H',raw,16)[0]==1 for raw in self.raw.values()))
        command=[sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--operand-profile',shift.SELECTOR,'--rom',str(self.root/'baserom.bin'),
            '--mapping',str(self.root/'config/functions.json'),'--index',str(self.root/'symbols/functions.txt')]
        for site,target in self.outputs.items():command+=['--output-call',f'{site:08X}:{target:08X}']
        run=subprocess.run(command+[f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-cli.json').write_text(run.stdout)

    def test_whole_range_bounds_and_saved_slot_overlap(self):
        site=next(iter(self.outputs));local=(False,False,True);saved=(True,True,False)
        self.proof().check_call(W,{ARM_REG_R2:-8,ARM_REG_R3:-7},[local,saved],site=site)
        for offsets in ((-5,-4),(-9,-8),(-1,0)):
            with self.subTest(offsets=offsets),self.assertRaisesRegex(ValueError,'outside allocated local words'):
                self.proof().check_call(W,dict(zip((ARM_REG_R2,ARM_REG_R3),offsets)),[local,saved],site=site)

    def test_native_caller_discharge_rejects_saved_output_window(self):
        body=bytearray(self.body)
        increment=next(item for item in self.instructions if item.mnemonic=='adds' and item.op_str=='r3, #1')
        # Negative mutation of the natural caller's immediate, changing the
        # second output from SP+1 to SP+4, its saved-register area.
        body[increment.address-A]=4
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            self.native(data=bytes(body),rom=bytes(rom))

    def test_callee_own_saved_or_upward_stack_writes_rejected(self):
        refined=owner.refine(self.bodies[L],L,self.mapping)
        instructions,*_=graph.graph(self.bodies[L],L,refined)
        store=next(item for item in instructions.values() if item.mnemonic=='strb')
        for slot in (0,2):
            rom=bytearray(self.rom)
            # Negative mutations of a compiler-emitted store, addressing the
            # saved r4 word or the word above the complete callee frame.
            rom[store.address-match.ROM_BASE:store.address-match.ROM_BASE+2]=(0x9000|slot).to_bytes(2,'little')
            with self.subTest(slot=slot),self.assertRaisesRegex(ValueError,'saved|tracked|frame'):
                self.proof(bytes(rom)).prove(W,(ARM_REG_R2,ARM_REG_R3))

    def test_signed16_and_canonical_runtime_remain_mandatory(self):
        body=bytearray(self.body)
        asr=next(item for item in self.instructions if item.mnemonic=='asrs')
        encoded=int.from_bytes(asr.bytes,'little')
        body[asr.address-A:asr.address-A+2]=((encoded & ~(31<<6)) | (15<<6)).to_bytes(2,'little')
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        with self.assertRaisesRegex(ValueError,'signed16|bounded immediate shift'):
            self.native(data=bytes(body),rom=bytes(rom))
        rom=bytearray(self.rom);rom[0x0814274C-match.ROM_BASE]^=1
        with self.assertRaisesRegex(ValueError,'canonical|identity|fingerprint|differs'):
            self.native(rom=bytes(rom))

    def test_output_argument_overlap_rejected(self):
        with self.assertRaisesRegex(ValueError,'argument effects overlap'):
            self.proof().check_call(W,{ARM_REG_R2:-4,ARM_REG_R3:-4},[(False,False,True)],site=next(iter(self.outputs)))

    def test_unmarked_ordinary_and_runtime_stack_arguments_rejected(self):
        for target in (W,0x08142950):
            with self.subTest(target=target),self.assertRaisesRegex(ValueError,'unmarked ordinary/runtime'):
                self.proof().check_call(target,{ARM_REG_R2:-4},[(False,False,True)],site=A+2)
        with self.assertRaisesRegex(ValueError,'stack aliases cannot cross calls'):
            framed.verify(self.body,A,self.rom,self.mapping,self.index,self.calls[A],self.bindings,selector=framed.SELECTOR)

    def compile_negative(self,source):
        address=0x08040000
        (self.root/f'src/{address:08X}.c').write_text(source)
        with self.runner.workspace() as workspace:
            raw,_,original=match.compile_object(self.runner,workspace,self.args,self.root,address,f'src/{address:08X}.c')
            data=match.function_bytes(raw,original['text'],f'func_{address:08X}',address,True)
            if self.retained:
                name=hashlib.sha256(source.encode()).hexdigest()[:12]
                (self.retained/f'negative-{name}.c').write_text(source)
                (self.retained/f'negative-{name}.o').write_bytes(raw)
                (self.retained/f'negative-{name}.s').write_bytes(self.runner.read_binary(f'{workspace}/f.s'))
        self.assertFalse(original['relocations'])
        rows=copy.deepcopy(self.rows)+[{'rom':f'0x{address:08X}','end':f'0x{address+len(data):08X}','mode':'thumb','instrs':0}]
        mapping,index=self.indexes(rows);rom=bytearray(self.rom)
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)]=data
        return self.proof(bytes(rom),mapping,index),address

    def test_natural_pointer_escape_and_global_write_rejected(self):
        sources=[('unsigned char *func_08040000(int x,int y,unsigned char*a,unsigned char*b){return a;}',
                  'ABI result register|unsupported use or escape'),
                 ('void func_08040000(int x,int y,unsigned char*a,unsigned char*b){*(unsigned char**)b=a;}',
                  'escape through memory'),
                 ('void func_08040000(int x,int y,unsigned char*a,unsigned char*b){*(unsigned char*)0x02000000=x;*a=y;}',
                  'unknown/global memory'),
                 ('void func_08040000(int x,int y,unsigned char*a,unsigned char*b){unsigned char*p;if(x)p=a;else p=(unsigned char*)y;*p=1;}',
                  'ambiguous|unknown/global|unsupported use or escape')]
        for source,message in sources:
            with self.subTest(source=source):
                proof,address=self.compile_negative(source)
                with self.assertRaisesRegex(ValueError,message):proof.prove(address,(ARM_REG_R2,ARM_REG_R3))

    def test_callee_saved_register_restoration_is_independent(self):
        refined=owner.refine(self.bodies[L],L,self.mapping)
        instructions,*_=graph.graph(self.bodies[L],L,refined)
        candidates=[item for item in instructions.values() if item.mnemonic=='pop' and
            any(item.reg_name(op.reg)=='r4' for op in item.operands)]
        self.assertTrue(candidates,'natural compiler fixture must save and restore r4')
        item=candidates[0];rom=bytearray(self.rom)
        encoded=int.from_bytes(item.bytes,'little');self.assertTrue(encoded & 0x10)
        # Negative mutation of a retained natural compiler instruction: restore
        # the saved r4 word into r5 instead. No assembled or positive ASM fixture.
        rom[item.address-match.ROM_BASE:item.address-match.ROM_BASE+2]=((encoded & ~0x10)|0x20).to_bytes(2,'little')
        with self.assertRaisesRegex(ValueError,'restore SP, r4-r11'):
            self.proof(bytes(rom)).prove(W,(ARM_REG_R2,ARM_REG_R3))

    def test_context_and_manifest_are_explicit(self):
        with self.assertRaisesRegex(ValueError,'explicit inventory-only'):
            self.native(selector=framed.SELECTOR)
        with self.assertRaisesRegex(ValueError,'sites differ'):
            self.native(output_calls={next(iter(self.outputs)):0x08142950})
        altered=copy.deepcopy(self.manifest);altered['bounded_output']['dependencies'][0]['effects']=[]
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.native(manifest=altered)
        with self.assertRaisesRegex(ValueError,'cannot be combined'):
            match.verify_leaf_instructions(self.body,A,True,self.calls[A],
                bounded_stack_output_inventory_context=(),remainder_byte_range_inventory_context=())


if __name__=='__main__':unittest.main()
