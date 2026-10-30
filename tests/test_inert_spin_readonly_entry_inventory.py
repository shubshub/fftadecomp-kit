"""Natural fifth-argument inert spin and focused composition boundaries."""
import argparse
import copy
import json
import os
from pathlib import Path
import shlex
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
if os.environ.get('FFTA_BASE_TOOLS'):
    sys.path.insert(1, os.environ['FFTA_BASE_TOOLS'])
import inert_spin_readonly_entry_inventory as profile
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import readonly_entry_stack_profile as entry

A, B = 0x08010000, 0x08020000
SOURCE = '''extern unsigned int func_08020000(unsigned int, unsigned int,
    unsigned int, unsigned int, unsigned int);
unsigned int func_08010000(unsigned int a, unsigned int b, unsigned int c,
    unsigned int d, unsigned int extra)
{
    unsigned int result = func_08020000(a, b, c, d, extra);
    if (extra > 8) {
        for (;;) { }
    }
    return result + extra;
}
'''


class InertEntryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(), ''.join(
            f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='inert_entry_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_INERT_ENTRY_RETAIN']) if os.environ.get('FFTA_INERT_ENTRY_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            if cls.retained:
                (cls.retained/'caller.c').write_text(SOURCE)
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(workspace+'/f.s'))
            script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
            script += '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
            script += '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
            script += '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
            script += 'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }'
            runner.write_text(workspace+'/f.ld',script)
            # Typed absolute linker symbol only, no assembly function body.
            runner.write_text(workspace+'/f.known.s','.syntax unified\n.thumb\n.global func_08020000\n'
                '.type func_08020000, %function\n'+f'.thumb_set func_08020000, 0x{B|1:08X}\n')
            q=shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
                f'-T {q}/f.ld -e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            linked=runner.read_binary(workspace+'/f.elf'); image=match.elf_image(linked)
            match.allocated_text_only(image)
            symbol,offset=match.function_record(image,'func_08010000',A,True)
            assert original['type']==1 and image['type']==2 and not image['relocations'] and offset==0
            cls.body=image['text'][:symbol['size']]
            assert len(image['text'])==len(original['text'])
            expected=bytearray(original['text'][:symbol['size']]); relocations=[]
            for section_index in original['relocations']:
                section=original['sections'][section_index]; symbols=original['symbol_tables'][section[6]]
                for position in range(0,section[5],8):
                    site,info=struct.unpack_from('<II',original['section_data'][section_index],position)
                    target=symbols[info>>8]
                    assert info&255==10 and target['name']=='func_08020000' and not target['section']
                    expected[site:site+4]=cls.body[site:site+4]; relocations.append([site,10])
            assert bytes(expected)==cls.body and relocations
            if cls.retained:
                (cls.retained/'linked.elf').write_bytes(linked)
                (cls.retained/'compiler-evidence.json').write_text(json.dumps({'ET_REL':original['type'],
                    'linked_type':image['type'],'compiler':args.cc,'flags':args.flags,'relocations':relocations,
                    'only_standard_linker_relocations_changed':True,'source_or_ELF_admission':False},indent=2)+'\n')
        cls.rows=[{'rom':f'0x{A:08X}','end':f'0x{A+len(cls.body):08X}','mode':'thumb','instrs':0},
            {'rom':f'0x{B:08X}','end':f'0x{B+2:08X}','mode':'thumb','instrs':1}]
        mapping,_=cls.indexes(cls.rows); refinement=owner.refine(cls.body,A,mapping)
        cls.rows[0]['instrs']=refinement['instrs']; cls.mapping,cls.index=cls.indexes(cls.rows)
        cls.ins,cls.edges,cls.calls,_=profile.graph(cls.body,A,refinement)
        rom=bytearray(B-match.ROM_BASE+2);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)]=cls.body
        cls.rom=bytes(rom); cls.bindings=profile.bind_calls(cls.calls,cls.mapping,A,len(cls.body),len(cls.rom))
        cls.manifest,cls.instructions=profile.verify(cls.body,A,cls.rom,cls.mapping,cls.index,cls.calls,
            cls.bindings,selector=profile.SELECTOR)
        for name,data in (('baserom.bin',cls.rom),('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index)):
            (cls.root/name).write_bytes(data)
        if cls.retained:
            (cls.retained/'fixture-proof.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
            (cls.retained/'body.bin').write_bytes(cls.body)

    def native(self,**changes):
        args=dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
            calls=self.calls,bindings=self.bindings,selector=profile.SELECTOR)
        args.update(changes)
        return profile.verify(**args)

    def changed(self,data,**changes):
        data=bytes(data);rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        return self.native(data=data,rom=bytes(rom),**changes)

    def frame_only(self,sequence,policy=True,initialization=False):
        data=b''.join(struct.pack('<H',word) for word in sequence)
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        ins={i.address:i for i in decoder.disasm(data,A)}
        edges={site: (() if i.mnemonic=='bx' else (site+i.size,)) for site,i in ins.items()}
        kwargs={'entry_stack_policy':{'schema':entry.SCHEMA,'words':[0]}} if policy else {}
        proved=frame.prove_frame(ins,edges,A,{}, {},stack_aliases=True,**kwargs)
        return profile.initialized_locals(ins,edges,A,proved) if initialization else proved

    def test_natural_ET_REL_fifth_argument_inert_spin_API_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertTrue(self.manifest['inventory_only'])
        self.assertEqual(self.manifest['entry_stack_contract'],entry.CONTRACT)
        self.assertEqual(self.manifest['frame']['entry_stack']['reads'][0][1:3],[0,4])
        self.assertTrue(self.manifest['spins'])
        for offset in self.manifest['spins']:self.assertEqual(self.body[offset:offset+2],b'\xfe\xe7')
        self.assertFalse(self.manifest['termination_claim'] or self.manifest['arithmetic_C_equivalence'] or self.manifest['memory_safety_claim'])
        self.assertFalse(self.manifest['source_or_ELF_admission'] or self.manifest['ordinary_callee_native_proof'])
        self.assertIn('conditional',self.manifest['ordinary_call_premise'])
        run=subprocess.run([sys.executable,profile.__file__,'--profile',profile.SELECTOR,'--rom',str(self.root/'baserom.bin'),
            '--mapping',str(self.root/'config/functions.json'),'--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'fixture-cli.json').write_text(run.stdout)

    def test_old_default_and_exact_selector_boundaries(self):
        with self.assertRaises(ValueError):self.native(selector='mixed-return-inert-spin-v1')
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        with self.assertRaisesRegex(ValueError,'leaves its established frame'):
            self.frame_only([0xB510,0xB081,0x9803,0xB001,0xBC10,0xBC02,0x4708],False)

    def test_entry_writes_out_of_range_and_missing_read(self):
        prefix,tail=[0xB510,0xB081],[0xB001,0xBC10,0xBC02,0x4708]
        for access in (0x9003,0x9804,0x9001):
            with self.subTest(access=access),self.assertRaises(ValueError):self.frame_only(prefix+[access]+tail)
        data=bytearray(self.body)
        site=self.manifest['frame']['entry_stack']['reads'][0][0]
        struct.pack_into('<H',data,site-A,0x2000)
        with self.assertRaises(ValueError):self.changed(data)

    def test_uninitialized_local_and_bypass_are_rejected(self):
        prefix,tail=[0xB510,0xB081,0x9803],[0xB001,0xBC10,0xBC02,0x4708]
        with self.assertRaisesRegex(ValueError,'not initialized'):
            self.frame_only(prefix+[0x9900]+tail,initialization=True)
        # Make the real outgoing local store a read. Full native binding/frame
        # remain required; the new initialization gate rejects that local read.
        store=next(i for i in self.instructions if i.mnemonic=='str' and any(
            op.type==profile.ARM_OP_MEM and op.mem.base==profile.ARM_REG_SP for op in i.operands))
        data=bytearray(self.body);encoded=int.from_bytes(store.bytes,'little')
        struct.pack_into('<H',data,store.address-A,encoded|0x0800)
        with self.assertRaisesRegex(ValueError,'not initialized'):self.changed(data)

    def test_local_alias_bounds_escape_and_initialization(self):
        prefix,tail=[0xB510,0xB081,0x9803],[0xB001,0xBC10,0xBC02,0x4708]
        for extra in ([0x466A,0x8812], [0x9000,0x466A,0x8892], [0x9000,0x466A,0x4610]):
            with self.subTest(extra=extra),self.assertRaises(ValueError):
                self.frame_only(prefix+extra+tail,initialization=True)

    def test_exact_inert_spin_mutation_and_bypass(self):
        offset=self.manifest['spins'][0]
        for encoded in (0xD1FE,0xE7FD,0x46C0):
            data=bytearray(self.body);struct.pack_into('<H',data,offset,encoded)
            with self.subTest(encoded=encoded),self.assertRaises(ValueError):self.changed(data)
        data=bytearray(self.body)
        # An unconditional branch skips the fifth-argument load on its only path.
        read=self.manifest['frame']['entry_stack']['reads'][0][0]
        struct.pack_into('<H',data,read-A,0xE000)
        with self.assertRaises(ValueError):self.changed(data)

    def test_call_binding_runtime_and_map_hash_integrity(self):
        for calls,bindings in (({},self.bindings),(self.calls,{})):
            with self.assertRaises(ValueError):self.native(calls=calls,bindings=bindings)
        rows=copy.deepcopy(self.rows); rows[1]['mode']='arm';mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        rows=copy.deepcopy(self.rows);rows[0]['instrs']+=1;mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        with self.assertRaises(ValueError):self.native(rom=bytes(len(self.rom)))
        stale=copy.deepcopy(self.manifest);stale['mapping_sha256']='0'*64
        with self.assertRaises(ValueError):self.native(manifest=stale)
        site=next(iter(self.calls))
        for target in (0x08142950,0x08142AB0,0x0814274C):
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls({site:target},self.mapping,A,len(self.body),len(self.rom))

    def test_branch_bypass_does_not_initialize_local_at_join(self):
        sequence=[0xB510,0xB081,0x9803,0x2800,0xD000,0x9000,0x9900,
            0xB001,0xBC10,0xBC02,0x4708]
        data=b''.join(struct.pack('<H',word) for word in sequence)
        decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        ins={i.address:i for i in decoder.disasm(data,A)}
        edges={site: (() if i.mnemonic=='bx' else (site+i.size,)) for site,i in ins.items()}
        edges[A+8]=(A+12,A+10)
        restored=frame.prove_frame(ins,edges,A,{}, {},stack_aliases=True,
            entry_stack_policy={'schema':entry.SCHEMA,'words':[0]})
        with self.assertRaisesRegex(ValueError,'not initialized on every path'):
            profile.initialized_locals(ins,edges,A,restored)

    def test_stack_alias_cannot_be_passed_to_ordinary_call(self):
        store=next(i for i in self.instructions if i.mnemonic=='str' and any(
            op.type==profile.ARM_OP_MEM and op.mem.base==profile.ARM_REG_SP for op in i.operands))
        data=bytearray(self.body);struct.pack_into('<H',data,store.address-A,0x4668)
        with self.assertRaisesRegex(ValueError,'aliases crossing calls'):
            self.changed(data)

    def test_frame_and_callee_saved_clobber_remain_rejected(self):
        prefix=[0xB510,0xB081,0x9803];tail=[0xB001,0xBC10,0xBC02,0x4708]
        for sequence in (prefix+[0x9001]+tail,prefix+[0xB000,0xBC10,0xBC02,0x4708],
                prefix+tail[:-1]+[0x2000,0x4700],prefix+tail[:-1]+[0x2400,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.frame_only(sequence)


if __name__=='__main__':unittest.main()
