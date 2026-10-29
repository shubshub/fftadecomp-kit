"""Natural callee-local descriptors, exact origins and mandatory final ABI proof."""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import descriptor_output_alias_profile as profile

A, B, C, D = 0x08010000, 0x08011000, 0x08012000, 0x08013000
SOURCE = '''extern unsigned int func_08011000(unsigned char *);
unsigned int func_08010000(unsigned int value)
{
    unsigned char marker[4];
    marker[0] = value;
    return func_08011000(marker) + marker[0] + 1;
}
'''
WORKER = '''struct Output { unsigned char *bytes; };
extern void func_08012000(struct Output *);
unsigned int func_08011000(unsigned char *marker)
{
    unsigned char bytes[4];
    struct Output output;
    output.bytes = bytes;
    func_08012000(&output);
    return bytes[0] + marker[0];
}
'''
LEAF = '''struct Output { unsigned char *bytes; };
void func_08012000(struct Output *output) { output->bytes[0] = 7; }
'''


def fixture(root, leaf=LEAF):
    root = Path(root)
    for name in ('src','include','config','symbols','build','original-elf'):
        (root/name).mkdir(parents=True,exist_ok=True)
    args = argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
    sources = {A:SOURCE,B:WORKER,C:leaf}
    images,raw,sizes = {},{},{}
    runner = match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root,timeout=120)
    with runner.workspace() as workspace:
        for address,source in sources.items():
            path=root/f'src/{address:08X}.c';path.write_text(source)
            raw[address],_,images[address]=match.compile_object(runner,workspace,args,root,address,
                path.relative_to(root).as_posix())
            (root/f'original-elf/{address:08X}.o').write_bytes(raw[address])
            (root/f'original-elf/{address:08X}.s').write_bytes(runner.read_binary(workspace+'/f.s'))
            (root/f'original-elf/{address:08X}.c').write_text(source)
            sizes[address]=match.function_record(images[address],f'func_{address:08X}',address,True)[0]['size']
            if address!=A:path.unlink()
        rows=[{'rom':f'0x{address:08X}','end':f'0x{address+size:08X}',
               'mode':'thumb','instrs':0} for address,size in sizes.items()]
        mapping=json.dumps(rows).encode();rom=bytearray(C-match.ROM_BASE+sizes[C])
        for address in (C,B,A):
            path=root/f'src/{address:08X}.c';path.write_text(sources[address])
            original,_,_=match.compile_object(runner,workspace,args,root,address,path.relative_to(root).as_posix())
            assert original==raw[address]
            if address==A:
                body,bindings=owner.object_bytes(runner,workspace,args,images[address],address,
                    bytes(rom),mapping,b'{}',selector=profile.SELECTOR)
            elif address==C:
                body=images[address]['text'][:sizes[address]]
            else:
                body,_,_=match.link_calls(runner,workspace,args,images[address],address,mapping,len(rom))
            rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)]=body
            next(row for row in rows if int(row['rom'],16)==address)['instrs']=owner.refine(body,address,mapping)['instrs']
            if address!=A:path.unlink()
    for name,data in (('config/functions.json',json.dumps(rows,indent=2).encode()),
            ('config/data_symbols.json',b'{}'),('baserom.bin',bytes(rom)),
            ('symbols/functions.txt',''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode())):
        (root/name).write_bytes(data)
    return bytes(rom[A-match.ROM_BASE:A-match.ROM_BASE+sizes[A]]),bindings,raw[A]


class SelectionTests(unittest.TestCase):
    def test_isolated_selector_and_mixed_schema_refusal(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        for report in (marker*2,marker+f'* verification: `{owner.watched_switch.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'),'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_output_',dir=scratch)
        cls.root=Path(cls.temporary.name);cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=profile.SELECTOR);cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.temporary.cleanup()

    def proof(self):
        r=self.result
        return profile.DescriptorOutputAliasProof(r[6],r[3],r[4],r[5])

    def replay(self,**changes):
        r=self.result
        values=dict(data=r[0],address=A,rom=r[6],mapping=r[3],index=r[4],objects=r[5],
                    manifest=r[1],selector=profile.SELECTOR);values.update(changes)
        return owner.verify(**values)

    def leaf(self,proof,**changes):
        values=dict(arguments={match.ARM_REG_R0:-8},stack=[(False,False,True)]*2,
            incoming={},protected=frozenset({-8}),words={-8:('pointer',-4)},constants={},
            frame_base=-8,root_frame=A,site=A+8)
        values.update(changes)
        return proof.check_arguments(C,**values)

    def malformed(self,body):
        rom=bytearray(self.result[6]);rom.extend(b'\0'*(D-match.ROM_BASE+len(body)-len(rom)))
        rom[D-match.ROM_BASE:D-match.ROM_BASE+len(body)]=body
        rows=json.loads(self.result[3]);rows.append({'rom':f'0x{D:08X}',
            'end':f'0x{D+len(body):08X}','mode':'thumb','instrs':len(body)//2})
        index=self.result[4]+f'{D:08X} {D+len(body):08X} {len(body)} {len(body)//2} return\n'.encode()
        return profile.DescriptorOutputAliasProof(bytes(rom),json.dumps(rows).encode(),index,b'{}')

    def test_natural_original_elf_and_exact_callee_local_pointer(self):
        self.assertEqual(self.original,self.result[8]);self.assertEqual(match.elf_image(self.original)['type'],1)
        buffers=self.result[1]['proof']['buffers']
        self.assertTrue(any(row['address']==B for row in buffers['frame_aliases']))
        self.assertTrue(any(row['kind']=='pointer' for row in buffers['word_reads']))
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))

    def test_structural_inventory_cannot_admit_unsafe_actual_effects(self):
        bad='''struct Output { unsigned char *bytes; };
void func_08012000(struct Output *output) { output->bytes[100] = 7; }
'''
        root=self.root/'unsafe';fixture(root,leaf=bad)
        proof=profile.DescriptorOutputAliasProof((root/'baserom.bin').read_bytes(),
            (root/'config/functions.json').read_bytes(),(root/'symbols/functions.txt').read_bytes(),b'{}')
        self.assertTrue(proof.inspect(C,proof.span(C)))
        with self.assertRaisesRegex(ValueError,'leaves the tracked frame'):self.leaf(proof)
        self.assertNotIn(C,proof.native_frames)

    def test_completed_effects_cannot_bypass_real_native_return_refusal(self):
        # mov lr,r0; movs r0,#1; bx lr: a closed CFG with an unproved return token.
        proof=self.malformed(bytes.fromhex('864601207047'))
        with patch.object(proof,'complete_frame',wraps=proof.complete_frame) as complete:
            with self.assertRaisesRegex(ValueError,'indirect control flow'):
                proof.check_arguments(D,{},[(False,False,True)],{},frozenset(),
                    words={-4:('constant',1)},frame_base=-4,root_frame=A)
        complete.assert_called_once();self.assertNotIn(D,proof.native_frames)

    def test_two_contexts_and_wrong_origin_cannot_share_effects(self):
        proof=self.proof();self.leaf(proof)
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            self.leaf(proof,words={-8:('pointer',0)})
        self.assertGreaterEqual(len(proof.contexts),2)
        with self.assertRaisesRegex(ValueError,'exact incoming live stack'):
            self.leaf(self.proof(),frame_base=-4)

    def test_partial_clobbered_and_saved_control_words_refuse(self):
        proof=self.proof();decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        ldr=next(decoder.disasm(bytes.fromhex('0068'),C));byte=next(decoder.disasm(bytes.fromhex('0078'),C))
        store=next(decoder.disasm(bytes.fromhex('0860'),C))
        stack=[(False,False,True)]*2;facts={-8:('pointer',-4)}
        with self.assertRaisesRegex(ValueError,'exact aligned full word'):
            proof.word_memory(byte,{match.ARM_REG_R0:-8},{},stack,dict(facts),-8,{-8})
        proof.word_memory(store,{}, {},stack,facts,-8,{-8});self.assertEqual(facts,{})
        with self.assertRaisesRegex(ValueError,'exact surviving word value'):
            proof.word_memory(ldr,{match.ARM_REG_R0:-8},{},stack,facts,-8,{-8})
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            proof.word_memory(ldr,{match.ARM_REG_R0:-8},{},[(False,True,False),stack[1]],
                              {-8:('pointer',-4)},-8,{-8})

    def test_expired_callee_pointer_cannot_escape_return(self):
        # sub sp,#4; mov r0,sp; add sp,#4; bx lr.
        proof=self.malformed(bytes.fromhex('81b0684601b07047'))
        with self.assertRaisesRegex(ValueError,'outside allocated local words'):
            proof.check_arguments(D,{},[(False,False,True)],{},frozenset(),
                words={-4:('constant',1)},frame_base=-4,root_frame=A)
        self.assertNotIn(D,proof.native_frames)

    def test_report_requires_actual_frame_and_word_context_and_source(self):
        for field in ('frame_aliases','word_reads','native_frame_replays'):
            manifest=copy.deepcopy(self.result[1]);manifest['proof']['buffers'][field]=[]
            with self.assertRaisesRegex(ValueError,'fresh native replay'):self.replay(manifest=manifest)
        path=self.root/'src/08010000.c';raw=path.read_bytes()
        try:
            path.write_bytes(raw+b'\n');self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
        finally:path.write_bytes(raw)


if __name__=='__main__':unittest.main(verbosity=2)
