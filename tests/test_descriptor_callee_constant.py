"""Native register-origin composition for repeated exact callback constants."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import descriptor_callee_constant_profile as profile
import local_long_branch_profile as frame
import test_static_callback_buffer as fixtures
from test_static_callback_buffer import A,B,C,D

SOURCE='''struct Output;
extern unsigned int func_08011000(unsigned char *, void (*)(struct Output *));
extern void func_08012000(struct Output *);
unsigned int func_08010000(unsigned int value)
{
    unsigned char marker[4];
    marker[0] = value;
    return func_08011000(marker, func_08012000) + marker[0] + 1;
}
'''
WORKER='''struct Output { unsigned int *words; };
unsigned int func_08011000(unsigned char *marker, void (*callback)(struct Output *))
{
    unsigned int words[5];
    struct Output output;
    words[0] = 1;
    words[1] = 3;
    words[2] = 5;
    words[3] = 7;
    words[4] = 9;
    output.words = words;
    if (marker[0])
        output.words = words + 1;
    callback(&output);
    callback(&output);
    return (words[0] + marker[0]) * (words[1] + marker[0]) + words[2];
}
'''
LEAF='''struct Output { unsigned int *words; };
void func_08012000(struct Output *output)
{
    unsigned int *cursor = output->words;
    if (cursor[0])
        cursor++;
    *cursor++ = 7;
    output->words = cursor;
}
'''


def fixture(root):
    root=Path(root)
    original=match.compile_object
    def capture(runner,workspace,args,source_root,address,source):
        result=original(runner,workspace,args,source_root,address,source)
        (root/f'original-elf/{address:08X}.s').write_bytes(runner.read_binary(workspace+'/f.s'))
        return result
    with patch.object(match,'compile_object',capture):
        return fixtures.fixture(root,source=SOURCE,worker=WORKER,leaf=LEAF)


def frame_body(raw, calls=None, summaries=None):
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    ins={item.address:item for item in decoder.disasm(bytes.fromhex(raw),D)}
    edges={}
    for site,item in ins.items():
        if item.mnemonic=='bx':edges[site]=()
        elif item.id==match.ARM_INS_B:
            edges[site]=(item.operands[0].imm,)
            if item.cc not in (match.ARM_CC_AL,match.ARM_CC_INVALID):edges[site]+=(site+item.size,)
        else:edges[site]=(site+item.size,)
    return frame.prove_frame(ins,edges,D,{},calls or {},call_preservation=summaries if summaries is not None else {})


class FrameTests(unittest.TestCase):
    def test_one_return_clobber_and_unknown_saved_origin_refuse(self):
        for raw in ('002b00d000267047','40b5009001bc024608bc1047'):
            with self.subTest(raw=raw),self.assertRaises(ValueError):frame_body(raw)
        self.assertEqual(frame_body('40b5002640bc01bc0047')['preserved'],'r4-r11,sp,entry-lr')

    def test_strict_call_coverage_and_unknown_registers_refuse(self):
        # push lr; bl external; pop r0; bx r0.
        raw='00b500f000f801bc0047';site=D+2
        # Encode the external destination rather than the in-owner placeholder.
        raw=raw[:4]+'fef7fdff'+raw[12:]
        with self.assertRaisesRegex(ValueError,'complete explicit'):
            frame_body(raw,{site:C},{})
        with self.assertRaisesRegex(ValueError,'restore'):
            frame_body(raw,{site:C},{site:frozenset()})
        self.assertEqual(frame_body(raw,{site:C},{site:profile.PRESERVED})['external_calls'],
                         'complete-native-callee-preservation-v1')

    def test_isolated_schema(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        with self.assertRaises(ValueError):owner.selected(marker+f'* verification: `{owner.disjunctive.SCHEMA}`\n')


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'),'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_constants_',dir=scratch)
        cls.root=Path(cls.temporary.name);cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=profile.SELECTOR);cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):cls.environment.stop();cls.temporary.cleanup()

    def proof(self):
        r=self.result
        return profile.DescriptorCalleeConstantProof(r[6],r[3],r[4],r[5])

    def test_natural_repeated_callback_native_report_and_status(self):
        self.assertEqual(self.original,self.result[8]);self.assertEqual(match.elf_image(self.original)['type'],1)
        proof=self.result[1]['proof']['buffers'];self.assertTrue(proof['callee_constants']['transfers'])
        self.assertGreaterEqual(len({row['site'] for row in proof['callbacks']}),2)
        self.assertTrue(all(register in profile.PRESERVED for row in proof['callee_constants']['transfers']
                            for register,value in row['kept']))
        native=subprocess.run([sys.executable,str(Path(match.__file__)),'--root',str(self.root),
            f'{A:08X}','--owner-runtime-profile',profile.SELECTOR],capture_output=True,text=True)
        self.assertEqual(native.returncode,0,native.stdout+native.stderr)
        saved=(self.root/f'docs/match/{A:08X}.md').read_text()
        self.assertEqual(saved,self.report);self.assertTrue(match_evidence.report_matches(saved,self.root,A))
        import status
        totals=status.collect(str(self.root),True,quiet=True)
        self.assertEqual((totals[1],totals[3],totals[4]),(1,len(self.data),[]))

    def test_previous_selector_retains_target_fact_loss(self):
        r=self.result
        with self.assertRaisesRegex(ValueError,'not an exact Thumb function pointer'):
            owner.verify(r[0],A,r[6],r[3],r[4],r[5],bindings=self.bindings,selector=owner.disjunctive.SELECTOR)

    def test_forged_result_and_unproved_call_cannot_retain_constants(self):
        from protected_descriptor_word_profile import WordResult
        proof=self.proof();result=WordResult({}, {})
        result.preserved_registers=profile.PRESERVED
        constants={match.ARM_REG_R0+6:C+1}
        proof.finish_call_constants(constants,result,site=A,target=C)
        self.assertEqual(constants,{})
        # The existing no-buffer shortcut proves no actual callee preservation.
        unproved=proof.check_arguments(C,{},[],{},frozenset(),constants={match.ARM_REG_R0+6:C+1})
        constants={match.ARM_REG_R0+6:C+1}
        proof.finish_call_constants(constants,unproved,site=None,target=C)
        self.assertEqual(constants,{})

    def test_unknown_or_tampered_callback_dependency_refuses(self):
        proof=self.proof();thunk=self.result[1]['proof']['buffers']['callbacks'][0]['thunk']
        with self.assertRaisesRegex(ValueError,'not an exact Thumb'):
            proof.check_arguments(thunk,{match.ARM_REG_R0:-4},[(False,False,True)],{},frozenset(),
                constants={},words={},frame_base=-4,root_frame=A)
        r=self.result;rom=bytearray(r[6]);rom[thunk-match.ROM_BASE]^=8
        with self.assertRaisesRegex(ValueError,'thunk identity'):
            owner.verify(r[0],A,bytes(rom),r[3],r[4],r[5],bindings=self.bindings,selector=profile.SELECTOR)

    def test_forged_preservation_and_effects_evidence_refuses(self):
        r=self.result
        for field in ('callee_constants','alias_alternatives','single_word_stores'):
            manifest=copy.deepcopy(r[1]);manifest['proof']['buffers'][field]={} if field=='callee_constants' else []
            with self.assertRaisesRegex(ValueError,'fresh native replay'):
                owner.verify(r[0],A,r[6],r[3],r[4],r[5],manifest=manifest,selector=profile.SELECTOR)


if __name__=='__main__':unittest.main(verbosity=2)
