"""Explicit overwritten control policy uses real compiler and report replay."""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"tools"))
import match
import match_evidence
import plausible
import owner_admission_profile as owner
import named_data_buffer_profile as named
import bios_cpuset_fill_profile as bios

A=0x08001000
SELECTOR=named.BIOS_OVERWRITE_SELECTOR


class ForwardedNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        build = Path(__file__).resolve().parents[1]/'build'
        build.mkdir(exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='forwarded-native-', dir=build)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = root = Path(cls.temporary.name)
        for folder in ('src','include','config','symbols','build'):
            (root/folder).mkdir()
        # All Python/native replay scratch stays in this disk-backed fixture.
        cls.scratch = patch.dict(os.environ, TMPDIR=str(root/'build'))
        cls.scratch.start()
        cls.addClassCleanup(cls.scratch.stop)
        cls.tempdir = patch.object(tempfile, 'tempdir', str(root/'build'))
        cls.tempdir.start()
        cls.addClassCleanup(cls.tempdir.stop)
        retention = os.environ.get('FFTA_NATIVE_TEST_ARTIFACTS')
        if retention:
            parent = Path(retention).resolve()/'forwarded-native'
            parent.mkdir(parents=True, exist_ok=True)
            cls.evidence = Path(tempfile.mkdtemp(prefix='run-',dir=parent))
        else:
            cls.evidence = root/'artifacts'
            cls.evidence.mkdir()
        entry=next(e for e in plausible.volatile_allow_entries() if e['symbol']=='g_control_flags_03000940')
        (root/'include/control_flags.h').write_text('#ifndef CONTROL_FLAGS_H\n#define CONTROL_FLAGS_H\n'+entry['declaration']+'\n#endif\n')
        source='''typedef unsigned char u8;
typedef unsigned short u16;
#include "control_flags.h"
extern u16 destination[];
typedef struct { u16 first; u16 second; } Descriptor;
extern Descriptor *descriptor;
extern void func_0814186C(void *, void *, unsigned int);
void func_08001000(void) {
    u16 first;
    u16 second;
    Descriptor *captured;
    first = 0;
    func_0814186C(&first, destination, 0x01000100);
    second = 0;
    func_0814186C(&second, destination + 0x100, 0x01000100);
    captured = descriptor;
    g_control_flags_03000940.win1h_lo = 0;
    g_control_flags_03000940.win1h_hi = g_control_flags_03000940.win1h_lo;
    g_control_flags_03000940.win1h_lo = 19;
    destination[0] = captured->first;
    destination[1] = captured->second;
}
'''
        (root/'src/08001000.c').write_text(source)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root)
        with runner.workspace() as workspace:
            raw,body,image=match.compile_object(runner,workspace,args,root,A,'src/08001000.c')
            cls.rows=[dict(rom=f'0x{address:08X}',end=f'0x{address+size:08X}',mode='thumb',instrs=count)
                for address,size,count in ((A,len(body),0),(bios.ADDRESS,4,2))]
            mapping=json.dumps(cls.rows).encode()
            cls.objects=json.dumps({'g_control_flags_03000940':'0x03000940','destination':'0x03003860','descriptor':'0x02001000'}).encode()
            rom=bytearray(bios.ADDRESS-match.ROM_BASE+4);rom[-4:]=b'\x0b\xdf\x70\x47'
            data,bindings=owner.object_bytes(runner,workspace,args,image,A,bytes(rom),mapping,cls.objects,selector=SELECTOR)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        cls.rows[0]['instrs']=owner.refine(data,A,mapping)['instrs']
        cls.mapping=json.dumps(cls.rows).encode()
        cls.index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n' for row in cls.rows).encode()
        for relative,value in (('config/functions.json',cls.mapping),('config/data_symbols.json',cls.objects),
                               ('symbols/functions.txt',cls.index),('baserom.bin',bytes(rom))):
            (root/relative).write_bytes(value)
        cls.env=patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin'));cls.env.start()
        cls.addClassCleanup(cls.env.stop)
        cls.result=owner.build(root,A,selector=SELECTOR)
        cls.report=owner.render(A,cls.result)
        evidence=cls.evidence
        evidence.mkdir(exist_ok=True)
        (evidence/'native-synthetic-report.md').write_text(cls.report)
        (evidence/'native-synthetic-manifest.json').write_text(json.dumps(cls.result[1],sort_keys=True,indent=2)+'\n')
        (evidence/'native-synthetic-original.o').write_bytes(cls.result[8])
        (evidence/'native-synthetic-linked.bin').write_bytes(cls.result[0])
        (evidence/'native-synthetic-source.c').write_text(source)

    def test_native_fresh_report_and_actual_cli(self):
        self.assertEqual(self.result[1]['profile'],named.BIOS_OVERWRITE_SCHEMA)
        import overwritten_control_store_composition as composition
        self.assertEqual(self.result[1]['proof']['conditional_overwritten_control_store_policy'],
                         composition.PREMISE)
        replay=owner.build(self.root,A,expected=json.loads(json.dumps(self.result[1])),selector=SELECTOR)
        self.assertEqual(owner.render(A,replay),self.report)
        self.assertTrue(owner.report_matches(self.report,self.root,A))
        records=match.allowlisted_volatile_semantics(self.root,A,owner_runtime_profile=SELECTOR)
        report=match_evidence.carry_volatile_records(self.report,plausible.allowlisted_volatile_uses(self.root,A)+records)
        self.assertTrue(match_evidence.report_matches(report,self.root,A))
        command=[sys.executable,str(Path(match.__file__)), '--root',str(self.root),f'{A:08X}',
                 '--owner-runtime-profile',SELECTOR,'--no-write']
        output=match._run_replay_process(command,self.root,120)
        self.assertEqual(output.returncode,0,output.stdout+output.stderr)
        self.assertIn('verdict MATCH - byte identical',output.stdout)
        evidence=self.evidence
        (evidence/'native-synthetic-cli.log').write_text(output.stdout+output.stderr)

    def test_artifact_isolation(self):
        build = Path(__file__).resolve().parents[1]/'build'
        self.assertTrue(self.root.is_relative_to(build))
        self.assertEqual(Path(tempfile.gettempdir()),self.root/'build')
        self.assertEqual(Path(os.environ['TMPDIR']),self.root/'build')
        retention = os.environ.get('FFTA_NATIVE_TEST_ARTIFACTS')
        if retention:
            self.assertEqual(self.evidence.parent,Path(retention).resolve()/'forwarded-native')
        else:
            self.assertEqual(self.evidence,self.root/'artifacts')
        self.assertTrue((self.evidence/'native-synthetic-report.md').is_file())
        self.assertNotEqual(self.evidence,Path(__file__).resolve().parents[2]/
            'overwritten-control-store-versions-evidence')

    def test_missing_mutated_native_semantics_and_runtime_refuse(self):
        import copy
        for mutation in ('missing','premise','evidence','runtime'):
            result=list(self.result); result[1]=copy.deepcopy(result[1])
            if mutation == 'missing': del result[1]['ordinary_overwrite_native']
            elif mutation == 'premise':
                result[1]['proof']['conditional_overwritten_control_store_policy']='ordinary'
            elif mutation == 'evidence':
                result[1]['ordinary_overwrite_native']['semantic_records']=['forged']
            else:
                result[1]['ordinary_overwrite_native']['environment']['toolchain']='changed'
            with self.subTest(mutation=mutation):
                self.assertFalse(owner.report_matches(owner.render(A,tuple(result)),self.root,A))
        with patch.object(owner.known_query,'environment_fingerprint',return_value={'changed':True}):
            self.assertFalse(owner.report_matches(self.report,self.root,A))

    def test_inventory_has_no_native_semantic_credit(self):
        manifest,_,_=owner.preflight(self.result[0],A,self.result[6],self.mapping,
            self.index,self.objects,selector=SELECTOR)
        self.assertNotIn('ordinary_overwrite_native',manifest)
        result=list(self.result);result[1]=manifest
        self.assertFalse(owner.report_matches(owner.render(A,tuple(result)),self.root,A))

    def test_old_policies_and_stale_evidence_refuse(self):
        for selector in (None,named.BIOS_FILL_SELECTOR,named.BIOS_LOCAL_FILL_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                match.allowlisted_volatile_semantics(self.root,A,owner_runtime_profile=selector)
        for path in ('src/08001000.c','include/control_flags.h','config/functions.json','config/data_symbols.json'):
            target=self.root/path;old=target.read_bytes()
            try:
                target.write_bytes(old+b'\n')
                self.assertFalse(owner.report_matches(self.report,self.root,A))
            finally:target.write_bytes(old)


if __name__=='__main__':unittest.main()
