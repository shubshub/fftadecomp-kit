"""Real agbcc, native CLI and source/report replay for the explicit composition."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import bios_word_switch_buffer_profile as profile
import bios_cpuset_fill_profile as bios

A,B,C=0x08010000,0x08020000,0x08020100
SOURCE='''extern unsigned char state[];
extern unsigned short destination[];
extern void func_08020000(unsigned char *, unsigned char *);
extern int func_08020100(void);
extern void func_0814186C(const void *, void *, unsigned int);
int func_08010000(void)
{
    unsigned char a, b;
    unsigned short value;
    switch (state[0]) {
    case 0:
        func_08020000(&a, &b);
        if (func_08020100())
            state[1] = a;
        else
            state[1] = b;
        break;
    case 1:
        value = 0;
        func_0814186C(&value, destination, 0x01000008);
        break;
    case 2: state[1] = 3; break;
    case 3: state[1] = 5; break;
    case 4: state[1] = 7; break;
    case 5: state[1] = 9; break;
    case 6: state[1] = 11; break;
    default: return -1;
    }
    return 0;
}
'''


class BiosWordSwitchNativeTests(unittest.TestCase):
    def test_real_compiler_cli_report_and_stale_source(self):
        retained=os.environ.get('FFTA_BIOS_SWITCH_FIXTURE')
        if retained:
            root=Path(retained);root.mkdir(parents=True,exist_ok=False)
        else:
            scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'))
            scratch.mkdir(parents=True,exist_ok=True)
            temporary=tempfile.TemporaryDirectory(prefix='bios_word_switch_',dir=scratch)
            self.addCleanup(temporary.cleanup);root=Path(temporary.name)
        for name in ('src','include','build','config','symbols','docs/match','compiler'):
            (root/name).mkdir(parents=True,exist_ok=True)
        source=root/'src/08010000.c';source.write_text(SOURCE)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        objects=b'{"state":"0x02000020","destination":"0x06000000"}'
        helper=bytes.fromhex('024b1a78027058780870704720000002')
        query=bytes.fromhex('02480078c00901214840704720000002')
        rom=bytearray(bios.ADDRESS-match.ROM_BASE+4)
        for address,data in ((B,helper),(C,query),(bios.ADDRESS,bios.WRAPPER)):
            rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)]=data
        runner=match.Runner(match.DEFAULT_CC,'Ubuntu',match.DEFAULT_WSL_PATH,root=root,timeout=120)
        with runner.workspace() as workspace:
            try:
                original,body,image=match.compile_object(runner,workspace,args,root,A,'src/08010000.c')
                complete_size=match.function_record(image,f'func_{A:08X}',A,True)[0]['size']
                rows=[dict(rom=hex(a),end=hex(a+n),mode='thumb',instrs=0)
                      for a,n in ((A,complete_size),(B,len(helper)),(C,len(query)),(bios.ADDRESS,4))]
                mapping=json.dumps(rows).encode()
                data,bindings=owner.object_bytes(runner,workspace,args,image,A,bytes(rom),mapping,objects,selector=profile.SELECTOR)
            finally:
                for path in Path(workspace).iterdir():
                    if path.is_file():shutil.copy2(path,root/'compiler'/path.name)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        refinement=profile.refine(data,A,mapping)
        (root/'compiler/refinement.json').write_text(json.dumps(refinement,indent=2)+'\n')
        self.assertTrue(refinement['cfg_closed'],refinement['partial_reasons'])
        self.assertEqual(len(refinement['word_switches']),1)
        rows[0]['instrs']=refinement['instrs'];rows[1]['instrs']=6;rows[2]['instrs']=6;rows[3]['instrs']=2
        (root/'config/functions.json').write_text(json.dumps(rows))
        (root/'config/data_symbols.json').write_bytes(objects)
        (root/'symbols/functions.txt').write_text(''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows))
        (root/'baserom.bin').write_bytes(rom)
        with patch.dict(os.environ,FFTA_ROM=str(root/'baserom.bin')):
            result=owner.build(root,A,selector=profile.SELECTOR)
            self.assertEqual(result[8],original)
            report=owner.render(A,result);(root/'compiler/report.md').write_text(report)
            self.assertTrue(match_evidence.report_matches(report,root,A))
            run=subprocess.run([sys.executable,str(Path(match.__file__)),'--root',str(root),f'0x{A:08X}',
                '--owner-runtime-profile',profile.SELECTOR],text=True,capture_output=True)
            (root/'compiler/cli.log').write_text(run.stdout+run.stderr)
            self.assertEqual(run.returncode,0,run.stdout+run.stderr);self.assertIn('MATCH',run.stdout)
            forged=report.replace('native-returned-local-aliases-v1','native-returned-local-aliases-v0')
            self.assertNotEqual(forged,report);self.assertFalse(match_evidence.report_matches(forged,root,A))
            source.write_text(SOURCE+'\n')
            self.assertFalse(match_evidence.report_matches(report,root,A))
            source.write_text(SOURCE)
            self.assertFalse(match_evidence.report_matches(report.replace(profile.SCHEMA,owner.ACYCLIC_SCHEMA),root,A))
        (root/'compiler/results.json').write_text(json.dumps(dict(compilation=True,native_build=True,
            native_CLI=True,report_replay=True,forged_report_rejected=True,stale_source_rejected=True,
            legacy_relabel_rejected=True,original_target_run=False),indent=2)+'\n')

if __name__=='__main__':unittest.main(verbosity=2)
