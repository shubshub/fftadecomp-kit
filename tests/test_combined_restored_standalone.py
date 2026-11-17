"""New327 interaction/lifecycle cases against the exact combined overlay only."""
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE/'tools'))
import match
import match_evidence as evidence
import owner_admission_profile as owner
import static_callback_r6_frame_profile as restored
import standalone_local_output_word_profile as resident
import static_callback_target_preservation_profile as r7
import word_result_callback_profile as nested
# Fixture constructors only; no method from either frozen test suite runs.
import test_static_callback_r6_frame as r6fixture
import test_standalone_word_output as localfixture


def envs():
    first=r6fixture.fixture(callback=bytes.fromhex('02220a6000207047'))
    second=localfixture.environment({4:0x2003})
    second.update(address=localfixture.ROOT,selector=resident.SELECTOR)
    return first,second


def prove(env,manifest=None,selector=None):
    return owner.verify(env['data'],env['address'],env['rom'],env['mapping'],env['index'],
        env['objects'],manifest,bindings=env['bindings'],selector=selector or env['selector'],
        source_fingerprint='a'*64)


def elf(env,linked=False,changed=False,wrong_type=False):
    address=env['address'];data=bytearray(env['data']);bindings=env['bindings']
    names=sorted({row[1] for key in ('calls','functions') for row in bindings[key]})
    symbols=[('',0,0,0,0),(f'func_{address:08X}',address|1 if linked else 1,len(data),0x12,1)]
    for name in names:symbols.append((name,int(name[5:],16)|1 if linked else 0,0,
        0x11 if wrong_type and name==names[0] else 0x12,0xfff1 if linked else 0))
    numbers={row[0]:index for index,row in enumerate(symbols)}
    relocations=bytearray()
    for site,name in bindings['calls']:
        if not linked:data[site:site+4]=r6fixture.bl(address+site,address+site)
        relocations+=struct.pack('<II',site,(numbers[name]<<8)|10)
    for site,name in bindings['functions']:
        if not linked:struct.pack_into('<I',data,site,0)
        relocations+=struct.pack('<II',site,(numbers[name]<<8)|2)
    if changed:data[0]^=1
    strings=bytearray(b'\0');encoded=bytearray()
    for name,value,size,info,section in symbols:
        offset=len(strings);strings+=name.encode()+b'\0'
        encoded+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    names_raw=b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    parts=[bytes(data),bytes(encoded),bytes(strings),b'' if linked else bytes(relocations),names_raw]
    raw=bytearray(52);offsets=[]
    for part in parts:
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    sections=[(0,0,0,0,0,0,0,0,0,0),
        (1,1,6,address if linked else 0,offsets[0],len(data),0,0,4,0),
        (7,2,0,0,offsets[1],len(encoded),3,1,4,16),
        (15,3,0,0,offsets[2],len(strings),0,0,1,0),
        (23,9,0,0,offsets[3],len(parts[3]),2,1,4,8),
        (33,3,0,0,offsets[4],len(names_raw),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw);raw+=b''.join(struct.pack('<IIIIIIIIII',*row)for row in sections)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,2 if linked else 1,40,1,address|1 if linked else 0,
        0,shoff,0,52,0,0,40,len(sections),5)
    return bytes(raw)


class Runner:
    def __init__(self,env,root):self.env,self.root=env,root;self.commands=[];self.files={}
    @contextlib.contextmanager
    def workspace(self):yield str(self.root/'build/synthetic-workspace')
    def read_binary(self,path):
        if path.endswith('/f.i'):return b'/* combined synthetic compiler boundary */'
        if path.endswith('/f.elf'):return elf(self.env,linked=True)
        return self.files[path]
    def sh(self,command):self.commands.append(command)
    def write_text(self,path,text):self.files[path]=text


@contextlib.contextmanager
def tree(env):
    (HERE/'scratch').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='combined327_',dir=HERE/'scratch')as directory:
        root=Path(directory)
        for name in ('src','include','config','symbols','docs/match','build'):(root/name).mkdir(parents=True)
        (root/'src'/f'{env["address"]:08X}.c').write_text('/* synthetic source identity; no C compilation */\n')
        (root/'include/fixture.h').write_text('/* synthetic header */\n')
        for name,key in [('config/functions.json','mapping'),('symbols/functions.txt','index'),
                         ('config/data_symbols.json','objects'),('fixture.bin','rom')]:
            (root/name).write_bytes(env[key])
        yield root


@contextlib.contextmanager
def build_mocks(env,root,change=None):
    runner=Runner(env,root)
    def compile_fixture(*unused):
        if change:change()
        raw=elf(env);return raw,[],match.elf_image(raw)
    with patch.object(match,'Runner',return_value=runner), \
         patch.object(match,'compile_object',side_effect=compile_fixture), \
         patch.object(match,'_run_replay_process',return_value=subprocess.CompletedProcess([],0,json.dumps(
             dict(findings=[],total=0,addr=f'0x{env["address"]:08X}',hand_asm_allowed=False,allow_entry=None)),'')), \
         patch.object(evidence,'report_rom_path',return_value=str(root/'fixture.bin')):
        yield runner


class CombinedPolicyTests(unittest.TestCase):
    def test_separate_policies_bind_exact_combined_producers_and_effects(self):
        restored_env,resident_env=envs()
        manifest,_=prove(restored_env)
        effect=manifest['proof']['buffers']['r6_restoration']
        self.assertTrue(effect['observations']);self.assertTrue(effect['r7_observations'])
        for name in ('match.py','owner_admission_profile.py','static_callback_r6_frame_profile.py'):
            self.assertEqual(effect['policy']['source_sha256'][name],hashlib.sha256((HERE/'tools'/name).read_bytes()).hexdigest())
        self.assertFalse(any('standalone_word_return' in row for row in manifest['proof'].values() if isinstance(row,dict)))
        manifest,_=prove(resident_env)
        effect=manifest['proof']['standalone_word_return']
        self.assertTrue(effect['local_effects']['ordered_output_effects'])
        self.assertTrue(effect['projections']);self.assertNotIn('buffers',manifest['proof'])
        engines=effect['local_effects']['engine_sources']
        self.assertEqual(engines['match.py'],hashlib.sha256((HERE/'tools/match.py').read_bytes()).hexdigest())
        self.assertFalse(match._ordinary_call_replay(resident.ResidentWordProof(resident_env['rom'],resident_env['mapping'],resident_env['index'],resident_env['objects'],root=resident_env['address'],bindings=resident_env['bindings'],source_fingerprint='a'*64)))

    def test_cross_selector_manifests_and_mixed_cli_policies_cannot_borrow_credit(self):
        a,b=envs();ma,_=prove(a);mb,_=prove(b)
        for env,wrong,manifest in ((a,resident.SELECTOR,mb),(b,restored.SELECTOR,ma)):
            with self.subTest(selector=wrong),self.assertRaises(ValueError):prove(env,selector=wrong)
            with self.subTest(manifest=wrong),self.assertRaises(ValueError):prove(env,manifest)
        for env in (a,b):
            for field in ('function_address_profile','addressed_signed_runtime_profile','signed_runtime_profile'):
                values=localfixture.args(owner_runtime_profile=env['selector'],**{field:'forged'})
                with self.subTest(selector=env['selector'],field=field),patch.object(owner,'build')as build,self.assertRaises(ValueError):
                    owner.issue(HERE,env['address'],values)
                build.assert_not_called()
        for schema in (restored.SCHEMA,resident.SCHEMA):
            text=f'* verification: `{schema}`\n'
            with self.assertRaises(ValueError):owner.selected(text+f'* verification: `{nested.SCHEMA}`\n')

    def test_both_real_cli_elf_report_and_status_paths_remain_isolated(self):
        import status
        for env in envs():
            address=env['address']
            with self.subTest(selector=env['selector']),tree(env)as root,build_mocks(env,root),contextlib.redirect_stdout(io.StringIO())as stdout:
                argv=['match.py','--root',str(root),'--owner-runtime-profile',env['selector'],hex(address)]
                with patch.object(sys,'argv',argv):self.assertEqual(match.main(),0)
                report=(root/'docs/match'/f'{address:08X}.md').read_text()
                self.assertIn('verdict MATCH',stdout.getvalue());self.assertEqual(owner.selector_for_report(report),env['selector'])
                self.assertTrue(evidence.report_matches(report,root,address))
                commands=[]
                def matcher(command,**unused):
                    commands.append(command)
                    with patch.object(sys,'argv',command[1:]),contextlib.redirect_stdout(io.StringIO())as output:code=match.main()
                    return subprocess.CompletedProcess(command,code,output.getvalue(),'')
                with patch.object(status.subprocess,'run',side_effect=matcher):values=status.collect(str(root),True,quiet=True,jobs=1)
                self.assertEqual(values[1],1);self.assertEqual(values[4],[]);self.assertEqual(len(commands),1)
                command=commands[0];self.assertEqual(command[command.index('--owner-runtime-profile')+1],env['selector'])
                self.assertIn('--no-write',command)
                forged=report.replace('"source_sha256":"','"source_sha256":"forged',1)
                self.assertFalse(evidence.report_matches(forged,root,address))

    def test_combined_build_original_elf_and_input_freshness_fail_closed(self):
        for env in envs():
            address=env['address']
            with self.subTest(selector=env['selector']),self.assertRaises(ValueError):
                owner.original_bindings(match.elf_image(elf(env,wrong_type=True)),address,env['rom'],env['mapping'],env['objects'],selector=env['selector'],index=env['index'])
            with tree(env)as root,build_mocks(env,root)as runner:
                runner.read_binary=lambda path:b'/* synthetic */'if path.endswith('/f.i')else elf(env,linked=True,changed=True)
                with self.assertRaisesRegex(ValueError,'outside exact original relocations'):
                    owner.object_bytes(runner,str(root/'build'),localfixture.args(),match.elf_image(elf(env)),address,env['rom'],env['mapping'],env['objects'],selector=env['selector'],index=env['index'])
            with tree(env)as root:
                def change():
                    path=root/'include/fixture.h';path.write_bytes(path.read_bytes()+b' ')
                with build_mocks(env,root,change),self.assertRaisesRegex(ValueError,'source, maps, headers or ROM changed'):
                    owner.build(root,address,selector=env['selector'])
            manifest,_=prove(env)
            with self.assertRaisesRegex(ValueError,'original ELF identity'):
                owner.fingerprint(address,env['data'],manifest,'a'*64,env['mapping'],env['index'],env['objects'],env['rom'])

    def test_each_feature_retains_local_escape_and_preservation_refusals(self):
        for changes in ({18:0x4668},{17:0x6062}):
            env=localfixture.environment(changes);env.update(address=localfixture.ROOT,selector=resident.SELECTOR)
            with self.subTest(changes=changes),self.assertRaises(ValueError):prove(env)
        for callback in (bytes.fromhex('002601220a6000207047'),bytes.fromhex('016000207047')):
            with self.subTest(callback=callback.hex()),self.assertRaises(ValueError):prove(r6fixture.fixture(callback=callback))
        for env,selector in ((envs()[0],r7.SELECTOR),(envs()[1],nested.SELECTOR)):
            with self.subTest(old_selector=selector),self.assertRaises(ValueError):prove(env,selector=selector)
