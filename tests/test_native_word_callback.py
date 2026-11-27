"""New296 synthetic integration cases. No original game proof or compiler."""
import argparse
import copy
import contextlib
import io
import json
from pathlib import Path
import struct
import subprocess
import tempfile
import sys
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parents[1]
BASE=HERE.parents[1]
sys.dont_write_bytecode=True
sys.path[:0]=[str(HERE/'tools'),str(BASE/'repos/fftadecomp-kit/tools')]
import match
import report_fixtures
import owner_admission_profile as owner
import word_result_callback_profile as selected
import static_callback_target_preservation_profile as r7
import entry_recursive_ordinary_call_profile as entry

ROOT,WALK,CB,HELP=0x08020000,0x08021000,0x08022000,0x08023000


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xf000|((delta>>12)&0x7ff),0xf800|((delta>>1)&0x7ff))


def build_words(address,words,target):
    out=bytearray();calls=[]
    for value in words:
        if value=='call':
            calls.append(address+len(out));out.extend(bl(calls[-1],target))
        else:out.extend(struct.pack('<H',value))
    return bytes(out),calls


def environment(callback_change=None,walker_change=None,root_tail=None):
    cb=[0xb530,0xb082,0x1C05,0x1C0C,0x2007,0x9000,0xaa01,0x1C28,0x4669,'call',
        0x6821,0x9800,0x4281,0xd102,0x6065,0x2000,0xe000,0x2001,0xb002,0xbc30,0xbc02,0x4708]
    for i,value in (callback_change or {}).items():cb[i]=value
    callback,helper_calls=build_words(CB,cb,HELP)
    walk=[0xb5f0,0x1C0F,0x1C16,0x1C04,0x2200,0x1C20,0x1C31,'call',0x2800,0xd001,
          0x2200,0xe7f8,0xbcf0,0xbc02,0x4708]
    for i,value in (walker_change or {}).items():walk[i]=value
    walker,callback_calls=build_words(WALK,walk,r7.THUNK)
    root=[0xb500,0xb082,0x1C03,0x9100,0x2000,0x9001,0x4900,0x1C18,0x466a,'call']
    root+=root_tail if root_tail is not None else [0x9801,0xb002,0xbc02,0x4708]
    data,root_calls=build_words(ROOT,root,WALK)
    if len(data)%4:data+=b'\x00\x00'
    literal=len(data)
    data=bytearray(data+struct.pack('<I',CB|1))
    struct.pack_into('<H',data,12,0x4900|((ROOT+literal-((ROOT+12+4)&~3))//4))
    data=bytes(data)
    helper=bytes.fromhex('43680b60006810607047')
    bodies=[(ROOT,data),(WALK,walker),(CB,callback),(HELP,helper),(r7.THUNK,bytes.fromhex('3847'))]
    rom=bytearray(r7.THUNK-match.ROM_BASE+4)
    rom[-2:]=bytes.fromhex('c046')
    for address,body in bodies:rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)]=body
    mapping=json.dumps([{'rom':f'0x{address:08X}','end':f'0x{address+len(body):08X}',
        'mode':'thumb','instrs':0}for address,body in bodies]).encode()
    # Compute metadata via the existing static inventory, not native proofs.
    import analyze
    rows=json.loads(mapping)
    for row,(address,body) in zip(rows,bodies):
        record=analyze.refine_function(body,address,rows,max_bytes=len(body),
            max_instructions=len(body)//2,rom_end=0x09000000,same_owner_long_branches=True)
        row['instrs']=record['instrs']
    mapping=json.dumps(rows).encode()
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} bx\n'for row in rows).encode()
    return dict(data=data,rom=bytes(rom),mapping=mapping,index=index,objects=b'{}',
        bindings={'calls':[[root_calls[0]-ROOT,f'func_{WALK:08X}']],
                  'data':[],'functions':[[literal,f'func_{CB:08X}']],'switches':[]},
        root_site=root_calls[0],callback_site=callback_calls[0],helper_site=helper_calls[0])


def prove(env,manifest=None,selector=selected.SELECTOR):
    return owner.verify(env['data'],ROOT,env['rom'],env['mapping'],env['index'],env['objects'],
        manifest,bindings=env['bindings'],selector=selector)


class NativeWordCallbackTests(unittest.TestCase):
    def test_full_owner_r7_local_effects_and_word_return_projection(self):
        env=environment();manifest,instructions=prove(env)
        self.assertEqual(manifest['profile'],selected.SCHEMA)
        effect=manifest['proof']['buffers']['word_result_callback']
        self.assertTrue(effect['projections'])
        self.assertTrue(effect['local_effects']['ordered_output_effects'])
        self.assertTrue(effect['r7_preservation']['observations'])
        self.assertEqual(effect['consumer']['abi_conditional'],'ordinary-arm-normal-return-r0-word-v1')
        self.assertEqual({row['address'] for row in effect['local_effects']['native_frames']},{CB,WALK})
        self.assertEqual(set(manifest['proof']['buffers']['dependencies'][i]['address']
            for i in range(len(manifest['proof']['buffers']['dependencies']))),{WALK,CB,HELP,r7.THUNK})


def elf(env,linked=False,callback_type=2,changed=False):
    """Real ELF32 input to existing readers; no compiler or linker execution."""
    data=bytearray(env['data']);call=env['bindings']['calls'][0][0]
    literal=env['bindings']['functions'][0][0]
    if not linked:
        data[call:call+4]=bl(ROOT+call,ROOT+call)
        struct.pack_into('<I',data,literal,0)
    if changed:data[0]^=1
    symbols=[('',0,0,0,0),(f'func_{ROOT:08X}',(ROOT if linked else 0)|1,len(data),0x12,1),
        (f'func_{WALK:08X}',WALK|1 if linked else 0,0,0x12,0xfff1 if linked else 0),
        (f'func_{CB:08X}',CB|1 if linked else 0,0,0x10|callback_type,0xfff1 if linked else 0)]
    strings=bytearray(b'\0');encoded=bytearray()
    for name,value,size,info,section in symbols:
        offset=len(strings);strings+=name.encode()+b'\0'
        encoded+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    rel=b'' if linked else struct.pack('<IIII',call,(2<<8)|10,literal,(3<<8)|2)
    names=b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    parts=[bytes(data),bytes(encoded),bytes(strings),rel,names];raw=bytearray(52);offsets=[]
    for part in parts:
        while len(raw)%4:raw+=b'\0'
        offsets.append(len(raw));raw+=part
    sections=[(0,0,0,0,0,0,0,0,0,0),
        (1,1,6,ROOT if linked else 0,offsets[0],len(data),0,0,4,0),
        (7,2,0,0,offsets[1],len(encoded),3,1,4,16),
        (15,3,0,0,offsets[2],len(strings),0,0,1,0),
        (23,9,0,0,offsets[3],len(rel),2,1,4,8),
        (33,3,0,0,offsets[4],len(names),0,0,1,0)]
    while len(raw)%4:raw+=b'\0'
    shoff=len(raw);raw+=b''.join(struct.pack('<IIIIIIIIII',*row)for row in sections)
    raw[:16]=b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH',raw,16,2 if linked else 1,40,1,ROOT|1 if linked else 0,
        0,shoff,0,52,0,0,40,len(sections),5)
    return bytes(raw)


def args(**changes):
    values=dict(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS,
        mode='thumb',control_flow_profile='ordinary',software_double_profile=None,
        software_double_remainder_profile=None,function_address_profile=None,switch_profile=None,
        label=None,wsl='Ubuntu',wsl_path=match.DEFAULT_WSL_PATH,signed_quotient_profile=None,
        signed_runtime_profile=None,addressed_signed_runtime_profile=None,switch_data_profile=None,
        owner_runtime_profile=selected.SELECTOR,emit=None,no_write=False)
    values.update(changes);return argparse.Namespace(**values)


class FakeRunner:
    def __init__(self,env,root=None,change=None):
        self.env,self.root,self.change=env,root,change;self.files={};self.commands=[]
    @contextlib.contextmanager
    def workspace(self):yield str(self.root/'build/synthetic-workspace') if self.root else '/synthetic'
    def read_binary(self,path):
        if path.endswith('/f.i'):return b'/* synthetic fixture; no compilation */'
        if path.endswith('/f.elf'):return elf(self.env,linked=True)
        return self.files[path]
    def write_text(self,path,text):self.files[path]=text
    def sh(self,command):self.commands.append(command)


@contextlib.contextmanager
def tree(env):
    (HERE/'scratch').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='word_callback_',dir=HERE/'scratch')as directory:
        root=Path(directory)
        for part in ('src','include','config','symbols','docs/match','build'):(root/part).mkdir(parents=True,exist_ok=True)
        (root/'src'/f'{ROOT:08X}.c').write_text('/* synthetic source identity only; compiler mocked */\n')
        (root/'include/fixture.h').write_text('/* synthetic header */\n')
        (root/'config/functions.json').write_bytes(env['mapping'])
        (root/'symbols/functions.txt').write_bytes(env['index'])
        (root/'config/data_symbols.json').write_bytes(env['objects'])
        (root/'fixture.bin').write_bytes(env['rom'])
        yield root


@contextlib.contextmanager
def build_mocks(env,root,change=None):
    import match_evidence as evidence
    runner=FakeRunner(env,root)
    def compile_fixture(*unused):
        if change:change()
        raw=elf(env);return raw,[],match.elf_image(raw)
    with patch.object(match,'Runner',return_value=runner), \
         patch.object(match,'compile_object',side_effect=compile_fixture), \
         patch.object(match,'_run_replay_process',return_value=subprocess.CompletedProcess([],0,json.dumps(dict(findings=[],total=0,addr=f'0x{ROOT:08X}',hand_asm_allowed=False,allow_entry=None)),'')), \
         patch.object(evidence,'report_rom_path',return_value=str(root/'fixture.bin')):
        yield runner


class NativeWordCallbackRejectionTests(unittest.TestCase):
    def test_consumer_read_store_forward_loop_and_partial_coverage(self):
        forwards='outer word-result continuation observes or forwards R2'
        cases=[(dict(walker_change={8:0x2a00}),'consumer lacks inspected R0 word-result use'),
            (dict(root_tail=[0x2a00,0x9801,0xb002,0xbc02,0x4708]),forwards),
            (dict(root_tail=[0x601a,0x9801,0xb002,0xbc02,0x4708]),forwards),
            (dict(root_tail=[0x1C10,0x9801,0xb002,0xbc02,0x4708]),forwards),
            (dict(root_tail=[0xe7fe,0x9801,0xb002,0xbc02,0x4708]),'structural inventory is not closed')]
        for changes,message in cases:
            with self.subTest(changes=changes),self.assertRaisesRegex(ValueError,message):prove(environment(**changes))
        env=environment();rows=json.loads(env['mapping']);rows[1]['end']=f'0x{WALK+4:08X}';env['mapping']=json.dumps(rows).encode()
        with self.assertRaisesRegex(ValueError,'text index disagrees with the complete symbol'):prove(env)

    def test_callback_r7_write_extra_alias_and_invalid_helper(self):
        for changes,message in (
                (dict(callback_change={3:0x1C0F}),'descriptor call does not prove preservation of a live alias register'),
                (dict(walker_change={4:0x46c0}),'callback context mismatch'),
                (dict(callback_change={17:0x4668}),'normal R0 word result carries a callback-local alias')):
            with self.subTest(changes=changes),self.assertRaisesRegex(ValueError,message):prove(environment(**changes))
        env=environment();rom=bytearray(env['rom']);rom[HELP-match.ROM_BASE:HELP-match.ROM_BASE+2]=bytes.fromhex('0b60');env['rom']=bytes(rom)
        with self.assertRaisesRegex(ValueError,'two-output helper differs from ordered scalar-load/word-store effects'):prove(env)

    def test_exact_binding_thunk_and_fresh_manifest_tamper(self):
        env=environment();manifest,_=prove(env)
        for key in ('mapping','index','objects'):
            altered=dict(env);altered[key]+=b' '
            with self.subTest(input=key),self.assertRaises(ValueError):prove(altered,manifest)
        for mutate in ('binding','thunk','effect','producer','boundary'):
            altered=copy.deepcopy(env);expected=copy.deepcopy(manifest)
            if mutate=='binding':altered['bindings']['functions'][0][1]=f'func_{HELP:08X}'
            elif mutate=='thunk':
                rom=bytearray(altered['rom']);rom[-1]^=1;altered['rom']=bytes(rom)
            else:
                effect=expected['proof']['buffers']['word_result_callback']
                if mutate=='effect':effect['local_effects']['ordered_output_effects'][0]['outputs'][0][1]+=4
                elif mutate=='producer':effect['producer_sha256']['word_result_callback_profile']='0'*64
                else:effect['consumer']['abi_conditional']='unattested'
            with self.subTest(mutate=mutate),self.assertRaises(ValueError):prove(altered,expected)

    def test_default_r7_entry_and_mixed_selectors_remain_closed(self):
        env=environment()
        for selector in (owner.SELECTOR,r7.SELECTOR,entry.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):prove(env,selector=selector)
        for field in ('function_address_profile','addressed_signed_runtime_profile','signed_runtime_profile'):
            with self.subTest(field=field),patch.object(owner,'build')as build,self.assertRaises(ValueError):
                owner.issue(HERE,ROOT,args(**{field:'forged'}))
            build.assert_not_called()


class NativeWordCallbackLifecycleTests(unittest.TestCase):
    def test_original_elf_relocations_linked_body_and_type_rejections(self):
        env=environment();image=match.elf_image(elf(env));runner=FakeRunner(env)
        data,bindings=owner.object_bytes(runner,'/synthetic',args(),image,ROOT,env['rom'],env['mapping'],env['objects'],selector=selected.SELECTOR,index=env['index'])
        self.assertEqual(data,env['data']);self.assertEqual(bindings,env['bindings']);self.assertEqual(len(runner.commands),2)
        with self.assertRaisesRegex(ValueError,'function pointer'):
            owner.original_bindings(match.elf_image(elf(env,callback_type=1)),ROOT,env['rom'],env['mapping'],env['objects'],selector=selected.SELECTOR,index=env['index'])
        runner.read_binary=lambda path: b'/* fixture */'if path.endswith('/f.i')else elf(env,linked=True,changed=True)
        with self.assertRaisesRegex(ValueError,'outside exact original relocations'):
            owner.object_bytes(runner,'/synthetic',args(),image,ROOT,env['rom'],env['mapping'],env['objects'],selector=selected.SELECTOR,index=env['index'])

    def test_captured_build_cli_report_evidence_and_fresh_replay(self):
        import match_evidence as evidence
        env=environment()
        with tree(env)as root,build_mocks(env,root)as runner,contextlib.redirect_stdout(io.StringIO())as stdout:
            self.assertEqual(owner.issue(root,ROOT,args()),0)
            report=(root/'docs/match'/f'{ROOT:08X}.md').read_text()
            self.assertIn('verdict MATCH',stdout.getvalue())
            self.assertEqual(owner.selector_for_report(report),selected.SELECTOR)
            self.assertTrue(evidence.report_matches(report_fixtures.carried(report, root, ROOT), root, ROOT))
            self.assertEqual(len(runner.commands),4)
            altered=report.replace('"abi_conditional":"ordinary-arm-normal-return-r0-word-v1"','"abi_conditional":"forged"',1)
            self.assertFalse(evidence.report_matches(altered,root,ROOT))

    def test_build_source_header_maps_and_elf_freshness(self):
        env=environment()
        for kind in ('source','header','mapping','index','data'):
            with self.subTest(kind=kind),tree(env)as root:
                paths={'source':root/'src'/f'{ROOT:08X}.c','header':root/'include/fixture.h',
                    'mapping':root/'config/functions.json','index':root/'symbols/functions.txt','data':root/'config/data_symbols.json'}
                def change():paths[kind].write_bytes(paths[kind].read_bytes()+b' ')
                with build_mocks(env,root,change),self.assertRaisesRegex(ValueError,'source, maps, headers or ROM changed'):
                    owner.build(root,ROOT,selector=selected.SELECTOR)
        manifest,_=prove(env)
        with self.assertRaisesRegex(ValueError,'original ELF identity'):
            owner.fingerprint(ROOT,env['data'],manifest,'source',env['mapping'],env['index'],env['objects'],env['rom'])
        raw=elf(env);fp=owner.fingerprint(ROOT,env['data'],manifest,'source',env['mapping'],env['index'],env['objects'],env['rom'],raw)
        self.assertNotEqual(fp,owner.fingerprint(ROOT,env['data'],manifest,'source',env['mapping'],env['index'],env['objects'],env['rom'],raw+b'x'))


class NativeWordCallbackRoutingTests(unittest.TestCase):
    def test_actual_cli_parser_status_selector_and_report_failure_propagation(self):
        import status
        import match_evidence as evidence
        env=environment()
        with tree(env)as root,build_mocks(env,root),contextlib.redirect_stdout(io.StringIO()):
            argv=['match.py','--root',str(root),'--owner-runtime-profile',selected.SELECTOR,hex(ROOT)]
            with patch.object(sys,'argv',argv):self.assertEqual(match.main(),0)
            report=(root/'docs/match'/f'{ROOT:08X}.md').read_text()
            commands=[]
            def matcher(command,**unused):
                commands.append(command)
                with patch.object(sys,'argv',command[1:]),contextlib.redirect_stdout(io.StringIO())as output:
                    code=match.main()
                return subprocess.CompletedProcess(command,code,output.getvalue(),'')
            with patch.object(status.subprocess,'run',side_effect=matcher):
                values=status.collect(str(root),True,quiet=True,jobs=1)
            self.assertEqual(values[1],1);self.assertEqual(values[4],[]);self.assertEqual(len(commands),1)
            command=commands[0];self.assertEqual(command[command.index('--owner-runtime-profile')+1],selected.SELECTOR)
            self.assertIn('--no-write',command)
            altered=report.replace('"body_sha256":"','"body_sha256":"tampered',1)
            (root/'docs/match'/f'{ROOT:08X}.md').write_text(altered)
            commands.clear()
            with patch.object(status.subprocess,'run',side_effect=matcher):
                values=status.collect(str(root),True,quiet=True,jobs=1)
            self.assertEqual(values[1],0);self.assertTrue(values[4]);self.assertEqual(commands,[])
            self.assertFalse(evidence.report_matches(altered,root,ROOT))

    def test_canonical_producer_and_one_use_r7_receipt_identity(self):
        env=environment();proof=selected.WordResultCallbackProof(env['rom'],env['mapping'],env['index'],env['objects'],root=ROOT,bindings=env['bindings'])
        self.assertIs(type(proof).finish_call_constants,r7.StaticCallbackTargetPreservationProof.finish_call_constants)
        genuine=r7._CallbackResult({});receipt=dict(site=proof.consumer_site,thunk=r7.THUNK,
            register=r7.REGISTER,value=CB|1,target=CB,watched=[r7.REGISTER],
            precondition='no reached instruction writes watched R7 in callback or inspected dependencies',
            returning='conditional normal return only')
        proof._completed[id(genuine)]=(genuine,receipt)
        constants={r7.REGISTER:CB|1}
        copied=r7._CallbackResult(genuine)
        proof.finish_call_constants(constants,copied,site=proof.consumer_site,target=r7.THUNK)
        self.assertNotIn(r7.REGISTER,constants)
        constants={r7.REGISTER:CB|1}
        proof.finish_call_constants(constants,genuine,site=proof.consumer_site,target=r7.THUNK)
        self.assertEqual(constants[r7.REGISTER],CB|1)
        proof.finish_call_constants(constants,genuine,site=proof.consumer_site,target=r7.THUNK)
        self.assertNotIn(r7.REGISTER,constants)
