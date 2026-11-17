"""New standalone resident-frame synthetic cases; no game workflow."""
import argparse
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

HERE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / 'tools'))
import analyze
import match
import owner_admission_profile as owner
import word_result_callback_profile as nested
import standalone_local_output_word_profile as resident

ROOT, HELPER = 0x08020000, 0x08021000
SELECTOR = 'standalone-local-output-word-return-v1'


def branch_link(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xf000 | ((delta >> 12) & 0x7ff),
                       0xf800 | ((delta >> 1) & 0x7ff))


def environment(changes=None, helper_change=None):
    words = [0xb530, 0xb082, 0x1C05, 0x1C0C, 0x2001, 0x4240, 0x9000,
             0xaa01, 0x1C28, 0x4669, 'call', 0x6821, 0x9800, 0x4281,
             0xd001, 0x2001, 0xe001, 0x6065, 0x2000, 0xb002,
             0xbc30, 0xbc02, 0x4708]
    for index, value in (changes or {}).items():
        words[index] = value
    data = bytearray()
    for value in words:
        data.extend(branch_link(ROOT + len(data), HELPER) if value == 'call'
                    else struct.pack('<H', value))
    helper = bytearray.fromhex('43680b60006810607047')
    if helper_change:
        helper[helper_change[0]:helper_change[0] + len(helper_change[1])] = helper_change[1]
    bodies = [(ROOT, bytes(data)), (HELPER, bytes(helper))]
    rom = bytearray(HELPER - match.ROM_BASE + len(helper))
    rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address + len(body):08X}',
             'mode': 'thumb', 'instrs': 0} for address, body in bodies]
    for row, (address, body) in zip(rows, bodies):
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(body)] = body
        row['instrs'] = analyze.refine_function(body, address, rows, max_bytes=len(body),
            max_instructions=len(body) // 2, rom_end=0x09000000,
            same_owner_long_branches=True)['instrs']
    return dict(data=bytes(data), rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
                      f'{int(row["end"], 16) - int(row["rom"], 16)} {row["instrs"]} bx\n'
                      for row in rows).encode(), objects=b'{}',
        bindings={'calls': [[20, f'func_{HELPER:08X}']], 'data': [],
                  'functions': [], 'switches': []})


class BaselineTests(unittest.TestCase):
    def test_existing_default_and_nested_selector_do_not_admit_resident_root(self):
        env = environment()
        for selector in (owner.SELECTOR, nested.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(env['data'], ROOT, env['rom'], env['mapping'], env['index'],
                    env['objects'], bindings=env['bindings'], selector=selector)


def prove(env, manifest=None, *, source='a'*64, selector=SELECTOR):
    return owner.verify(env['data'],ROOT,env['rom'],env['mapping'],env['index'],env['objects'],
        manifest,bindings=env['bindings'],selector=selector,source_fingerprint=source)


class ResidentPositiveTests(unittest.TestCase):
    def test_empty_entry_frame_ordered_outputs_and_r0_word_boundary(self):
        env=environment();manifest,instructions=prove(env)
        effect=manifest['proof']['standalone_word_return']
        self.assertEqual(manifest['profile'],resident.SCHEMA)
        self.assertEqual(len(instructions),23)
        self.assertEqual(effect['entry'],{'stack':[],'local_aliases':[],'incoming_stack_arguments':[]})
        self.assertEqual(effect['source_sha256'],'a'*64)
        self.assertEqual(effect['abi'],'ordinary-arm-normal-return-r0-word-v1')
        self.assertTrue(effect['projections'])
        self.assertTrue(all(row['register']=='R2' and row['expired_local_offset']==-16 and
                            not row['R0_projected'] for row in effect['projections']))
        local=effect['local_effects']
        self.assertTrue(local['ordered_output_effects'])
        self.assertTrue(local['local_scalar_reads'])
        self.assertEqual({row['address'] for row in local['native_frames']},{ROOT})
        self.assertEqual({row['address'] for row in local['dependencies']},{ROOT,HELPER})
        self.assertEqual(prove(env,manifest)[0],manifest)


class ResidentRejectionTests(unittest.TestCase):
    def test_local_pointer_result_store_forward_and_dead_stack_read(self):
        cases={
            'R0-result':({18:0x4668},'resident R0 word result carries a local stack address'),
            'R0-copied-R2':({18:0x1C10},'resident R0 word result carries a local stack address'),
            'external-store':({17:0x6062},'callback-local output pointer cannot be stored or escape'),
            'forward-local-source':({8:0x4668},'two-output helper requires separate callback-local R1/R2 words'),
            'read-after-free':({20:0x9801},'non-leaf indirect control flow requires linked CFG verification'),
            'tail-local':({22:0x4710},'structural inventory is not closed'),
        }
        for kind,(changes,message) in cases.items():
            with self.subTest(kind=kind),self.assertRaisesRegex(ValueError,message):prove(environment(changes))

    def test_all_paths_frame_initialization_helper_identity_and_order(self):
        cases={
            'overlapping-outputs':({7:0xaa00},None),
            'uninitialized-before-call':({6:0x9801},None),
            'larger-frame':({1:0xb083},None),
            'bypass-helper':({4:0xe008},None),
            'loop':({16:0xe7fe},None),
            'helper-wrong-load':({},(0,bytes.fromhex('0368'))),
            'helper-swapped-destination':({},(2,bytes.fromhex('1360'))),
            'helper-wrong-return':({},(8,bytes.fromhex('6047'))),
        }
        for kind,(changes,helper) in cases.items():
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                prove(environment(changes,helper))

    def test_source_owner_inputs_bindings_and_manifest_are_fresh(self):
        env=environment();manifest,_=prove(env)
        for source in (None,True,'A'*64,'a'*63,'g'*64):
            with self.subTest(source=source),self.assertRaises(ValueError):prove(env,source=source)
        for kind in ('source','mapping','index','objects','rom','binding','effect','projection','producer'):
            changed=copy.deepcopy(env);expected=copy.deepcopy(manifest);source='a'*64
            if kind=='source':source='b'*64
            elif kind in ('mapping','index','objects'):changed[kind]+=b' '
            elif kind=='rom':changed['rom']+=b'\0'
            elif kind=='binding':changed['bindings']['calls'][0][1]=f'func_{ROOT:08X}'
            else:
                effect=expected['proof']['standalone_word_return']
                if kind=='effect':effect['local_effects']['ordered_output_effects'][0]['outputs'][0][1]+=4
                elif kind=='projection':effect['projections'][0]['R0_projected']=True
                else:effect['producer_sha256']['standalone_local_output_word_profile.py']='0'*64
            with self.subTest(kind=kind),self.assertRaises(ValueError):prove(changed,expected,source=source)
        rows=json.loads(env['mapping']);rows.append(dict(rows[0]));changed=dict(env,mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):prove(changed)
        rows=json.loads(env['mapping']);rows[0]['end']=f'0x{ROOT+44:08X}'
        with self.assertRaises(ValueError):prove(dict(env,mapping=json.dumps(rows).encode()))

    def test_no_preflight_mixed_profile_or_unattested_projection(self):
        env=environment()
        with self.assertRaisesRegex(ValueError,'original ELF'):
            owner.preflight(env['data'],ROOT,env['rom'],env['mapping'],env['index'],env['objects'],selector=SELECTOR)
        for selector in (owner.ACYCLIC_SELECTOR,'static-callback-target-preservation-r7-v1'):
            with self.subTest(selector=selector),self.assertRaises(ValueError):prove(env,selector=selector)
        for field in ('function_address_profile','addressed_signed_runtime_profile','signed_runtime_profile','switch_data_profile'):
            with self.subTest(field=field),patch.object(owner,'build')as build,self.assertRaises(ValueError):
                owner.issue(HERE,ROOT,args(**{field:'forged'}))
            build.assert_not_called()
        proof=resident.ResidentWordProof(env['rom'],env['mapping'],env['index'],env['objects'],
            root=ROOT,bindings=env['bindings'],source_fingerprint='a'*64)
        with self.assertRaisesRegex(ValueError,'active normal-return'):
            proof.normal_return_aliases(ROOT,ROOT+46,{match.ARM_REG_R2:-16})


def elf(env,linked=False,helper_type=2,changed=False):
    """Real ELF32 relocation/member evidence; execution boundary is mocked."""
    data=bytearray(env['data']);call=env['bindings']['calls'][0][0]
    if not linked:data[call:call+4]=branch_link(ROOT+call,ROOT+call)
    if changed:data[0]^=1
    symbols=[('',0,0,0,0),(f'func_{ROOT:08X}',(ROOT if linked else 0)|1,len(data),0x12,1),
        (f'func_{HELPER:08X}',HELPER|1 if linked else 0,0,0x10|helper_type,0xfff1 if linked else 0)]
    strings=bytearray(b'\0');encoded=bytearray()
    for name,value,size,info,section in symbols:
        offset=len(strings);strings+=name.encode()+b'\0'
        encoded+=struct.pack('<IIIBBH',offset,value,size,info,0,section)
    rel=b'' if linked else struct.pack('<II',call,(2<<8)|10)
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
        owner_runtime_profile=SELECTOR,emit=None,no_write=False)
    values.update(changes);return argparse.Namespace(**values)


class FakeRunner:
    def __init__(self,env,root=None):self.env,self.root=env,root;self.files={};self.commands=[]
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
    with tempfile.TemporaryDirectory(prefix='resident_word_',dir=HERE/'scratch')as directory:
        root=Path(directory)
        for part in ('src','include','config','symbols','docs/match','build'):(root/part).mkdir(parents=True,exist_ok=True)
        (root/'src'/f'{ROOT:08X}.c').write_text('/* synthetic source identity; compiler mocked */\n')
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
         patch.object(match,'_run_replay_process',return_value=subprocess.CompletedProcess([],0,json.dumps(
             dict(findings=[],total=0,addr=f'0x{ROOT:08X}',hand_asm_allowed=False,allow_entry=None)),'')), \
         patch.object(evidence,'report_rom_path',return_value=str(root/'fixture.bin')):
        yield runner


class ResidentLifecycleTests(unittest.TestCase):
    def test_original_elf_function_relocation_and_link_integrity(self):
        env=environment();image=match.elf_image(elf(env));runner=FakeRunner(env)
        data,bindings=owner.object_bytes(runner,'/synthetic',args(),image,ROOT,env['rom'],env['mapping'],env['objects'],selector=SELECTOR,index=env['index'])
        self.assertEqual(data,env['data']);self.assertEqual(bindings,env['bindings']);self.assertEqual(len(runner.commands),2)
        with self.assertRaises(ValueError):
            owner.original_bindings(match.elf_image(elf(env,helper_type=1)),ROOT,env['rom'],env['mapping'],env['objects'],selector=SELECTOR,index=env['index'])
        runner.read_binary=lambda path:b'/* fixture */' if path.endswith('/f.i')else elf(env,linked=True,changed=True)
        with self.assertRaisesRegex(ValueError,'outside exact original relocations'):
            owner.object_bytes(runner,'/synthetic',args(),image,ROOT,env['rom'],env['mapping'],env['objects'],selector=SELECTOR,index=env['index'])

    def test_cli_fresh_report_effect_tamper_and_status_routing(self):
        import status
        import match_evidence as evidence
        env=environment()
        with tree(env)as root,build_mocks(env,root)as runner,contextlib.redirect_stdout(io.StringIO())as output:
            argv=['match.py','--root',str(root),'--owner-runtime-profile',SELECTOR,hex(ROOT)]
            with patch.object(sys,'argv',argv):self.assertEqual(match.main(),0)
            report=(root/'docs/match'/f'{ROOT:08X}.md').read_text()
            self.assertIn('verdict MATCH',output.getvalue())
            self.assertEqual(owner.selector_for_report(report),SELECTOR)
            self.assertTrue(evidence.report_matches(report,root,ROOT))
            commands=[]
            def matcher(command,**unused):
                commands.append(command)
                with patch.object(sys,'argv',command[1:]),contextlib.redirect_stdout(io.StringIO())as stdout:
                    code=match.main()
                return subprocess.CompletedProcess(command,code,stdout.getvalue(),'')
            with patch.object(status.subprocess,'run',side_effect=matcher):
                values=status.collect(str(root),True,quiet=True,jobs=1)
            self.assertEqual(values[1],1);self.assertEqual(values[4],[]);self.assertEqual(len(commands),1)
            command=commands[0];self.assertEqual(command[command.index('--owner-runtime-profile')+1],SELECTOR)
            self.assertIn('--no-write',command)
            altered=report.replace('"R0_projected":false','"R0_projected":true',1)
            self.assertNotEqual(report,altered)
            (root/'docs/match'/f'{ROOT:08X}.md').write_text(altered);commands.clear()
            with patch.object(status.subprocess,'run',side_effect=matcher):
                values=status.collect(str(root),True,quiet=True,jobs=1)
            self.assertEqual(values[1],0);self.assertTrue(values[4]);self.assertEqual(commands,[])
            self.assertFalse(evidence.report_matches(altered,root,ROOT))

    def test_during_build_source_headers_maps_and_missing_elf_refused(self):
        env=environment()
        for kind in ('source','header','mapping','index','data'):
            with self.subTest(kind=kind),tree(env)as root:
                paths={'source':root/'src'/f'{ROOT:08X}.c','header':root/'include/fixture.h',
                    'mapping':root/'config/functions.json','index':root/'symbols/functions.txt','data':root/'config/data_symbols.json'}
                def change():paths[kind].write_bytes(paths[kind].read_bytes()+b' ')
                with build_mocks(env,root,change),self.assertRaisesRegex(ValueError,'source, maps, headers or ROM changed'):
                    owner.build(root,ROOT,selector=SELECTOR)
        manifest,_=prove(env)
        with self.assertRaisesRegex(ValueError,'original ELF identity'):
            owner.fingerprint(ROOT,env['data'],manifest,'a'*64,env['mapping'],env['index'],env['objects'],env['rom'])


class ResidentCompatibilityTests(unittest.TestCase):
    def test_plain_acyclic_leaf_and_existing_entry_dispatch_stay_unchanged(self):
        import entry_recursive_ordinary_call_profile as entry
        data=bytes.fromhex('07207047')
        mapping=json.dumps([dict(rom=f'0x{ROOT:08X}',end=f'0x{ROOT+4:08X}',mode='thumb',instrs=2)]).encode()
        index=f'{ROOT:08X} {ROOT+4:08X} 4 2 bx\n'.encode()
        rom=b'\0'*(ROOT-match.ROM_BASE)+data
        bindings=dict(calls=[],data=[],functions=[],switches=[])
        manifest,instructions=owner.verify(data,ROOT,rom,mapping,index,b'{}',bindings=bindings,selector=owner.ACYCLIC_SELECTOR)
        self.assertEqual(manifest['profile'],owner.ACYCLIC_SCHEMA)
        self.assertEqual(len(instructions),2)
        sentinel=object()
        with patch.object(entry,'verify_owner',return_value=sentinel)as native:
            self.assertIs(owner.verify(data,ROOT,rom,mapping,index,b'{}',bindings=bindings,selector=entry.SELECTOR),sentinel)
        self.assertEqual(native.call_count,1)
        with self.assertRaisesRegex(ValueError,'entry native admission requires original resident-owner ELF bindings'):
            owner.preflight(data,ROOT,rom,mapping,index,b'{}',selector=entry.SELECTOR)
        for change,message in (({18:0x1C13},'resident scratch is not the unique second-output R2 alias'),
                               ({7:0xaa00},'two-output helper requires separate callback-local R1/R2 words')):
            with self.subTest(change=change),self.assertRaisesRegex(ValueError,message):prove(environment(change))
