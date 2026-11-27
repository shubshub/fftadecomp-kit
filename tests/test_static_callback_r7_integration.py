"""New synthetic integration boundaries only; no original compiler/ROM workflow."""
import argparse
import copy
import report_fixtures
import contextlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

CASE = Path(__file__).resolve().parents[1]
BASE = CASE.parents[1]
sys.dont_write_bytecode = True
sys.path[:0] = [str(CASE/'tools'), str(BASE/'repos/fftadecomp-kit/tools')]
import match
import owner_admission_profile as owner
import function_thunk_profile as thunk
import static_callback_target_preservation_profile as r7
import static_callback_buffer_profile as default
import match_evidence
import status

A,W,C = 0x08008000,0x08010000,0x08011000


def bl(site,target):
    delta=target-site-4
    return struct.pack('<HH',0xf000|((delta>>12)&0x7ff),0xf800|((delta>>1)&0x7ff))


def fixture():
    # A real initialized local word, typed callback literal, and direct worker.
    root=bytes.fromhex('00b581b00020009003496846')+bl(A+12,W)+bytes.fromhex('01b001bc00470000')+struct.pack('<I',C+1)
    worker=bytes.fromhex('90b50f1c041c201c')+bl(W+8,thunk.ALIASES['_call_via_r7'])+bytes.fromhex('0028fad190bc01bc0047')
    leaf=bytes.fromhex('01780931017001207047')
    bodies={A:root,W:worker,C:leaf}
    rom=bytearray(thunk.END-match.ROM_BASE)
    for number,address in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH',rom,address-match.ROM_BASE,0x4700+(number<<3),0x46c0)
    for address,body in bodies.items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)]=body
    rows=[dict(rom=f'0x{address:08X}',end=f'0x{address+len(body):08X}',mode='thumb',instrs=0) for address,body in bodies.items()]
    rows += [dict(rom=f'0x{address:08X}',end=f'0x{address+2:08X}',mode='thumb',instrs=1) for address in thunk.ALIASES.values()]
    index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} {int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode()
    bindings=dict(calls=[[12,f'func_{W:08X}']],data=[],functions=[[24,f'func_{C:08X}']],switches=[])
    return dict(data=root,address=A,rom=bytes(rom),mapping=json.dumps(rows).encode(),index=index,objects=b'{}',bindings=bindings,selector=r7.SELECTOR)


def result():
    v=fixture();manifest,instructions=owner.verify(**v)
    return (v['data'],manifest,'synthetic-source',v['mapping'],v['index'],v['objects'],v['rom'],len(instructions),b'synthetic original ELF boundary')


def synthetic_original_image():
    v=fixture();text=bytearray(v['data']);text[12:16]=bl(A+12,A+12);text[24:28]=b'\0'*4
    symbols=[dict(name=f'func_{A:08X}',value=1,size=len(text),type=2,bind=1,section=1),
             dict(name=f'func_{W:08X}',value=0,size=0,type=0,bind=1,section=0),
             dict(name=f'func_{C:08X}',value=0,size=0,type=0,bind=1,section=0)]
    sections=[(0,)*10,(0,1,6,0,0,len(text),0,0,4,0),(0,2,0,0,0,0,0,0,4,16),
              (0,9,0,0,0,16,2,1,4,8)]
    reloc=struct.pack('<IIII',12,(1<<8)|10,24,(2<<8)|2)
    return dict(type=1,sections=sections,text_index=1,text=bytes(text),symbols=symbols,
                relocations=[3],symbol_tables={2:symbols},section_data=[b'',bytes(text),b'',reloc])


class IntegrationTests(unittest.TestCase):
    def test_cli_routes_exact_explicit_selector(self):
        argv=['match.py','--root',str(CASE/'scratch'),'--owner-runtime-profile',r7.SELECTOR,f'0x{A:08X}']
        with patch.object(sys,'argv',argv),patch.object(owner,'issue',return_value=19) as issue:
            self.assertEqual(match.main(),19)
        self.assertEqual(issue.call_args.args[1],A)
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile,r7.SELECTOR)

    def test_owner_manifest_binds_full_replay_policy_and_sources(self):
        r=result();e=r[1]['proof']['buffers'];policy=e['r7_preservation']['policy']
        self.assertEqual(r[1]['profile'],r7.SCHEMA)
        self.assertEqual(policy['selector'],r7.SELECTOR)
        self.assertEqual(policy['register'],7)
        self.assertEqual(policy['thunk'],thunk.ALIASES['_call_via_r7'])
        self.assertFalse(policy['descriptor_words'])
        self.assertIn('owner_admission_profile.py',policy['source_sha256'])
        self.assertIn('static_callback_target_preservation_profile.py',policy['source_sha256'])
        self.assertTrue(e['r7_preservation']['observations'])
        self.assertGreaterEqual(len(e['callbacks']),2)
        self.assertTrue({W,C,thunk.ALIASES['_call_via_r7']} <= {row['address'] for row in e['dependencies']})
        self.assertEqual(owner.verify(**fixture(),manifest=r[1])[0],r[1])

    def test_default_owner_route_still_refuses_repeated_target(self):
        v=fixture();v['selector']=default.SELECTOR
        with self.assertRaisesRegex(ValueError,'not an exact Thumb'):
            owner.verify(**v)

    def test_tampered_policy_sources_effects_and_one_use_receipts_refuse(self):
        original=result()[1]
        for mutate in (
            lambda m:m['proof']['buffers']['r7_preservation']['policy'].update(register=6),
            lambda m:m['proof']['buffers']['r7_preservation']['policy']['source_sha256'].update({'match.py':'0'*64}),
            lambda m:m['proof']['buffers']['r7_preservation'].update(observations=[]),
            lambda m:m['proof']['buffers']['callbacks'].clear(),
            lambda m:m['proof']['buffers']['dependencies'][0].update(body_sha256='0'*64),
        ):
            changed=copy.deepcopy(original);mutate(changed)
            with self.assertRaisesRegex(ValueError,'manifest differs'):
                owner.verify(**fixture(),manifest=changed)

    def test_actual_target_and_original_binding_guards_remain_strict(self):
        v=fixture()
        for key,value in [('functions',[]),('calls',[]),('switches',[[0,0]])]:
            bindings=copy.deepcopy(v['bindings']);bindings[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):
                owner.verify(**dict(v,bindings=bindings))
        rows=json.loads(v['mapping']);rows.append(dict(rows[2]))
        with self.assertRaises(ValueError):owner.verify(**dict(v,mapping=json.dumps(rows).encode()))
        rom=bytearray(v['rom']);rom[thunk.ALIASES['_call_via_r7']-match.ROM_BASE]^=8
        with self.assertRaises(ValueError):owner.verify(**dict(v,rom=bytes(rom)))
        rom=bytearray(v['rom']);rom[C-match.ROM_BASE:C-match.ROM_BASE+2]=bytes.fromhex('0027')
        with self.assertRaisesRegex(ValueError,'preservation of a live alias register'):
            owner.verify(**dict(v,rom=bytes(rom)))

    def test_report_selection_is_explicit_and_closed(self):
        report=owner.render(A,result())
        self.assertEqual(owner.selector_for_report(report),r7.SELECTOR)
        self.assertIn('* owner runtime: '+r7.SELECTOR,report)
        self.assertIn('original_elf_sha256',report)
        for extra in ('* verification: `unknown-profile-v1`\n','* buffer calls: legacy\n'):
            with self.assertRaises(ValueError):owner.selected(report+extra)
        with self.assertRaises(ValueError):
            owner.selected(report.replace(r7.SCHEMA,'unknown-profile-v1'))

    def test_saved_report_dispatch_replays_exact_selector_and_manifest(self):
        r=result();report=owner.render(A,r)
        report_fixtures.rom_image(self,r[6])
        with patch.object(owner,'build',return_value=r) as build:
            self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, CASE/'scratch', A), CASE/'scratch', A))
        self.assertEqual(build.call_count,1)
        self.assertEqual(build.call_args.kwargs,dict(expected=r[1],selector=r7.SELECTOR))

    def test_saved_report_tamper_and_missing_original_elf_refuse(self):
        r=result();report=owner.render(A,r)
        with patch.object(owner,'build',return_value=r):
            for changed in (report.replace('synthetic-source','different-source'),report.replace('* owner runtime: '+r7.SELECTOR,'* owner runtime: '+default.SELECTOR),report.replace('* compiled : `','* compiled : `00')):
                self.assertFalse(match_evidence.report_matches(changed,CASE/'scratch',A))
        with self.assertRaisesRegex(ValueError,'original ELF identity'):
            owner.fingerprint(A,r[0],r[1],r[2],r[3],r[4],r[5],r[6])

    def test_status_forwards_selector_without_bypassing_report_validation(self):
        r=result();report=owner.render(A,r)
        (CASE/'scratch').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=CASE/'scratch',prefix='synthetic_status_') as tmp:
            root=Path(tmp)
            for name in ('config','src','docs/match'):(root/name).mkdir(parents=True,exist_ok=True)
            (root/'config/functions.json').write_text(json.dumps([dict(rom=f'0x{A:08X}',end=f'0x{A+len(r[0]):08X}',mode='thumb')]))
            target=root/f'docs/match/{A:08X}.md';target.write_text(report)
            virtual=root/f'src/{A:08X}.c' # Discovery mock only; no C file is authored.
            completed=subprocess.CompletedProcess([],0,f'extent    {len(r[0])} bytes\nverdict MATCH - byte identical\n','')
            with patch.object(Path,'rglob',return_value=[virtual]),patch.object(status,'report_matches',return_value=True) as validates,patch.object(status.subprocess,'run',return_value=completed) as run:
                found=status.collect(str(root),True,quiet=True)
            self.assertFalse(found[4]);self.assertEqual(found[1],1)
            self.assertEqual(validates.call_count,2)
            self.assertIn('--owner-runtime-profile',run.call_args.args[0])
            self.assertIn(r7.SELECTOR,run.call_args.args[0])
            target.write_text(report.replace(r7.SCHEMA,'unknown-profile-v1'))
            with patch.object(Path,'rglob',return_value=[virtual]),patch.object(status.subprocess,'run') as run:
                found=status.collect(str(root),True,quiet=True)
            self.assertTrue(found[4]);run.assert_not_called()

    def test_original_elf_call_and_callback_identity_are_not_replaced_by_policy(self):
        v=fixture();image=synthetic_original_image()
        bindings,targets=owner.original_bindings(image,A,v['rom'],v['mapping'],v['objects'],selector=r7.SELECTOR)
        self.assertEqual(bindings,v['bindings']);self.assertEqual(targets[f'func_{C:08X}'],(C,False))
        for mutation in ('pointer_addend','symbol_kind','duplicate_symbol','extra_function','relocation_kind'):
            changed=copy.deepcopy(image)
            if mutation=='pointer_addend':changed['text']=changed['text'][:24]+struct.pack('<I',4)
            elif mutation=='symbol_kind':changed['symbols'][2]['type']=1
            elif mutation=='duplicate_symbol':changed['symbols'].append(dict(changed['symbols'][2]))
            elif mutation=='extra_function':changed['symbols'].append(dict(changed['symbols'][0],name='extra'))
            else:changed['section_data'][3]=struct.pack('<IIII',12,(1<<8)|10,24,(2<<8)|3)
            with self.subTest(mutation=mutation),self.assertRaises(ValueError):
                owner.original_bindings(changed,A,v['rom'],v['mapping'],v['objects'],selector=r7.SELECTOR)

    def test_linked_object_boundary_compares_complete_text_and_exact_relocations(self):
        v=fixture();original=synthetic_original_image();linked=copy.deepcopy(original)
        linked.update(type=2,text=v['data'],relocations=[])
        linked['symbols'][0]['value']=A+1
        section=list(linked['sections'][1]);section[3]=A;linked['sections'][1]=tuple(section)
        args=argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        class Runner:
            def __init__(self):self.commands=[]
            def read_binary(self,path):return b'' if path.endswith('/f.i') else b'synthetic linked ELF boundary'
            def write_text(self,path,text):pass
            def sh(self,command):self.commands.append(command)
        runner=Runner()
        with patch.object(match,'elf_image',return_value=linked):
            body,bindings=owner.object_bytes(runner,'synthetic',args,original,A,v['rom'],v['mapping'],v['objects'],selector=r7.SELECTOR)
        self.assertEqual(body,v['data']);self.assertEqual(bindings,v['bindings']);self.assertEqual(len(runner.commands),2)
        for mutation in ('nonrelocated_byte','wrong_call','extent','residual_relocation'):
            changed=copy.deepcopy(linked)
            if mutation=='nonrelocated_byte':changed['text']=changed['text'][:4]+b'\x01'+changed['text'][5:]
            elif mutation=='wrong_call':changed['text']=changed['text'][:12]+bl(A+12,C)+changed['text'][16:]
            elif mutation=='extent':changed['symbols'][0]['size']-=2
            else:changed['relocations']=[3]
            with self.subTest(mutation=mutation),patch.object(match,'elf_image',return_value=changed),self.assertRaises(ValueError):
                owner.object_bytes(Runner(),'synthetic',args,original,A,v['rom'],v['mapping'],v['objects'],selector=r7.SELECTOR)

    def test_owner_issue_rejects_mixed_new_selector_before_compilation(self):
        args=argparse.Namespace(owner_runtime_profile=r7.SELECTOR,mode='thumb',control_flow_profile='ordinary',software_double_profile=None,software_double_remainder_profile=None,function_address_profile=None,switch_profile=None,label='',wsl='Ubuntu',wsl_path=match.DEFAULT_WSL_PATH,signed_quotient_profile='other',signed_runtime_profile=None,addressed_signed_runtime_profile=None,switch_data_profile=None)
        with patch.object(owner,'build') as build,self.assertRaises(ValueError):
            owner.issue(CASE/'scratch',A,args)
        build.assert_not_called()


if __name__=='__main__':unittest.main(verbosity=2)
