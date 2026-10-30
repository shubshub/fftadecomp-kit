"""Synthetic addressed-call admission tests. No C compiler or approved ROM needed."""
import argparse
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch
from contextlib import contextmanager

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence as evidence
import status
import push
import addressed_signed_runtime_profile as profile

A, B = 0x08010000, 0x08011000


def bl(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF),
                       0xF800 | ((delta >> 1) & 0x7FF))


def indexes(rows):
    return (json.dumps(rows).encode(), ''.join(
        f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
        for r in rows).encode())


class AddressedSignedRuntimeTests(unittest.TestCase):
    def setUp(self):
        forbidden = patch.object(match, 'compile_object', side_effect=AssertionError('C compilation forbidden'))
        forbidden.start(); self.addCleanup(forbidden.stop)
        # Deliberately synthetic identities, patched only in this test process.
        self.rom = bytearray(0x143000)
        self.rom[0x14274C:0x14274E] = bytes.fromhex('7047')
        self.rom[0x142742:0x142746] = bl(0x08142742, 0x0814274C)
        self.rom[0x142A16:0x142A1A] = bl(0x08142A16, 0x0814274C)
        for module in (profile.quotient, profile.remainder):
            ids = tuple((lo, hi, hashlib.sha256(self.rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                        for lo, hi, _ in module.IDENTITIES)
            change = patch.object(module, 'IDENTITIES', ids)
            change.start(); self.addCleanup(change.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def fixture(self, tokens=(0xB510, 'div', 'mod', 0xBC10, 0xBC02, 0x4708)):
        data, calls, bindings = bytearray(), {}, {}
        for token in tokens:
            if isinstance(token, int):
                data += struct.pack('<H', token)
            else:
                target = B if token == 'ordinary' else profile.OPERATIONS[
                    'func_081426B8' if token == 'div' else 'func_08142950']
                site = A + len(data)
                data += bl(site, target); calls[site] = target
                if token != 'ordinary': bindings[site] = f'func_{target:08X}'
        rows = [{'rom':f'0x{A:08X}', 'end':f'0x{A+len(data):08X}', 'mode':'thumb',
                 'instrs':len(tokens)},
                {'rom':f'0x{B:08X}', 'end':f'0x{B+2:08X}', 'mode':'thumb', 'instrs':1}]
        rows += [{'rom':f'0x{lo:08X}', 'end':f'0x{hi:08X}', 'mode':'thumb', 'instrs':(hi-lo)//2}
                 for lo, hi, _ in sorted(set(profile.quotient.IDENTITIES + profile.remainder.IDENTITIES))]
        mapping, index = indexes(rows)
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(data=bytes(data), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, calls=calls, bindings=bindings)

    def image(self, fixture):
        """The same canonical ELF32 fields consumed by the production ELF reader."""
        text = bytearray(fixture['data']); relocations, symbols = bytearray(), [dict(
            name=f'func_{A:08X}', value=1, size=len(text), type=2, bind=1, section=1)]
        for site, target in fixture['calls'].items():
            name = f'func_{target:08X}'
            symbols.append(dict(name=name,value=0,size=0,type=0,bind=1,section=0))
            offset = site-A; text[offset:offset+4] = bl(site, site)
            relocations += struct.pack('<II', offset, ((len(symbols)-1)<<8)|10)
        sections = [(0,0,0,0,0,0,0,0,0,0), (0,1,6,0,0,len(text),0,0,2,0),
                    (0,9,0,0,0,len(relocations),3,1,4,8)]
        return dict(type=1,text=bytes(text),text_index=1,sections=sections,
            section_data=[b'',bytes(text),bytes(relocations)],symbols=symbols,
            symbol_tables={3:symbols},relocations=[2])

    def test_single_and_mixed_actual_addressed_calls_accept_full_words_and_zero(self):
        for calls in [('div',),('mod',),('div','mod')]:
            with self.subTest(calls=calls):
                f = self.fixture((0xB510,0x2100,*calls,0xBC10,0xBC02,0x4708))
                manifest, instructions = profile.verify(**f)
                self.assertFalse(manifest['arithmetic_C_equivalence'])
                self.assertEqual(manifest['runtime_numeric_return_facts'], [])
                self.assertEqual(manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
                self.assertEqual(len(instructions), len(calls)+5)
                self.assertEqual(profile.verify(**f,manifest=manifest)[0],manifest)
        f=self.fixture((0xB510,0x2A00,0xD003,'div','mod',0xBC10,0xBC02,0x4708))
        self.assertEqual(len(profile.verify(**f)[1]),8)
        f=self.fixture((0xB510,'div','mod',0x4C02,0xBC10,0xBC02,0x4708,0,999,0))
        self.assertEqual(profile.verify(**f)[0]['partition']['literal_and_table_bytes'],4)

    def test_original_relocations_and_no_default_alias_weakening(self):
        f=self.fixture(); image=self.image(f)
        calls,bindings,targets=profile.original_bindings(image,A,f['rom'],f['mapping'])
        self.assertEqual((calls,bindings),(f['calls'],f['bindings']))
        self.assertEqual(set(targets),set(profile.OPERATIONS))
        with self.assertRaises(ValueError):
            match.call_bindings(image,f'func_{A:08X}',A,f['mapping'],len(f['rom']),f['rom'],
                                divsi3_bindings={},modsi3_bindings={})
        for alias in ('__divsi3','__modsi3','func_081426BA','_call_via_r0','other'):
            bad=copy.deepcopy(image);bad['symbols'][1]['name']=alias
            with self.subTest(alias=alias),self.assertRaises(ValueError):
                profile.original_bindings(bad,A,f['rom'],f['mapping'])
        for field,value in [('value',2),('type',1),('section',1),('bind',0)]:
            bad=copy.deepcopy(image);bad['symbols'][1][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):
                profile.original_bindings(bad,A,f['rom'],f['mapping'])
        bad=copy.deepcopy(image);entries=bytearray(bad['section_data'][2]);entries[4]=2
        bad['section_data'][2]=bytes(entries)
        with self.assertRaises(ValueError):profile.original_bindings(bad,A,f['rom'],f['mapping'])

    def test_runtime_hook_and_both_indexes_are_authentic(self):
        f=self.fixture()
        for address in (0x081426B8,0x08142950,0x0814274C):
            bad=dict(f);rom=bytearray(f['rom']);rom[address-match.ROM_BASE]^=1;bad['rom']=bytes(rom)
            with self.subTest(address=address),self.assertRaises(ValueError):profile.verify(**bad)
            rows=json.loads(f['mapping']);rows=[r for r in rows if int(r['rom'],16)!=address]
            bad=dict(f);bad['mapping'],bad['index']=indexes(rows)
            with self.assertRaises(ValueError):profile.verify(**bad)
        for change in ('duplicate','overlap','end','mode','text'):
            bad=dict(f);rows=json.loads(f['mapping'])
            if change=='duplicate':rows.append(rows[0].copy())
            elif change=='overlap':rows.append(dict(rows[0],rom=f'0x{A+2:08X}'))
            elif change=='end':rows[0]['end']=f'0x{A+len(f["data"])+2:08X}'
            elif change=='mode':rows[0]['mode']='arm'
            bad['mapping'],bad['index']=indexes(rows)
            if change=='text':bad['index']=bad['index'].replace(b'0814274E',b'08142750')
            with self.subTest(change=change),self.assertRaises(ValueError):profile.verify(**bad)

    def test_bindings_other_runtimes_and_profile_composition_fail_closed(self):
        f=self.fixture()
        for bindings in ({},{A+2:'__divsi3'},dict(f['bindings'],**{})):
            if bindings==f['bindings']:bindings={s:'__modsi3' for s in bindings}
            with self.subTest(bindings=bindings),self.assertRaises(ValueError):
                profile.verify(**dict(f,bindings=bindings))
        context=(f['rom'],f['mapping'],f['index'],f['bindings'],{})
        for options in ({'buffer_proof':object()},{'modsi3_context':()},
                        {'signed_runtime_context':()},{'function_thunk_context':{}},
                        {'remainder_inventory_context':()},{'preloaded_switch':True}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'],A,True,f['calls'],
                    addressed_signed_runtime_context=context,**options)
        bad=dict(f['calls']);bad[A+2]=match.UDIVSI3_ADDRESS
        with self.assertRaises(ValueError):profile.verify(**dict(f,calls=bad))
        div={site:'__divsi3' for site,target in f['calls'].items() if target==profile.quotient.ADDRESS}
        mod={site:'__modsi3' for site,target in f['calls'].items() if target==profile.remainder.ADDRESS}
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'],A,True,f['calls'],
                divsi3_context=(f['rom'],f['mapping'],div,{}),modsi3_context=(f['rom'],f['mapping'],mod))
        with self.assertRaises(ValueError):
            match.signed_divmod.verify(f['data'],A,f['rom'],f['mapping'],f['index'],f['calls'],f['bindings'])

    def linked_image(self,f,original):
        image=copy.deepcopy(original);image['type']=2;image['text']=f['data'];image['relocations']=[]
        image['sections'][1]=tuple(list(image['sections'][1][:3])+[A]+list(image['sections'][1][4:]))
        for symbol in image['symbols']:
            if symbol['section']:symbol['value']=A|1
            else:
                symbol.update(value=profile.OPERATIONS[symbol['name']]|1,section=0xFFF1,type=2)
        return image

    def test_linked_complete_ELF_and_modification_surface(self):
        f=self.fixture();original=self.image(f);linked=self.linked_image(f,original)
        calls,bindings,targets=profile.original_bindings(original,A,f['rom'],f['mapping'])
        self.assertEqual(profile.linked_bytes(original,linked,A,calls,targets),f['data'])
        for change in ('outside','call','size','undefined','address','ARM','object','relocation','veneer'):
            image=copy.deepcopy(linked)
            if change in ('outside','call'):
                body=bytearray(image['text']);body[0 if change=='outside' else 2]^=1;image['text']=bytes(body)
            elif change=='size':image['symbols'][0]['size']-=2
            elif change=='undefined':image['symbols'][1]['section']=0
            elif change=='address':image['symbols'][1]['value']+=2
            elif change=='ARM':image['symbols'][0]['value']&=~1
            elif change=='object':image['symbols'][1]['type']=1
            elif change=='relocation':image['relocations']=[2]
            elif change=='veneer':image['text']+=b'\0\0'
            with self.subTest(change=change),self.assertRaises(ValueError):
                profile.linked_bytes(original,image,A,calls,targets)
        bad=dict(f);bad['bindings']={next(iter(bindings)):next(iter(bindings.values()))}
        with self.assertRaises(ValueError):profile.verify(**bad)

    def test_frame_alias_return_partition_and_address_literals_stay_guarded(self):
        good=(0xB510,0xB082,'div','mod',0xB002,0xBC10,0xBC02,0x4708)
        self.assertTrue(profile.verify(**self.fixture(good))[0]['frame'])
        bads=[(0xB510,0xA800,'div','mod',0xBC10,0xBC02,0x4708),
              (0xB510,'div','mod',0xBC02,0x4708),
              (0xB510,'div','mod',0xBC10,0x2400,0xBC02,0x4708),
              (0xB510,'div','mod',0xBC10,0xBC02,0x4708,0x1234),
              (0xB510,'div','mod',0x4C02,0xBC10,0xBC02,0x4708,0,0,0x0201)]
        for tokens in bads:
            with self.subTest(tokens=tokens),self.assertRaises(ValueError):profile.verify(**self.fixture(tokens))

    def synthetic_result(self,root,f,selector=None):
        selector=selector or profile.SELECTOR
        manifest,_=profile.verify(**f,selector=selector)
        result=dict(address=A,body=f['data'],manifest=manifest,
            source_sha256=evidence.source_fingerprint(root,A),
            mapping_sha256=profile.sha(f['mapping']),index_sha256=profile.sha(f['index']),
            objects_sha256=profile.sha((root/'config/data_symbols.json').read_bytes()),
            rom_sha256=profile.sha(f['rom']),instructions=len(f['calls'])+4,
            toolchain=profile.toolchain_fingerprint(),original_elf=b'synthetic ELF fixture',
            assembly=b'synthetic assembly fixture',linked_elf=b'synthetic linked ELF fixture')
        if selector != profile.SELECTOR:
            result['runtime']=profile.runtime_fingerprint()
        return result

    def test_readonly_word0_requires_actual_read_and_preserves_base(self):
        for calls in [('div',),('div','mod')]:
            f=self.fixture((0xB570,0x1C04,0x9804,*calls,0xBC70,0xBC02,0x4708))
            manifest,_=profile.verify(**f,selector=profile.READONLY_SELECTOR)
            self.assertEqual(manifest['schema'],profile.READONLY_SCHEMA)
            incoming=manifest['frame']['entry_stack']
            self.assertEqual(incoming['words'],[0])
            self.assertEqual(incoming['reads'],[[A+4,0,4,'0498']])
            self.assertEqual(incoming['loaded_value'],'unknown scalar; no provenance facts')
            self.assertIn('readonly_entry_stack_profile.py',manifest['producer_source_sha256'])
            self.assertFalse(manifest['arithmetic_C_equivalence'])
            with self.assertRaises(ValueError):profile.verify(**f)
        f=self.fixture()
        self.assertEqual(profile.verify(**f)[0]['schema'],profile.SCHEMA)
        with self.assertRaises(ValueError):profile.verify(**f,selector=profile.READONLY_SELECTOR)
        with self.assertRaises(ValueError):profile.verify(**f,selector='other')
        with self.assertRaises(ValueError):
            match.call_bindings(self.image(f),f'func_{A:08X}',A,f['mapping'],len(f['rom']),f['rom'],
                                divsi3_bindings={},modsi3_bindings={})

    def test_readonly_word0_rejects_writes_other_words_aliases_and_returns(self):
        bads={
            'entry write':(0xB570,0x9004,'div',0xBC70,0xBC02,0x4708),
            'entry word1':(0xB570,0x9805,'div',0xBC70,0xBC02,0x4708),
            'unaligned entry halfword via address':(0xB570,0xA804,0x3002,0x8800,'div',0xBC70,0xBC02,0x4708),
            'entry pointer passed to call':(0xB570,0x9804,0xA804,'div',0xBC70,0xBC02,0x4708),
            'local pointer escape':(0xB570,0x9804,0xB081,0xA800,'div',0xB001,0xBC70,0xBC02,0x4708),
            'corrupt saved return':(0xB570,0x9804,'div',0xBC30,0xBC02,0x4708),
            'return incoming scalar':(0xB570,0x9804,'div',0xBC70,0xBC02,0x9800,0x4700),
        }
        for reason,tokens in bads.items():
            with self.subTest(reason=reason),self.assertRaises(ValueError):
                profile.verify(**self.fixture(tokens),selector=profile.READONLY_SELECTOR)
        f=self.fixture((0xB570,0x9804,'div',0xBC70,0xBC02,0x4708))
        context=(f['rom'],f['mapping'],f['index'],f['bindings'],{},profile.READONLY_SELECTOR)
        for options in ({'buffer_proof':object()},{'function_thunk_context':{}},{'modsi3_context':()}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'],A,True,f['calls'],
                    addressed_signed_runtime_context=context,**options)

    def test_readonly_word0_selector_status_publisher_and_stale_evidence(self):
        scratch=Path(__file__).resolve().parents[1]/'build/tests';scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='readonly_word0_',dir=scratch) as directory:
            root=Path(directory);f=self.fixture((0xB570,0x9804,'div',0xBC70,0xBC02,0x4708))
            for sub in ('src','include','config','symbols','docs/match'):(root/sub).mkdir(parents=True)
            (root/'src/08010000.c').write_text('/* synthetic fingerprint only */\n')
            (root/'config/functions.json').write_bytes(f['mapping']);(root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_text('{}\n');rom=root/'baserom.bin';rom.write_bytes(f['rom'])
            with patch.dict(os.environ,FFTA_ROM=str(rom)):
                result=self.synthetic_result(root,f,profile.READONLY_SELECTOR)
                with patch.object(profile,'build',return_value=result) as build:
                    with patch.object(sys,'argv',['match.py','--root',str(root),
                         '--addressed-signed-runtime-profile',profile.READONLY_SELECTOR,f'{A:08X}']),redirect_stdout(io.StringIO()):
                        self.assertEqual(match.main(),0)
                    self.assertEqual(build.call_args.kwargs['selector'],profile.READONLY_SELECTOR)
                    report=(root/'docs/match/08010000.md').read_text()
                    self.assertEqual(profile.selector_for_report(report),profile.READONLY_SELECTOR)
                    self.assertIn('readable aligned 4-byte incoming ABI word',report)
                    self.assertTrue(evidence.report_matches(report,root,A))
                    self.assertEqual(build.call_args.kwargs['selector'],profile.READONLY_SELECTOR)
                    with patch.object(status.subprocess,'run',return_value=type('R',(),{
                         'returncode':0,'stdout':f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n','stderr':''})()) as run:
                        self.assertEqual(status.collect(str(root),verify=True)[1],1)
                        self.assertIn(profile.READONLY_SELECTOR,run.call_args[0][0])
                    with redirect_stdout(io.StringIO()):
                        self.assertTrue(push.check_reports(str(root)))
                        with patch.object(push,'run',return_value=(0,'up to date')) as gate:
                            self.assertTrue(push.check_matches(str(root)))
                            self.assertIn('--verify',gate.call_args[0][0])
                    for relative in ('src/08010000.c','symbols/functions.txt','config/functions.json',
                                     'config/data_symbols.json','baserom.bin'):
                        path=root/relative;old=path.read_bytes();path.write_bytes(old+b' ')
                        try:self.assertFalse(evidence.report_matches(report,root,A))
                        finally:path.write_bytes(old)
                    header=root/'include/new.h';header.write_text('/* stale */\n')
                    try:self.assertFalse(evidence.report_matches(report,root,A))
                    finally:header.unlink()
                    with patch.object(profile,'runtime_fingerprint',return_value={'stale':True}):
                        self.assertFalse(evidence.report_matches(report,root,A))
                    self.assertFalse(evidence.report_matches(report.replace(profile.READONLY_SELECTOR,profile.SELECTOR),root,A))
                    self.assertFalse(evidence.report_matches(report.replace('one readable aligned','two readable aligned'),root,A))
                    forged=copy.deepcopy(result);forged['manifest']['frame']['entry_stack']['words']=[1]
                    self.assertFalse(evidence.report_matches(profile.render(forged),root,A))

    def test_readonly_word0_fresh_build_binds_context_and_runtime(self):
        scratch=Path(__file__).resolve().parents[1]/'build/tests';scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='readonly_build_',dir=scratch) as directory:
            root=Path(directory);f=self.fixture((0xB570,0x9804,'div',0xBC70,0xBC02,0x4708))
            original=self.image(f);linked=self.linked_image(f,original)
            for sub in ('src','include','config','symbols'):(root/sub).mkdir()
            (root/'src/08010000.c').write_text('/* synthetic fingerprint only */\n')
            (root/'config/functions.json').write_bytes(f['mapping']);(root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_text('{}\n');rom=root/'baserom.bin';rom.write_bytes(f['rom'])
            commands=[]
            class Runner:
                def __init__(self,*args,**kwargs):self.root=kwargs['root']
                @contextmanager
                def workspace(self):
                    path=self.root/'workspace';path.mkdir();yield str(path)
                def read_binary(self,path):
                    return f['data'] if path.endswith('f.linked.bin') else b'synthetic ELF/assembly'
                def write_text(self,path,value):Path(path).write_text(value)
                def sh(self,command):commands.append(command)
            with (patch.dict(os.environ,FFTA_ROM=str(rom)),patch.object(match,'Runner',Runner),
                  patch.object(match,'compile_object',return_value=(b'synthetic ET_REL',None,original)),
                  patch.object(match,'elf_image',return_value=linked),
                  patch.object(match,'_run_replay_process',return_value=None),
                  patch.object(match,'plausibility_result',return_value=([],None))):
                result=profile.build(root,A,selector=profile.READONLY_SELECTOR)
                self.assertEqual(result['manifest']['schema'],profile.READONLY_SCHEMA)
                self.assertEqual(result['runtime'],profile.runtime_fingerprint())
                self.assertEqual(result['manifest']['frame']['entry_stack']['reads'],[[A+2,0,4,'0498']])
                self.assertEqual(len(commands),3)
                self.assertIn('--no-relax',commands[1])
                with patch.object(profile,'runtime_fingerprint',side_effect=[result['runtime'],{'changed':True}]):
                    with self.assertRaises(ValueError):profile.build(root,A,selector=profile.READONLY_SELECTOR)

    def test_explicit_cli_report_status_and_publisher_roundtrip_without_compilation(self):
        scratch=Path(__file__).resolve().parents[1]/'build/tests';scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='addressed_signed_',dir=scratch) as directory:
            root=Path(directory);f=self.fixture()
            for sub in ('src','include','config','symbols','docs/match'): (root/sub).mkdir(parents=True,exist_ok=True)
            # This is a source-fingerprint token, never compiled C.
            source=root/'src/08010000.c';source.write_text('/* synthetic source token */\n')
            (root/'config/functions.json').write_bytes(f['mapping']);(root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_text('{}\n');rom=root/'baserom.bin';rom.write_bytes(f['rom'])
            with patch.dict(os.environ,FFTA_ROM=str(rom)):
                result=self.synthetic_result(root,f)
                with patch.object(profile,'build',return_value=result) as build:
                    output=io.StringIO()
                    with patch.object(sys,'argv',['match.py','--root',str(root),
                         '--addressed-signed-runtime-profile',profile.SELECTOR,f'{A:08X}']),redirect_stdout(output):
                        self.assertEqual(match.main(),0)
                    build.assert_called_once()
                    report=(root/'docs/match/08010000.md').read_text()
                    self.assertTrue(evidence.report_matches(report,root,A))
                    self.assertEqual(status.collect(str(root),verify=False)[1],1)
                    with redirect_stdout(io.StringIO()):
                        self.assertTrue(push.check_reports(str(root)))
                        with patch.object(push,'run',return_value=(0,'status block up to date\n')) as gate:
                            self.assertTrue(push.check_matches(str(root)))
                            self.assertIn('--verify',gate.call_args[0][0])
                    with patch.object(status.subprocess,'run',return_value=type('R',(),{
                        'returncode':0,'stdout':f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n','stderr':''})()) as run:
                        self.assertEqual(status.collect(str(root),verify=True)[1],1)
                        command=run.call_args[0][0]
                        self.assertIn('--addressed-signed-runtime-profile',command)
                        self.assertIn(profile.SELECTOR,command)
                    for relative,payload in [('src/08010000.c',b'changed'),('config/functions.json',b'[]'),
                                              ('symbols/functions.txt',b''),('config/data_symbols.json',b'{"stale":"0x02000000"}'),
                                              ('baserom.bin',b'changed')]:
                        path=root/relative;saved=path.read_bytes();path.write_bytes(payload)
                        try:self.assertFalse(evidence.report_matches(report,root,A))
                        finally:path.write_bytes(saved)
                    self.assertFalse(evidence.report_matches(report+'* verification: `other`\n',root,A))
                    altered=report.replace('conditional returning ARM ABI','numeric division theorem')
                    self.assertFalse(evidence.report_matches(altered,root,A))
                    header=root/'include/stale.h';header.write_text('/* changed header */\n')
                    try:self.assertFalse(evidence.report_matches(report,root,A))
                    finally:header.unlink()
                    prefix='* addressed signed runtime evidence: `'
                    line=next(row for row in report.splitlines() if row.startswith(prefix))
                    payload=json.loads(line[len(prefix):-1]);payload['manifest']['arithmetic_C_equivalence']=True
                    changed=profile.text(payload);forged=report.replace(line,prefix+changed+'`')
                    old_hash=next(row for row in report.splitlines() if row.startswith('* addressed signed runtime proof SHA-256:'))
                    forged=forged.replace(old_hash,f'* addressed signed runtime proof SHA-256: `{profile.sha(changed.encode())}`')
                    self.assertFalse(evidence.report_matches(forged,root,A))
                    with patch.object(profile,'toolchain_fingerprint',return_value={}):
                        self.assertFalse(evidence.report_matches(report,root,A))
        # The tests mock the source-build boundary; no compiler/native source replay ran.

    def test_fixed_toolchain_and_conflicting_CLI_selectors_stop_before_build(self):
        args=copy.copy(self.args);args.flags='-O1'
        with self.assertRaises(ValueError):profile.build(Path('unused'),A,args)
        for option,value in [('--signed-runtime-profile',match.signed_divmod.SELECTOR),
                             ('--function-address-profile',match.function_thunk.SELECTOR),
                             ('--mode','arm')]:
            with (patch.object(profile,'build',side_effect=AssertionError('must not build')),
                  patch.object(sys,'argv',['match.py','--root','.',
                      '--addressed-signed-runtime-profile',profile.SELECTOR,option,value,f'{A:08X}'])):
                with self.assertRaises(ValueError):match.main()

    def test_fresh_build_pipeline_captures_and_rejects_mutation_without_a_compiler(self):
        scratch=Path(__file__).resolve().parents[1]/'build/tests';scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='addressed_build_',dir=scratch) as directory:
            root=Path(directory);f=self.fixture();original=self.image(f);linked=self.linked_image(f,original)
            for sub in ('src','include','config','symbols'): (root/sub).mkdir()
            source=root/'src/08010000.c';source.write_text('/* source fingerprint token */\n')
            (root/'config/functions.json').write_bytes(f['mapping']);(root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_text('{}\n');rom=root/'baserom.bin';rom.write_bytes(f['rom'])
            commands=[]
            class Runner:
                def __init__(self,*args,**kwargs):self.root=kwargs['root']
                @contextmanager
                def workspace(self):
                    path=self.root/'workspace';path.mkdir();yield str(path)
                def read_binary(self,path):
                    return f['data'] if path.endswith('f.linked.bin') else b'synthetic ELF/assembly'
                def write_text(self,path,value):Path(path).write_text(value)
                def sh(self,command):commands.append(command)
            with (patch.dict(os.environ,FFTA_ROM=str(rom)),patch.object(match,'Runner',Runner),
                  patch.object(match,'compile_object',return_value=(b'synthetic ET_REL',None,original)) as compile_call,
                  patch.object(match,'elf_image',return_value=linked),
                  patch.object(match,'_run_replay_process',return_value=None) as plausible,
                  patch.object(match,'plausibility_result',return_value=([],None))):
                result=profile.build(root,A)
                compile_call.assert_called_once()
                self.assertEqual(result['body'],f['data']);self.assertEqual(len(commands),3)
                self.assertIn('--no-relax',commands[1]);self.assertIn('--orphan-handling=error',commands[1])
                self.assertEqual(plausible.call_args[0][0][1],str(Path(profile.__file__).with_name('plausible.py')))
                # A fresh source replay must build again; no saved-byte shortcut.
                report=profile.render(result);compile_call.reset_mock()
                self.assertTrue(evidence.report_matches(report,root,A));compile_call.assert_called_once()
                with patch.object(match,'plausibility_result',return_value=(['implausible'],None)):
                    with self.assertRaises(ValueError):profile.build(root,A)
                saved=source.read_bytes()
                def mutate_source(*args,**kwargs):source.write_text('/* changed during proof */\n')
                with patch.object(match,'_run_replay_process',side_effect=mutate_source):
                    try:
                        with self.assertRaises(ValueError):profile.build(root,A)
                    finally:source.write_bytes(saved)
                with patch.object(profile,'toolchain_fingerprint',side_effect=[result['toolchain'],[]]):
                    with self.assertRaises(ValueError):profile.build(root,A)


    def data_fixture(self, operations=('mod',), addends=(0, 8)):
        tokens=(0xB510,0x4C00,0x6820,0x2100,*operations,0x4C00,
                'ordinary',0xBC10,0xBC02,0x4708)
        f=self.fixture(tokens); body=bytearray(f['data'])
        if len(body)%4: body+=b'\0\0'
        offset=len(body); sites=(2,8+4*len(operations))
        objects={'state':'0x03002810','table':'0x030009E0'}
        records=[]
        for index,(name,base) in enumerate(objects.items()):
            literal=offset+index*4;site=sites[index]
            struct.pack_into('<H',body,site,0x4C00|((literal-((site+4)&~3))//4))
            body+=struct.pack('<I',int(base,16)+addends[index])
            records.append([literal,name,addends[index]])
        f['data']=bytes(body);rom=bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body;f['rom']=bytes(rom)
        rows=json.loads(f['mapping']);rows[0].update(end=f'0x{A+len(body):08X}',instrs=len(tokens))
        f['mapping'],f['index']=indexes(rows)
        f.update(data_mapping=json.dumps(objects).encode(),data_bindings=records)
        return f

    def data_image(self,f):
        image=self.image(f);text=bytearray(image['text']);rels=bytearray(image['section_data'][2])
        for offset,name,addend in f['data_bindings']:
            image['symbols'].append(dict(name=name,value=0,size=0,type=0,bind=1,section=0))
            rels+=struct.pack('<II',offset,((len(image['symbols'])-1)<<8)|2)
            struct.pack_into('<i',text,offset,addend)
        image['text']=image['section_data'][1]=bytes(text)
        image['section_data'][2]=bytes(rels)
        section=list(image['sections'][2]);section[5]=len(rels);image['sections'][2]=tuple(section)
        return image

    def linked_data_image(self,f,original):
        linked=copy.deepcopy(original);linked.update(type=2,text=f['data'],relocations=[])
        section=list(linked['sections'][1]);section[3]=A;linked['sections'][1]=tuple(section)
        objects=json.loads(f['data_mapping'])
        for symbol in linked['symbols']:
            if symbol['section']:symbol['value']=A|1
            elif symbol['name'] in objects:
                symbol.update(value=int(objects[symbol['name']],16),section=0xFFF1,type=1)
            else:
                symbol.update(value=int(symbol['name'][5:],16)|1,section=0xFFF1,type=2)
        return linked

    def data_original_bindings(self,f,image=None):
        data={}
        calls,bindings,targets=profile.original_bindings(image or self.data_image(f),A,
            f['rom'],f['mapping'],data_mapping=f['data_mapping'],data_relocations=data)
        return calls,bindings,targets,data

    def test_data_selector_admits_actual_typed_words_and_conditional_runtime(self):
        for operations in (('div',),('mod',),('div','mod')):
            for addends in ((0,8),(-4,0)):
                with self.subTest(operations=operations,addends=addends):
                    f=self.data_fixture(operations,addends)
                    manifest,_=profile.verify(**f,selector=profile.DATA_SELECTOR)
                    self.assertEqual(manifest['schema'],profile.DATA_SCHEMA)
                    self.assertEqual(manifest['data_bindings'],f['data_bindings'])
                    self.assertEqual(manifest['data_contract'],profile.DATA_CONTRACT)
                    self.assertEqual(manifest['runtime_numeric_return_facts'],[])
                    self.assertFalse(manifest['arithmetic_C_equivalence'])
                    self.assertNotIn('entry_stack',manifest['frame'])
                    self.assertEqual(profile.verify(**f,selector=profile.DATA_SELECTOR,manifest=manifest)[0],manifest)
                    calls,bindings,targets,data=self.data_original_bindings(f)
                    self.assertEqual((calls,bindings),(f['calls'],f['bindings']))
                    self.assertEqual(data,{off:(name,addend) for off,name,addend in f['data_bindings']})
                    self.assertEqual(targets['state'],0x03002810)

    def test_data_selector_does_not_weaken_base_readonly_or_defaults(self):
        f=self.data_fixture()
        for selector in (profile.SELECTOR,profile.READONLY_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):
                profile.verify(**f,selector=selector)
        with self.assertRaises(ValueError):profile.verify(**self.fixture(),selector=profile.DATA_SELECTOR)
        plain={k:v for k,v in f.items() if k not in ('data_mapping','data_bindings')}
        for selector in (profile.SELECTOR,profile.READONLY_SELECTOR):
            with self.assertRaises(ValueError):profile.verify(**plain,selector=selector)
        with self.assertRaises(ValueError):
            profile.original_bindings(self.data_image(f),A,f['rom'],f['mapping'])
        with self.assertRaises(ValueError):
            match.call_bindings(self.data_image(f),f'func_{A:08X}',A,f['mapping'],len(f['rom']),
                f['rom'],f['data_mapping'],modsi3_bindings={})
        context=(f['rom'],f['mapping'],f['index'],f['bindings'],{},profile.DATA_SELECTOR,
                 f['data_mapping'],f['data_bindings'])
        for extra in ({'buffer_proof':object()},{'switch_data_relocations':{}},
                      {'function_thunk_context':{}},{'modsi3_context':()}):
            with self.subTest(extra=extra),self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'],A,True,f['calls'],
                    addressed_signed_runtime_context=context,**extra)
        incoming=self.data_fixture();body=bytearray(incoming['data']);struct.pack_into('<H',body,4,0x9802)
        rom=bytearray(incoming['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        incoming.update(data=bytes(body),rom=bytes(rom))
        with self.assertRaises(ValueError):profile.verify(**incoming,selector=profile.DATA_SELECTOR)

    def test_data_original_relocations_require_unique_typed_mapped_objects(self):
        f=self.data_fixture();image=self.data_image(f)
        for field,value in [('value',4),('size',4),('type',2),('bind',0),('section',1),('name','missing')]:
            bad=copy.deepcopy(image);bad['symbols'][-1][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):self.data_original_bindings(f,bad)
        bad=copy.deepcopy(image);bad['symbols'].append(dict(bad['symbols'][-1]))
        with self.assertRaises(ValueError):self.data_original_bindings(f,bad)
        for offset,kind in ((1,2),(8,2),(f['data_bindings'][0][0],2),(len(f['data'])-2,2),(24,3)):
            bad=copy.deepcopy(image);raw=bytearray(bad['section_data'][2])
            struct.pack_into('<II',raw,len(raw)-8,offset,((len(bad['symbols'])-1)<<8)|kind)
            bad['section_data'][2]=bytes(raw)
            with self.subTest(offset=offset,kind=kind),self.assertRaises(ValueError):self.data_original_bindings(f,bad)
        for objects in (b'{}',b'{"state":"0x03002810","state":"0x03002810"}',
                        b'{"state":"0x03002810","table":"0xFFFFFFFF"}',
                        b'{"state":"0x03002810","table":"0x08011000"}',
                        b'{"state":"0x03002810","table":"0x08142244"}',
                        b'{"state":"0x03002810","table":"0x08142950"}'):
            with self.subTest(objects=objects),self.assertRaises(ValueError):
                self.data_original_bindings(dict(f,data_mapping=objects))
        bad=copy.deepcopy(image);bad['symbols'][1]['name']='__modsi3'
        with self.assertRaises(ValueError):self.data_original_bindings(f,bad)
        with self.assertRaises(ValueError):
            profile.original_bindings(image,A,f['rom'],f['mapping'],data_mapping=f['data_mapping'],data_relocations={0:('state',0)})

    def test_data_linked_symbols_words_and_modification_surface_are_exact(self):
        f=self.data_fixture();original=self.data_image(f);linked=self.linked_data_image(f,original)
        calls,_,targets,data=self.data_original_bindings(f,original)
        self.assertEqual(profile.linked_bytes(original,linked,A,calls,targets,data_relocations=data),f['data'])
        for change in ('word','outside','call','object_type','object_address','object_binding','object_section',
                       'extra_object','undefined','relocations','text_extent','addend'):
            bad=copy.deepcopy(linked);records=copy.deepcopy(data)
            if change in ('word','outside','call'):
                body=bytearray(bad['text']);body[24 if change=='word' else 0 if change=='outside' else 8]^=1
                bad['text']=bytes(body)
            elif change=='object_type':bad['symbols'][-1]['type']=2
            elif change=='object_address':bad['symbols'][-1]['value']+=4
            elif change=='object_binding':bad['symbols'][-1]['bind']=0
            elif change=='object_section':bad['symbols'][-1]['section']=1
            elif change=='extra_object':bad['symbols'].append(dict(bad['symbols'][-1],name='extra'))
            elif change=='undefined':bad['symbols'][-1]['section']=0
            elif change=='relocations':bad['relocations']=[2]
            elif change=='text_extent':bad['text']+=b'\0\0'
            else:records[next(iter(records))]=('state',4)
            with self.subTest(change=change),self.assertRaises(ValueError):
                profile.linked_bytes(original,bad,A,calls,targets,data_relocations=records)

    def test_data_manifest_covers_only_reached_address_words_without_forgery(self):
        f=self.data_fixture()
        bads=[[],f['data_bindings'][:1],f['data_bindings']*2,
              [[0,'state',0],f['data_bindings'][1]],
              [[24,'state',4],f['data_bindings'][1]],
              [[24,'missing',0],f['data_bindings'][1]],
              [[24,'state',True],f['data_bindings'][1]],list(reversed(f['data_bindings']))]
        for records in bads:
            with self.subTest(records=records),self.assertRaises(ValueError):
                profile.verify(**dict(f,data_bindings=records),selector=profile.DATA_SELECTOR)
        for objects in (None,b'{}',b'{"state":"0x03002814","table":"0x030009E0"}'):
            with self.assertRaises(ValueError):profile.verify(**dict(f,data_mapping=objects),selector=profile.DATA_SELECTOR)
        # A forged binding to code is not an object identity, even with matching final bytes.
        bad=dict(f);body=bytearray(f['data']);struct.pack_into('<I',body,24,B)
        rom=bytearray(f['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        bad.update(data=bytes(body),rom=bytes(rom),data_mapping=b'{"state":"0x08011000","table":"0x030009E0"}')
        with self.assertRaises(ValueError):profile.verify(**bad,selector=profile.DATA_SELECTOR)
        # Move an actual reached load away: an ABS32 in an unreferenced word cannot qualify.
        bad=dict(f);body=bytearray(f['data']);struct.pack_into('<H',body,2,0x46C0)
        rom=bytearray(f['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        bad.update(data=bytes(body),rom=bytes(rom))
        with self.assertRaises(ValueError):profile.verify(**bad,selector=profile.DATA_SELECTOR)

    @contextmanager
    def data_build_fixture(self):
        scratch=Path(__file__).resolve().parents[1]/'build/tests';scratch.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='addressed_data_',dir=scratch) as directory:
            root=Path(directory);f=self.data_fixture();original=self.data_image(f);linked=self.linked_data_image(f,original)
            for sub in ('src','include','config','symbols','docs/match'):(root/sub).mkdir(parents=True,exist_ok=True)
            (root/'src/08010000.c').write_text('/* synthetic fingerprint token; never compiled */\n')
            (root/'config/functions.json').write_bytes(f['mapping']);(root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_bytes(f['data_mapping']);rom=root/'baserom.bin';rom.write_bytes(f['rom'])
            commands=[]
            class Runner:
                def __init__(self,*args,**kwargs):self.root=kwargs['root']
                @contextmanager
                def workspace(self):
                    path=self.root/'workspace';path.mkdir();yield str(path)
                def read_binary(self,path):
                    return f['data'] if path.endswith('f.linked.bin') else b'synthetic ELF or assembly boundary'
                def write_text(self,path,value):Path(path).write_text(value)
                def sh(self,command):commands.append(command)
            with (patch.dict(os.environ,FFTA_ROM=str(rom)),patch.object(match,'Runner',Runner),
                  patch.object(match,'compile_object',return_value=(b'synthetic originalELF',None,original)) as compiler,
                  patch.object(match,'elf_image',return_value=linked),
                  patch.object(match,'_run_replay_process',return_value=None),
                  patch.object(match,'plausibility_result',return_value=([],None))):
                yield root,f,commands,compiler

    def test_data_fresh_build_replays_original_link_and_detects_input_mutations(self):
        with self.data_build_fixture() as (root,f,commands,compiler):
            result=profile.build(root,A,selector=profile.DATA_SELECTOR)
            self.assertEqual(result['manifest']['data_bindings'],f['data_bindings'])
            self.assertEqual(result['runtime'],profile.runtime_fingerprint())
            self.assertEqual(len(commands),3)
            self.assertIn('--no-relax',commands[1])
            self.assertIn('--orphan-handling=error',commands[1])
            report=profile.render(result);compiler.reset_mock()
            self.assertTrue(evidence.report_matches(report,root,A));compiler.assert_called_once()
            self.assertIn('identity only',report)
            for relative in ('config/data_symbols.json','config/functions.json','symbols/functions.txt',
                             'src/08010000.c','baserom.bin'):
                p=root/relative;old=p.read_bytes();p.write_bytes(old+b' ')
                try:self.assertFalse(evidence.report_matches(report,root,A))
                finally:p.write_bytes(old)
            p=root/'include/new.h';p.write_text('/* stale */\n')
            try:self.assertFalse(evidence.report_matches(report,root,A))
            finally:p.unlink()
            with patch.object(profile,'runtime_fingerprint',return_value={'stale':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            with patch.object(profile,'toolchain_fingerprint',return_value=[]):
                self.assertFalse(evidence.report_matches(report,root,A))
            forged=copy.deepcopy(result);forged['manifest']['data_bindings'][0][2]=4
            self.assertFalse(evidence.report_matches(profile.render(forged),root,A))
            forged=copy.deepcopy(result);forged['manifest']['producer_source_sha256']['match.py']='0'*64
            self.assertFalse(evidence.report_matches(profile.render(forged),root,A))
            objects=root/'config/data_symbols.json';old=objects.read_bytes()
            def mutation(*args,**kwargs):objects.write_bytes(old+b' ')
            with patch.object(match,'_run_replay_process',side_effect=mutation):
                try:
                    with self.assertRaises(ValueError):profile.build(root,A,selector=profile.DATA_SELECTOR)
                finally:objects.write_bytes(old)
            with patch.object(match,'plausibility_result',return_value=(['implausible'],None)):
                with self.assertRaises(ValueError):profile.build(root,A,selector=profile.DATA_SELECTOR)
            pins=result['manifest']['producer_source_sha256']
            for snapshots in ([pins,pins,{'changed':True}],[pins,{'changed':True},pins]):
                with patch.object(profile,'data_producer_fingerprint',side_effect=snapshots):
                    with self.assertRaises(ValueError):profile.build(root,A,selector=profile.DATA_SELECTOR)

    def test_data_explicit_CLI_status_publisher_roundtrip_and_selector_isolation(self):
        with self.data_build_fixture() as (root,f,commands,compiler):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                 '--addressed-signed-runtime-profile',profile.DATA_SELECTOR,f'{A:08X}']),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report=(root/'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report),profile.DATA_SELECTOR)
            self.assertTrue(evidence.report_matches(report,root,A))
            self.assertEqual(status.collect(str(root),verify=False)[1],1)
            with patch.object(status.subprocess,'run',return_value=type('R',(),{
                 'returncode':0,'stdout':f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n','stderr':''})()) as run:
                self.assertEqual(status.collect(str(root),verify=True)[1],1)
                self.assertIn(profile.DATA_SELECTOR,run.call_args[0][0])
            with redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_reports(str(root)))
                with patch.object(push,'run',return_value=(0,'up to date')) as gate:
                    self.assertTrue(push.check_matches(str(root)))
                    self.assertIn('--verify',gate.call_args[0][0])
            self.assertFalse(evidence.report_matches(report.replace(profile.DATA_SELECTOR,profile.SELECTOR),root,A))
            self.assertFalse(evidence.report_matches(report+'* verification: `other`\n',root,A))
            for option,value in [('--signed-runtime-profile',match.signed_divmod.SELECTOR),
                                 ('--function-address-profile',match.function_thunk.SELECTOR),('--mode','arm')]:
                with (patch.object(profile,'build',side_effect=AssertionError('must not build')),
                      patch.object(sys,'argv',['match.py','--root',str(root),
                          '--addressed-signed-runtime-profile',profile.DATA_SELECTOR,option,value,f'{A:08X}'])):
                    with self.assertRaises(ValueError):match.main()


if __name__=='__main__':unittest.main()
