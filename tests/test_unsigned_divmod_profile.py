"""Portable synthetic composition tests: no approved ROM or compiler is used."""
import argparse
import copy
from contextlib import contextmanager, redirect_stdout
import hashlib
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

STAGED = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get('FFTA_TEST_PRODUCTION_KIT', STAGED))
sys.path[:0] = [str(STAGED/'tools'), str(PRODUCTION/'tools')]
import match
import report_fixtures
import match_evidence as evidence
import owner_admission_profile as owner
import unsigned_divmod_profile as profile
import status
import push

A = 0x08011000
DEFAULT = (0xB530, 0x1C05, 0x1C0C, 0x1C20, 0x210A, 'q', 0x8028,
           0x1C20, 0x210A, 'm', 0x8068, 0xBC30, 0xBC01, 0x4700)


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))


def indexes(rows):
    return ((json.dumps(rows, indent=2)+'\n').encode(), ''.join(
        f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
        for row in rows).encode())


def elf_bytes(fixture, linked=False):
    """Construct actual ELF32 containers, not a compiler or assembly invocation."""
    body = bytearray(fixture['data'])
    strings = b'\0'; symbols = bytearray(b'\0'*16); rel = bytearray()
    def symbol(name, value, size, kind, section):
        nonlocal strings
        offset = len(strings); strings += name.encode()+b'\0'
        symbols.extend(struct.pack('<IIIBBH', offset, value, size, 16|kind, 0, section))
    symbol(f'func_{A:08X}', (A if linked else 0)|1, len(body), 2, 1)
    for number, (site, name) in enumerate(fixture['bindings'].items(), 2):
        target = profile.OPERATIONS[name]
        symbol(name, target|1 if linked else 0, 0, 2 if linked else 0, 0xFFF1 if linked else 0)
        if not linked:
            body[site-A:site-A+4] = bl(site, site)
            rel += struct.pack('<II', site-A, (number<<8)|10)
    names = b'\0.text\0.symtab\0.strtab\0.rel.text\0.shstrtab\0'
    payloads = [b'', bytes(body), bytes(symbols), strings, b'' if linked else bytes(rel), names]
    sections = [(0,)*10]
    output = bytearray(b'\0'*52)
    specs = [(1,1,6,A if linked else 0,0,0,2,0), (7,2,0,0,3,1,4,16),
             (15,3,0,0,0,0,1,0), (23,9,0,0,2,1,4,8), (33,3,0,0,0,0,1,0)]
    for payload, spec in zip(payloads[1:], specs):
        output += b'\0'*(-len(output)%4)
        pos = len(output); output += payload
        name,kind,flags,address,link,info,align,size = spec
        sections.append((name,kind,flags,address,pos,len(payload),link,info,align,size))
    output += b'\0'*(-len(output)%4); section_offset = len(output)
    for section in sections: output += struct.pack('<10I', *section)
    output[:16] = b'\x7fELF\x01\x01\x01'+b'\0'*9
    struct.pack_into('<HHIIIIIHHHHHH', output, 16, 2 if linked else 1, 40, 1,
                     A|1 if linked else 0, 0, section_offset, 0, 52, 0, 0, 40, len(sections), 5)
    return bytes(output)


class UnsignedDivmodCompositionTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH']); scratch.mkdir(parents=True, exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix=self._testMethodName+'_', dir=scratch)
        self.addCleanup(temp.cleanup); self.root = Path(temp.name)
        for relative in ('src','include','config','symbols','build','docs/match'):
            (self.root/relative).mkdir(parents=True)
        self.runtime = bytearray(0x142BE8)
        self.runtime[0x14274C:0x14274E] = bytes.fromhex('7047')
        self.runtime[0x142B20:0x142B24] = bl(0x08142B20, 0x0814274C)
        self.runtime[0x142BE0:0x142BE4] = bl(0x08142BE0, 0x0814274C)
        self.ids = {}
        for module, field in ((match,'UDIVSI3_IDENTITIES'), (profile.remainder,'IDENTITIES')):
            identities = tuple((lo,hi,hashlib.sha256(self.runtime[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                               for lo,hi,_ in getattr(module,field))
            change = patch.object(module, field, identities); change.start(); self.addCleanup(change.stop)
            self.ids.update((lo,(hi,digest)) for lo,hi,digest in identities)
        # Only the old runtime interpreter boundary is mocked. Real canonical
        # identity/index checks and all new caller/ELF/frame/CFG/report code run.
        runtime = patch.object(profile.inventory, 'runtime_closure', side_effect=self.runtime_closure)
        runtime.start(); self.addCleanup(runtime.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)

    def runtime_closure(self, rom, mapping, index):
        match.verify_udivsi3_identity(rom, mapping)
        profile.remainder.verify_identity(rom, mapping)
        from software_double_profile import indices, span_record
        entries, rows = indices(mapping,index)
        for lo,(hi,_) in self.ids.items(): span_record(lo,hi,entries,rows,rom)
        return ([[lo, {'synthetic_runtime_boundary':True}] for lo in sorted(self.ids)],
                [[lo, {'synthetic_frame_boundary':True}] for lo in sorted(self.ids)])

    def fixture(self, tokens=DEFAULT):
        data, calls, bindings = bytearray(), {}, {}
        for token in tokens:
            if type(token) is int: data += struct.pack('<H',token)
            else:
                name = '__udivsi3' if token=='q' else '__umodsi3'
                site = A+len(data); target = profile.OPERATIONS[name]
                data += bl(site,target); calls[site]=target; bindings[site]=name
        rows = [{'rom':f'0x{A:08X}','end':f'0x{A+len(data):08X}','mode':'thumb','instrs':0}]
        rows += [{'rom':f'0x{lo:08X}','end':f'0x{hi:08X}','mode':'thumb','instrs':(hi-lo)//2}
                 for lo,(hi,_) in sorted(self.ids.items())]
        mapping,_ = indexes(rows)
        rows[0]['instrs'] = owner.refine(bytes(data),A,mapping)['instrs']
        mapping,index = indexes(rows)
        rom = bytearray(self.runtime); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(data=bytes(data),address=A,rom=bytes(rom),mapping=mapping,index=index,calls=calls,bindings=bindings)

    def bind(self, f, original=None, selector=profile.SELECTOR, **changes):
        options = dict(udivsi3_bindings={},umodsi3_bindings={},unsigned_runtime_profile=selector)
        options.update(changes)
        return match.call_bindings(original or match.elf_image(elf_bytes(f)), f'func_{A:08X}',A,
            f['mapping'],len(f['rom']),f['rom'],**options),options

    @contextmanager
    def build_fixture(self):
        f=self.fixture(); raw=elf_bytes(f); linked=elf_bytes(f,True); commands=[]
        (self.root/f'src/{A:08X}.c').write_text('/* synthetic source token, never compiled */\n')
        (self.root/'include/types.h').write_text('/* synthetic header */\n')
        for relative,data in (('config/functions.json',f['mapping']),('symbols/functions.txt',f['index']),
                              ('config/data_symbols.json',b'{}\n'),('baserom.bin',f['rom'])):
            (self.root/relative).write_bytes(data)
        class Runner:
            def __init__(this,*args,**kwargs): this.root=kwargs['root']
            @contextmanager
            def workspace(this):
                path=this.root/'workspace';path.mkdir();yield str(path)
            def read_binary(this,path):
                if path.endswith('f.linked.bin'): return f['data']
                if path.endswith('f.elf'): return linked
                return b'synthetic assembly boundary\n'
            def write_text(this,path,value): Path(path).write_text(value)
            def sh(this,command): commands.append(command)
        with (patch.dict(os.environ,FFTA_ROM=str(self.root/'baserom.bin')),
              patch.object(match,'Runner',Runner),
              patch.object(match,'compile_object',return_value=(raw,f['data'],match.elf_image(raw))) as compiler,
              patch.object(match,'_run_replay_process',return_value=None),
              patch.object(match,'plausibility_result',return_value=([],None))):
            yield f,commands,compiler

    def test_01_complete_unsigned_composition_and_ordered_memory_effects(self):
        f=self.fixture(); manifest,instructions=profile.verify(**f)
        self.assertEqual(manifest['divisors'],[[10,10],[20,10]])
        self.assertEqual([ins.mnemonic for ins in instructions].count('strh'),2)
        self.assertEqual(manifest['unsigned_runtime_inventory']['frame']['preserved'],'r4-r11,sp,entry-lr')
        self.assertEqual(manifest['runtime_numeric_return_facts'],[])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        # Both orders are allowed, while the two exact identities stay distinct.
        reverse = tuple('m' if t=='q' else 'q' if t=='m' else t for t in DEFAULT)
        self.assertEqual(len(profile.verify(**self.fixture(reverse))[1]),len(instructions))

    def test_02_divisor_clobber_join_and_unsigned_identities_fail_closed(self):
        variants=[tuple(0x2109 if t==0x210A else t for t in DEFAULT),
                  tuple(0x2100 if t==0x210A else t for t in DEFAULT),
                  (0xB510,0x210A,'q','m',0xBC10,0xBC01,0x4700),
                  (0xB510,0x210A,0x2A00,0xD000,0x2109,'q',0x210A,'m',0xBC10,0xBC01,0x4700)]
        for tokens in variants:
            with self.subTest(tokens=tokens),self.assertRaises(ValueError): profile.verify(**self.fixture(tokens))
        f=self.fixture()
        for binding in ({}, {next(iter(f['calls'])):'__udivsi3'},
                        {s:'__modsi3' if n=='__umodsi3' else n for s,n in f['bindings'].items()}):
            with self.subTest(binding=binding),self.assertRaises(ValueError):
                profile.verify(**dict(f,bindings=binding))
        calls=dict(f['calls']);calls[next(reversed(calls))]=0x08142950
        with self.assertRaises(ValueError):profile.verify(**dict(f,calls=calls))

    def test_03_frame_CFG_and_stack_escape_guards_remain(self):
        good=(0xB510,0x210A,'q',0x210A,'m')
        variants=[(0xB510,0xB081,0x210A,'q',0x210A,'m',0xB001,0xBC10,0xBC01,0x4700),
                  (0xB510,0xA800,0x210A,'q',0x210A,'m',0xBC10,0xBC01,0x4700),
                  (0xB510,0x9802,0x210A,'q',0x210A,'m',0xBC10,0xBC01,0x4700),
                  good+(0x2A00,0xD1FD,0xBC10,0xBC01,0x4700),
                  good+(0xBC10,0x2400,0xBC01,0x4700), good+(0xBC10,0xBC01,0x4770),
                  good+(0xBC10,0xBC01,0x4700,0x1234)]
        for tokens in variants:
            with self.subTest(tokens=tokens),self.assertRaises(ValueError):profile.verify(**self.fixture(tokens))

    def test_04_original_ET_REL_and_legacy_mixed_rejection(self):
        f=self.fixture(); original=match.elf_image(elf_bytes(f))
        (calls,targets,literals),options=self.bind(f,original)
        self.assertEqual(calls,f['calls']);self.assertEqual(targets,profile.OPERATIONS);self.assertFalse(literals)
        with self.assertRaisesRegex(ValueError,'excludes other runtime'):self.bind(f,original,selector=None)
        for field,value in [('name','func_08142B28'),('value',2),('type',1),('section',1),('bind',0)]:
            bad=copy.deepcopy(original);bad['symbols'][-1][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):self.bind(f,bad)
        bad=copy.deepcopy(original);body=bytearray(bad['text']);body[10:14]=bl(A+10,A+12);bad['text']=bytes(body)
        with self.assertRaisesRegex(ValueError,'noncanonical addend'):self.bind(f,bad)
        for changes in ({'function_thunks':True}, {'data_mapping':b'{}'},
                        {'signed_runtime_profile':'numeric-divmod-v1'}, {'unsigned_runtime_profile':True}):
            with self.subTest(changes=changes),self.assertRaises(ValueError):self.bind(f,**changes)

    def test_05_resident_whole_ELF_link_surface_and_binding_seals(self):
        f=self.fixture(); original=match.elf_image(elf_bytes(f)); linked=match.elf_image(elf_bytes(f,True))
        (calls,targets,literals),options=self.bind(f,original)
        def validate(image,**changes):
            opts=dict(options);opts.update(changes)
            return match.linked_function_bytes(original,image,f'func_{A:08X}',A,calls,targets,literals,**opts)
        self.assertEqual(validate(linked),f['data'])
        for change in ('outside','target','size','undefined','mode','object','relocation','extra','missing_binding'):
            image=copy.deepcopy(linked);opts={}
            if change=='outside':image['text']=bytes([image['text'][0]^1])+image['text'][1:]
            elif change=='target':image['symbols'][-1]['value']+=2
            elif change=='size':image['symbols'][1]['size']-=2
            elif change=='undefined':image['symbols'][-1]['section']=0
            elif change=='mode':image['symbols'][1]['value']&=~1
            elif change=='object':image['symbols'][-1]['type']=1
            elif change=='relocation':image['relocations']=[4]
            elif change=='extra':image['sections'][3]=tuple([0,1,2,0,0,4,0,0,4,0])
            elif change=='missing_binding':opts={'umodsi3_bindings':{}}
            with self.subTest(change=change),self.assertRaises(ValueError):validate(image,**opts)

    def test_06_complete_owner_helper_dependencies_and_manifest_tamper(self):
        f=self.fixture();manifest,_=profile.verify(**f)
        mutations=[]
        for key,value in [('divisors',[[10,9],[20,10]]),('runtime_numeric_return_facts',['invented'])]:
            bad=copy.deepcopy(manifest);bad[key]=value;mutations.append(bad)
        bad=copy.deepcopy(manifest);bad['producer_source_sha256']['match.py']='0'*64;mutations.append(bad)
        bad=copy.deepcopy(manifest);bad['unsigned_runtime_inventory']['frame']['preserved']='assumed';mutations.append(bad)
        for changed in mutations:
            with self.subTest(manifest=changed),self.assertRaisesRegex(ValueError,'manifest differs'):
                profile.verify(**f,manifest=changed)
        for changed in ('root_bytes','runtime_bytes','duplicate','overlap','count','index'):
            bad=dict(f);rows=json.loads(f['mapping'])
            if changed.endswith('bytes'):
                rom=bytearray(f['rom']);rom[(A if changed=='root_bytes' else 0x08142B28)-match.ROM_BASE]^=1;bad['rom']=bytes(rom)
            elif changed=='duplicate':rows.append(rows[0].copy())
            elif changed=='overlap':rows.append(dict(rows[0],rom=f'0x{A+2:08X}'))
            elif changed=='count':rows[0]['instrs']+=1
            elif changed=='index':bad['index']=f['index'].replace(f'{A+len(f["data"]):08X}'.encode(),b'080110FF')
            if changed in ('duplicate','overlap','count'):bad['mapping'],bad['index']=indexes(rows)
            with self.subTest(changed=changed),self.assertRaises(ValueError):profile.verify(**bad)

    def test_07_mocked_native_CLI_fresh_report_and_input_mutations(self):
        with self.build_fixture() as (f,commands,compiler):
            argv=['match.py','--root',str(self.root),'--unsigned-runtime-profile',profile.SELECTOR,f'{A:08X}']
            with patch.object(sys,'argv',argv),redirect_stdout(io.StringIO()):self.assertEqual(match.main(),0)
            report=(self.root/f'docs/match/{A:08X}.md').read_text()
            self.assertTrue(evidence.report_matches(report,self.root,A))
            self.assertEqual(len(commands),6)
            self.assertIn('--no-relax',commands[1]);self.assertIn('--orphan-handling=error',commands[1])
            for relative in ('src/08011000.c','include/types.h','config/functions.json',
                             'symbols/functions.txt','config/data_symbols.json','baserom.bin'):
                path=self.root/relative;before=path.read_bytes();path.write_bytes(before+b' ')
                try:self.assertFalse(evidence.report_matches(report,self.root,A),relative)
                finally:path.write_bytes(before)
            with patch.object(profile,'producers',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,self.root,A))
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,self.root,A))
            with patch.object(profile,'toolchain_fingerprint',return_value=[]):
                self.assertFalse(evidence.report_matches(report,self.root,A))
            target=self.root/'config/data_symbols.json';before=target.read_bytes()
            def mutate(*args,**kwargs):target.write_bytes(before+b' ')
            with patch.object(match,'_run_replay_process',side_effect=mutate):
                try:
                    with self.assertRaisesRegex(ValueError,'changed during replay'):profile.build(self.root,A)
                finally:target.write_bytes(before)
            with patch.object(match,'plausibility_result',return_value=(['implausible'],None)):
                with self.assertRaisesRegex(ValueError,'implausible'):profile.build(self.root,A)

    def test_08_mixed_CLI_and_malformed_report_never_rebuild(self):
        with self.build_fixture() as (f,commands,compiler):
            report=profile.render(profile.build(self.root,A))
            for suffix in (['--signed-runtime-profile','numeric-divmod-v1'],
                           ['--function-address-profile','canonical-thunks-v1'],
                           ['--owner-runtime-profile','restoring-owner-runtime-v1'],['--mode','arm']):
                argv=['match.py','--root',str(self.root),'--unsigned-runtime-profile',profile.SELECTOR,f'{A:08X}']+suffix
                with self.subTest(suffix=suffix),patch.object(sys,'argv',argv),patch.object(profile,'build') as build:
                    with self.assertRaises(ValueError):match.main()
                    build.assert_not_called()
            variants=[report.replace(profile.SELECTOR,'unsigned-divmod-ten-v2'),
                report+f'* unsigned runtime: {profile.SELECTOR}\n',
                report+'* verification: `elf-symbol-cfg-leaf-v2`\n',
                report+'* signed runtime: numeric-divmod-v1\n',report.replace('* unsigned runtime evidence: `','* unsigned runtime evidence: `{"duplicate":1,')]
            for changed in variants:
                with self.subTest(report=changed[:100]),patch.object(profile,'build',side_effect=AssertionError('no rebuild')) as build:
                    self.assertFalse(evidence.report_matches(changed,self.root,A));build.assert_not_called()

    def test_09_status_and_publisher_delegate_exact_explicit_selector(self):
        with self.build_fixture() as (f,commands,compiler):
            report=report_fixtures.carried(profile.render(profile.build(self.root,A)),self.root,A);path=self.root/f'docs/match/{A:08X}.md';path.write_text(report)
            self.assertEqual(status.collect(str(self.root),verify=False)[:4],(4,1,346,32))
            output=f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n'
            for write in (False,True):
                def run(command,**kwargs):
                    self.assertIn('--unsigned-runtime-profile',command);self.assertIn(profile.SELECTOR,command)
                    self.assertEqual('--no-write' in command,not write)
                    return subprocess.CompletedProcess(command,0,output,'')
                with self.subTest(write=write),patch.object(status.subprocess,'run',side_effect=run) as invoke:
                    self.assertEqual(status.collect(str(self.root),verify=True,write_reports=write)[1],1)
                    invoke.assert_called_once()
            with patch.object(push,'run',return_value=(0,'identical\nup to date')) as gate,redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_matches(str(self.root)));gate.assert_called_once()
                self.assertIn('--verify',gate.call_args[0][0]);self.assertIn('--check',gate.call_args[0][0])

    def test_10_stale_report_or_failed_process_cannot_count(self):
        with self.build_fixture() as (f,commands,compiler):
            report=report_fixtures.carried(profile.render(profile.build(self.root,A)),self.root,A);path=self.root/f'docs/match/{A:08X}.md';path.write_text(report)
            def invoke(command,**kwargs):
                path.write_text(report.replace('structural unsigned','forged unsigned'))
                return subprocess.CompletedProcess(command,0,f'extent    {len(f["data"])} bytes\nverdict MATCH - byte identical\n','')
            with patch.object(status.subprocess,'run',side_effect=invoke):
                self.assertEqual(status.collect(str(self.root),verify=True)[1],0)
            path.write_text(report)
            with patch.object(status.subprocess,'run',return_value=subprocess.CompletedProcess([],1,'verdict MATCH - byte identical\n','failure')):
                self.assertEqual(status.collect(str(self.root),verify=True)[1],0)
            path.write_text(report+'* owner runtime: restoring-owner-runtime-v1\n')
            with patch.object(status.subprocess,'run') as native:
                self.assertEqual(status.collect(str(self.root),verify=True)[1],0);native.assert_not_called()


if __name__=='__main__':unittest.main()
