"""Synthetic source-admission lifecycle; no compiler or original ROM fixtures."""
import argparse
from contextlib import contextmanager
import copy
import hashlib
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
sys.path[:0] = [str(STAGED/'tools'), str(PRODUCTION/'tools'), str(PRODUCTION/'tests')]
import match
import match_evidence as evidence
import private_float_pack_admission_profile as admission
import private_float_pack_effects_inventory as inventory
import software_float_profile as runtime
import test_private_float_pack_effects_inventory as fixtures

ADDRESS, UNPACK, PACK = fixtures.ADDRESS, fixtures.UNPACK, fixtures.PACK
words, call = fixtures.words, fixtures.call


def arguments(**changes):
    values = dict(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
        objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS,
        mode='thumb', control_flow_profile='ordinary', label='', wsl='Ubuntu',
        wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=admission.SELECTOR,
        emit=None, no_write=True)
    values.update(changes)
    return argparse.Namespace(**values)


def elf_pair(body):
    names = [f'func_{ADDRESS:08X}', f'func_{UNPACK:08X}', f'func_{PACK:08X}']
    symbols = [dict(name=names[0], type=2, bind=1, section=1, value=1, size=len(body))]
    symbols += [dict(name=name, type=2, bind=1, section=0, value=0, size=0) for name in names[1:]]
    original = bytearray(body)
    sites = (10, 28)
    for site in sites:
        original[site:site+4] = call(ADDRESS+site, ADDRESS+site)
    rels = b''.join(struct.pack('<II', site, number << 8 | 10)
                    for site, number in zip(sites, (1, 2)))
    image = dict(type=1, text_index=1, text=bytes(original), symbols=symbols,
        sections=[(0,)*10, (0,1,6,0,0,len(body),0,0,2,0), (0,9,0,0,0,len(rels),3,1,4,8)],
        symbol_tables={3:symbols}, relocations=[2], section_data=[b'',bytes(original),rels])
    linked = copy.deepcopy(image)
    linked.update(type=2, text=body, relocations=[])
    linked['sections'][1] = (0,1,6,ADDRESS,0,len(body),0,0,2,0)
    linked['symbols'][0]['value'] = ADDRESS | 1
    for symbol, target in zip(linked['symbols'][1:], (UNPACK, PACK)):
        symbol.update(value=target | 1, section=0xFFF1)
    return image, linked


class PrivateFloatPackAdmissionTests(unittest.TestCase):
    def fixture(self, **changes):
        return fixtures.PrivateFloatPackEffectsTests().fixture(**changes)

    @contextmanager
    def closure(self, fixture=None):
        selected = self.fixture() if fixture is None else fixture
        with patch.object(inventory, 'HELPERS', selected[-1]), \
                patch.object(runtime, 'ROM_SHA256', admission.sha(selected[1])):
            yield selected

    def verified(self, fixture=None, **changes):
        with self.closure(fixture) as (body, rom, _, mapping, index, _):
            calls = [[10, f'func_{UNPACK:08X}'], [28, f'func_{PACK:08X}']]
            return admission.verify(body, ADDRESS, rom, mapping, index, calls, **changes)

    @contextmanager
    def project(self, fixture=None):
        fixture = self.fixture() if fixture is None else fixture
        with tempfile.TemporaryDirectory(prefix='float_admission_test_', dir=os.environ['TMPDIR']) as path:
            root = Path(path)
            for name, data in {
                f'src/{ADDRESS:08X}.c': b'/* synthetic source-capture fixture; never compiled */\n',
                'include/types.h': b'/* synthetic header */\n',
                'config/functions.json': fixture[3], 'symbols/functions.txt': fixture[4],
                'config/data_symbols.json': b'{}', 'synthetic.rom': fixture[1],
            }.items():
                target = root/name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            with self.closure(fixture), patch.object(evidence, 'report_rom_path', return_value=root/'synthetic.rom'):
                yield root, fixture

    def result(self, root, fixture):
        manifest, instructions = self.verified(fixture)
        return dict(address=ADDRESS, body=fixture[0], manifest=manifest,
            source_sha256=evidence.source_fingerprint(root, ADDRESS),
            mapping_sha256=admission.sha(fixture[3]), index_sha256=admission.sha(fixture[4]),
            objects_sha256=admission.sha(b'{}'), rom_sha256=admission.sha(fixture[1]),
            instructions=len(instructions), toolchain=admission.toolchain_fingerprint(),
            runtime=admission.runtime_fingerprint(), original_elf=b'synthetic ET_REL',
            linked_elf=b'synthetic ET_EXEC')

    def test_closed_effects_unknown_contents_and_exact_manifest(self):
        # The synthetic unpack deliberately leaves exponent/fraction unwritten.
        base = self.fixture()
        unpack = words(0xB510,0x6802,0x600A,0x604A,0xBC10,0xBC01,0x4700)
        parts = {ADDRESS:base[0], UNPACK:unpack, PACK:base[1][PACK-fixtures.BASE:PACK-fixtures.BASE+18]}
        counts = {start:len(list(match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB).disasm(data,start)))
                  for start,data in parts.items()}
        rom, rows, mapping, index = fixtures.image(parts, counts)
        specs = tuple((name,(start,start+len(parts[start]),counts[start],admission.sha(parts[start])),bounds)
            for (name,_,bounds),start in zip(base[-1],(UNPACK,PACK)))
        fixture = parts[ADDRESS], rom, rows, mapping, index, specs
        manifest, instructions = self.verified(fixture)
        self.assertEqual(len(instructions),17)
        self.assertEqual(manifest['bindings'],[[10,f'func_{UNPACK:08X}'],[28,f'func_{PACK:08X}']])
        self.assertEqual(manifest['inventory']['helper_closure'][0]['native_proof']['argument_effects']['writes'],
                         [[1,0,4],[1,4,4]])
        self.assertEqual(manifest['inventory']['numeric_return_facts'],[])
        self.assertIn('initialized contents',manifest['contract'])
        self.assertFalse(manifest['inventory']['source_or_ELF_admission'])
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            self.verified(fixture,manifest={})
        with self.assertRaisesRegex(ValueError,'explicit selector'):
            self.verified(fixture,selector=inventory.SELECTOR)

    def test_original_relocations_closed_and_forged_surface_rejected(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,_ = elf_pair(body)
            calls, targets = admission.original_bindings(original,ADDRESS,rom,mapping,index)
            self.assertEqual(list(targets.values()),[UNPACK,PACK])
            self.assertEqual(calls,[[10,f'func_{UNPACK:08X}'],[28,f'func_{PACK:08X}']])
            def relocation(image,site=10,symbol=1,kind=10,position=0):
                data=bytearray(image['section_data'][2]);struct.pack_into('<II',data,position,site,symbol<<8|kind)
                image['section_data'][2]=bytes(data)
            cases = []
            for field,value in (('name','__unpack_alias'),('name',f'func_{UNPACK+2:08X}'),
                                ('name',f'func_{UNPACK|1:08X}'),('type',1),('bind',0),('value',1),('section',1)):
                image=copy.deepcopy(original);image['symbols'][1][field]=value;cases.append((field+str(value),image))
            for kind in (2,0,255):
                image=copy.deepcopy(original);relocation(image,kind=kind);cases.append(('kind'+str(kind),image))
            for site in (11,len(body)-2,12):
                image=copy.deepcopy(original);relocation(image,site=site);cases.append(('site'+str(site),image))
            image=copy.deepcopy(original);relocation(image,site=10,symbol=2,position=8);cases.append(('overlap',image))
            image=copy.deepcopy(original);relocation(image,symbol=2);cases.append(('repeated-pack',image))
            image=copy.deepcopy(original);image['symbols'].append(copy.deepcopy(image['symbols'][1]));cases.append(('duplicate',image))
            image=copy.deepcopy(original);image['relocations']=[];cases.append(('missing',image))
            image=copy.deepcopy(original);image['symbols'].append(dict(name='extra',type=0,bind=1,section=0,value=0,size=0));cases.append(('extra',image))
            image=copy.deepcopy(original);image['text']=image['text'][:10]+call(ADDRESS+10,ADDRESS+12)+image['text'][14:];cases.append(('addend',image))
            image=copy.deepcopy(original);image['type']=2;cases.append(('not-relocatable',image))
            image=copy.deepcopy(original);image['sections'][2]=(0,4,0,0,0,16,3,1,4,8);cases.append(('rela',image))
            image=copy.deepcopy(original);image['sections'][2]=(0,9,0,0,0,15,3,1,4,8);cases.append(('truncated-rel',image))
            for name,image in cases:
                with self.subTest(name=name),self.assertRaises(ValueError):
                    admission.original_bindings(image,ADDRESS,rom,mapping,index)

    def test_linked_whole_symbol_only_real_call_bytes_may_change(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked=elf_pair(body)
            calls,targets=admission.original_bindings(original,ADDRESS,rom,mapping,index)
            self.assertEqual(admission.linked_bytes(original,linked,ADDRESS,calls,targets),body)
            cases=[]
            for position,replacement in ((0,words(0xB510)),(10,call(ADDRESS+10,PACK)),(28,call(ADDRESS+28,UNPACK))):
                changed=copy.deepcopy(linked);changed['text']=body[:position]+replacement+body[position+len(replacement):]
                cases.append((str(position),changed))
            changed=copy.deepcopy(linked);changed['text']+=words(0x4770);changed['symbols'][0]['size']+=2;cases.append(('veneer',changed))
            changed=copy.deepcopy(linked);changed['symbols'][0]['size']-=2;cases.append(('short-symbol',changed))
            changed=copy.deepcopy(linked);changed['symbols'][0]['value']&=~1;cases.append(('arm',changed))
            changed=copy.deepcopy(linked);changed['relocations']=[2];cases.append(('relocations',changed))
            changed=copy.deepcopy(linked);changed['sections'].append((0,1,3,0,0,4,0,0,4,0));cases.append(('allocated-data',changed))
            changed=copy.deepcopy(linked);changed['symbols'].append(dict(name='local_helper',type=2,bind=0,section=1,value=ADDRESS|1,size=2));cases.append(('foreign-function',changed))
            for name,changed in cases:
                with self.subTest(name=name),self.assertRaises(ValueError):
                    admission.linked_bytes(original,changed,ADDRESS,calls,targets)

    def test_dependency_counts_owners_body_and_effect_receipts(self):
        fixture=self.fixture();body,rom,_,mapping,index,specs=fixture
        for key,value in (('end',f'0x{PACK+16:08X}'),('instrs',8),('mode','arm')):
            rows=json.loads(mapping);rows[2][key]=value
            changed=body,rom,rows,json.dumps(rows).encode(),index,specs
            with self.subTest(key=key),self.assertRaises(ValueError):self.verified(changed)
        rows=json.loads(mapping);rows.append(rows[-1])
        with self.assertRaises(ValueError):self.verified((body,rom,rows,json.dumps(rows).encode(),index,specs))
        with self.assertRaises(ValueError):self.verified((body,rom,fixture[2],mapping,index+index.splitlines(keepends=True)[-1],specs))
        changed=bytearray(rom);changed[PACK-fixtures.BASE]^=1
        with self.assertRaisesRegex(ValueError,'identity'):
            self.verified((body,bytes(changed),fixture[2],mapping,index,specs))
        prove=runtime.prove_runtime
        for field,value in (('schema','forged'),('complete',False),('body_sha256','0'*64),('missing',None)):
            def corrupt(*args,**kwargs):
                proof=prove(*args,**kwargs)
                if args[2]==PACK:
                    if field=='missing':proof.pop('argument_effects')
                    else:proof['argument_effects'][field]=value
                return proof
            with self.subTest(field=field),patch.object(runtime,'prove_runtime',side_effect=corrupt),self.assertRaises(ValueError):
                self.verified()
        with patch.object(runtime,'EDGES',((PACK+2,UNPACK),)),self.assertRaisesRegex(ValueError,'closed leaf'):
            self.verified()

    def test_live_local_bounds_return_provenance_and_unknown_dereference(self):
        base=self.fixture()[0]
        for opcode in (0xA805,0xA806):
            changed=base[:26]+words(opcode)+base[28:]
            with self.subTest(pack_pointer=opcode),self.assertRaises(ValueError):self.verified(self.fixture(caller=changed))
        for position,opcode in ((6,0xA806),(8,0xA905),(32,0xB004),(34,0xBC04)):
            changed=base[:position]+words(opcode)+base[position+2:]
            with self.subTest(position=position),self.assertRaises(ValueError):self.verified(self.fixture(caller=changed))
        for pack in (words(0x6800,0x6800,0x4770),words(0x6900,0x4770),
                     words(0x2100,0x6101,0x4770),words(0x1C04,0x4770)):
            with self.subTest(pack=pack.hex()),self.assertRaises(ValueError):self.verified(self.fixture(pack=pack))

    def test_default_reservations_public_aliases_and_fixed_selector_unchanged(self):
        for target in (0x08143A84,0x081439C8):
            with self.subTest(target=target),self.assertRaisesRegex(ValueError,'canonical versioned proof'):
                match.function_address_target(f'func_{target:08X}',[],ADDRESS,38,0x200000)
        self.assertNotIn('func_08143A84',runtime.OPERATIONS)
        self.assertNotIn('func_081439C8',runtime.OPERATIONS)
        with self.closure() as (body,rom,_,mapping,index,_):
            original,_=elf_pair(body)
            original['symbols'][1]['name']='__unpack_f'
            with self.assertRaises(ValueError):admission.original_bindings(original,ADDRESS,rom,mapping,index)
        for field,value in (('flags','-O0'),('cc','other-compiler'),('linker','other-linker')):
            with self.subTest(field=field),self.assertRaises(ValueError):
                admission.fixed_configuration(arguments(**{field:value}))
        for field,value in (('mode','arm'),('control_flow_profile','inert-spin-v1'),('label','alias'),
                            ('wsl','other'),('owner_runtime_profile',inventory.SELECTOR),
                            ('addressed_signed_runtime_profile','addressed-signed-runtime-v1'),
                            ('function_address_profile','canonical-thunks-v1'),('switch_data_profile','u16-scalars-v1')):
            with self.subTest(field=field),patch.object(admission,'build',side_effect=AssertionError('must not build')),self.assertRaises(ValueError):
                admission.issue(Path('.'),ADDRESS,arguments(**{field:value}))

    def test_cli_dispatch_is_explicit_and_other_profiles_still_route(self):
        with patch.object(sys,'argv',['match.py','--root',str(STAGED),'--owner-runtime-profile',admission.SELECTOR,f'{ADDRESS:08X}']), \
                patch.object(admission,'issue',return_value=0) as issue:
            self.assertEqual(match.main(),0)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,admission.SELECTOR)
        import owner_admission_profile as owner
        with patch.object(sys,'argv',['match.py','--root',str(STAGED),'--owner-runtime-profile',owner.SELECTOR,f'{ADDRESS:08X}']), \
                patch.object(owner,'issue',return_value=7) as legacy,patch.object(admission,'issue',side_effect=AssertionError('wrong route')):
            self.assertEqual(match.main(),7)
            self.assertTrue(legacy.called)

    def fake_native(self,root,fixture,*,findings=False,mutate=None):
        original,linked=elf_pair(fixture[0]);commands=[];written={}
        class Runner:
            def __init__(self,*args,**kwargs):pass
            @contextmanager
            def workspace(self):yield str(root/'synthetic-workspace')
            def write_text(self,path,value):written[Path(path).name]=value
            def sh(self,command):commands.append(command)
            def read_binary(self,path):return b'synthetic ET_EXEC'
        def plausible(command,cwd,timeout):
            if mutate:mutate(root)
            records=[dict(file='synthetic.c',rule='fixture',severity='error',message='fixture',line=1)] if findings else []
            payload=dict(findings=records,total=len(records),addr=f'0x{ADDRESS:08X}',hand_asm_allowed=False,allow_entry=None)
            return subprocess.CompletedProcess(command,int(findings),json.dumps(payload),'')
        @contextmanager
        def mocks():
            with patch.object(match,'Runner',Runner),patch.object(match,'compile_object',return_value=(b'synthetic ET_REL',b'',original)), \
                    patch.object(match,'elf_image',return_value=linked),patch.object(match,'_run_replay_process',side_effect=plausible):
                yield commands,written
        return mocks()

    def test_real_build_relocation_inventory_and_plausibility_pipeline(self):
        with self.project() as (root,fixture),self.fake_native(root,fixture) as (commands,written):
            result=admission.build(root,ADDRESS)
            self.assertEqual(result['body'],fixture[0]);self.assertEqual(result['instructions'],17)
            self.assertEqual(result['original_elf'],b'synthetic ET_REL')
            self.assertEqual(result['linked_elf'],b'synthetic ET_EXEC')
            self.assertEqual(len(commands),2)
            self.assertIn('--no-undefined --no-relax --orphan-handling=error',commands[1])
            self.assertIn(f'.thumb_set func_{UNPACK:08X}',written['f.known.s'])
            self.assertIn('ASSERT(SIZEOF(.unexpected)==0',written['f.ld'])
            self.assertEqual(list((root/'build').iterdir()),[])

    def test_build_rejects_plausibility_capture_change_and_live_map_change(self):
        for reason,options in (('plausibility',dict(findings=True)),
                ('source',dict(mutate=lambda root:(root/f'src/{ADDRESS:08X}.c').write_text('changed source'))),
                ('map',dict(mutate=lambda root:(root/'config/data_symbols.json').write_text('{"other":"0x02000000"}')))):
            with self.subTest(reason=reason),self.project() as (root,fixture),self.fake_native(root,fixture,**options),self.assertRaises(ValueError):
                admission.build(root,ADDRESS)

    def test_canonical_report_rebuild_route_and_stale_input_rejection(self):
        with self.project() as (root,fixture):
            result=self.result(root,fixture);report=admission.render(result)
            with patch.object(admission,'build',return_value=result) as rebuild:
                self.assertTrue(evidence.report_matches(report,root,ADDRESS))
                self.assertEqual(admission.text(rebuild.call_args.kwargs['expected']),admission.text(result['manifest']))
            for relative in (f'src/{ADDRESS:08X}.c','include/types.h','config/functions.json',
                             'symbols/functions.txt','config/data_symbols.json','synthetic.rom'):
                path=root/relative;old=path.read_bytes();path.write_bytes(old+b' ')
                try:
                    with self.subTest(stale=relative),patch.object(admission,'build',side_effect=AssertionError('stale must not compile')):
                        self.assertFalse(evidence.report_matches(report,root,ADDRESS))
                finally:path.write_bytes(old)
            for field in ('toolchain','runtime'):
                with self.subTest(stale=field),patch.object(admission,field+'_fingerprint',return_value={}), \
                        patch.object(admission,'build',side_effect=AssertionError('stale must not compile')):
                    self.assertFalse(evidence.report_matches(report,root,ADDRESS))
            with patch.object(admission,'producer_fingerprint',return_value={}),patch.object(admission,'build',side_effect=AssertionError('stale must not compile')):
                self.assertFalse(evidence.report_matches(report,root,ADDRESS))
            with patch.object(admission,'build',side_effect=ValueError('fresh helper/source proof differs')):
                self.assertFalse(evidence.report_matches(report,root,ADDRESS))

    def test_reports_fail_closed_for_mixed_duplicate_forged_and_recursive_evidence(self):
        with self.project() as (root,fixture):
            result=self.result(root,fixture);report=admission.render(result)
            encoded=admission.text({key:value for key,value in result.items() if key not in ('body','original_elf','linked_elf')})
            evidence_line=next(line for line in report.splitlines() if line.startswith('* private float pack evidence:'))
            variants=[report+'* verification: `elf-symbol-cfg-leaf-v2`\n',
                report+f'* private float pack: `{admission.SELECTOR}`\n',report+evidence_line+'\n',
                report.replace(admission.SCHEMA,inventory.SCHEMA),
                report.replace('**MATCH - byte identical**','**NON-MATCH**'),
                report.replace('* compiled : `','* compiled : `00'),
                report.replace('"address":'+str(ADDRESS),'"address":'+str(ADDRESS)+',"address":'+str(ADDRESS)),
                report.replace('"address":'+str(ADDRESS),'"address": '+str(ADDRESS)),
                report.replace(admission.SELECTOR,'other-selector')]
            for number,changed in enumerate(variants):
                with self.subTest(number=number),patch.object(admission,'build',return_value=result):
                    self.assertFalse(evidence.report_matches(changed,root,ADDRESS))
            def recurse(*args,**kwargs):
                self.assertFalse(evidence.report_matches(report,root,ADDRESS))
                return result
            with patch.object(admission,'build',side_effect=recurse):
                self.assertTrue(evidence.report_matches(report,root,ADDRESS))
            self.assertFalse(admission._replay.get())

    def test_issue_and_fresh_report_recompile_use_real_build_and_reject_changed_plausibility(self):
        with self.project() as (root,fixture),self.fake_native(root,fixture) as (commands,_):
            with patch('builtins.print'):
                self.assertEqual(admission.issue(root,ADDRESS,arguments(no_write=False,emit='build/verified.bin')),0)
            report=(root/f'docs/match/{ADDRESS:08X}.md').read_text()
            self.assertEqual((root/'build/verified.bin').read_bytes(),fixture[0])
            self.assertEqual(len(commands),2)
            self.assertTrue(evidence.report_matches(report,root,ADDRESS))
            self.assertEqual(len(commands),4)
            self.assertIn('"original_elf_sha256":',report)
            self.assertIn('"linked_elf_sha256":',report)
            self.assertIn('"producer_source_sha256":',report)
            with self.fake_native(root,fixture,findings=True):
                self.assertFalse(evidence.report_matches(report,root,ADDRESS))


class PrivateFloatTerminalAlignmentTests(unittest.TestCase):
    def fixture(self):
        return PrivateFloatPackAdmissionTests().fixture()

    @contextmanager
    def closure(self):
        with PrivateFloatPackAdmissionTests().closure() as fixture:
            yield fixture

    def padded(self, body):
        original, linked = elf_pair(body)
        for image in (original, linked):
            image['text'] += bytes.fromhex('c046')
            section = list(image['sections'][1])
            section[5], section[8] = len(image['text']), 4
            image['sections'][1] = tuple(section)
        return original, linked

    def test_terminal_alignment_original_linked_and_exact_function_bytes(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked=self.padded(body)
            calls,targets=admission.original_bindings(original,ADDRESS,rom,mapping,index)
            compiled=admission.linked_bytes(original,linked,ADDRESS,calls,targets)
            self.assertEqual(compiled,body)
            self.assertEqual(len(original['text']),40)
            self.assertEqual(original['symbols'][0]['size'],38)
            manifest,instructions=admission.verify(compiled,ADDRESS,rom,mapping,index,calls)
            self.assertEqual(len(instructions),17)
            self.assertEqual(manifest['inventory']['body_sha256'],admission.sha(body))

    def test_terminal_alignment_malformed_extent_and_section_geometry(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked=self.padded(body)
            calls=[[10,f'func_{UNPACK:08X}'],[28,f'func_{PACK:08X}']]
            targets={f'func_{UNPACK:08X}':UNPACK,f'func_{PACK:08X}':PACK}
            changes=[]
            for tail in (b'\0\0',bytes.fromhex('00bf'),bytes.fromhex('7047'),b'\0',bytes.fromhex('c046c046')):
                changes.append(('tail '+tail.hex(),lambda image,tail=tail:image.update(text=image['text'][:38]+tail)))
            for size in (0,36,37,39,40,42):
                changes.append(('size '+str(size),lambda image,size=size:image['symbols'][0].update(size=size)))
            for field,value in ((8,1),(8,2),(8,8),(5,38),(3,2)):
                def section(image,field=field,value=value):
                    row=list(image['sections'][1]);row[field]=value;image['sections'][1]=tuple(row)
                changes.append(('section '+str((field,value)),section))
            for name,change in changes:
                for phase,base in (('original',original),('linked',linked)):
                    image=copy.deepcopy(base);change(image)
                    with self.subTest(name=name,phase=phase),self.assertRaises(ValueError):
                        if phase=='original':admission.original_bindings(image,ADDRESS,rom,mapping,index)
                        else:admission.linked_bytes(original,image,ADDRESS,calls,targets)

    def test_terminal_alignment_rejects_symbols_ownership_and_relocations(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked=self.padded(body)
            calls=[[10,f'func_{UNPACK:08X}'],[28,f'func_{PACK:08X}']]
            targets={f'func_{UNPACK:08X}':UNPACK,f'func_{PACK:08X}':PACK}
            for phase,base in (('original',original),('linked',linked)):
                for name,kind,value,size in (('tail_label',0,38,0),('$t.tail',0,38,0),
                        ('$d',0,39,0),('end_label',0,40,0),('overlap',0,36,4),
                        ('foreign',2,2,2),('object',1,0,4)):
                    image=copy.deepcopy(base)
                    base_address=ADDRESS if phase=='linked' else 0
                    image['symbols'].append(dict(name=name,type=kind,bind=0,section=1,
                        value=base_address+value,size=size))
                    with self.subTest(phase=phase,name=name),self.assertRaises(ValueError):
                        if phase=='original':admission.original_bindings(image,ADDRESS,rom,mapping,index)
                        else:admission.linked_bytes(original,image,ADDRESS,calls,targets)
            for site in (36,38,40):
                changed=copy.deepcopy(original)
                data=changed['section_data'][2]+struct.pack('<II',site,1<<8|10)
                changed['section_data'][2]=data
                row=list(changed['sections'][2]);row[5]=len(data);changed['sections'][2]=tuple(row)
                with self.subTest(relocation=site),self.assertRaises(ValueError):
                    admission.original_bindings(changed,ADDRESS,rom,mapping,index)
            rows=json.loads(mapping);rows.append(dict(rom=f'0x{ADDRESS+38:08X}',end=f'0x{ADDRESS+40:08X}',mode='thumb',instrs=1))
            # ELF-only padding never enlarges the mapped ROM owner or its proof body.
            calls,targets=admission.original_bindings(original,ADDRESS,rom,json.dumps(rows).encode(),index)
            self.assertEqual(admission.linked_bytes(original,linked,ADDRESS,calls,targets),body)

    def test_terminal_alignment_rejects_control_and_literal_padding_references(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,_=self.padded(body)
            for opcode in (0xE011,0xD011,0x4808,0xA008,0x4678):
                changed=copy.deepcopy(original)
                changed['text']=words(opcode)+changed['text'][2:]
                with self.subTest(opcode=hex(opcode)),self.assertRaises(ValueError):
                    admission.original_bindings(changed,ADDRESS,rom,mapping,index)

    def test_terminal_alignment_object_path_integrity_and_unpadded_compatibility(self):
        with self.closure() as (body,rom,_,mapping,index,_):
            original,linked=self.padded(body)
            commands=[]
            class Runner:
                def write_text(self,path,data):pass
                def sh(self,command):commands.append(command)
                def read_binary(self,path):return b'synthetic linked ELF'
            with patch.object(match,'elf_image',return_value=linked):
                compiled,calls=admission.object_bytes(Runner(),'/synthetic/workspace',arguments(),original,
                                                       ADDRESS,rom,mapping,index)
            self.assertEqual(compiled,body)
            self.assertEqual(len(commands),2)
            self.assertIn('--no-undefined --no-relax --orphan-handling=error',commands[1])
            for offset in (0,38):
                changed=copy.deepcopy(linked);data=bytearray(changed['text']);data[offset]^=1;changed['text']=bytes(data)
                with self.subTest(offset=offset),self.assertRaises(ValueError):
                    admission.linked_bytes(original,changed,ADDRESS,calls,
                        {f'func_{UNPACK:08X}':UNPACK,f'func_{PACK:08X}':PACK})
            plain,plain_linked=elf_pair(body)
            bindings,targets=admission.original_bindings(plain,ADDRESS,rom,mapping,index)
            self.assertEqual(admission.linked_bytes(plain,plain_linked,ADDRESS,bindings,targets),body)

    def test_terminal_alignment_fresh_report_replays_complete_function_only(self):
        helper=PrivateFloatPackAdmissionTests()
        with helper.project() as (root,fixture),helper.fake_native(root,fixture) as (commands,_):
            original,linked=self.padded(fixture[0])
            with patch.object(match,'compile_object',return_value=(b'synthetic padded ET_REL',b'',original)), \
                    patch.object(match,'elf_image',return_value=linked):
                result=admission.build(root,ADDRESS)
                report=admission.render(result)
                self.assertEqual(len(result['body']),38)
                self.assertEqual(len(original['text']),40)
                self.assertTrue(evidence.report_matches(report,root,ADDRESS))
                self.assertEqual(len(commands),4)
                self.assertIn('38/38 bytes',report)


if __name__=='__main__':
    unittest.main()
