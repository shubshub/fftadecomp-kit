"""Portable synthetic source-admission boundaries; no original ROM or compiler.

Only the already separately tested canonical UMOD implementation closure is
replaced at its dependency boundary. The caller CFG/frame/divisor, real thunk
identity, ELF relocation/link surface, report fingerprint and freshness checks
execute here. Fixtures are generated independently from public Thumb encodings.
"""
import argparse
import ast
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parents[1]
PRODUCTION = Path(os.environ.get('FFTA_UMOD_SOURCE_DEPENDENCIES', HERE))
sys.path[:0] = [str(HERE/'tools'), str(PRODUCTION/'tools')]
import match
import match_evidence as evidence
import function_thunk_profile as thunks
import umod_r1_thunk_profile as profile
import umod_r1_thunk_inventory as inventory
import owner_admission_profile as owner
import owner_graph_profile as graph

A = match.ROM_BASE + 0x10000
OBJECT = 0x02001000
NAME = f'func_{A:08X}'


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000|((delta>>12)&0x7ff), 0xF800|((delta>>1)&0x7ff))


class UmodR1SourceTests(unittest.TestCase):
    def setUp(self):
        closure = patch.object(inventory.umod, 'runtime_closure', return_value=(
            [['synthetic already-authenticated runtime closure']], [['synthetic own-frame closure']]))
        self.closure = closure.start()
        self.addCleanup(closure.stop)
        self.fixture()

    def fixture(self, *, divisor=48, middle=(), suffix=None):
        body = bytearray()
        sequence = [0xB510, 0x1C04, 'literal', 0x7810, 0x2100|divisor, *middle,
            'umod', 0x7060, 0x6821, 0x1C20, 'thunk',
            *(suffix if suffix is not None else [0xBC10, 0xBC01, 0x4700])]
        calls = {}
        load = None
        for value in sequence:
            site = A+len(body)
            if value == 'literal':
                load = len(body)
                body += b'\0\0'
            elif value in ('umod', 'thunk'):
                target = inventory.remainder.ADDRESS if value == 'umod' else inventory.THUNK_ADDRESS
                calls[site] = target
                body += bl(site, target)
            else:
                body += struct.pack('<H', value)
        while len(body)%4:
            body += b'\0\0'
        word = len(body)
        body += struct.pack('<I', OBJECT)
        struct.pack_into('<H', body, load, 0x4A00|((A+word-((A+load+4)&~3))//4))
        self.body, self.calls, self.word = bytes(body), calls, word
        self.rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb', instrs=0),
            dict(rom=f'0x{inventory.THUNK_ADDRESS:08X}', end=f'0x{inventory.THUNK_ADDRESS+4:08X}', mode='thumb', instrs=2),
            dict(rom=f'0x{inventory.remainder.ADDRESS:08X}', end='0x08142BE8', mode='thumb', instrs=95),
            dict(rom='0x0814274C', end='0x0814274E', mode='thumb', instrs=1)]
        self.rows[0]['instrs'] = owner.refine(self.body,A,json.dumps(self.rows).encode())['instrs']
        self.mapping = (json.dumps(self.rows,indent=2)+'\n').encode()
        self.index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in self.rows).encode()
        image = bytearray(0x142BE8)
        image[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        struct.pack_into('<HH',image,inventory.THUNK_ADDRESS-match.ROM_BASE,
                         0x4700+(1<<3),0x4600+(6<<5))
        self.rom = bytes(image)
        self.objects = json.dumps({'synthetic_object':f'0x{OBJECT:08X}'}).encode()
        decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
        refinement = owner.refine(self.body,A,self.mapping)
        instructions,*_ = graph.graph(self.body,A,refinement)
        self.manifest = thunks.make_manifest(self.calls,{}, {word:('synthetic_object',OBJECT)},
            A,self.rom,self.objects,list(instructions.values()),selector=profile.SELECTOR)

    def verify(self, **changes):
        values = dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,
                      index=self.index,objects=self.objects,manifest=self.manifest)
        values.update(changes)
        return thunks.verify(**values)

    def images(self):
        original = bytearray(self.body)
        records = []
        symbols = [dict(name=NAME,value=1,size=len(original),type=2,bind=1,section=1)]
        for site,target in sorted(self.calls.items()):
            name = '__umodsi3' if target == inventory.remainder.ADDRESS else inventory.THUNK
            symbols.append(dict(name=name,value=0,size=0,type=2,bind=1,section=0))
            records.append(struct.pack('<II',site-A,((len(symbols)-1)<<8)|10))
            original[site-A:site-A+4] = bl(site,site)
        symbols.append(dict(name='synthetic_object',value=0,size=0,type=1,bind=1,section=0))
        records.append(struct.pack('<II',self.word,((len(symbols)-1)<<8)|2))
        struct.pack_into('<I',original,self.word,0)
        relocation = b''.join(records)
        section = (0,1,6,0,0,len(original),0,0,4,0)
        rel = (0,9,0,0,0,len(relocation),3,1,4,8)
        image = dict(type=1,text=bytes(original),text_index=1,
            sections=[(0,)*10,section,rel,(0,)*10],
            section_data=[b'',bytes(original),relocation,b''],symbols=symbols,
            symbol_tables={3:symbols},relocations=[2])
        linked = copy.deepcopy(image)
        linked.update(type=2,text=self.body,relocations=[])
        linked['sections'][1] = (*section[:3],A,*section[4:])
        linked['symbols'][0]['value'] = A|1
        for symbol in linked['symbols'][1:]:
            symbol.update(section=0xfff1,value=(OBJECT if symbol['type']==1 else
                (inventory.remainder.ADDRESS if symbol['name']=='__umodsi3' else inventory.THUNK_ADDRESS)|1))
        return image,linked

    def bindings(self, original, **changes):
        values = dict(function_thunks=True,umodsi3_bindings={},umod_r1_profile=profile.SELECTOR)
        values.update(changes)
        return match.call_bindings(original,NAME,A,self.mapping,len(self.rom),self.rom,self.objects,{}, {},**values)

    def test_synthetic_complete_frame_divisor_and_typed_pool(self):
        instructions = self.verify()
        self.assertEqual(len(instructions), self.rows[0]['instrs'])
        self.assertFalse(self.manifest['frame'])  # Legacy marker denotes local/SP accesses, not saved pushes.
        self.assertEqual(self.closure.call_count,1)
        self.assertEqual(self.manifest['calls'],[])
        self.assertEqual(self.manifest['functions'],[])
        self.assertEqual(self.manifest['unsigned_remainder'],[[10,'__umodsi3']])

    def test_original_typed_ELF_bindings_and_exact_linked_surface(self):
        original,linked = self.images()
        with patch.object(inventory.remainder,'verify_identity') as identity:
            calls,functions,literals = thunks.original_bindings(original,A,self.mapping,self.rom,self.objects,selector=profile.SELECTOR)
        identity.assert_called_once_with(self.rom,self.mapping)
        self.assertEqual((calls,functions,literals),(self.calls,{}, {self.word:('synthetic_object',OBJECT)}))
        targets = {'__umodsi3':inventory.remainder.ADDRESS,inventory.THUNK:inventory.THUNK_ADDRESS,'synthetic_object':OBJECT}
        result = match.linked_function_bytes(original,linked,NAME,A,calls,targets,literals,{}, {},
            function_thunks=True,umodsi3_bindings={A+10:'__umodsi3'},umod_r1_profile=profile.SELECTOR)
        self.assertEqual(result,self.body)
        for location in (0,len(self.body)-1):
            bad = copy.deepcopy(linked);data=bytearray(bad['text']);data[location]^=1;bad['text']=bytes(data)
            with self.subTest(location=location), self.assertRaises(ValueError):
                match.linked_function_bytes(original,bad,NAME,A,calls,targets,literals,{}, {},
                    function_thunks=True,umodsi3_bindings={A+10:'__umodsi3'},umod_r1_profile=profile.SELECTOR)

    def test_old_DEFAULT_and_canonical_thunk_paths_still_refuse_composition(self):
        original,linked=self.images()
        with self.assertRaises(ValueError):thunks.original_bindings(original,A,self.mapping,self.rom,self.objects)
        targets={'__umodsi3':inventory.remainder.ADDRESS,inventory.THUNK:inventory.THUNK_ADDRESS,'synthetic_object':OBJECT}
        with self.assertRaises(ValueError):
            match.linked_function_bytes(original,linked,NAME,A,self.calls,targets,
                {self.word:('synthetic_object',OBJECT)},{},{},function_thunks=True,umodsi3_bindings={A+10:'__umodsi3'})
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls,function_thunk_context={})

    def test_wrong_or_missing_divisor_is_not_admitted(self):
        for value in (0,47,49):
            self.fixture(divisor=value)
            with self.subTest(value=value),self.assertRaises(ValueError):self.verify()

    def test_all_path_divisor_definition_required(self):
        # A bypass goes directly from the preceding compare to the UMOD call.
        data=bytearray(self.body);struct.pack_into('<H',data,6,0xD000)
        rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
        with self.assertRaises(ValueError):self.verify(data=bytes(data),rom=bytes(rom))

    def test_allocations_SP_exports_entry_words_and_block_transfers_refuse(self):
        for instruction in (0xB081,0x4668,0x9803,0x9000,0xC810):
            self.fixture(middle=(instruction,))
            with self.subTest(instruction=instruction),self.assertRaises(ValueError):self.verify()

    def test_bad_saved_frame_and_cycles_refuse(self):
        for suffix in ([0xBC01,0x4700],[0xBC10,0x2400,0xBC01,0x4700],[0x2800,0xD0FE,0xBC10,0xBC01,0x4700]):
            self.fixture(suffix=suffix)
            with self.subTest(suffix=suffix),self.assertRaises(ValueError):self.verify()

    def test_exact_actual_call_aliases_and_non_R1_targets_refuse(self):
        original,_=self.images()
        for symbol in original['symbols'][1:3]:
            bad=copy.deepcopy(original)
            bad['symbols'][original['symbols'].index(symbol)]['name']='func_08142B28' if symbol['name']=='__umodsi3' else '_call_via_r2'
            with self.subTest(symbol=symbol['name']),patch.object(inventory.remainder,'verify_identity'),self.assertRaises(ValueError):
                thunks.original_bindings(bad,A,self.mapping,self.rom,self.objects,selector=profile.SELECTOR)

    def test_extra_mixed_contexts_and_non_explicit_opt_in_refuse(self):
        original,_=self.images()
        for changes in ({'umod_r1_profile':True},{'umod_r1_profile':'canonical-thunks-v1'},
                        {'function_thunks':False},{'allow_switch_data':True},{'divsi3_bindings':{}},
                        {'thunk_pool_words':0},{'umodsi3_bindings':None}):
            with self.subTest(changes=changes),self.assertRaises(ValueError):self.bindings(original,**changes)

    def test_missing_duplicate_extra_misaligned_and_overlapping_data_refuse(self):
        variants=([],self.manifest['data']*2,[[self.word-2,'synthetic_object',0]],
            [[10,'synthetic_object',0]],[[self.word,'unknown',0]],[[self.word,'synthetic_object',1]])
        for records in variants:
            bad=copy.deepcopy(self.manifest);bad['data']=records
            with self.subTest(records=records),self.assertRaises(ValueError):self.verify(manifest=bad)

    def test_ambiguous_defined_or_untyped_ELF_symbols_refuse(self):
        original,_=self.images()
        variants=[]
        duplicate=copy.deepcopy(original);duplicate['symbols'].append(copy.deepcopy(duplicate['symbols'][1]));variants.append(duplicate)
        for field,value in (('section',1),('bind',0),('value',4),('type',1)):
            bad=copy.deepcopy(original);bad['symbols'][1][field]=value;variants.append(bad)
        for number,bad in enumerate(variants):
            with self.subTest(number=number),patch.object(inventory.remainder,'verify_identity'),self.assertRaises(ValueError):
                thunks.original_bindings(bad,A,self.mapping,self.rom,self.objects,selector=profile.SELECTOR)

    def test_changed_thunk_identity_and_call_manifest_refuse(self):
        rom=bytearray(self.rom);rom[inventory.THUNK_ADDRESS-match.ROM_BASE]^=1
        with self.assertRaises(ValueError):self.verify(rom=bytes(rom))
        for field in ('thunks','unsigned_remainder'):
            for records in ([],self.manifest[field]*2,[[self.manifest[field][0][0]+2,self.manifest[field][0][1]]]):
                bad=copy.deepcopy(self.manifest);bad[field]=records
                with self.subTest(field=field,records=records),self.assertRaises(ValueError):self.verify(manifest=bad)

    def test_stale_sources_maps_indices_and_object_bindings_refuse(self):
        bad=copy.deepcopy(self.manifest);bad['producer_source_sha256']['match.py']='0'*64
        with self.assertRaises(ValueError):self.verify(manifest=bad)
        rows=copy.deepcopy(self.rows);rows[0]['instrs']-=1
        with self.assertRaises(ValueError):self.verify(mapping=json.dumps(rows).encode())
        fields=self.index.decode().splitlines();first=fields[0].split();first[3]=str(int(first[3])-1);fields[0]=' '.join(first)
        with self.assertRaises(ValueError):self.verify(index=('\n'.join(fields)+'\n').encode())
        with self.assertRaises(ValueError):self.verify(objects=json.dumps({'synthetic_object':'0x02001004'}).encode())

    def test_closed_new_schema_and_legacy_report_selector_extraction(self):
        for selector in thunks.SELECTORS:
            report=f'* verification: `{thunks.schema_for(selector)}`\n* function-address thunks: {selector}\n'
            self.assertEqual(thunks.selector_for_report(report),selector)
        report=f'* verification: `{profile.SCHEMA}`\n* function-address thunks: {profile.SELECTOR}\n'
        for extra in ('* unsigned division: synthetic\n','* function-address thunks: canonical-thunks-v1\n'):
            with self.subTest(extra=extra),self.assertRaises(ValueError):thunks.selector_for_report(report+extra)
        with self.assertRaises(ValueError):thunks.selector_from_manifest({'selector':'unknown'})

    def test_CLI_exposes_only_explicit_composition_without_running_workflows(self):
        with patch.object(sys,'argv',['match.py','--help']),redirect_stdout(io.StringIO()) as output,self.assertRaises(SystemExit) as result:
            match.main()
        self.assertEqual(result.exception.code,0)
        self.assertIn(profile.SELECTOR,output.getvalue())
        self.assertIn('--function-address-profile',output.getvalue())
        # Current status forwards the authenticated extracted thunk selector,
        # and match_evidence routes the same selected report validator.
        status=ast.parse((PRODUCTION/'tools/status.py').read_text())
        self.assertTrue(any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='selector_for_report'
                            and isinstance(n.func.value,ast.Name) and n.func.value.id=='function_thunk' for n in ast.walk(status)))
        self.assertIn('"--function-address-profile", thunk_profile',(PRODUCTION/'tools/status.py').read_text())
        self.assertIn('return function_thunk.report_matches(report, root, address)',(PRODUCTION/'tools/match_evidence.py').read_text())

    def test_report_fingerprint_binds_all_current_context_and_source(self):
        baseline=thunks.fingerprint(A,self.body,self.manifest,'a'*64,self.mapping,self.index,self.objects,self.rom)
        variants=(('data',self.body[:-1]+b'\1'),('source_digest','b'*64),('mapping',self.mapping+b' '),
                  ('index',self.index+b'\n'),('objects',self.objects+b' '),('rom',self.rom+b'\0'))
        for field,value in variants:
            args=dict(address=A,data=self.body,manifest=self.manifest,source_digest='a'*64,
                      mapping=self.mapping,index=self.index,objects=self.objects,rom=self.rom)
            args[field]=value
            with self.subTest(field=field):self.assertNotEqual(thunks.fingerprint(**args),baseline)


    def report_root(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', HERE/'build'))
        scratch.mkdir(parents=True,exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='umod_source_',dir=scratch)
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for directory in ('src','include','config','symbols','docs/match'):
            (root/directory).mkdir(parents=True)
        (root/f'src/{A:08X}.c').write_text('void func_08010000(void *item) { (void)item; }\n')
        (root/'include/context.h').write_text('struct Synthetic;\n')
        (root/'config/functions.json').write_bytes(self.mapping)
        (root/'config/data_symbols.json').write_bytes(self.objects)
        (root/'symbols/functions.txt').write_bytes(self.index)
        rom_path = root/'synthetic-image.bin';rom_path.write_bytes(self.rom)
        return root,rom_path

    def report(self,root):
        source=evidence.source_fingerprint(root,A)
        proof=thunks.fingerprint(A,self.body,self.manifest,source,self.mapping,self.index,self.objects,self.rom)
        return '\n'.join([f'* verification: `{profile.SCHEMA}`',f'* function-address thunks: {profile.SELECTOR}',
            f'* control flow: {thunks.CONTROL_FLOW}',f'* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`',
            f'* source SHA-256: `{source}`',f'* mapping SHA-256: `{sha(self.mapping)}`',
            f'* function index SHA-256: `{sha(self.index)}`',f'* data symbols SHA-256: `{sha(self.objects)}`',
            f'* ROM SHA-256: `{sha(self.rom)}`','* verified extent: complete ELF function symbol, including literal pools',
            '* relocations: none','* source plausibility: plausible','* hand-asm allow list: not listed',
            f'* source: `src/{A:08X}.c`',f'* compiled : `{self.body.hex()}`',
            f'* function-address-thunk manifest: `{thunks.manifest_text(self.manifest)}`',
            f'* function-address-thunk sha256: `{proof}`',f'* ROM bytes: `{self.body.hex()}` ({len(self.body)} bytes)',
            f'**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes'])+'\n'

    def test_report_acceptance_requires_fresh_source_maps_and_runtime_producer(self):
        root,rom_path=self.report_root();report=self.report(root)
        with patch.object(evidence,'report_rom_path',return_value=rom_path),patch.object(thunks,'verify_source',return_value=True) as source:
            self.assertTrue(thunks.report_matches(report,root,A))
            source.assert_called_once()
            source.reset_mock()
            for path in (root/'config/functions.json',root/'symbols/functions.txt',root/'config/data_symbols.json',
                         root/'include/context.h',root/f'src/{A:08X}.c'):
                before=path.read_bytes();path.write_bytes(before+b' ')
                with self.subTest(path=path.name):self.assertFalse(thunks.report_matches(report,root,A))
                path.write_bytes(before)
            source.assert_not_called()
            with patch.object(thunks,'verify_source',side_effect=ValueError('synthetic fresh C/ELF differs')):
                self.assertFalse(thunks.report_matches(report,root,A))
            stale=copy.deepcopy(self.manifest);stale['producer_source_sha256']['match.py']='0'*64
            encoded=thunks.manifest_text(stale)
            changed=report.replace(thunks.manifest_text(self.manifest),encoded)
            self.assertFalse(thunks.report_matches(changed,root,A))

    def test_fresh_source_capture_reuses_original_ELF_binding_and_complete_proof(self):
        from contextlib import contextmanager
        root,rom_path=self.report_root();original,_=self.images()
        captured=[]
        class Runner:
            def __init__(self,*args,**kwargs):captured.append(kwargs['root'])
            @contextmanager
            def workspace(self):yield '/synthetic-workspace'
            def read_binary(self,path):
                if path.endswith('/f.i'):return b'void func_08010000(void *item) { (void)item; }'
                raise AssertionError('Unexpected fake runner read')
        literals={self.word:('synthetic_object',OBJECT)}
        with patch.object(evidence,'report_rom_path',return_value=rom_path),patch.object(match,'Runner',Runner),\
                patch.object(match,'compile_object',return_value=(b'synthetic original object',b'',original)) as compile_once,\
                patch.object(match,'link_calls',return_value=(self.body,self.calls,literals)) as link_once,\
                patch.object(inventory.remainder,'verify_identity'),\
                patch.object(match,'_run_replay_process',return_value=object()),\
                patch.object(match,'plausibility_result',return_value=([],[])):
            self.assertTrue(thunks.verify_source(root,A,self.body,self.rom,self.mapping,self.index,self.objects,
                            evidence.source_fingerprint(root,A),self.manifest))
            compile_once.assert_called_once();link_once.assert_called_once()
            self.assertEqual(link_once.call_args.kwargs['umod_r1_profile'],profile.SELECTOR)
            self.assertEqual(link_once.call_args.kwargs['umodsi3_bindings'],{})
            self.assertTrue(captured and captured[0]!=root)
            self.assertFalse(thunks._replay_active.get())

    def test_explicit_link_context_rejects_other_functions_switches_and_runtime_aliases(self):
        calls=self.calls;targets={'__umodsi3':inventory.remainder.ADDRESS,inventory.THUNK:inventory.THUNK_ADDRESS}
        unsigned={A+10:'__umodsi3'}
        for functions,switches in (({0:('func_08011000',0x08011001)},{}),({}, {0:4})):
            with self.subTest(functions=functions,switches=switches),self.assertRaises(ValueError):
                profile.check_link_context(profile.SELECTOR,True,5,functions,switches,unsigned,
                                           (False,False,False,False),(None,)*7)
        for mutated in ({**targets,'func_08011000':0x08011000},
                        {**targets,'__umodsi3':inventory.remainder.ADDRESS+2},
                        {**targets,inventory.THUNK:thunks.ALIASES['_call_via_r2']}):
            with self.subTest(targets=mutated),self.assertRaises(ValueError):
                profile.check_link_bindings(calls,mutated,{}, {}, {},unsigned)

    def test_reserved_and_indexed_code_addresses_cannot_become_typed_data(self):
        for value in (inventory.THUNK_ADDRESS,inventory.remainder.ADDRESS):
            data=bytearray(self.body);struct.pack_into('<I',data,self.word,value)
            rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
            objects=json.dumps({'synthetic_object':f'0x{value:08X}'}).encode()
            with self.subTest(value=value),self.assertRaises(ValueError):
                self.verify(data=bytes(data),rom=bytes(rom),objects=objects)

    def test_reached_literal_naming_the_callers_own_bytes_refuses_after_composition(self):
        # Typed data inside the caller is refused by the object binding before
        # the composed proof returns, so the own-span rule after it is reached
        # only through that boundary: substitute the composed result there.
        instructions=self.verify()
        with patch.object(profile,'verify',return_value=instructions) as composed:
            self.assertIs(self.verify(),instructions)
            composed.assert_called_once()
            for value in (A+8,A+9):
                data=bytearray(self.body);struct.pack_into('<I',data,self.word,value)
                rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
                with self.subTest(value=value),self.assertRaisesRegex(ValueError,"caller's own bytes"):
                    self.verify(data=bytes(data),rom=bytes(rom))
        for value in (A+8,A+9):
            data=bytearray(self.body);struct.pack_into('<I',data,self.word,value)
            rom=bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)]=data
            objects=json.dumps({'synthetic_object':f'0x{value:08X}'}).encode()
            with self.subTest(value=value),self.assertRaisesRegex(ValueError,'references itself'):
                self.verify(data=bytes(data),rom=bytes(rom),objects=objects)


if __name__=='__main__':unittest.main()
