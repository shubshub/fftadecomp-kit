"""Synthetic R3 callback admission; no game ROM, C compiler or external API."""
import copy
from contextlib import contextmanager, redirect_stdout
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

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parents[1]
KIT = Path(os.environ.get('FFTA_R3_PRODUCTION_KIT', HERE))
sys.path[:0] = [str(HERE / 'tools'), str(KIT / 'tools'), str(KIT / 'tests')]
import match
import match_evidence as evidence
import addressed_signed_runtime_profile as profile
import status
import push
from test_addressed_signed_runtime_profile import AddressedSignedRuntimeTests, A, bl, indexes
from test_addressed_r2_callback import R2CallbackTests

SELECTOR = 'addressed-signed-runtime-r3-callback-data-v1'
SCHEMA = 'elf-symbol-thumb-addressed-signed-runtime-r3-callback-data-v1'


class R3CallbackTests(unittest.TestCase):
    def setUp(self):
        self.helper = AddressedSignedRuntimeTests('runTest')
        self.helper.setUp()
        self.addCleanup(self.helper.doCleanups)

    def fixture(self):
        tokens = [0xB570, 0x1C05, 0x1C0E, 0x2007, 0x2103, 'div', 'mod']
        shapes = []
        for offset in (0, 32, 64):
            start = sum(2 if isinstance(x, int) else 4 for x in tokens)
            if not offset:
                tokens += [0x4800, 0x1871, 0x6803, 0x1C28, 0x2220, 'ordinary']
            else:
                tokens += [0x4A00, 0x1C28, 0x3000 | offset, 0x1871,
                           0x6813, 0x2220, 'ordinary']
            shapes.append((start, offset))
        tokens += [0xBC70, 0xBC01, 0x4700]
        f = self.helper.fixture(tokens)
        body = bytearray(f['data'])
        if len(body) % 4:
            body += b'\0\0'
        literal = len(body)
        body += struct.pack('<I', 0x02001000)
        target = match.function_thunk.ALIASES['_call_via_r3']
        for start, destination in shapes:
            delta = (A + literal - ((A + start + 4) & ~3)) // 4
            struct.pack_into('<H', body, start, (0x4800 if not destination else 0x4A00) | delta)
            site = A + start + (10 if not destination else 12)
            body[site-A:site-A+4] = bl(site, target)
            f['calls'][site] = target
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[target-match.ROM_BASE:target-match.ROM_BASE+4] = bytes.fromhex('1847c046')
        rows = json.loads(f['mapping'])
        rows[0]['end'] = f'0x{A+len(body):08X}'
        rows.append(dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1))
        f['mapping'], f['index'] = indexes(rows)
        f.update(data=bytes(body), rom=bytes(rom),
                 data_mapping=b'{"callbacks":"0x02001000"}',
                 data_bindings=[[literal, 'callbacks', 0]])
        self.shapes, self.literal = shapes, literal
        return f

    def verify(self, f, **options):
        return profile.verify(**f, selector=SELECTOR, **options)

    def mutate(self, f, offset, word):
        f = copy.deepcopy(f)
        data = bytearray(f['data'])
        struct.pack_into('<H', data, offset, word)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(f, data=bytes(data), rom=bytes(rom))

    def images(self, f):
        text = bytearray(f['data'])
        symbols = [dict(name=f'func_{A:08X}', value=1, size=len(text), type=2, bind=1, section=1)]
        symbol_ids, relocations = {}, bytearray()
        for site, target in f['calls'].items():
            name = '_call_via_r3' if target == match.function_thunk.ALIASES['_call_via_r3'] else f'func_{target:08X}'
            if name not in symbol_ids:
                symbol_ids[name] = len(symbols)
                symbols.append(dict(name=name, value=0, size=0, type=0, bind=1, section=0))
            offset = site-A
            text[offset:offset+4] = bl(site, site)
            relocations += struct.pack('<II', offset, symbol_ids[name] << 8 | 10)
        for offset, name, addend in f['data_bindings']:
            symbol_ids[name] = len(symbols)
            symbols.append(dict(name=name, value=0, size=0, type=0, bind=1, section=0))
            struct.pack_into('<i', text, offset, addend)
            relocations += struct.pack('<II', offset, symbol_ids[name] << 8 | 2)
        sections = [(0,0,0,0,0,0,0,0,0,0), (0,1,6,0,0,len(text),0,0,2,0),
                    (0,9,0,0,0,len(relocations),3,1,4,8)]
        original = dict(type=1, text=bytes(text), text_index=1, sections=sections,
            section_data=[b'', bytes(text), bytes(relocations)], symbols=symbols,
            symbol_tables={3:symbols}, relocations=[2])
        linked = copy.deepcopy(original)
        linked.update(type=2, text=f['data'], relocations=[])
        section = list(linked['sections'][1]); section[3] = A
        linked['sections'][1] = tuple(section)
        objects = json.loads(f['data_mapping'])
        for symbol in linked['symbols']:
            name = symbol['name']
            if symbol['section']:
                symbol['value'] = A | 1
            elif name in objects:
                symbol.update(value=int(objects[name], 16), section=0xFFF1, type=1)
            else:
                target = match.function_thunk.ALIASES[name] if name.startswith('_call_via_') else int(name[5:], 16)
                symbol.update(value=target | 1, section=0xFFF1, type=2)
        return original, linked

    def original_bindings(self, f, original):
        records = {}
        calls, bindings, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            data_mapping=f['data_mapping'], data_relocations=records, selector=SELECTOR)
        return calls, bindings, targets, records

    @contextmanager
    def build_fixture(self, f=None, preprocessed=b'typedef void (*Copy)(void*,const void*,unsigned);\n'):
        f = f or self.fixture()
        original, linked = self.images(f)
        scratch = Path(os.environ.get('FFTA_R3_RETAIN', HERE / 'runs'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='synthetic_r3_', dir=scratch) as directory:
            root = Path(directory)
            for sub in ('src', 'include', 'config', 'symbols', 'docs/match'):
                (root/sub).mkdir(parents=True)
            (root/'src/08010000.c').write_text('/* synthetic fingerprint only; never compiled */\n')
            (root/'config/functions.json').write_bytes(f['mapping'])
            (root/'symbols/functions.txt').write_bytes(f['index'])
            (root/'config/data_symbols.json').write_bytes(f['data_mapping'])
            rom = root/'baserom.bin'; rom.write_bytes(f['rom'])
            commands = []

            class SyntheticRunner:
                def __init__(self, *args, **kwargs): self.root = kwargs['root']
                @contextmanager
                def workspace(self):
                    path = self.root/'workspace'; path.mkdir(); yield str(path)
                def read_binary(self, path):
                    if path.endswith('f.linked.bin'): return f['data']
                    if path.endswith('f.i'): return preprocessed
                    return b'synthetic ELF or assembly token'
                def write_text(self, path, value): Path(path).write_text(value)
                def sh(self, command): commands.append(command)

            with (patch.dict(os.environ, FFTA_ROM=str(rom)),
                  patch.object(match, 'Runner', SyntheticRunner),
                  patch.object(match, 'compile_object', return_value=(b'synthetic ELF', None, original)) as capture,
                  patch.object(match, 'elf_image', return_value=linked),
                  patch.object(match, '_run_replay_process', return_value=None),
                  patch.object(match, 'plausibility_result', return_value=([], None))):
                yield root, f, commands, capture

    def test_positive_three_producer_chains(self):
        f = self.fixture()
        manifest, instructions = self.verify(f)
        self.assertEqual(manifest['schema'], SCHEMA)
        self.assertEqual(len(manifest['callback']['sites']), 3)
        self.assertEqual([row[5]['base_register'] for row in manifest['callback']['sites']], ['r0','r2','r2'])
        self.assertEqual([row[5]['destination_offset'] for row in manifest['callback']['sites']], [0,32,64])
        self.assertEqual(manifest['callback']['dependencies'][0][:3], ['_call_via_r3',0x08142250,0x08142254])
        self.assertIn('not a fourth C formal', manifest['callback']['contract'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertEqual(manifest['producer_source_sha256']['match.py'], hashlib.sha256(Path(match.__file__).read_bytes()).hexdigest())
        self.assertEqual(manifest['producer_source_sha256']['match_evidence.py'], hashlib.sha256(Path(evidence.__file__).read_bytes()).hexdigest())
        self.assertTrue(instructions)

    def test_cli_original_ELF_and_canonical_report_replay(self):
        with self.build_fixture() as (root, f, commands, capture):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-signed-runtime-profile', SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()) as output:
                self.assertEqual(match.main(), 0)
            self.assertIn('verdict MATCH - byte identical', output.getvalue())
            capture.assert_called_once()
            self.assertEqual(len(commands), 3)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report), SELECTOR)
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(capture.call_count, 2)
            self.assertIn('not a fourth C formal', report)
            self.assertIn('mapped r3 callback ABI', report)

    def test_legacy_selectors_and_cross_selector_isolation(self):
        plain = self.helper.fixture()
        self.assertEqual(profile.verify(**plain)[0]['schema'], profile.SCHEMA)
        data = self.helper.data_fixture()
        self.assertEqual(profile.verify(**data, selector=profile.DATA_SELECTOR)[0]['schema'], profile.DATA_SCHEMA)
        for selector, tokens in ((profile.READONLY_SELECTOR, (0xB570,0x9804,'div',0xBC70,0xBC02,0x4708)),
                                 (profile.READONLY_TWO_SELECTOR, (0xB570,0x9804,0x9905,'div',0xBC70,0xBC02,0x4708))):
            self.assertEqual(profile.verify(**self.helper.fixture(tokens), selector=selector)[0]['schema'], profile.SCHEMAS[selector])
        old = R2CallbackTests('runTest'); old.setUp(); self.addCleanup(old.doCleanups)
        r2 = old.fixture()
        self.assertEqual(old.verify(r2)[0]['callback']['sites'], [[10,2,8,28,'callbacks']])
        with self.assertRaises(ValueError): self.verify(r2)
        r3 = self.fixture()
        for selector in profile.SCHEMAS:
            if selector != SELECTOR:
                with self.subTest(selector=selector), self.assertRaises(ValueError):
                    profile.verify(**r3, selector=selector)
        with self.assertRaises(ValueError): self.verify(plain)
        context = (r3['rom'],r3['mapping'],r3['index'],r3['bindings'],{},SELECTOR,
                   r3['data_mapping'],r3['data_bindings'])
        for option in ({'function_thunk_context':{}}, {'buffer_proof':object()}, {'modsi3_context':()}):
            with self.subTest(option=option), self.assertRaises(ValueError):
                match.verify_leaf_instructions(r3['data'], A, True, r3['calls'],
                    addressed_signed_runtime_context=context, **option)

    def test_argument_target_slot_and_SP_alias_refusals(self):
        f = self.fixture(); first = self.shapes[0][0]; second = self.shapes[1][0]
        mutations = [(first+2,0x1870), (first+4,0x6843), (first+4,0x6802),
                     (first+4,0x58C3), (first+6,0x2300), (first+8,0x2300),
                     (second+2,0x1C00), (second+4,0x3100), (second+6,0x2300),
                     (second+8,0x6853), (second+10,0x2100), (2,0xAD00), (2,0x9D04)]
        for offset, word in mutations:
            with self.subTest(offset=offset, word=hex(word)), self.assertRaises(ValueError):
                self.verify(self.mutate(f, offset, word))
        with self.assertRaises(ValueError): self.verify(dict(f, bindings={}))
        with self.assertRaises(ValueError): self.verify(dict(f, data_mapping=b'{}'))
        with self.assertRaises(ValueError): self.verify(dict(f, data_mapping=b'{"callbacks":"0x08010000"}'))
        bad = copy.deepcopy(f); bad['data_bindings'][0][2] = 4
        body = bytearray(bad['data']); struct.pack_into('<I', body, self.literal, 0x02001004)
        rom = bytearray(bad['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        bad.update(data=bytes(body), rom=bytes(rom))
        with self.assertRaisesRegex(ValueError, 'slot-zero'): self.verify(bad)

    def test_ambiguous_join_intervening_call_and_discontinuous_producer(self):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        f = self.fixture(); start = self.shapes[1][0]
        refinement = owner.refine(f['data'], A, f['mapping'])
        instructions, edges, _, calls, _ = graph.graph(f['data'], A, refinement)
        for change in ('join','branch','call','gap'):
            bad_edges, bad_calls = dict(edges), dict(calls)
            if change == 'join': bad_edges[A] = (A+2,A+start+8)
            elif change == 'branch': bad_edges[A+start+4] = (A+start+6,A+start+10)
            elif change == 'call': bad_calls[A+start+6] = 0x08011000
            else: bad_edges[A+start+6] = (A+start+10,)
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.r3_callback_sites(instructions,bad_edges,bad_calls,A,f['data_bindings'])

    def test_thunk_runtime_owner_extent_and_return_authentication(self):
        f = self.fixture(); target = match.function_thunk.ALIASES['_call_via_r3']
        for location in (target,target+2,profile.quotient.ADDRESS,profile.remainder.ADDRESS):
            bad = copy.deepcopy(f); rom = bytearray(bad['rom']); rom[location-match.ROM_BASE] ^= 1
            bad['rom'] = bytes(rom)
            with self.subTest(location=hex(location)), self.assertRaises(ValueError): self.verify(bad)
        bad = dict(f, index=f['index'].replace(b'08142252',b'08142254'))
        with self.assertRaises(ValueError): self.verify(bad)
        rows = [row for row in json.loads(f['mapping']) if int(row['rom'],16) != target]
        mapping, index = indexes(rows)
        with self.assertRaises(ValueError): self.verify(dict(f,mapping=mapping,index=index))
        with self.assertRaises(ValueError): self.verify(dict(f,data=f['data'][:-4]))
        with self.assertRaises(ValueError): self.verify(self.mutate(f,self.literal-2,0x4700))

    def test_original_ELF_alias_type_binding_and_source_namespace(self):
        f = self.fixture(); original, _ = self.images(f)
        callback = next(i for i,s in enumerate(original['symbols']) if s['name']=='_call_via_r3')
        for field,value in (('name','func_08142250'),('name','_call_via_r2'),('type',1),
                            ('bind',0),('section',1),('value',4)):
            bad = copy.deepcopy(original); bad['symbols'][callback][field] = value
            with self.subTest(field=field,value=value), self.assertRaises(ValueError): self.original_bindings(f,bad)
        bad = copy.deepcopy(original); bad['symbols'].append(dict(bad['symbols'][callback]))
        with self.assertRaises(ValueError): self.original_bindings(f,bad)
        for field,value in (('type',2),('bind',0),('value',4)):
            bad = copy.deepcopy(original)
            next(s for s in bad['symbols'] if s['name']=='callbacks')[field] = value
            with self.subTest(object_field=field), self.assertRaises(ValueError): self.original_bindings(f,bad)
        with self.build_fixture(preprocessed=b'extern void _call_via_r3(void*,const void*,unsigned,void*);') as (root,*_):
            with self.assertRaisesRegex(ValueError,'reserved for compiler emission'):
                profile.build(root,A,selector=SELECTOR)

    def test_linked_ELF_replay_and_fresh_manifest_tampering(self):
        f = self.fixture(); original, linked = self.images(f)
        calls, _, targets, records = self.original_bindings(f,original)
        self.assertEqual(profile.linked_bytes(original,linked,A,calls,targets,data_relocations=records),f['data'])
        for change in ('argument','call','data','symbol','extra','extent'):
            bad = copy.deepcopy(linked)
            if change in ('argument','call','data'):
                offset = {'argument':self.shapes[0][0]+8,'call':self.shapes[0][0]+10,'data':self.literal}[change]
                body = bytearray(bad['text']); body[offset] ^= 1; bad['text'] = bytes(body)
            elif change == 'symbol': next(s for s in bad['symbols'] if s['name']=='_call_via_r3')['value'] += 4
            elif change == 'extra': bad['symbols'].append(dict(bad['symbols'][1],name='unexpected'))
            else: bad['symbols'][0]['size'] -= 2
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.linked_bytes(original,bad,A,calls,targets,data_relocations=records)
        manifest,_ = self.verify(f)
        for change in ('producer','argument','literal','dependency','numeric','schema'):
            bad = copy.deepcopy(manifest)
            if change=='producer': bad['producer_source_sha256']['match.py']='0'*64
            elif change=='argument': bad['callback']['sites'][0][5]['argument_setup'][0]['bytes']='0000'
            elif change=='literal': bad['callback']['sites'][0][3] += 4
            elif change=='dependency': bad['callback']['dependencies'][0][3]='0'*64
            elif change=='numeric': bad['runtime_numeric_return_facts']=[0]
            else: bad['schema']=profile.CALLBACK_SCHEMA
            with self.subTest(change=change), self.assertRaises(ValueError): self.verify(f,manifest=bad)

    def test_report_freshness_and_midrun_input_producer_mutations(self):
        with self.build_fixture() as (root,f,commands,capture):
            result = profile.build(root,A,selector=SELECTOR); report = profile.render(result)
            for relative in ('src/08010000.c','symbols/functions.txt','config/functions.json',
                             'config/data_symbols.json','baserom.bin'):
                path = root/relative; prior = path.read_bytes(); path.write_bytes(prior+b' ')
                try:
                    with self.subTest(relative=relative): self.assertFalse(evidence.report_matches(report,root,A))
                finally: path.write_bytes(prior)
            header = root/'include/changed.h'; header.write_text('/* synthetic */\n')
            try: self.assertFalse(evidence.report_matches(report,root,A))
            finally: header.unlink()
            with patch.object(profile,'runtime_fingerprint',return_value={'stale':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            forged = copy.deepcopy(result); forged['original_elf']=b'replayed unrelated ELF'
            self.assertFalse(evidence.report_matches(profile.render(forged),root,A))
            self.assertFalse(evidence.report_matches(report.replace(SELECTOR,profile.DATA_SELECTOR),root,A))
            source = root/'src/08010000.c'
            def change(*args,**kwargs): source.write_text('/* changed during build */\n')
            with patch.object(match,'_run_replay_process',side_effect=change):
                with self.assertRaisesRegex(ValueError,'source|inputs'): profile.build(root,A,selector=SELECTOR)
        with self.build_fixture() as (root,*_):
            actual = profile.data_producer_fingerprint; count = 0
            def changed():
                nonlocal count
                count += 1; value = actual()
                if count >= 3: value['addressed_signed_runtime_profile.py']='0'*64
                return value
            with patch.object(profile,'data_producer_fingerprint',side_effect=changed):
                with self.assertRaisesRegex(ValueError,'source, inputs or tools changed'):
                    profile.build(root,A,selector=SELECTOR)

    def test_status_and_native_publisher_selector_propagation(self):
        with self.build_fixture() as (root,f,commands,capture):
            result = profile.build(root,A,selector=SELECTOR)
            (root/'docs/match/08010000.md').write_text(profile.render(result))
            self.assertEqual(status.collect(str(root),verify=False)[1],1)
            output = type('Result',(),{'returncode':0,'stdout':f'extent {len(f["data"])} bytes\nverdict MATCH - byte identical\n','stderr':''})()
            with patch.object(status.subprocess,'run',return_value=output) as run:
                self.assertEqual(status.collect(str(root),verify=True)[1],1)
                command = run.call_args[0][0]
                self.assertEqual(command[command.index('--addressed-signed-runtime-profile')+1],SELECTOR)
                self.assertIn('--no-write',command)
            with redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_reports(str(root)))
                with patch.object(push,'run',return_value=(0,'up to date')) as gate:
                    self.assertTrue(push.check_matches(str(root)))
                    self.assertIn('--verify',gate.call_args[0][0])
            source = root/'src/08010000.c'; source.write_text('/* stale */\n')
            with patch.object(status.subprocess,'run',side_effect=AssertionError('stale report must stop before command')):
                self.assertEqual(status.collect(str(root),verify=True)[1],0)

    def test_complete_producer_bytes_and_mixed_callback_and_CLI_policy(self):
        f = self.fixture(); manifest,_ = self.verify(f)
        for (start,destination), row in zip(self.shapes,manifest['callback']['sites']):
            expected = [dict(offset=offset,bytes=f['data'][offset:offset+2].hex())
                        for offset in range(start,start+(12 if destination else 10),2)]
            self.assertEqual(row[5]['producer_instructions'],expected)
        bad = copy.deepcopy(manifest)
        bad['callback']['sites'][0][5]['producer_instructions'][0]['bytes']='0000'
        with self.assertRaises(ValueError): self.verify(f,manifest=bad)
        site = next(site for site,target in f['calls'].items() if target==0x08142250)
        bad = copy.deepcopy(f); bad['calls'][site]=0x0814224C
        body = bytearray(bad['data']); body[site-A:site-A+4]=bl(site,0x0814224C)
        rom = bytearray(bad['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        bad.update(data=bytes(body),rom=bytes(rom))
        with self.assertRaises(ValueError): self.verify(bad)
        with self.build_fixture() as (root,_,commands,capture):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                 '--addressed-signed-runtime-profile',SELECTOR,
                 '--function-address-profile','canonical-thunks-v1',f'{A:08X}']), \
                 redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError,'isolated explicit'):
                match.main()
            capture.assert_not_called()
            result = profile.build(root,A,selector=SELECTOR)
            report = profile.render(result)
            self.assertTrue(evidence.report_matches(report,root,A))
            self.assertEqual(result['manifest']['producer_source_sha256']['addressed_signed_runtime_profile.py'],
                             hashlib.sha256(Path(profile.__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    unittest.main()
