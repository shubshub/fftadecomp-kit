"""Synthetic source/ELF/CFG/report boundaries. No game ROM or C compiler."""
import copy
import argparse
from contextlib import contextmanager, redirect_stdout
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
KIT = Path(os.environ.get('FFTA_CALLBACK_RUNTIME_KIT', HERE))
sys.path[:0] = [str(HERE / 'tools'), str(KIT / 'tools'), str(KIT / 'tests')]
import match
import match_evidence as evidence
import addressed_signed_runtime_profile as profile
from test_addressed_signed_runtime_profile import AddressedSignedRuntimeTests, A, bl, indexes


class R2CallbackTests(unittest.TestCase):
    def setUp(self):
        self.helper = AddressedSignedRuntimeTests('runTest')
        self.helper.setUp()
        self.addCleanup(self.helper.doCleanups)

    def fixture(self):
        f = self.helper.fixture((0xB510, 0x4A06, 0x4806, 0x2104, 0x6812,
                                 'ordinary', 0x2040, 0x2100, 'div',
                                 0xBC10, 0xBC02, 0x4708))
        target = match.function_thunk.ALIASES['_call_via_r2']
        body = bytearray(f['data'])
        body[10:14] = bl(A+10, target)
        body += struct.pack('<II', 0x02001000, 0x03001000)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[target-match.ROM_BASE:target-match.ROM_BASE+4] = bytes.fromhex('1047c046')
        rows = json.loads(f['mapping'])
        rows[0]['end'] = f'0x{A+len(body):08X}'
        rows.append(dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1))
        f['mapping'], f['index'] = indexes(rows)
        f.update(data=bytes(body), rom=bytes(rom),
                 data_mapping=b'{"callbacks":"0x02001000","destination":"0x03001000"}',
                 data_bindings=[[28, 'callbacks', 0], [32, 'destination', 0]])
        f['calls'][A+10] = target
        return f

    def verify(self, f, **kwargs):
        return profile.verify(**f, selector=profile.CALLBACK_SELECTOR, **kwargs)

    def mutate_body(self, f, offset, word):
        f = copy.deepcopy(f)
        body = bytearray(f['data']); struct.pack_into('<H', body, offset, word)
        rom = bytearray(f['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        f.update(data=bytes(body), rom=bytes(rom))
        return f

    def images(self, f):
        original = self.helper.data_image(f)
        for symbol in original['symbols']:
            if symbol['name'] == 'func_0814224C': symbol['name'] = '_call_via_r2'
        linked = copy.deepcopy(original)
        linked.update(type=2, text=f['data'], relocations=[])
        section = list(linked['sections'][1]); section[3] = A
        linked['sections'][1] = tuple(section)
        objects = json.loads(f['data_mapping'])
        for symbol in linked['symbols']:
            if symbol['section']: symbol['value'] = A | 1
            elif symbol['name'] in objects:
                symbol.update(value=int(objects[symbol['name']], 16), section=0xFFF1, type=1)
            else:
                target = (match.function_thunk.ALIASES['_call_via_r2'] if
                          symbol['name'] == '_call_via_r2' else int(symbol['name'][5:], 16))
                symbol.update(value=target | 1, section=0xFFF1, type=2)
        return original, linked

    def original_bindings(self, f, original):
        records = {}
        result = profile.original_bindings(original, A, f['rom'], f['mapping'],
            data_mapping=f['data_mapping'], data_relocations=records,
            selector=profile.CALLBACK_SELECTOR)
        return (*result, records)

    @contextmanager
    def build_fixture(self, f=None, preprocessed=b'/* synthetic typed callback source boundary */\n'):
        f = f or self.fixture(); original, linked = self.images(f)
        scratch = HERE / 'runs' / 'fixtures'; scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='r2_callback_', dir=scratch) as directory:
            root = Path(directory)
            for sub in ('src', 'include', 'config', 'symbols', 'docs/match'):
                (root/sub).mkdir(parents=True)
            (root/'src/08010000.c').write_text('/* synthetic fingerprint token, never compiled */\n')
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
                    return b'synthetic original/linked ELF/assembly boundary'
                def write_text(self, path, value): Path(path).write_text(value)
                def sh(self, command): commands.append(command)

            with (patch.dict(os.environ, FFTA_ROM=str(rom)),
                  patch.object(match, 'Runner', SyntheticRunner),
                  patch.object(match, 'compile_object', return_value=(b'synthetic ELF', None, original)) as capture,
                  patch.object(match, 'elf_image', return_value=linked),
                  patch.object(match, '_run_replay_process', return_value=None),
                  patch.object(match, 'plausibility_result', return_value=([], None))):
                yield root, f, commands, capture

    def test_positive_original_linked_elf_and_both_premises(self):
        f = self.fixture(); manifest, instructions = self.verify(f)
        self.assertEqual(len(instructions), 12)
        self.assertEqual(manifest['callback']['sites'], [[10, 2, 8, 28, 'callbacks']])
        self.assertEqual(manifest['callback']['dependencies'][0][:3],
                         ['_call_via_r2', 0x0814224C, 0x08142250])
        self.assertTrue(manifest['dependencies'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertIn('function_thunk_profile.py', manifest['producer_source_sha256'])
        original, linked = self.images(f)
        calls, bindings, targets, records = self.original_bindings(f, original)
        self.assertEqual(calls, f['calls']); self.assertEqual(bindings, f['bindings'])
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records), f['data'])

    def test_cli_build_and_actual_report_admission(self):
        with self.build_fixture() as (root, f, commands, capture):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                '--addressed-signed-runtime-profile', profile.CALLBACK_SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()) as output:
                self.assertEqual(match.main(), 0)
            self.assertIn('verdict MATCH - byte identical', output.getvalue())
            capture.assert_called_once()
            report = (root/'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report), profile.CALLBACK_SELECTOR)
            self.assertIn('r2 is the target, not a third C formal', report)
            self.assertEqual(len(commands), 3)
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(capture.call_count, 2)  # Synthetic fresh source replay, no game proof.

    def test_thunk_identity_indexes_and_other_registers_reject(self):
        f = self.fixture(); target = 0x0814224C
        for change in ('canonical bytes', 'padding bytes', 'missing index', 'text owner', 'r3 thunk'):
            bad = copy.deepcopy(f)
            if change in ('canonical bytes', 'padding bytes'):
                rom = bytearray(bad['rom']); rom[target-match.ROM_BASE+(2 if change=='padding bytes' else 0)] ^= 1
                bad['rom'] = bytes(rom)
            elif change == 'missing index':
                rows = [r for r in json.loads(bad['mapping']) if int(r['rom'],16) != target]
                bad['mapping'], bad['index'] = indexes(rows)
            elif change == 'text owner':
                bad['index'] = bad['index'].replace(b'0814224E', b'08142250')
            else:
                bad['calls'][A+10] = target+4
                body = bytearray(bad['data']); body[10:14] = bl(A+10, target+4)
                rom = bytearray(bad['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
                bad.update(data=bytes(body), rom=bytes(rom))
            with self.subTest(change=change), self.assertRaises(ValueError): self.verify(bad)

    def test_target_provenance_rejects_offsets_clobber_and_ambiguous_chain(self):
        f = self.fixture()
        for offset, word in ((8, 0x6852), (8, 0x6813), (6, 0x2200), (6, 0xD106)):
            with self.subTest(offset=offset, word=hex(word)), self.assertRaises(ValueError):
                self.verify(self.mutate_body(f, offset, word))
        bad = copy.deepcopy(f); bad['data_bindings'][0][2] = 4
        body = bytearray(bad['data']); struct.pack_into('<I', body, 28, 0x02001004)
        rom = bytearray(bad['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        bad.update(data=bytes(body), rom=bytes(rom))
        with self.assertRaisesRegex(ValueError, 'slot-zero'): self.verify(bad)
        for objects in (b'{}', b'{"callbacks":"0x08010000","destination":"0x03001000"}'):
            with self.assertRaises(ValueError): self.verify(dict(f, data_mapping=objects))

    def test_old_selectors_keep_their_boundary_and_new_selector_is_explicit(self):
        plain = self.helper.fixture()
        self.assertEqual(profile.verify(**plain)[0]['schema'], profile.SCHEMA)
        data = self.helper.data_fixture()
        self.assertEqual(profile.verify(**data, selector=profile.DATA_SELECTOR)[0]['schema'], profile.DATA_SCHEMA)
        word = self.helper.fixture((0xB570, 0x9804, 'div', 0xBC70, 0xBC02, 0x4708))
        self.assertEqual(profile.verify(**word, selector=profile.READONLY_SELECTOR)[0]['schema'], profile.READONLY_SCHEMA)
        two = self.helper.fixture((0xB570, 0x9804, 0x9905, 'div', 0xBC70, 0xBC02, 0x4708))
        self.assertEqual(profile.verify(**two, selector=profile.READONLY_TWO_SELECTOR)[0]['schema'], profile.READONLY_TWO_SCHEMA)
        f = self.fixture()
        for selector in (profile.SELECTOR, profile.DATA_SELECTOR, profile.READONLY_SELECTOR, profile.READONLY_TWO_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError): profile.verify(**f, selector=selector)
        with self.assertRaises(ValueError): profile.verify(**plain, selector=profile.CALLBACK_SELECTOR)
        context = (f['rom'], f['mapping'], f['index'], f['bindings'], {},
                   profile.CALLBACK_SELECTOR, f['data_mapping'], f['data_bindings'])
        for mixed in ({'function_thunk_context': {}}, {'buffer_proof': object()}, {'modsi3_context': ()}):
            with self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                    addressed_signed_runtime_context=context, **mixed)

    def test_original_elf_aliases_types_and_explicit_thunk_source_reject(self):
        f = self.fixture(); original, _ = self.images(f)
        callback = next(i for i,s in enumerate(original['symbols']) if s['name']=='_call_via_r2')
        for field, value in (('name','func_0814224C'), ('name','_call_via_r3'),
                             ('type',1), ('bind',0), ('section',1), ('value',4)):
            bad = copy.deepcopy(original); bad['symbols'][callback][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError): self.original_bindings(f,bad)
        bad = copy.deepcopy(original); bad['symbols'].append(dict(bad['symbols'][callback]))
        with self.assertRaises(ValueError): self.original_bindings(f,bad)
        with self.build_fixture(preprocessed=b'extern void _call_via_r2(void);') as (root, *_):
            with self.assertRaisesRegex(ValueError, 'reserved for compiler emission'):
                profile.build(root, A, selector=profile.CALLBACK_SELECTOR)

    def test_linked_modification_and_manifest_forgery_reject(self):
        f = self.fixture(); original, linked = self.images(f)
        calls, _, targets, records = self.original_bindings(f, original)
        for change in ('outside byte', 'call byte', 'data word', 'thunk symbol', 'extra symbol'):
            bad = copy.deepcopy(linked)
            if change in ('outside byte', 'call byte', 'data word'):
                body=bytearray(bad['text']); body[{'outside byte':0,'call byte':10,'data word':28}[change]] ^= 1
                bad['text']=bytes(body)
            elif change == 'thunk symbol':
                next(s for s in bad['symbols'] if s['name']=='_call_via_r2')['value'] += 4
            else: bad['symbols'].append(dict(bad['symbols'][1],name='unexpected'))
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.linked_bytes(original,bad,A,calls,targets,data_relocations=records)
        manifest, _ = self.verify(f)
        for change in ('sites', 'dependencies', 'producer', 'numeric'):
            bad=copy.deepcopy(manifest)
            if change=='sites':bad['callback']['sites'][0][3]+=4
            elif change=='dependencies':bad['callback']['dependencies'][0][3]='0'*64
            elif change=='producer':bad['producer_source_sha256']['function_thunk_profile.py']='0'*64
            else:bad['runtime_numeric_return_facts']=[0]
            with self.subTest(change=change), self.assertRaises(ValueError):self.verify(f,manifest=bad)

    def test_report_freshness_binds_all_inputs_runtime_and_schema(self):
        with self.build_fixture() as (root, f, commands, capture):
            result=profile.build(root,A,selector=profile.CALLBACK_SELECTOR)
            report=profile.render(result)
            for relative in ('src/08010000.c','symbols/functions.txt','config/functions.json',
                             'config/data_symbols.json','baserom.bin'):
                path=root/relative; original=path.read_bytes(); path.write_bytes(original+b' ')
                try:
                    with self.subTest(relative=relative):self.assertFalse(evidence.report_matches(report,root,A))
                finally:path.write_bytes(original)
            header=root/'include/changed.h';header.write_text('/* changed synthetic header */\n')
            try:self.assertFalse(evidence.report_matches(report,root,A))
            finally:header.unlink()
            with patch.object(profile,'runtime_fingerprint',return_value={'stale':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            self.assertFalse(evidence.report_matches(report.replace(profile.CALLBACK_SELECTOR,profile.DATA_SELECTOR),root,A))
            forged=copy.deepcopy(result);forged['manifest']['callback']['sites'][0][4]='other'
            self.assertFalse(evidence.report_matches(profile.render(forged),root,A))

    def test_build_rejects_midrun_source_and_producer_change(self):
        with self.build_fixture() as (root, f, commands, capture):
            source=root/'src/08010000.c'
            def change(*args,**kwargs):source.write_text('/* mutated during synthetic build */\n')
            with patch.object(match,'_run_replay_process',side_effect=change):
                with self.assertRaisesRegex(ValueError,'source|inputs'):
                    profile.build(root,A,selector=profile.CALLBACK_SELECTOR)

    def test_both_premises_and_isolated_cli_stack_contract_are_required(self):
        f = self.fixture()
        with self.assertRaises(ValueError): self.verify(dict(f, bindings={}))
        for word in (0xA800, 0x9802):  # Escaped local-SP address or incoming entry word.
            with self.subTest(word=hex(word)), self.assertRaises(ValueError):
                self.verify(self.mutate_body(f, 6, word))
        args = argparse.Namespace(mode='thumb', control_flow_profile='ordinary', label=None,
            wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH,
            addressed_signed_runtime_profile=profile.CALLBACK_SELECTOR,
            signed_runtime_profile=None, signed_quotient_profile=None,
            software_double_profile=None, software_double_remainder_profile=None,
            function_address_profile='canonical-thunks-v1', switch_profile=None,
            owner_runtime_profile=None)
        with self.assertRaisesRegex(ValueError, 'isolated explicit'):
            profile.issue(HERE, A, args)
        with self.build_fixture() as (root, f, commands, capture):
            actual=profile.data_producer_fingerprint; count=0
            def changed():
                nonlocal count
                count+=1; result=actual()
                if count>=3:result['function_thunk_profile.py']='0'*64
                return result
            with patch.object(profile,'data_producer_fingerprint',side_effect=changed):
                with self.assertRaisesRegex(ValueError,'source, inputs or tools changed'):
                    profile.build(root,A,selector=profile.CALLBACK_SELECTOR)


if __name__ == '__main__':
    unittest.main()
