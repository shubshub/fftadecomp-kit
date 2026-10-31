"""Synthetic R0 slot-zero provenance. No game ROM or compiler is used."""
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
CASE = Path(__file__).resolve().parents[2]
BASE = CASE.parents[1]
KIT = BASE / 'repos/fftadecomp-kit'
SWITCH = BASE / 'state/matching-08062248-switch-scalar-prerequisite/proposed/tools'
sys.path[:0] = [str(CASE / 'proposed/tools'), str(SWITCH), str(KIT / 'tools'), str(KIT / 'tests')]
import match
import match_evidence as evidence
import addressed_signed_runtime_profile as profile
import test_addressed_r2_callback as legacy
import status
import push

A, bl, indexes = legacy.A, legacy.bl, legacy.indexes


class R0SlotTests(unittest.TestCase):
    def setUp(self):
        self.old = legacy.R2CallbackTests('runTest')
        self.old.setUp()
        self.addCleanup(self.old.doCleanups)
        self.where = patch.object(legacy, 'HERE', CASE)
        self.where.start()
        self.addCleanup(self.where.stop)

    def fixture(self):
        f = self.old.helper.fixture((0xB510, 0x1C04, 0x4806, 0x6802,
            0x1C20, 0x2110, 'ordinary', 0x2040, 0x2100, 'div',
            0xBC10, 0xBC02, 0x4708))
        target = match.function_thunk.ALIASES['_call_via_r2']
        body = bytearray(f['data'])
        body[12:16] = bl(A + 12, target)
        body += b'\0\0' + struct.pack('<I', 0x02001000)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[target-match.ROM_BASE:target-match.ROM_BASE+4] = bytes.fromhex('1047c046')
        rows = json.loads(f['mapping'])
        rows[0]['end'] = f'0x{A+len(body):08X}'
        rows.append(dict(rom=f'0x{target:08X}', end=f'0x{target+2:08X}', mode='thumb', instrs=1))
        f['mapping'], f['index'] = indexes(rows)
        f.update(data=bytes(body), rom=bytes(rom),
            data_mapping=b'{"callbacks":"0x02001000"}', data_bindings=[[32, 'callbacks', 0]])
        f['calls'][A+12] = target
        return f

    def verify(self, f, **kwargs):
        return profile.verify(**f, selector=profile.CALLBACK_SELECTOR, **kwargs)

    def graph(self, f):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        refinement = owner.refine(f['data'], A, f['mapping'])
        instructions, edges, _, calls, _ = graph.graph(f['data'], A, refinement)
        return instructions, edges, calls

    def test_new_shape_binds_exact_loads_arguments_and_conditional_policy(self):
        manifest, instructions = self.verify(self.fixture())
        row = manifest['callback']['sites'][0]
        self.assertEqual(row[:5], [12, 4, 6, 32, 'callbacks'])
        self.assertEqual(row[5], dict(policy='r0-slot-zero-argument-setup-v1',
            base_register='r0', target_register='r2', slot_offset=0,
            argument_setup=[dict(offset=8, bytes='201c', destination='r0', source='r4'),
                            dict(offset=10, bytes='1021', destination='r1', immediate=16)]))
        self.assertEqual(len(instructions), 13)
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        self.assertIn('not a third C formal', manifest['callback']['contract'])
        self.assertEqual(manifest['producer_source_sha256']['match.py'],
                         hashlib.sha256((SWITCH/'match.py').read_bytes()).hexdigest())
        self.assertEqual(manifest['producer_source_sha256']['match_evidence.py'],
                         hashlib.sha256((SWITCH/'match_evidence.py').read_bytes()).hexdigest())

    def test_other_callee_saved_argument_and_u8_immediate_are_supported(self):
        f = self.old.mutate_body(self.fixture(), 8, 0x1C38)  # adds r0,r7,#0
        f = self.old.mutate_body(f, 10, 0x21FF)
        manifest, _ = self.verify(f)
        setup = manifest['callback']['sites'][0][5]['argument_setup']
        self.assertEqual(setup[0]['source'], 'r7')
        self.assertEqual(setup[1]['immediate'], 255)

    def test_clobber_alias_nonzero_slot_and_unsupported_setup_reject(self):
        f = self.fixture()
        for offset, word in ((2, 0xAC00),  # escaped SP-derived argument
                             (2, 0x9C02), # unselected incoming word
                             (4, 0x4906),  # PC base into r1
                             (6, 0x6842),  # nonzero slot
                             (6, 0x6803),  # wrong target register
                             (6, 0x5882),  # indexed alias
                             (8, 0x2200),  # overwrite target
                             (8, 0x1C00),  # unknown r0 argument alias
                             (8, 0x3000),  # unsupported arithmetic spelling
                             (8, 0x1C21),  # wrong argument destination
                             (10, 0x2200), # overwrite target
                             (10, 0x1C21), # r1 unknown argument alias
                             (10, 0xC004)): # unsupported memory write
            with self.subTest(offset=offset, word=hex(word)), self.assertRaises(ValueError):
                self.verify(self.old.mutate_body(f, offset, word))

    def test_branch_join_intervening_call_and_gap_reject(self):
        f = self.fixture()
        for kind in ('branch', 'join', 'call', 'gap'):
            instructions, edges, calls = self.graph(f)
            edges = dict(edges); calls = dict(calls)
            if kind == 'branch': edges[A+8] = (A+10, A+16)
            elif kind == 'join': edges[A] = (A+2, A+10)
            elif kind == 'call': calls[A+8] = 0x08011000
            else: edges[A+8] = (A+12,)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.callback_sites(instructions, edges, calls, A, f['data_bindings'])

    def test_typed_binding_addend_missing_object_and_code_alias_reject(self):
        f = self.fixture()
        for change in ('addend', 'missing', 'code'):
            bad = copy.deepcopy(f)
            if change == 'addend':
                bad['data_bindings'][0][2] = 4
                body = bytearray(bad['data']); struct.pack_into('<I', body, 32, 0x02001004)
                rom = bytearray(bad['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
                bad.update(data=bytes(body), rom=bytes(rom))
            else:
                bad['data_mapping'] = b'{}' if change == 'missing' else b'{"callbacks":"0x08010000"}'
            with self.subTest(change=change), self.assertRaises(ValueError): self.verify(bad)

    def test_original_linked_ELF_and_provenance_manifest_tampering_reject(self):
        f = self.fixture(); original, linked = self.old.images(f)
        calls, _, targets, records = self.old.original_bindings(f, original)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records), f['data'])
        for field, value in (('name', 'func_0814224C'), ('type', 1), ('value', 4)):
            bad = copy.deepcopy(original)
            callback = next(s for s in bad['symbols'] if s['name'] == '_call_via_r2')
            callback[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.old.original_bindings(f, bad)
        bad = copy.deepcopy(linked); body = bytearray(bad['text']); body[8] ^= 1; bad['text'] = bytes(body)
        with self.assertRaises(ValueError): profile.linked_bytes(original, bad, A, calls, targets, data_relocations=records)
        manifest, _ = self.verify(f)
        for field, value in (('policy', 'other'), ('base_register', 'r1'), ('slot_offset', 4)):
            bad = copy.deepcopy(manifest); bad['callback']['sites'][0][5][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): self.verify(f, manifest=bad)
        bad = copy.deepcopy(manifest); bad['callback']['sites'][0][5]['argument_setup'][0]['offset'] += 2
        with self.assertRaises(ValueError): self.verify(f, manifest=bad)

    def test_legacy_row_and_other_selector_refusals_are_preserved(self):
        manifest, _ = self.old.verify(self.old.fixture())
        self.assertEqual(manifest['callback']['sites'], [[10, 2, 8, 28, 'callbacks']])
        f = self.fixture()
        for selector in (profile.SELECTOR, profile.DATA_SELECTOR, profile.READONLY_SELECTOR,
                         profile.READONLY_TWO_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**f, selector=selector)
        context = (f['rom'], f['mapping'], f['index'], f['bindings'], {},
                   profile.CALLBACK_SELECTOR, f['data_mapping'], f['data_bindings'])
        for option in ({'buffer_proof': object()}, {'modsi3_context': ()},
                       {'function_thunk_context': {}}):
            with self.subTest(option=option), self.assertRaises(ValueError):
                match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                    addressed_signed_runtime_context=context, **option)

    def test_thunk_runtime_hook_owner_and_return_corruption_reject(self):
        f = self.fixture()
        for location in (0x0814224C, 0x081426B8, 0x0814274C):
            bad = copy.deepcopy(f); rom = bytearray(bad['rom']); rom[location-match.ROM_BASE] ^= 1
            bad['rom'] = bytes(rom)
            with self.subTest(location=hex(location)), self.assertRaises(ValueError): self.verify(bad)
        bad = dict(f, index=f['index'].replace(b'0814224E', b'08142250'))
        with self.assertRaises(ValueError): self.verify(bad)
        with self.assertRaises(ValueError): self.verify(self.old.mutate_body(f, 28, 0x4700))

    def test_staged_CLI_status_publisher_and_stale_evidence_roundtrip(self):
        f = self.fixture()
        with self.old.build_fixture(f) as (root, _, commands, capture):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                 '--addressed-signed-runtime-profile', profile.CALLBACK_SELECTOR, f'{A:08X}']), \
                    redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertEqual(profile.selector_for_report(report), profile.CALLBACK_SELECTOR)
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(status.collect(str(root), verify=False)[1], 1)
            with patch.object(status.subprocess, 'run', return_value=type('R', (), {
                    'returncode':0, 'stdout':'extent 36 bytes\nverdict MATCH - byte identical\n', 'stderr':''})()) as run:
                self.assertEqual(status.collect(str(root), verify=True)[1], 1)
                self.assertIn(profile.CALLBACK_SELECTOR, run.call_args[0][0])
            with redirect_stdout(io.StringIO()):
                self.assertTrue(push.check_reports(str(root)))
                with patch.object(push, 'run', return_value=(0, 'up to date')) as gate:
                    self.assertTrue(push.check_matches(str(root)))
                    self.assertIn('--verify', gate.call_args[0][0])
            for relative in ('src/08010000.c', 'config/functions.json',
                             'symbols/functions.txt', 'config/data_symbols.json'):
                path = root/relative; prior = path.read_bytes(); path.write_bytes(prior+b' ')
                try: self.assertFalse(evidence.report_matches(report, root, A))
                finally: path.write_bytes(prior)
            result = profile.build(root, A, selector=profile.CALLBACK_SELECTOR)
            result['manifest']['callback']['sites'][0][5]['argument_setup'][1]['immediate'] = 17
            self.assertFalse(evidence.report_matches(profile.render(result), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'stale': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            self.assertTrue(commands)


if __name__ == '__main__':
    unittest.main()
