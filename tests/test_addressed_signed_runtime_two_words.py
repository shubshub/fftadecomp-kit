"""Synthetic two-word admission checks; no original ROM or C compiler."""
import argparse
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

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ROOT / 'tools'
sys.dont_write_bytecode = True
sys.path.insert(0, str(TOOLS))
import addressed_signed_runtime_profile as profile
import match
import match_evidence as evidence

A, B = 0x08010000, 0x08011000
SCRATCH = ROOT / 'build'


def bl(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF),
                       0xF800 | ((delta >> 1) & 0x7FF))


def indexes(rows):
    return json.dumps(rows).encode(), ''.join(
        f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
        for row in rows).encode()


class TwoReadonlyWordsTests(unittest.TestCase):
    def setUp(self):
        self.assertEqual(Path(profile.__file__).resolve(),
                         TOOLS / 'addressed_signed_runtime_profile.py')
        self.assertEqual(Path(match.__file__).resolve(), TOOLS / 'match.py')
        self.assertEqual(Path(evidence.__file__).resolve(), TOOLS / 'match_evidence.py')
        forbidden = patch.object(match, 'compile_object',
            side_effect=AssertionError('C compilation forbidden in synthetic tests'))
        forbidden.start()
        self.addCleanup(forbidden.stop)
        self.synthetic_rom = bytearray(0x143000)
        self.synthetic_rom[0x14274C:0x14274E] = bytes.fromhex('7047')
        self.synthetic_rom[0x142742:0x142746] = bl(0x08142742, 0x0814274C)
        self.synthetic_rom[0x142A16:0x142A1A] = bl(0x08142A16, 0x0814274C)
        for module in (profile.quotient, profile.remainder):
            identities = tuple((lo, hi, hashlib.sha256(
                self.synthetic_rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                for lo, hi, _ in module.IDENTITIES)
            replacement = patch.object(module, 'IDENTITIES', identities)
            replacement.start()
            self.addCleanup(replacement.stop)

    def fixture(self, tokens=(0xB570, 0x9804, 0x9905, 'div', 0xBC70, 0xBC02, 0x4708)):
        data, calls, bindings = bytearray(), {}, {}
        for token in tokens:
            if type(token) is int:
                data += struct.pack('<H', token)
            else:
                target = B if token == 'ordinary' else profile.OPERATIONS[
                    'func_081426B8' if token == 'div' else 'func_08142950']
                site = A + len(data)
                data += bl(site, target)
                calls[site] = target
                if token != 'ordinary':
                    bindings[site] = f'func_{target:08X}'
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}',
                     mode='thumb', instrs=len(tokens)),
                dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1)]
        rows += [dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb', instrs=(hi-lo)//2)
                 for lo, hi, _ in sorted(set(profile.quotient.IDENTITIES + profile.remainder.IDENTITIES))]
        mapping, index = indexes(rows)
        rom = bytearray(self.synthetic_rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return dict(data=bytes(data), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, calls=calls, bindings=bindings)

    def verify(self, fixture, **options):
        return profile.verify(**fixture, selector=profile.READONLY_TWO_SELECTOR, **options)

    @contextmanager
    def fixture_root(self, fixture):
        SCRATCH.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='two_words_', dir=SCRATCH) as directory:
            root = Path(directory)
            for sub in ('src', 'include', 'config', 'symbols', 'docs/match'):
                (root / sub).mkdir(parents=True)
            # Fingerprint input only; no C implementation and no compilation.
            (root / 'src/08010000.c').write_text('/* synthetic fingerprint marker */\n')
            (root / 'config/functions.json').write_bytes(fixture['mapping'])
            (root / 'symbols/functions.txt').write_bytes(fixture['index'])
            (root / 'config/data_symbols.json').write_text('{}\n')
            (root / 'baserom.bin').write_bytes(fixture['rom'])
            with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
                yield root

    def result(self, root, fixture):
        manifest, instructions = self.verify(fixture)
        return dict(address=A, body=fixture['data'], manifest=manifest,
            source_sha256=evidence.source_fingerprint(root, A),
            mapping_sha256=profile.sha(fixture['mapping']),
            index_sha256=profile.sha(fixture['index']),
            objects_sha256=profile.sha((root / 'config/data_symbols.json').read_bytes()),
            rom_sha256=profile.sha(fixture['rom']), instructions=len(instructions),
            toolchain=profile.toolchain_fingerprint(), runtime=profile.runtime_fingerprint(),
            original_elf=b'synthetic original ELF', assembly=b'synthetic assembly',
            linked_elf=b'synthetic linked ELF')

    def test_actual_two_reads_and_frame_normalization_keep_values_unknown(self):
        fixtures = [self.fixture(), self.fixture((0xB570, 0xB082, 0x9806, 0x9907,
            'div', 'mod', 0xB002, 0xBC70, 0xBC02, 0x4708))]
        for f in fixtures:
            with self.subTest(frame=f['data'].hex()):
                manifest, _ = self.verify(f)
                incoming = manifest['frame']['entry_stack']
                self.assertEqual(manifest['schema'], profile.READONLY_TWO_SCHEMA)
                self.assertEqual(incoming['words'], [0, 1])
                self.assertEqual({row[1] for row in incoming['reads']}, {0, 4})
                self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
                self.assertEqual(manifest['runtime_numeric_return_facts'], [])
                self.assertFalse(manifest['arithmetic_C_equivalence'])
                self.assertFalse(manifest['original_formal_type_certainty'])
                self.assertIn('readonly_entry_stack_words_profile.py', manifest['producer_source_sha256'])
                self.assertEqual(manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
                for selector in (profile.SELECTOR, profile.READONLY_SELECTOR):
                    with self.assertRaises(ValueError):
                        profile.verify(**f, selector=selector)
        one = self.fixture((0xB570, 0x9804, 'div', 0xBC70, 0xBC02, 0x4708))
        self.assertEqual(profile.verify(**one, selector=profile.READONLY_SELECTOR)[0]['schema'],
                         profile.READONLY_SCHEMA)

    def test_exact_two_word_coverage_rejects_offset8_missing_and_extra_reads(self):
        cases = {
            'none': (), 'only0': (0x9804,), 'only4': (0x9905,),
            'duplicate0': (0x9804, 0x9904), 'offset8': (0x9804, 0x9905, 0x9A06),
            'outside_only': (0x9806, 0x9907),
        }
        for reason, reads in cases.items():
            with self.subTest(reason=reason), self.assertRaisesRegex(ValueError, 'entry stack'):
                self.verify(self.fixture((0xB570, *reads, 'div', 0xBC70, 0xBC02, 0x4708)))

    def test_incoming_writes_partial_reads_and_saved_register_corruption_reject(self):
        cases = {
            'write0': (0x9004,), 'write4': (0x9105,), 'write8': (0x9206,),
            'halfword_via_incoming_address': (0xA804, 0x8800),
            'unaligned_halfword_address': (0xA804, 0x3002, 0x8800),
            'saved_register_write': (0x9000,),
        }
        for reason, accesses in cases.items():
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                self.verify(self.fixture((0xB570, 0x9804, 0x9905, *accesses,
                    'div', 0xBC70, 0xBC02, 0x4708)))

    def test_stack_pointer_escapes_and_mixed_contexts_reject(self):
        cases = {
            'incoming_pointer_call': (0xA805, 'div'),
            'incoming_pointer_store': (0xA804, 0x6028, 'div'),
            'local_pointer_call': (0xB081, 0xA800, 'div', 0xB001),
        }
        for reason, body in cases.items():
            with self.subTest(reason=reason), self.assertRaises(ValueError):
                self.verify(self.fixture((0xB570, 0x9804, 0x9905, *body,
                    0xBC70, 0xBC02, 0x4708)))
        f = self.fixture()
        context = (f['rom'], f['mapping'], f['index'], f['bindings'], {}, profile.READONLY_TWO_SELECTOR)
        for other in ({'buffer_proof': object()}, {'function_thunk_context': {}},
                      {'modsi3_context': ()}, {'preloaded_switch': True}):
            with self.subTest(other=other), self.assertRaisesRegex(ValueError, 'isolated explicit'):
                match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                    addressed_signed_runtime_context=context, **other)
        with self.assertRaisesRegex(ValueError, 'separate explicit'):
            self.verify(f, data_mapping=b'{}', data_bindings=[])

    def test_fresh_native_manifest_rejects_malformed_policy_and_producer_evidence(self):
        f = self.fixture()
        manifest, _ = self.verify(f)
        changes = [(['frame', 'entry_stack', 'words'], [0]),
                   (['frame', 'entry_stack', 'words'], [0, 1, 2]),
                   (['frame', 'entry_stack', 'words'], [False, 1]),
                   (['frame', 'entry_stack', 'schema'], 'thumb-readonly-entry-stack-word-v1'),
                   (['frame', 'entry_stack', 'reads'], []),
                   (['runtime_numeric_return_facts'], [0]),
                   (['producer_source_sha256', 'readonly_entry_stack_words_profile.py'], '0'*64)]
        for path, value in changes:
            bad = copy.deepcopy(manifest)
            cursor = bad
            for key in path[:-1]:
                cursor = cursor[key]
            cursor[path[-1]] = value
            with self.subTest(path=path, value=value), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.verify(f, manifest=bad)
        for bad_context in [(f['rom'], f['mapping'], f['index'], f['bindings'], {},
                             profile.READONLY_TWO_SELECTOR, {}),
                            (f['rom'], f['mapping'], f['index'], f['bindings'], {},
                             profile.READONLY_TWO_SELECTOR, None, [])]:
            with self.assertRaisesRegex(ValueError, 'exact explicit context'):
                profile.context_selector(bad_context)

    def test_stale_owner_index_runtime_and_bindings_reject_synthetic_verification(self):
        f = self.fixture()
        for changed in ('owner extent', 'index extent', 'runtime bytes', 'call binding'):
            bad = dict(f)
            if changed == 'owner extent':
                rows = json.loads(f['mapping']); rows[0]['end'] = f'0x{A+len(f["data"])-2:08X}'
                bad['mapping'] = json.dumps(rows).encode()
            elif changed == 'index extent':
                lines = f['index'].decode().splitlines(); fields = lines[0].split(); fields[1] = f'{A+len(f["data"])+2:08X}'
                lines[0] = ' '.join(fields); bad['index'] = ('\n'.join(lines)+'\n').encode()
            elif changed == 'runtime bytes':
                rom = bytearray(f['rom']); rom[profile.quotient.ADDRESS-match.ROM_BASE] ^= 1
                bad['rom'] = bytes(rom)
            else:
                bad['bindings'] = {}
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.verify(bad)

    def test_report_freshness_binds_source_headers_maps_data_runtime_and_policy(self):
        f = self.fixture()
        with self.fixture_root(f) as root:
            result = self.result(root, f)
            report = profile.render(result)
            self.assertEqual(profile.selector_for_report(report), profile.READONLY_TWO_SELECTOR)
            with patch.object(profile, 'build', return_value=result) as build:
                self.assertTrue(profile.report_matches(report, root, A))
                self.assertEqual(build.call_args.kwargs['selector'], profile.READONLY_TWO_SELECTOR)
                for relative in ('src/08010000.c', 'symbols/functions.txt', 'config/functions.json',
                                 'config/data_symbols.json', 'baserom.bin'):
                    path = root / relative; original = path.read_bytes(); path.write_bytes(original+b' ')
                    try:
                        with self.subTest(stale=relative):
                            self.assertFalse(profile.report_matches(report, root, A))
                    finally:
                        path.write_bytes(original)
                header = root / 'include/new.h'; header.write_text('/* synthetic changed header */\n')
                try:
                    self.assertFalse(profile.report_matches(report, root, A))
                finally:
                    header.unlink()
                with patch.object(profile, 'runtime_fingerprint', return_value={'stale': True}):
                    self.assertFalse(profile.report_matches(report, root, A))
                self.assertFalse(profile.report_matches(report.replace(
                    profile.READONLY_TWO_SELECTOR, profile.READONLY_SELECTOR), root, A))
            forged = copy.deepcopy(result)
            forged['manifest']['frame']['entry_stack']['words'] = [0, 1, 2]
            with patch.object(profile, 'build', return_value=result):
                self.assertFalse(profile.report_matches(profile.render(forged), root, A))

    def test_cli_routes_new_selector_and_rejects_mixing_without_compiler(self):
        f = self.fixture()
        with self.fixture_root(f) as root:
            result = self.result(root, f)
            with patch.object(profile, 'build', return_value=result) as build:
                with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-signed-runtime-profile', profile.READONLY_TWO_SELECTOR, f'{A:08X}']), \
                        redirect_stdout(io.StringIO()):
                    self.assertEqual(match.main(), 0)
                self.assertEqual(build.call_args.kwargs['selector'], profile.READONLY_TWO_SELECTOR)
                self.assertEqual((root / 'docs/match/08010000.md').read_text(), profile.render(result))
                args = argparse.Namespace(mode='thumb', control_flow_profile='ordinary', label=None,
                    wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH,
                    addressed_signed_runtime_profile=profile.READONLY_TWO_SELECTOR,
                    signed_runtime_profile=None, signed_quotient_profile=None,
                    software_double_profile=None, software_double_remainder_profile=None,
                    function_address_profile='canonical-thunks-v1', switch_profile=None,
                    owner_runtime_profile=None)
                with self.assertRaisesRegex(ValueError, 'isolated explicit'):
                    profile.issue(root, A, args)

    def test_synthetic_build_captures_runtime_and_rejects_midrun_runtime_change(self):
        f = self.fixture()
        site = next(iter(f['calls']))
        raw = bytearray(f['data'])
        raw[site-A:site-A+4] = bl(site, site)
        symbols = [dict(name=f'func_{A:08X}', value=1, size=len(raw), type=2, bind=1, section=1),
                   dict(name='func_081426B8', value=0, size=0, type=0, bind=1, section=0)]
        relocations = struct.pack('<II', site-A, (1 << 8) | 10)
        sections = [(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                    (0, 1, 6, 0, 0, len(raw), 0, 0, 2, 0),
                    (0, 9, 0, 0, 0, len(relocations), 3, 1, 4, 8)]
        original = dict(type=1, text=bytes(raw), text_index=1, sections=sections,
            section_data=[b'', bytes(raw), relocations], symbols=symbols,
            symbol_tables={3: symbols}, relocations=[2])
        linked = copy.deepcopy(original)
        linked.update(type=2, text=f['data'], relocations=[])
        linked['sections'][1] = tuple(list(sections[1][:3]) + [A] + list(sections[1][4:]))
        linked['symbols'][0]['value'] = A | 1
        linked['symbols'][1].update(value=profile.quotient.ADDRESS | 1, section=0xFFF1, type=2)
        commands = []

        class SyntheticRunner:
            def __init__(self, *args, **kwargs):
                self.root = kwargs['root']

            @contextmanager
            def workspace(self):
                path = self.root / 'workspace'; path.mkdir()
                yield str(path)

            def read_binary(self, path):
                return f['data'] if path.endswith('f.linked.bin') else b'synthetic ELF/assembly'

            def write_text(self, path, value):
                Path(path).write_text(value)

            def sh(self, command):
                commands.append(command)  # Recorded only; no subprocess or compiler.

        with self.fixture_root(f) as root, \
                patch.object(match, 'Runner', SyntheticRunner), \
                patch.object(match, 'compile_object', return_value=(b'synthetic ET_REL', None, original)), \
                patch.object(match, 'elf_image', return_value=linked), \
                patch.object(match, '_run_replay_process', return_value=None), \
                patch.object(match, 'plausibility_result', return_value=([], None)):
            result = profile.build(root, A, selector=profile.READONLY_TWO_SELECTOR)
            self.assertEqual(result['runtime'], profile.runtime_fingerprint())
            self.assertEqual(result['manifest']['frame']['entry_stack']['words'], [0, 1])
            self.assertEqual(result['body'], f['data'])
            self.assertEqual(len(commands), 3)
            runtime = profile.runtime_fingerprint()
            with patch.object(profile, 'runtime_fingerprint', side_effect=[runtime, {'changed': True}]), \
                    self.assertRaisesRegex(ValueError, 'changed during verification'):
                profile.build(root, A, selector=profile.READONLY_TWO_SELECTOR)


if __name__ == '__main__':
    unittest.main()
