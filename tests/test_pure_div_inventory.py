"""Focused native boundaries for the opt-in saved-only pure DIV inventory."""
import argparse
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

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import pure_div_inventory as profile
import div_only_ordinary_inventory as old_ordinary
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner

A = 0x08010000
SOURCE = '''int func_08010000(int dividend, int divisor)
{
    return dividend / divisor;
}
'''


class PureDivInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        mapping = (json.dumps(rows, indent=2) + '\n').encode()
        index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                        for row in rows).encode()
        return mapping, index

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='pure_div_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        cls.retained = Path(os.environ['FFTA_PURE_DIV_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            cls.raw = (cls.retained / 'original.o').read_bytes()
            cls.body = (cls.retained / 'body.bin').read_bytes()
            cls.rom = (cls.retained / 'baserom.bin').read_bytes()
            cls.mapping = (cls.retained / 'functions.json').read_bytes()
            cls.index = (cls.retained / 'functions.txt').read_bytes()
            cls.rows = json.loads(cls.mapping)
            if (cls.retained / 'native-inventory.json').exists():
                cls.manifest = json.loads((cls.retained / 'native-inventory.json').read_bytes())
                cls.calls = {A + offset: profile.quotient.ADDRESS for offset, name in cls.manifest['calls']}
                cls.bindings = {A + offset: name for offset, name in cls.manifest['calls']}
            else:
                # A retained compiler object can contain trailing .text alignment
                # beyond the linked function symbol. Reuse its exact body.
                cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
                mapping, _ = cls.indexes(cls.rows)
                refinement = owner.refine(cls.body, A, mapping)
                cls.rows[0]['instrs'] = refinement['instrs']
                cls.mapping, cls.index = cls.indexes(cls.rows)
                cls.calls = {int(row['site'], 16): int(row['target'], 16) for row in refinement['calls']}
                cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
                cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                                                cls.calls, cls.bindings, selector=profile.SELECTOR)
                (cls.retained / 'functions.json').write_bytes(cls.mapping)
                (cls.retained / 'functions.txt').write_bytes(cls.index)
                (cls.retained / 'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2) + '\n')
            assert cls.manifest['producer_source_sha256']['pure_div_inventory.py'] == hashlib.sha256(Path(profile.__file__).read_bytes()).hexdigest()
        else:
            assert not (cls.retained / 'original.o').exists(), 'compile already retained; explicit reuse required'
            (cls.retained / 'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                      objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                cls.rows = [
                    {'rom': f'0x{A:08X}', 'end': f'0x{A+len(original["text"]):08X}', 'mode': 'thumb', 'instrs': 0},
                    {'rom': '0x081426B8', 'end': '0x0814274A', 'mode': 'thumb', 'instrs': 72},
                    {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
                mapping, _ = cls.indexes(cls.rows)
                division = {}
                cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A,
                    mapping, len(approved), approved, divsi3_bindings=division)
                assert not literals and set(division.values()) == {'__divsi3'}
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            rom = bytearray(approved)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
            cls.rom = bytes(rom)
            cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
            for name, data in (('body.bin', cls.body), ('baserom.bin', cls.rom),
                               ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained / name).write_bytes(data)
            (cls.retained / 'compiler-evidence.json').write_text(json.dumps({
                'ELF_type': original['type'], 'compiler': match.DEFAULT_CC, 'flags': match.DEFAULT_FLAGS,
                'unmodified_natural_source': True, 'fixture_compile_count': 1,
                'no_asm_volatile_pragmas_or_steering': True,
                'synthetic_only': True, 'source_or_ELF_admission': False}, indent=2) + '\n')
            cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                                            cls.calls, cls.bindings, selector=profile.SELECTOR)
            (cls.retained / 'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2) + '\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index),
                           ('baserom.bin', cls.rom)):
            (cls.root / name).write_bytes(data)

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = profile.quotient.ADDRESS if value == 'div' else value[1]
                delta = target - (A + len(data)) - 4
                data += struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        refinement = owner.refine(data, A, mapping)
        rows[0]['instrs'] = refinement['instrs']
        mapping, index = self.indexes(rows)
        calls = {int(row['site'], 16): int(row['target'], 16) for row in refinement['calls']}
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_O2_ET_REL_pure_DIV_API_and_explicit_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__divsi3'})
        self.assertEqual(len(self.bindings), 1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertEqual(self.manifest['ordinary_calls'], [])
        self.assertIsNone(self.manifest['ordinary_call_premise'])
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.quotient.ADDRESS, profile.ZERO})
        self.assertEqual(closure[profile.quotient.ADDRESS]['returns'], [0x0814273E, 0x08142748])
        self.assertEqual(closure[profile.ZERO]['returns'], [profile.ZERO])
        self.assertTrue(all(not row['writes'] and not row['stack_reads'] for row in closure.values()))
        self.assertEqual(dict(self.manifest['native_runtime_frames'])[profile.quotient.ADDRESS]['maximum_additional_stack_bytes'], 4)
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        (self.retained / 'CLI.stdout').write_text(run.stdout)
        (self.retained / 'CLI.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)

    def test_arbitrary_inputs_including_explicit_zero_have_no_numeric_facts(self):
        for sequence in ([0xB510, 'div', 'div', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x2100, 'div', 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(sequence=sequence):
                observed, _ = self.machine(sequence)
                self.assertTrue(observed['complete_native_structural_proof'])
                for key in ('runtime_numeric_return_facts', 'numeric_operand_preconditions', 'nonzero_facts'):
                    self.assertEqual(observed[key], [])
                for key in ('arithmetic_C_equivalence', 'termination_claim', 'memory_safety_claim',
                            'physical_stack_nonalias_claim', 'physical_memory_preservation_claim'):
                    self.assertFalse(observed[key])

    def test_typed_records_and_explicit_selector_are_required(self):
        for key, value in (('data', bytearray(self.body)), ('rom', bytearray(self.rom)),
                           ('mapping', self.mapping.decode()), ('index', self.index.decode()),
                           ('address', True), ('calls', list(self.calls)), ('bindings', list(self.bindings)),
                           ('selector', None), ('selector', old_ordinary.SELECTOR)):
            with self.subTest(key=key, value_type=type(value).__name__), self.assertRaises(ValueError):
                self.native(**{key: value})
        for calls in ({}, {A+2: True}, {True: profile.quotient.ADDRESS},
                      {A+1: profile.quotient.ADDRESS}, {A+len(self.body)-2: profile.quotient.ADDRESS}):
            with self.subTest(calls=calls), self.assertRaises(ValueError):
                profile.bind_calls(calls, self.mapping, A, len(self.body), len(self.rom))

    def test_exact_owner_mapping_body_modes_and_dual_counts(self):
        for key, value in (('mode', 'arm'), ('end', f'0x{A+len(self.body)+2:08X}'),
                           ('instrs', self.rows[0]['instrs']+1)):
            rows = copy.deepcopy(self.rows)
            rows[0][key] = value
            mapping, index = self.indexes(rows)
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        rows = self.rows + [dict(self.rows[0])]
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(b' return', b'1 return', 1))
        data = bytearray(self.body)
        data[0] ^= 1
        with self.assertRaises(ValueError):
            self.native(data=bytes(data))

    def test_runtime_identity_real_zero_edge_and_runtime_counts(self):
        for site in (0x081426BA, 0x08142742, 0x08142748, profile.ZERO):
            rom = bytearray(self.rom)
            rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for number in (1, 2):
            rows = copy.deepcopy(self.rows)
            rows[number]['instrs'] -= 1
            mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)

    def test_exact_actual_calls_reject_ordinary_runtime_thunk_and_alias_targets(self):
        for target in (0x08020000, profile.quotient.ADDRESS+2, profile.quotient.ADDRESS+1,
                       profile.ZERO, 0x08142950, 0x08142B28, match.UDIVSI3_ADDRESS,
                       0x08144378, thunks.START, thunks.START+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: target}, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            self.native(calls={})
        with self.assertRaises(ValueError):
            self.native(bindings={site: '__modsi3' for site in self.calls})
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0xBC10, 0xBC01, 0x4700])

    def test_saved_slots_SP_entry_allocation_returns_and_operations_stay_strict(self):
        sequences = [
            [0xB510, 0x9000, 'div', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 0x9802, 'div', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 0xB081, 'div', 0xB001, 0xBC10, 0xBC01, 0x4700],
            [0xB510, 0x4668, 'div', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 'div', 0xBC01, 0x4700],
            [0xB510, 'div', 0xBC10, 0xBC02, 0x4700],
            [0xB510, 0xDF00, 'div', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 'div', 0xE7FE, 0xBC10, 0xBC01, 0x4700]]
        for sequence in sequences:
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):
                self.machine(sequence)

    def test_manifest_old_selector_numeric_defaults_and_source_admission(self):
        for key, value in (('arithmetic_C_equivalence', True), ('native_runtime_closure', []),
                           ('frame', {}), ('calls', []), ('producer_source_sha256', {})):
            manifest = copy.deepcopy(self.manifest)
            manifest[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)
        with self.assertRaisesRegex(ValueError, 'actual DIV and ordinary calls'):
            old_ordinary.bind_calls(self.calls, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, False, self.calls)
        manifest = {'runtime': profile.quotient.RUNTIME, 'calls': self.manifest['calls'],
                    'divisors': [[site-A, 1] for site in self.calls]}
        with self.assertRaisesRegex(ValueError, 'CFG-proven positive signed32 constant'):
            match.verify_divsi3(self.body, A, self.rom, self.mapping, manifest)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
