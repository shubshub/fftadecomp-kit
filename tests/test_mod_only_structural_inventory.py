"""Focused boundaries for the opt-in saved-only arbitrary-scalar MOD inventory."""
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
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import mod_only_structural_inventory as profile
import owner_admission_profile as owner
import zero_aware_remainder_ordinary_inventory as old_ordinary
import zero_aware_remainder_shift_inventory as old_shift

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int value);
int func_08010000(int dividend, int divisor)
{
    return func_08020000(dividend % divisor);
}
'''


class ModOnlyStructuralInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
            ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='mod_only_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        cls.retained = Path(os.environ['FFTA_MOD_ONLY_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            cls.raw = (cls.retained / 'original.o').read_bytes()
            cls.body = (cls.retained / 'body.bin').read_bytes()
            cls.mapping = (cls.retained / 'functions.json').read_bytes()
            cls.index = (cls.retained / 'functions.txt').read_bytes()
            cls.rows = json.loads(cls.mapping)
            cls.manifest = json.loads((cls.retained / 'native-inventory.json').read_bytes())
            cls.bindings = {A + offset: name for offset, name in cls.manifest['calls']}
            cls.calls = {site: profile.remainder.ADDRESS if name == '__modsi3' else int(name[5:], 16)
                         for site, name in cls.bindings.items()}
            assert cls.manifest['producer_source_sha256'][Path(profile.__file__).name] == hashlib.sha256(Path(profile.__file__).read_bytes()).hexdigest()
        else:
            assert not (cls.retained / 'original.o').exists(), 'compile already retained; explicit reuse required'
            (cls.retained / 'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            assert args.flags == '-mthumb-interwork -O2'
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                cls.rows = [
                    {'rom': f'0x{A:08X}', 'end': f'0x{A+len(original["text"]):08X}', 'mode': 'thumb', 'instrs': 0},
                    {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                    {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
                    {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
                mapping, _ = cls.indexes(cls.rows)
                runtime_bindings = {}
                cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A,
                    mapping, len(approved), approved, modsi3_bindings=runtime_bindings)
                assert not literals and set(runtime_bindings.values()) == {'__modsi3'}
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(approved))
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained / name).write_bytes(data)
            (cls.retained / 'compiler-evidence.json').write_text(json.dumps({
                'ELF_type': original['type'], 'compiler': match.DEFAULT_CC, 'flags': args.flags,
                'natural_signed_dynamic_remainder_and_sink': True, 'fixture_compile_count': 1,
                'no_asm_volatile_pragmas_or_steering': True,
                'synthetic_only': True, 'source_or_ELF_admission': False}, indent=2) + '\n')
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        if os.environ.get('FFTA_REUSE_FIXTURE') != '1':
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
                target = profile.remainder.ADDRESS if value == 'mod' else ORDINARY if value == 'ordinary' else value[1]
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

    def test_natural_O2_ET_REL_dynamic_MOD_ordinary_API_and_explicit_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__modsi3', f'func_{ORDINARY:08X}'})
        self.assertEqual(len(self.bindings), 2)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertEqual(len(self.manifest['ordinary_calls']), 1)
        self.assertIn('conditional:', self.manifest['ordinary_call_premise'])
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.remainder.ADDRESS, profile.ZERO})
        self.assertEqual(closure[profile.remainder.ADDRESS]['returns'], [0x08142A12, 0x08142A1C])
        self.assertEqual(closure[profile.ZERO]['returns'], [profile.ZERO])
        self.assertTrue(all(not row['writes'] and not row['stack_reads'] for row in closure.values()))
        frames = dict(self.manifest['native_runtime_frames'])
        self.assertEqual(set(frames), set(closure))
        self.assertTrue(all(row['frame']['preserved'] == 'r4-r11,sp,entry-lr' for row in frames.values()))
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        (self.retained / 'CLI.stdout').write_text(run.stdout)
        (self.retained / 'CLI.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)

    def test_arbitrary_and_zero_operands_pure_calls_and_retained_cycle(self):
        sequences = ([0xB510, 'mod', 'mod', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 0x2100, 'mod', 0xBC10, 0xBC01, 0x4700],
            [0xB510, 0x1C04, 0x2C00, 0xD003, 'mod', 0x3C01, 0xD1FB, 0xBC10, 0xBC01, 0x4700])
        for sequence in sequences:
            with self.subTest(sequence=sequence):
                manifest, _ = self.machine(sequence)
                self.assertTrue(manifest['complete_native_structural_proof'])
                self.assertIsNone(manifest['ordinary_call_premise'])
                self.assertEqual(manifest['ordinary_calls'], [])
                for key in ('runtime_numeric_return_facts', 'numeric_operand_preconditions', 'nonzero_facts'):
                    self.assertEqual(manifest[key], [])
                for key in ('arithmetic_C_equivalence', 'memory_safety_claim', 'physical_stack_nonalias_claim',
                            'physical_memory_preservation_claim', 'termination_claim', 'source_or_ELF_admission'):
                    self.assertFalse(manifest[key])

    def test_typed_records_and_explicit_selector_are_required(self):
        for key, value in (('data', bytearray(self.body)), ('rom', bytearray(self.rom)),
                ('mapping', self.mapping.decode()), ('index', self.index.decode()), ('address', True),
                ('calls', list(self.calls)), ('bindings', list(self.bindings)), ('selector', None),
                ('selector', old_ordinary.SELECTOR)):
            with self.subTest(key=key), self.assertRaises(ValueError):self.native(**{key: value})
        for calls in ({}, {A+2: True}, {True: profile.remainder.ADDRESS},
                {A+1: profile.remainder.ADDRESS}, {A+len(self.body)-2: profile.remainder.ADDRESS}):
            with self.subTest(calls=calls), self.assertRaises(ValueError):
                profile.bind_calls(calls, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            profile.bind_calls(self.calls, b'{}', A, len(self.body), len(self.rom))

    def test_exact_owner_mapping_bytes_modes_and_dual_counts(self):
        for key, value in (('mode', 'arm'), ('end', f'0x{A+len(self.body)+2:08X}'),
                ('instrs', self.rows[0]['instrs']+1)):
            rows = copy.deepcopy(self.rows);rows[0][key] = value;mapping, index = self.indexes(rows)
            with self.subTest(key=key), self.assertRaises(ValueError):self.native(mapping=mapping, index=index)
        rows = self.rows + [dict(self.rows[0])];mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):self.native(index=self.index.replace(b' return', b'1 return', 1))
        data = bytearray(self.body);data[0] ^= 1
        with self.assertRaises(ValueError):self.native(data=bytes(data))

    def test_runtime_identity_real_zero_edge_returns_and_runtime_indices(self):
        for site in (profile.remainder.ADDRESS, 0x08142952, 0x08142A12, 0x08142A16, 0x08142A1C, profile.ZERO):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for number in (2, 3):
            rows = copy.deepcopy(self.rows);rows[number]['instrs'] -= 1;mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):self.native(mapping=mapping, index=index)
        rows = [row for row in self.rows if int(row['rom'],16) != profile.ZERO];mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping, index=index)

    def test_exact_actual_calls_bindings_canonical_alias_and_thunk_exclusions(self):
        for target in (profile.remainder.ADDRESS+1, profile.remainder.ADDRESS+2, profile.ZERO,
                0x081426B8, 0x08142B28, match.UDIVSI3_ADDRESS, 0x08144378, thunks.START, thunks.START+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: target}, self.mapping, A, len(self.body), len(self.rom))
        for sequence in ([0xB510, 'ordinary', 0xBC10, 0xBC01, 0x4700],
                [0xB510, 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):self.machine(sequence)
        calls = dict(self.calls);calls.pop(next(iter(calls)))
        with self.assertRaises(ValueError):self.native(calls=calls)
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = 'func_08142950'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        with self.assertRaises(ValueError):self.native(bindings={})

    def test_ordinary_target_uniqueness_modes_and_span_overlap(self):
        for kind in ('duplicate', 'arm', 'overlap'):
            rows = copy.deepcopy(self.rows)
            if kind == 'duplicate':rows.append(dict(rows[1]))
            elif kind == 'arm':rows[1]['mode'] = 'arm'
            else:rows.append({'rom': f'0x{ORDINARY+1:08X}', 'end': f'0x{ORDINARY+4:08X}', 'mode': 'thumb', 'instrs': 1})
            mapping, index = self.indexes(rows)
            with self.subTest(kind=kind), self.assertRaises(ValueError):self.native(mapping=mapping, index=index)

    def test_saved_slots_SP_entry_allocation_block_transfers_returns_and_calls_stay_strict(self):
        for middle in ([0x9000], [0x9802], [0xB081], [0x4668], [0xA800], [0x4685], [0xC901], [0xC101], [0xDF00]):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                self.machine([0xB510]+middle+['mod',0xBC10,0xBC01,0x4700])
        for sequence in ([0xB510,'mod',0xBC01,0x4700],
                [0xB510,'mod',0xBC10,0xBC02,0x4700],
                [0xB510,'mod',0xE7FE,0xBC10,0xBC01,0x4700]):
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):self.machine(sequence)
        # Entry LR copied into r0 is destroyed by the real runtime call.
        with self.assertRaises(ValueError):self.machine([0xB510,0x4670,'mod',0xBC10,0xBC02,0x4700])
        with self.assertRaises(ValueError):self.machine([0xB510,0xB081,'mod',0xB001,0xBC10,0xBC01,0x4700])

    def test_forged_manifests_runtime_literals_old_numeric_defaults_and_no_source_admission(self):
        for key, value in (('arithmetic_C_equivalence', True), ('native_runtime_closure', []),
                ('native_runtime_frames', []), ('frame', {}), ('calls', []), ('producer_source_sha256', {})):
            manifest = copy.deepcopy(self.manifest);manifest[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):self.native(manifest=manifest)
        for value in (profile.remainder.ADDRESS, thunks.START):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.machine([0xB510,0x4803,'mod',0xBC10,0xBC01,0x4700,0,value&0xFFFF,value>>16])
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body, A, True, self.calls)
        for old in (old_ordinary, old_shift):
            with self.subTest(old=old.SELECTOR), self.assertRaises(ValueError):
                old.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings, selector=old.SELECTOR)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
