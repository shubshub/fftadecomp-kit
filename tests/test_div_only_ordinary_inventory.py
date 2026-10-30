"""Focused boundaries for structural DIV-only ordinary-call inventory."""
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
import div_only_ordinary_inventory as profile
import full_width_signed_runtime_inventory as old_mixed
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int value);
int func_08010000(int value, int divisor)
{
    int adjusted = func_08020000(value);
    return adjusted / divisor;
}
'''


class DivOnlyOrdinaryInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        mapping = (json.dumps(rows, indent=2)+'\n').encode()
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='div_only_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_DIV_ONLY_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        (cls.root/'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            cls.raw = (cls.retained/'original.o').read_bytes()
            cls.body = (cls.retained/'body.bin').read_bytes()
            cls.rom = (cls.retained/'baserom.bin').read_bytes()
            cls.mapping = (cls.retained/'functions.json').read_bytes()
            cls.index = (cls.retained/'functions.txt').read_bytes()
            cls.rows = json.loads(cls.mapping)
            cls.manifest = json.loads((cls.retained/'native-inventory.json').read_text())
            cls.calls = {A+offset: profile.quotient.ADDRESS if name == '__divsi3' else int(name[5:], 16)
                         for offset, name in cls.manifest['calls']}
            cls.bindings = {A+offset: name for offset, name in cls.manifest['calls']}
        else:
            assert not (cls.retained/'original.o').exists(), 'fixture compile already retained; use explicit reuse'
            (cls.retained/'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                      objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                cls.rows = [
                    {'rom': f'0x{A:08X}', 'end': f'0x{A+len(original["text"]):08X}', 'mode': 'thumb', 'instrs': 0},
                    {'rom': '0x081426B8', 'end': '0x0814274A', 'mode': 'thumb', 'instrs': 72},
                    {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1},
                    {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1}]
                mapping, _ = cls.indexes(cls.rows)
                division = {}
                cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A,
                    mapping, len(approved), approved, divsi3_bindings=division)
                assert not literals and set(division.values()) == {'__divsi3'}
                (cls.retained/'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            rom = bytearray(approved)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
            cls.rom = bytes(rom)
            cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
            cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                                           cls.calls, cls.bindings, selector=profile.SELECTOR)
            for name, data in (('body.bin', cls.body), ('baserom.bin', cls.rom),
                               ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained/name).write_bytes(data)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')
            (cls.retained/'compiler-evidence.json').write_text(json.dumps({
                'ELF_type': original['type'], 'compiler': match.DEFAULT_CC, 'flags': match.DEFAULT_FLAGS,
                'unmodified_natural_source': True, 'fixture_compile_count': 1,
                'conditional_ordinary_ABI': True, 'synthetic_only': True,
                'source_or_ELF_admission': False}, indent=2)+'\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index),
                           ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)

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
                target = profile.quotient.ADDRESS if value == 'div' else ORDINARY if value == 'ordinary' else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF), 0xF800|((delta >> 1)&0x7FF))
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

    def test_natural_O2_ET_REL_dynamic_division_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__divsi3', 'func_08020000'})
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertFalse(self.manifest['source_or_ELF_admission'] or self.manifest['arithmetic_C_equivalence'])
        self.assertFalse(self.manifest['memory_safety_claim'] or self.manifest['termination_claim'])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'], [])
        self.assertEqual(self.manifest['numeric_operand_preconditions'], [])
        self.assertEqual(self.manifest['nonzero_facts'], [])
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.quotient.ADDRESS, profile.ZERO})
        self.assertEqual(closure[profile.quotient.ADDRESS]['returns'], [0x0814273E, 0x08142748])
        self.assertEqual(closure[profile.ZERO]['returns'], [profile.ZERO])
        self.assertEqual(dict(self.manifest['native_runtime_frames'])[profile.quotient.ADDRESS]['maximum_additional_stack_bytes'], 4)
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)
        (self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_arbitrary_dynamic_and_zero_inputs_have_only_structural_claim(self):
        for sequence in ([0xB510, 'ordinary', 'div', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 'ordinary', 0x2100, 'div', 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(sequence=sequence):
                observed, _ = self.machine(sequence)
                self.assertTrue(observed['complete_native_structural_proof'])
                self.assertEqual(observed['nonzero_facts'], [])
                self.assertEqual(observed['runtime_numeric_return_facts'], [])
                self.assertFalse(observed['arithmetic_C_equivalence'])

    def test_exact_runtime_bytes_zero_edge_and_dual_index_counts(self):
        for site in (0x081426BA, 0x08142742, 0x08142748, profile.ZERO):
            rom = bytearray(self.rom)
            rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for number in (0, 1, 2):
            rows = copy.deepcopy(self.rows)
            rows[number]['instrs'] -= 1
            mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)

    def test_complete_calls_central_reserved_targets_and_exact_ordinary_entries(self):
        for target in (0x081426BA, profile.ZERO, 0x08142950, 0x08142B28,
                       match.UDIVSI3_ADDRESS, 0x08144378, thunks.START, thunks.START+2,
                       ORDINARY+2, A+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, 'ordinary', 'div', ('call', target), 0xBC10, 0xBC01, 0x4700])
        # Thumb BL encodes even targets. Odd target claims belong at the typed
        # binding boundary rather than in a byte sequence that clears bit0.
        for target in (profile.quotient.ADDRESS+1, ORDINARY+1):
            with self.subTest(odd_target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: profile.quotient.ADDRESS, A+6: ORDINARY, A+10: target},
                                   self.mapping, A, 20, len(self.rom))
        for sequence in ([0xB510, 'ordinary', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 'div', 0xBC10, 0xBC01, 0x4700]):
            with self.assertRaises(ValueError):
                self.machine(sequence)
        rows = copy.deepcopy(self.rows)
        rows.append(dict(rows[-1]))
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)
        for site in self.calls:
            calls = dict(self.calls)
            calls.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(calls=calls)

    def test_strict_saved_slots_SP_exports_allocation_returns_and_operations(self):
        for sequence in ([0xB510, 0x9000, 'ordinary', 'div', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 'ordinary', 'div', 0xBC01, 0x4700],
                         [0xB510, 0xB081, 'ordinary', 'div', 0xB001, 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x4668, 'ordinary', 'div', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0xDF00, 'ordinary', 'div', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 'ordinary', 'div', 0x2A00, 0xD001, 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):
                self.machine(sequence)

    def test_exact_manifest_and_explicit_selector(self):
        for key, value in (('arithmetic_C_equivalence', True), ('native_runtime_closure', []),
                           ('frame', {}), ('calls', []), ('producer_source_sha256', {})):
            manifest = copy.deepcopy(self.manifest)
            manifest[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)
        with self.assertRaises(ValueError):
            self.native(selector=old_mixed.SELECTOR)

    def test_old_numeric_mixed_defaults_and_source_admission_remain_closed(self):
        with self.assertRaises(ValueError):
            old_mixed.bind_calls(self.calls, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls)
        manifest = {'runtime': profile.quotient.RUNTIME, 'calls': self.manifest['calls'],
                    'divisors': [[site-A, 1] for site, name in self.bindings.items() if name == '__divsi3']}
        with self.assertRaisesRegex(ValueError, 'CFG-proven positive signed32 constant'):
            match.verify_divsi3(self.body, A, self.rom, self.mapping, manifest)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
