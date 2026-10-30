"""Focused boundaries for UMOD-only ordinary-call scalar-frame inventory."""
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
import umod_only_ordinary_inventory as profile
import div_only_ordinary_inventory as div_only
import unsigned_remainder_closure_inventory as mixed
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned func_08020000(unsigned value);
unsigned func_08010000(unsigned value)
{
    volatile unsigned snapshot = value;
    unsigned result = (unsigned short)func_08020000(value);
    snapshot += result % 30;
    return snapshot;
}
'''


class UmodOnlyOrdinaryInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(),
            ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='umod_only_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_UMOD_ONLY_RETAIN'])
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
            cls.calls = {A+offset: profile.remainder.ADDRESS if name == '__umodsi3' else int(name[5:], 16)
                for offset, name in cls.manifest['calls']}
            cls.bindings = {A+offset: name for offset, name in cls.manifest['calls']}
        else:
            assert not (cls.retained/'original.o').exists(), 'fixture already retained; explicit reuse required'
            (cls.retained/'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                symbol = next(row for row in original['symbols'] if row['name'] == 'func_08010000')
                cls.rows = [
                    {'rom': f'0x{A:08X}', 'end': f'0x{A+symbol["size"]:08X}', 'mode': 'thumb', 'instrs': 0},
                    {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                    {'rom': '0x08142B28', 'end': '0x08142BE8', 'mode': 'thumb', 'instrs': 95},
                    {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
                mapping, _ = cls.indexes(cls.rows)
                runtime = {}
                cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A,
                    mapping, len(approved), approved, umodsi3_bindings=runtime)
                assert not literals and set(runtime.values()) == {'__umodsi3'}
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
            (cls.retained/'compiler-evidence.json').write_text(json.dumps({'ELF_type': original['type'],
                'compiler': match.DEFAULT_CC, 'flags': match.DEFAULT_FLAGS, 'fixture_compile_count': 1,
                'unmodified_natural_source': True, 'synthetic_only': True,
                'source_or_ELF_admission': False}, indent=2)+'\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping, index=self.index,
            calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = (profile.remainder.ADDRESS if value == 'umod' else ORDINARY if value == 'ordinary' else value[1])
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

    def test_natural_O2_ET_REL_scalar_frame_ordinary_UMOD_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__umodsi3', 'func_08020000'})
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertGreater(self.manifest['frame']['maximum_frame_bytes'], 4)
        self.assertEqual([value for _, value in self.manifest['caller_divisors']], [30])
        self.assertEqual(self.manifest['numeric_input_preconditions'], [])
        self.assertIsNone(self.manifest['dividend_requirement'])
        self.assertFalse(self.manifest['source_or_ELF_admission'] or self.manifest['arithmetic_C_equivalence'])
        self.assertFalse(self.manifest['memory_safety_claim'] or self.manifest['termination_claim'])
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.remainder.ADDRESS, profile.ZERO})
        self.assertEqual(closure[profile.remainder.ADDRESS]['returns'], [0x08142B32, 0x08142BAE, 0x08142BDC, 0x08142BE6])
        self.assertTrue(all(not proof['writes'] and not proof['stack_reads'] for proof in closure.values()))
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(profile.text(json.loads(run.stdout)), profile.text(self.manifest))
        (self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_arbitrary_dividend_and_constant_copy_retain_structural_claim_only(self):
        for prefix in ([0x211E], [0x221E, 0x4611]):
            with self.subTest(prefix=prefix):
                observed, _ = self.machine([0xB510, 0xB081, 'ordinary']+prefix+['umod', 0xB001, 0xBC10, 0xBC02, 0x4708])
                self.assertEqual([value for _, value in observed['caller_divisors']], [30])
                self.assertEqual(observed['runtime_numeric_return_facts'], [])
                self.assertIsNone(observed['dividend_requirement'])

    def test_zero_unknown_and_call_killed_divisors_refuse(self):
        for middle in ([], [0x2100], [0x211E, 'ordinary']):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'CFG-proven nonzero unsigned32 constant'):
                self.machine([0xB510, 0xB081, 'ordinary']+middle+['umod', 0xB001, 0xBC10, 0xBC02, 0x4708])

    def test_bypassed_definition_and_conflicting_join_constants_refuse(self):
        for branch in ([0x2800, 0xD000, 0x211E], [0x2800, 0xD001, 0x211E, 0xE000, 0x211F]):
            with self.subTest(branch=branch), self.assertRaisesRegex(ValueError, 'CFG-proven nonzero unsigned32 constant'):
                self.machine([0xB510, 0xB081, 'ordinary']+branch+['umod', 0xB001, 0xBC10, 0xBC02, 0x4708])

    def test_strict_frame_saved_slots_entry_word_SP_export_and_restoration(self):
        sequences = [
            [0xB510, 'ordinary', 0x211E, 'umod', 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 0x4669, 'ordinary', 0x211E, 'umod', 0xB001, 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 0x9001, 'ordinary', 0x211E, 'umod', 0xB001, 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 0x9002, 'ordinary', 0x211E, 'umod', 0xB001, 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 0x9803, 'ordinary', 0x211E, 'umod', 0xB001, 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 'ordinary', 0x211E, 'umod', 0xBC10, 0xBC02, 0x4708],
            [0xB510, 0xB081, 'ordinary', 0x211E, 'umod', 0xB001, 0xBC10, 0x2400, 0xBC02, 0x4708]]
        for sequence in sequences:
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):
                self.machine(sequence)

    def test_actual_cycle_interrupt_and_block_transfer_refuse(self):
        for extra in ([0x2A00, 0xD1FD], [0xDF00], [0xC810]):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, 'ordinary', 0x211E, 'umod']+extra+[0xB001, 0xBC10, 0xBC02, 0x4708])

    def test_runtime_identity_zero_edge_returns_and_dual_index_counts(self):
        for site in (profile.remainder.ADDRESS, 0x08142BE0, 0x08142B32, 0x08142BAE, 0x08142BDC, 0x08142BE6, profile.ZERO):
            rom = bytearray(self.rom)
            rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for number in (0, 2, 3):
            rows = copy.deepcopy(self.rows)
            rows[number]['instrs'] -= 1
            mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)

    def test_complete_call_bindings_reserved_helpers_aliases_and_exact_entries(self):
        for target in (profile.remainder.ADDRESS+2, profile.ZERO, 0x081426B8, 0x08142950,
                match.UDIVSI3_ADDRESS, thunks.START, thunks.START+2, ORDINARY+2, A+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+4: profile.remainder.ADDRESS, A+8: ORDINARY, A+12: target}, self.mapping, A, 20, len(self.rom))
        for target in (profile.remainder.ADDRESS+1, ORDINARY+1):
            with self.subTest(odd=target), self.assertRaises(ValueError):
                profile.bind_calls({A+4: profile.remainder.ADDRESS, A+8: target}, self.mapping, A, 20, len(self.rom))
        for sequence in ([0xB510, 0xB081, 'ordinary', 0xB001, 0xBC10, 0xBC02, 0x4708],
                [0xB510, 0xB081, 0x211E, 'umod', 0xB001, 0xBC10, 0xBC02, 0x4708]):
            with self.assertRaises(ValueError):
                self.machine(sequence)
        for site in self.calls:
            calls = dict(self.calls)
            calls.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(calls=calls)
        rows = copy.deepcopy(self.rows)
        rows.append(dict(rows[1]))
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)

    def test_exact_inputs_manifest_and_explicit_selector(self):
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.native(rom=bytes(rom))
        for key, value in (('arithmetic_C_equivalence', True), ('native_runtime_closure', []),
                ('caller_divisors', []), ('frame', {}), ('producer_source_sha256', {})):
            manifest = copy.deepcopy(self.manifest)
            manifest[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)
        with self.assertRaises(ValueError):
            self.native(selector=div_only.SELECTOR)

    def test_old_runtime_sets_defaults_and_source_ELF_admission_remain_closed(self):
        for module in (div_only, mixed):
            with self.subTest(module=module.__name__), self.assertRaises(ValueError):
                module.bind_calls(self.calls, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
