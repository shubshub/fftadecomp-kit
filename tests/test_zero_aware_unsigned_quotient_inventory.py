"""Explicit UDIV/MOD inventory retains exact closure and ordinary ABI limits."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shlex
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence as evidence
import owner_admission_profile as owner
import zero_aware_remainder_inventory as pure
import zero_aware_remainder_shift_inventory as shift
import zero_aware_mixed_runtime_inventory as mixed
import zero_aware_unsigned_quotient_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(unsigned);
int func_08010000(unsigned value, unsigned divisor, int modulus)
{
    return (short)func_08020000(value / divisor) % modulus;
}
'''


class UnsignedQuotientInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='unsigned_quotient_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_UNSIGNED_QUOTIENT_RETAIN']) if os.environ.get('FFTA_UNSIGNED_QUOTIENT_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
            (cls.retained / 'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            # This test-only linker constructs a native fixture, without adding
            # a mixed-runtime source/ELF admission path to match.link_calls.
            targets = dict(profile.OPERATIONS, func_08020000=ORDINARY)
            undefined = {s['name'] for s in original['symbols'] if not s['section'] and s['bind'] == 1}
            assert undefined == set(targets)
            definitions = ['.syntax unified', '.thumb']
            for name, target in sorted(targets.items()):
                definitions += [f'.global {name}', f'.type {name}, %function',
                    f'.thumb_set {name}, 0x{target | 1:08X}']
            runner.write_text(f'{workspace}/f.known.s', '\n'.join(definitions) + '\n')
            runner.write_text(f'{workspace}/f.ld',
                f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) }} /DISCARD/ : {{ *(.comment) *(.note.GNU-stack) }} }}')
            q = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax -T {q}/f.ld '
                f'-e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            linked = match.elf_image(runner.read_binary(f'{workspace}/f.elf'))
            cls.body = linked['text']
            assert len(cls.body) == len(original['text'])
            if cls.retained:
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.original = original
        cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
            {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
            {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 59},
            {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
            {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
        mapping, _ = cls.indexes(cls.rows)
        refinement = owner.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = refinement['instrs']
        cls.calls = {int(r['site'], 16): int(r['target'], 16) for r in refinement['calls']}
        assert set(cls.calls.values()) == set(targets.values())
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(approved); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root / name).write_bytes(data)
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
            cls.calls, cls.bindings, selector=profile.SELECTOR)
        if cls.retained:
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained / name).write_bytes(data)
            (cls.retained / 'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2) + '\n')
            (cls.retained / 'fixture.json').write_text(json.dumps({'ELF_type': original['type'],
                'calls': cls.calls, 'bindings': cls.bindings, 'synthetic_only': True,
                'source_or_ELF_admission': False, 'test_only_linker': True,
                'compiler': [match.DEFAULT_CC, match.DEFAULT_FLAGS]}, indent=2) + '\n')

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
                target = {'mod': pure.remainder.ADDRESS, 'udiv': profile.UDIV, 'ordinary': ORDINARY}.get(value) if type(value) is str else value[1]
                delta = target - (A + len(data)) - 4
                data += struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows); rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        refinement = owner.refine(data, A, mapping); rows[0]['instrs'] = refinement['instrs']
        mapping, index = self.indexes(rows)
        calls = {int(r['site'],16): int(r['target'],16) for r in refinement['calls']}
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    @staticmethod
    def asr(destination=0, source=2, amount=16):
        return 0x1000 | ((amount & 31) << 6) | (source << 3) | destination

    def test_natural_original_O2_ET_REL_full_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__udivsi3', '__modsi3', 'func_08020000'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertIn('conditional', self.manifest['ordinary_call_premise'])
        self.assertEqual(self.manifest['frame']['external_calls'], 'existing-direct-call-ABI-summary')
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.UDIV, pure.remainder.ADDRESS, 0x0814274C})
        self.assertEqual(closure[profile.UDIV]['returns'], [0x08142B1C, 0x08142B26])
        self.assertTrue(all(not p['writes'] and not p['stack_reads'] for p in closure.values()))
        self.assertEqual(len(self.manifest['operand_shift_origins']), 1)
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])), persisted)
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), persisted)
        self.assertNotIn('MATCH', run.stdout)
        if self.retained:
            (self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_UDIV_zero_and_unrestricted_inputs_require_no_signed16_or_nonzero_premise(self):
        manifest, _ = self.machine([0xB510, 0x2100, 'udiv', self.asr(), 0x2100, 'mod', 0xBC10, 0xBC02, 0x4708])
        self.assertEqual(len(manifest['operand_shift_origins']), 1)
        self.assertIsNone(manifest['ordinary_call_premise'])
        self.assertEqual(manifest['frame']['external_calls'], 'complete-native-callee-preservation-v1')
        self.assertEqual(manifest['runtime_cases']['quotient']['zero']['return_r0'], 0)
        self.assertEqual(manifest['shift_transfers'][0][5:7], [-32768, 32767])

    def test_MOD_shift_producer_is_mandatory_and_every_call_kills_result_facts(self):
        tail = ['mod', 0xBC10, 0xBC02, 0x4708]
        for prefix in ([0xB510, 'udiv'], [0xB510, self.asr(), 'udiv'],
                [0xB510, 'udiv', self.asr(), 'ordinary'],
                [0xB510, 'udiv', self.asr(0, 2, 15)], [0xB510, 'udiv', 0x0C10],
                [0xB510, 'udiv', self.asr(), 0x4108]):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError,
                    'signed16 r0|actual exact bounded immediate shift'):
                self.machine(prefix + tail)
        self.machine([0xB510, self.asr(4), 'udiv', 'ordinary', 0x4620] + tail)

    def test_every_CFG_arm_needs_actual_MOD_shift_provenance(self):
        tail = ['mod', 0xBC10, 0xBC02, 0x4708]
        for arm in (0x6810, 0x0C10, 0x4108):
            with self.subTest(arm=arm), self.assertRaisesRegex(ValueError, 'signed16 r0'):
                self.machine([0xB510, 'udiv', 0x2A00, 0xD001, self.asr(), 0xE000, arm] + tail)
        self.machine([0xB510, 'udiv', 0x2A00, 0xD001, self.asr(), 0xE000, self.asr(0, 3, 17)] + tail)

    def test_all_bindings_and_reserved_targets_remain_exact(self):
        for target in (profile.UDIV+2, 0x0814274C, 0x081426B8, 0x08142250):
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, 'udiv', self.asr(), 'mod', ('call', target), 0xBC10, 0xBC02, 0x4708])
        for site in self.calls:
            bindings = dict(self.bindings); bindings.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError): self.native(bindings=bindings)
            calls = dict(self.calls); calls.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError): self.native(calls=calls)
        wrong = dict(self.bindings); wrong[next(s for s, t in self.calls.items() if t == profile.UDIV)] = 'func_08142AB0'
        with self.assertRaises(ValueError): self.native(bindings=wrong)
        for omitted in ('udiv', 'mod'):
            with self.subTest(omitted=omitted), self.assertRaises(ValueError):
                self.machine([0xB510, self.asr(), 'mod' if omitted == 'udiv' else 'udiv', 0xBC10, 0xBC02, 0x4708])

    def test_runtime_identity_zero_hook_returns_and_dual_index_counts_are_exact(self):
        for site in (0x08142AB0, 0x08142AB2, 0x08142B1C, 0x08142B20, 0x08142B24,
                0x08142B26, 0x0814274C, 0x08142A16, 0x08142A1C):
            rom = bytearray(self.rom); rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError): self.native(rom=bytes(rom))
        bad_index = self.index.replace(b'08142AB0 08142B28 120 59', b'08142AB0 08142B28 120 60')
        self.assertNotEqual(bad_index, self.index)
        with self.assertRaises(ValueError): self.native(index=bad_index)
        rows = copy.deepcopy(self.rows); rows[2]['instrs'] = 60
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError): self.native(mapping=mapping, index=index)

    def test_frame_saved_slots_SP_and_alias_escapes_keep_existing_limits(self):
        for sequence in ([0xB510, 0x9000, 'udiv', self.asr(), 'mod', 0xBC10, 0xBC02, 0x4708],
                [0xB510, 'udiv', self.asr(), 'mod', 0xBC02, 0x4708],
                [0xB510, 0xB081, 'udiv', self.asr(), 'mod', 0xB001, 0xBC10, 0xBC02, 0x4708],
                [0xB510, 0x4668, 'ordinary', 'udiv', self.asr(), 'mod', 0xBC10, 0xBC02, 0x4708]):
            with self.subTest(sequence=sequence), self.assertRaises(ValueError): self.machine(sequence)

    def test_manifest_is_fresh_and_complete(self):
        for key in ('native_runtime_closure', 'runtime_cases', 'dependencies', 'frame', 'calls',
                'runtime_calls', 'ordinary_calls', 'ordinary_call_premise', 'operand_shift_origins',
                'unsigned_quotient_operand_policy', 'caller_facts'):
            forged = copy.deepcopy(self.manifest); forged[key] = 'forged'
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=forged)

    def test_default_old_profiles_and_source_ELF_admission_remain_closed(self):
        with self.assertRaises(ValueError): match.verify_leaf_instructions(self.body, A, True, self.calls)
        with self.assertRaises(ValueError):
            shift.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings, selector=shift.SELECTOR)
        with self.assertRaises(ValueError):
            mixed.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings, selector=mixed.SELECTOR)
        for option in ('--signed-runtime-profile', '--owner-runtime-profile'):
            run = subprocess.run([sys.executable, str(Path(match.__file__)), '--root', str(self.root),
                option, profile.SELECTOR, f'{A:08X}'], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, 'func_08010000', A, self.mapping, len(self.rom), self.rom,
                udivsi3_bindings={}, modsi3_bindings={})

    def test_new_selector_requires_isolated_explicit_context(self):
        context = (self.rom, self.mapping, self.index, self.bindings, {}, profile.SELECTOR)
        for name in ('double_context', 'signed_runtime_context', 'remainder_inventory_context',
                'remainder_ordinary_inventory_context', 'remainder_shift_inventory_context',
                'remainder_framed_shift_inventory_context', 'remainder_byte_range_inventory_context',
                'bounded_stack_output_inventory_context', 'bounded_stack_output_zero_index_inventory_context',
                'zero_aware_mixed_inventory_context'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, A, True, self.calls,
                    zero_aware_unsigned_quotient_inventory_context=context, **{name: context})
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                zero_aware_unsigned_quotient_inventory_context=context[:4] + ({'invented': True}, profile.SELECTOR))
        with self.assertRaises(ValueError): self.native(selector=mixed.SELECTOR)


if __name__ == '__main__':
    unittest.main()
