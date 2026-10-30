"""Allocated caller frames compose only with explicit SHIFT MOD inventory."""
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
import match
import match_evidence as evidence
import owner_admission_profile as owner
import zero_aware_remainder_inventory as pure
import zero_aware_remainder_ordinary_inventory as ordinary
import zero_aware_remainder_shift_inventory as shift
import zero_aware_remainder_framed_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int, int, int, int, int);
int func_08010000(int value, int divisor)
{
    return (short)func_08020000(value, 2, 3, 4, 5) % divisor;
}
'''


class FramedRemainderTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='framed_shift_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        retained = os.environ.get('FFTA_FRAMED_REMAINDER_RETAIN')
        cls.retained = Path(retained) if retained else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
            (cls.retained / 'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            if cls.retained:
                (cls.retained / 'original.o').write_bytes(cls.raw)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
            cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(original["text"]):08X}', 'mode': 'thumb', 'instrs': 0},
                {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
                {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
            mapping, _ = cls.indexes(cls.rows)
            runtime = {}
            cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A, mapping,
                len(approved), approved, modsi3_bindings=runtime)
            assert not literals and set(runtime.values()) == {'__modsi3'}
            if cls.retained:
                (cls.retained / 'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
        cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
        cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
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
                'conditional_ordinary_call_ABI': True, 'source_or_ELF_admission': False,
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
                target = pure.remainder.ADDRESS if value == 'mod' else ORDINARY
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

    def test_natural_fixed_O2_allocated_frame_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__modsi3', 'func_08020000'})
        self.assertTrue(any((match.thumb_stack_adjustment(i) or 0) < 0 for i in self.instructions))
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertEqual(self.manifest['frame']['external_calls'], 'existing-direct-call-ABI-summary')
        self.assertIn('conditional', self.manifest['ordinary_call_premise'])
        self.assertIsNone(self.manifest['ordinary_call_stack_bound'])
        self.assertEqual(self.manifest['maximum_MOD_stack_bytes_below_caller_SP'], 8)
        self.assertEqual(set(dict(self.manifest['native_runtime_frames'])), {0x0814274C, pure.remainder.ADDRESS})
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])), persisted)
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), persisted)
        self.assertNotIn('MATCH', run.stdout)
        if self.retained:
            (self.retained / 'native-inventory-cli.json').write_text(run.stdout)

    def test_existing_selectors_still_refuse_allocated_frame(self):
        for module in (ordinary, shift):
            with self.subTest(selector=module.SELECTOR), self.assertRaisesRegex(ValueError, 'frameless caller'):
                module.verify(self.body, A, self.rom, self.mapping, self.index, self.calls,
                    self.bindings, selector=module.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'every call to be canonical MOD'):
            pure.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings, selector=pure.SELECTOR)

    def test_local_bounds_and_saved_slot_stores(self):
        tail = ['ordinary', 0x0400, 0x1400, 0x2103, 'mod', 0xB001, 0xBC10, 0xBC02, 0x4708]
        self.machine([0xB510, 0xB081, 0x9000] + tail)
        for store in (0x9001, 0x9002, 0x9003):
            with self.subTest(store=store), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, store] + tail)

    def test_SP_saved_register_and_entry_LR_restoration(self):
        head = [0xB510, 0xB081, 'ordinary', 0x0400, 0x1400, 0x2103, 'mod']
        for tail in ([0xBC10, 0xBC02, 0x4708],
                     [0xB002, 0xBC10, 0xBC02, 0x4708],
                     [0xB001, 0xBC02, 0x4708],
                     [0xB001, 0xBC10, 0xBC02, 0x4770]):
            with self.subTest(tail=tail), self.assertRaises(ValueError):
                self.machine(head + tail)

    def test_call_clobbers_numeric_facts_at_every_site(self):
        head = [0xB510, 0xB081, 0x0400, 0x1400]
        tail = [0x2103, 'mod', 0xB001, 0xBC10, 0xBC02, 0x4708]
        for middle in (['ordinary'], ['ordinary', 0x4600], ['ordinary', 0x0400],
                       ['ordinary', 0x0400, 0x1400, 0x2103, 'mod']):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'signed16 r0'):
                self.machine(head + middle + tail)

    def test_stack_alias_escape_and_call_crossing(self):
        tail = [0x0400, 0x1400, 0x2103, 'mod', 0xB001, 0xBC10, 0xBC02, 0x4708]
        for head in ([0xB510, 0xB081, 0x4668, 'ordinary'],
                     [0xB510, 0xB081, 0x466A, 'ordinary', 0x6010],
                     [0xB510, 0xB081, 0x466C, 0x3404, 0x6020, 'ordinary']):
            with self.subTest(head=head), self.assertRaises(ValueError):
                self.machine(head + tail)

    def test_canonical_zero_nonzero_runtime_and_stack_bytes_are_exact(self):
        for address in (0x08142950, 0x08142954, 0x08142A10, 0x08142A12,
                        0x08142A14, 0x08142A16, 0x0814274C, 0x08142A1A, 0x08142A1C):
            rom = bytearray(self.rom)
            rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))

    def test_manifest_replay_covers_frame_stack_and_provenance(self):
        for key in ('native_runtime_frames', 'frame', 'ordinary_calls', 'runtime_calls',
                    'divisor_partition', 'native_runtime_closure', 'ordinary_call_stack_bound',
                    'maximum_MOD_stack_bytes_below_caller_SP'):
            changed = copy.deepcopy(self.manifest)
            changed[key] = 'forged'
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=changed)

    def test_fresh_isolated_selector_and_actual_allocation_are_required(self):
        context = (self.rom, self.mapping, self.index, self.bindings, {}, profile.SELECTOR)
        for name in ('remainder_inventory_context', 'remainder_ordinary_inventory_context',
                     'remainder_shift_inventory_context', 'double_context', 'signed_runtime_context'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body, A, True, self.calls,
                    remainder_framed_shift_inventory_context=context, **{name: context})
        with self.assertRaises(ValueError):
            self.native(selector=shift.SELECTOR)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                remainder_framed_shift_inventory_context=context[:4] + ({'stale': True}, profile.SELECTOR))
        with self.assertRaisesRegex(ValueError, 'allocated caller stack frame'):
            self.machine([0xB510, 'ordinary', 0x0400, 0x1400, 0x2103, 'mod', 0xBC10, 0xBC02, 0x4708])

    def test_new_inventory_selector_has_no_source_or_ELF_admission(self):
        for option in ('--signed-runtime-profile', '--owner-runtime-profile'):
            run = subprocess.run([sys.executable, str(Path(match.__file__)), '--root', str(self.root),
                option, profile.SELECTOR, f'{A:08X}'], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertNotIn('verdict MATCH - byte identical', run.stdout)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
