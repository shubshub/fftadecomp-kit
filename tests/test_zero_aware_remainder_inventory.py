"""Exact zero-aware MOD inventory remains separate from source admission."""
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
import status
import zero_aware_remainder_inventory as profile

A = 0x08010000
SOURCE = '''int func_08010000(int value, int divisor)
{
    return (value & 0x7F7F) % divisor;
}
'''


class ZeroAwareRemainderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        cls.approved = Path(selected).read_bytes()
        if hashlib.sha256(cls.approved).hexdigest() != '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19':
            raise ValueError('fixture requires the approved ROM identity')
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='zero_mod_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            assembly = runner.read_binary(f'{workspace}/f.s')
            cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(original["text"]):08X}', 'mode': 'thumb', 'instrs': 0},
                        {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
                        {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
            mapping, _ = cls.indexes(cls.rows)
            cls.bindings = {}
            cls.body, cls.calls, literals = match.link_calls(runner, workspace, args, original, A, mapping,
                len(cls.approved), cls.approved, modsi3_bindings=cls.bindings)
            assert not literals
            linked = runner.read_binary(f'{workspace}/f.elf')
        cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(cls.approved); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        (cls.root/'config/functions.json').write_bytes(cls.mapping)
        (cls.root/'symbols/functions.txt').write_bytes(cls.index)
        (cls.root/'config/data_symbols.json').write_text('{}\n')
        (cls.root/'baserom.bin').write_bytes(cls.rom)
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
            cls.calls, cls.bindings, selector=profile.SELECTOR)
        retained = os.environ.get('FFTA_ZERO_REMAINDER_RETAIN')
        if retained:
            destination = Path(retained); destination.mkdir(parents=True, exist_ok=True)
            for name, data in (('caller.c', SOURCE.encode()), ('original.o', cls.raw),
                               ('compiler.s', assembly), ('linked.elf', linked)):
                path = destination/name
                if path.exists():
                    if path.read_bytes() != data:
                        raise ValueError('retained natural fixture differs')
                else:
                    path.write_bytes(data)

    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping, index=self.index,
                      calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def body_native(self, data):
        rows = copy.deepcopy(self.rows); rows[0]['end'] = f'0x{A+len(data):08X}'
        initial, _ = self.indexes(rows)
        rows[0]['instrs'] = owner.refine(data, A, initial)['instrs']
        mapping, index = self.indexes(rows)
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        refinement = owner.refine(data, A, mapping)
        calls = {int(row['site'],16): int(row['target'],16) for row in refinement['calls']}
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index,
            calls=calls, bindings={site: '__modsi3' for site in calls})

    def machine(self, sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                site = A+len(data); target = profile.remainder.ADDRESS
                delta = target-site-4
                data += struct.pack('<HH', 0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))
        return self.body_native(bytes(data))

    def test_natural_AND_variable_mod_and_complete_zero_closure(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual((len(self.body), len(self.instructions)), (20, 7))
        self.assertEqual(set(self.bindings.values()), {'__modsi3'})
        self.assertEqual(self.manifest['mask_transfers'][0][3], 0x7F7F)
        self.assertTrue(self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {0x08142950, 0x0814274C})
        self.assertEqual(set(closure[0x08142950]['returns']), {0x08142A12, 0x08142A1C})
        self.assertEqual(self.manifest['runtime_cases']['zero']['return_r0'], 0)
        self.assertEqual(self.manifest['frame']['external_calls'], 'complete-native-callee-preservation-v1')
        self.assertEqual(self.native(manifest=self.manifest)[0], self.manifest)
        for divisor in (0, 1, 127):
            self.machine([0xB510, 0x237F, 0x4610, 0x4018, 0x2100|divisor,
                          'mod', 0xBC10, 0xBC02, 0x4708])
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertTrue(json.loads(run.stdout)['complete_native_proof'])
        self.assertNotIn('MATCH', run.stdout)
        retained = os.environ.get('FFTA_ZERO_REMAINDER_RETAIN')
        if retained:
            (Path(retained)/'native-inventory-cli.json').write_text(run.stdout)

    def test_mask_boundary_and_exact_literal_provenance(self):
        for mask in (0, 0x7F7F, 0x7FFF):
            data = self.body[:-4]+struct.pack('<I', mask)
            with self.subTest(mask=mask): self.body_native(data)
        for mask in (0x8000, 0xFFFF, 0xFFFFFFFF):
            data = self.body[:-4]+struct.pack('<I', mask)
            with self.subTest(mask=mask), self.assertRaisesRegex(ValueError, 'signed16 r0'):
                self.body_native(data)
        data = bytearray(self.body); data[4] += 1
        with self.assertRaises(ValueError): self.body_native(bytes(data))
        changed = copy.deepcopy(self.manifest)
        changed['mask_transfers'][0][4] = ['literal', 16, '0'*64]
        with self.assertRaisesRegex(ValueError, 'manifest differs'): self.native(manifest=changed)

    def test_clobbers_unknown_masks_and_all_join_arms(self):
        head = [0xB510, 0x237F]
        tail = ['mod', 0xBC10, 0xBC02, 0x4708]
        for middle in ([0x4610, 0x4010], [0x4610, 0x4018, 0x4610],
                       [0x4610, 0x4018, 'mod'], [0x2A00, 0xD001, 0x4610, 0x4018]):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'signed16 r0'):
                self.machine(head+middle+tail)
        self.machine(head+[0x2A00, 0xD002, 0x4610, 0x4018, 0xE001, 0x4610, 0x4018]+tail)

    def test_zero_entry_hook_returns_and_complete_dependency_identity(self):
        for address in (0x08142950, 0x08142952, 0x08142954, 0x08142A14, 0x08142A16,
                        0x0814274C, 0x08142A1A, 0x08142A1C, 0x08142A12):
            rom = bytearray(self.rom); rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError): self.native(rom=bytes(rom))
        for kind in ('missing_hook', 'count', 'mode', 'span', 'duplicate'):
            rows = copy.deepcopy(self.rows)
            row = next(r for r in rows if r['rom'] == '0x08142950')
            if kind == 'missing_hook': rows = [r for r in rows if r['rom'] != '0x0814274C']
            elif kind == 'count': row['instrs'] += 1
            elif kind == 'mode': row['mode'] = 'arm'
            elif kind == 'span': row['end'] = '0x08142A1C'
            else: rows.append(copy.deepcopy(row))
            mapping, index = self.indexes(rows)
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.native(mapping=mapping, index=index)

    def test_forged_case_effect_frame_and_call_evidence(self):
        for key in ('native_runtime_closure', 'runtime_cases', 'divisor_partition', 'frame', 'calls'):
            changed = copy.deepcopy(self.manifest); changed[key] = []
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=changed)
        with self.assertRaises(ValueError): self.native(bindings={})
        calls = dict(self.calls); calls[next(iter(calls))] = 0x0814274C
        with self.assertRaises(ValueError): self.native(calls=calls)
        with self.assertRaises(ValueError): self.native(selector='default')
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x237F, 0x4610, 0x4018, 'mod', 0xBC02, 0x4708])
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x9000, 0x237F, 0x4610, 0x4018, 'mod', 0xBC10, 0xBC02, 0x4708])

    def test_inventory_selector_has_no_C_match_report_or_status_admission(self):
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                modsi3_context=(self.rom, self.mapping, self.bindings))
        for option in ('--signed-runtime-profile', '--owner-runtime-profile'):
            run = subprocess.run([sys.executable, str(Path(match.__file__)), '--root', str(self.root),
                option, profile.SELECTOR, f'{A:08X}'], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertNotIn('verdict MATCH - byte identical', run.stdout)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))
        destination = self.root/'docs/match/08010000.md'; destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(report)
        result = status.collect(str(self.root), verify=False)
        self.assertEqual((result[1], result[3]), (0, 0))
        self.assertTrue(result[4])
        destination.unlink()

    def test_inventory_context_cannot_mix_or_export_other_policies(self):
        context = (self.rom, self.mapping, self.index, self.bindings, {}, profile.SELECTOR)
        for options in ({'double_context': ()}, {'signed_runtime_context': ()},
                        {'signed_quotient_profile': 'positive-constant-frame-v1'},
                        {'buffer_proof': object()}, {'stack_pointer_compare_profile': 'anything'}):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'isolated inventory'):
                match.verify_leaf_instructions(self.body, A, True, self.calls,
                    remainder_inventory_context=context, **options)
        with self.assertRaisesRegex(ValueError, 'fresh explicit inventory'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                remainder_inventory_context=context[:4]+({'assumed': True}, profile.SELECTOR))


if __name__ == '__main__':
    unittest.main()
