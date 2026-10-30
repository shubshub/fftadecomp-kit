"""Natural compiler evidence and strict unsigned DIV/MOD inventory boundaries."""
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
import unsigned_divmod_ordinary_inventory as profile
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner
import umod_only_ordinary_inventory as old_umod
import zero_aware_unsigned_quotient_inventory as old_quotient

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned func_08020000(unsigned value);
unsigned func_08010000(unsigned a, unsigned b)
{
    return func_08020000(a / 10 + b % 10);
}
'''


class UnsignedDivmodOrdinaryInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(), ''.join(
            f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode())

    @classmethod
    def setUpClass(cls):
        approved = Path(os.environ['FFTA_ROM']).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='unsigned_divmod_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        cls.retained = Path(os.environ['FFTA_UNSIGNED_DIVMOD_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            cls.raw = (cls.retained/'original.o').read_bytes()
            cls.body = (cls.retained/'body.bin').read_bytes()
            cls.mapping = (cls.retained/'functions.json').read_bytes()
            cls.index = (cls.retained/'functions.txt').read_bytes()
            cls.manifest = json.loads((cls.retained/'native-inventory.json').read_text())
        else:
            assert not (cls.retained/'original.o').exists(), 'fixture already compiled; explicit reuse required'
            (cls.retained/'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                targets = dict(profile.OPERATIONS, func_08020000=ORDINARY)
                undefined = {row['name'] for row in original['symbols'] if not row['section'] and row['bind'] == 1}
                assert undefined == set(targets), undefined
                # Symbol-only definitions link genuine compiler instructions;
                # this supplies no mixed-runtime source/ELF admission route.
                definitions = ['.syntax unified', '.thumb']
                for name, target in sorted(targets.items()):
                    definitions += [f'.global {name}', f'.type {name}, %function',
                        f'.thumb_set {name}, 0x{target|1:08X}']
                runner.write_text(f'{workspace}/f.known.s', '\n'.join(definitions)+'\n')
                script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) }} /DISCARD/ : {{ *(.comment) *(.note.GNU-stack) }} }}'
                runner.write_text(f'{workspace}/f.ld', script)
                q = shlex.quote(workspace)
                runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
                runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax -T {q}/f.ld '
                    f'-e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
                linked_bytes = runner.read_binary(f'{workspace}/f.elf')
                (cls.retained/'linked.elf').write_bytes(linked_bytes)
                linked = match.elf_image(linked_bytes)
                symbol, offset = match.function_record(linked, 'func_08010000', A, True)
                cls.body = linked['text'][offset:offset+symbol['size']]
                assert symbol['size'] == next(row['size'] for row in original['symbols'] if row['name'] == 'func_08010000')
            cls.rows = [
                {'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
                {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 59},
                {'rom': '0x08142B28', 'end': '0x08142BE8', 'mode': 'thumb', 'instrs': 95},
                {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            (cls.retained/'compiler-evidence.json').write_text(json.dumps({'ELF_type': original['type'],
                'compiler': match.DEFAULT_CC, 'flags': match.DEFAULT_FLAGS, 'fixture_compile_count': 1,
                'natural_source': True, 'synthetic_only': True, 'source_or_ELF_admission': False}, indent=2)+'\n')
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained/name).write_bytes(data)
        cls.rows = json.loads(cls.mapping)
        refinement = owner.refine(cls.body, A, cls.mapping)
        cls.calls = {int(row['site'],16): int(row['target'],16) for row in refinement['calls']}
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)
        if os.environ.get('FFTA_REUSE_FIXTURE') != '1' or os.environ.get('FFTA_REFRESH_PROOF') == '1':
            cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                cls.calls, cls.bindings, selector=profile.SELECTOR)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping, index=self.index,
            calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence):
        data = bytearray()
        targets = dict(profile.OPERATIONS, ordinary=ORDINARY)
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = targets[value] if type(value) is str else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH', 0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        refinement = owner.refine(data, A, mapping)
        rows[0]['instrs'] = refinement['instrs']
        mapping, index = self.indexes(rows)
        calls = {int(row['site'],16): int(row['target'],16) for row in refinement['calls']}
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_unsigned_divmod_ordinary_ET_REL_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()), {'__udivsi3', '__umodsi3', 'func_08020000'})
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertTrue(self.manifest['shared_zero_identity_equal'])
        self.assertEqual(self.manifest['numeric_input_preconditions'], [])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'], [])
        self.assertIsNone(self.manifest['entry_stack_contract'])
        self.assertIn('conditional:', self.manifest['ordinary_call_premise'])
        self.assertEqual(self.manifest['frame']['external_calls'], 'existing-direct-call-ABI-summary')
        for key in ('arithmetic_C_equivalence','memory_safety_claim','termination_claim','physical_memory_nonalias_claim','source_or_ELF_admission'):
            self.assertFalse(self.manifest[key])
        closure, frames = dict(self.manifest['native_runtime_closure']), dict(self.manifest['native_runtime_frames'])
        self.assertEqual(set(closure), {profile.ZERO, *profile.OPERATIONS.values()})
        for site, proof in closure.items():
            self.assertEqual(proof['returns'], frames[site]['frame']['returns'])
            self.assertFalse(proof['writes'] or proof['stack_reads'])
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        (self.retained/'cli.stdout').write_text(run.stdout)
        (self.retained/'cli.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(profile.text(json.loads(run.stdout)), profile.text(self.manifest))

    def test_no_ordinary_or_divisor_premise_and_real_zero_paths(self):
        manifest, _ = self.machine([0xB510, '__udivsi3', '__umodsi3', 0xBC10, 0xBC02, 0x4708])
        self.assertEqual(manifest['ordinary_calls'], [])
        self.assertIsNone(manifest['ordinary_call_premise'])
        self.assertEqual(manifest['numeric_input_preconditions'], [])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])

    def test_saved_only_frame_rejects_locals_entry_words_exports_and_clobbers(self):
        prefixes = ([0xB081], [0x4669], [0xA900], [0x9802], [0x9000])
        for prefix in prefixes:
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                self.machine([0xB510]+prefix+['__udivsi3', '__umodsi3', 0xBC10, 0xBC02, 0x4708])
        for suffix in ([0xBC10,0x2400,0xBC02,0x4708], [0xBC10,0xBC02,0x4770]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.machine([0xB510,'__udivsi3','__umodsi3']+suffix)

    def test_cycle_interrupt_block_and_unresolved_jump_refuse(self):
        for extra in ([0x2A00,0xD1FD], [0xDF00], [0xC810], [0x4718]):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                self.machine([0xB510,'__udivsi3','__umodsi3']+extra+[0xBC10,0xBC02,0x4708])

    def test_both_runtime_families_and_complete_bindings_are_required(self):
        for family in profile.OPERATIONS:
            with self.subTest(family=family), self.assertRaises(ValueError):
                self.machine([0xB510,family,'ordinary',0xBC10,0xBC02,0x4708])
        for site in self.calls:
            calls = dict(self.calls); calls.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(calls=calls)
        bindings = dict(self.bindings)
        bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):
            self.native(bindings=bindings)

    def test_reserved_alias_thunk_odd_and_overlapping_ordinary_targets_refuse(self):
        for target in (profile.quotient.UDIV+2, profile.ZERO, profile.ZERO+1, 0x08142950,
                thunks.START, thunks.START+2, ORDINARY+1, ORDINARY+2, A+2):
            calls = {A+2: profile.quotient.UDIV, A+6: profile.OPERATIONS['__umodsi3'], A+10: target}
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, self.mapping, A, 18, len(self.rom))
        rows = copy.deepcopy(self.rows); rows.append(dict(rows[1]))
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)

    def test_full_runtime_and_real_zero_instruction_identities(self):
        for site in (profile.ZERO, profile.quotient.UDIV, 0x08142B20, 0x08142B26,
                profile.OPERATIONS['__umodsi3'], 0x08142BE0, 0x08142BE6):
            rom = bytearray(self.rom); rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))

    def test_caller_and_runtime_dual_indexes_are_exact(self):
        for number in (0,2,3,4):
            rows = copy.deepcopy(self.rows); rows[number]['instrs'] += 1
            mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        index = self.index.replace(f'{A:08X}'.encode(), f'{A+2:08X}'.encode(), 1)
        with self.assertRaises(ValueError):
            self.native(index=index)

    def test_exact_ROM_manifest_selector_and_immutable_input_types(self):
        rom = bytearray(self.rom); rom[A-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError): self.native(rom=bytes(rom))
        with self.assertRaises(ValueError): self.native(mapping=bytearray(self.mapping))
        with self.assertRaises(ValueError): self.native(selector=old_quotient.SELECTOR)
        manifest = copy.deepcopy(self.manifest); manifest['arithmetic_C_equivalence'] = True
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.native(manifest=manifest)

    def test_old_profiles_default_and_C_ELF_admission_remain_closed(self):
        for module in (old_umod,old_quotient):
            with self.subTest(module=module.__name__), self.assertRaises(ValueError):
                module.bind_calls(self.calls, self.mapping, A, len(self.body), len(self.rom))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report, self.root, A))


if __name__ == '__main__':
    unittest.main()
