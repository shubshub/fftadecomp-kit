"""Natural original-ELF fixture and finite-choice UDIV inventory boundaries."""
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
import udiv_constant_choices_inventory as profile
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as previous_policy

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned int func_08020000(unsigned int value);
unsigned int func_08010000(unsigned int value, int wide)
{
    unsigned int adjusted = func_08020000(value);
    unsigned int divisor = wide ? 8 : 4;
    return adjusted / divisor;
}
'''


class UdivConstantChoicesInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='udiv_choices_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_UDIV_CHOICES_RETAIN'])
        cls.retained.mkdir(parents=True, exist_ok=True)
        (cls.root/'src/08010000.c').write_text(SOURCE)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            assert (cls.retained/'caller.c').read_text() == SOURCE
            cls.raw = (cls.retained/'original.o').read_bytes()
            cls.body = (cls.retained/'body.bin').read_bytes()
            cls.mapping = (cls.retained/'functions.json').read_bytes()
            cls.index = (cls.retained/'functions.txt').read_bytes()
            cls.rows = json.loads(cls.mapping)
        else:
            assert not (cls.retained/'original.o').exists(), 'fixture already compiled; use explicit reuse'
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
                    {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                    {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 59},
                    {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
                mapping, _ = cls.indexes(cls.rows)
                division = {}
                cls.body, _, literals = match.link_calls(runner, workspace, args, original, A,
                    mapping, len(approved), approved, udivsi3_bindings=division)
                assert not literals and set(division.values()) == {'__udivsi3'}
                (cls.retained/'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
            cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained/name).write_bytes(data)
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        refinement = owner.refine(cls.body, A, cls.mapping)
        _, _, _, cls.calls, _ = graph.graph(cls.body, A, refinement)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
            cls.calls, cls.bindings, selector=profile.SELECTOR)
        (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')
        (cls.retained/'fixture-evidence.json').write_text(json.dumps({
            'ELF_type': match.elf_image(cls.raw)['type'], 'compiler': match.DEFAULT_CC,
            'flags': match.DEFAULT_FLAGS, 'natural_original_source': True,
            'fixture_compile_invocations': 1, 'source_or_ELF_admission': False,
            'original_relocation_names': sorted(cls.bindings.values()),
            'dynamic_conditional_divisor_choices': cls.manifest['derived_divisor_choices']}, indent=2)+'\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index),
                           ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence):
        """Explicit synthetic instruction tests, never claimed as original ELF."""
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = profile.quotient.UDIV if value == 'udiv' else ORDINARY if value == 'ordinary' else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF), 0xF800|((delta >> 1)&0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
        mapping, index = self.indexes(rows)
        refinement = owner.refine(data, A, mapping)
        _, _, _, calls, _ = graph.graph(data, A, refinement)
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_O2_original_ET_REL_and_exact_runtime_closure(self):
        self.assertEqual(match.elf_image(self.raw)['type'], 1)
        self.assertEqual(match.elf_image((self.retained/'linked.elf').read_bytes())['type'], 2)
        self.assertEqual(set(self.bindings.values()), {'__udivsi3', 'func_08020000'})
        self.assertEqual([values for _, values in self.manifest['derived_divisor_choices']], [[4, 8]])
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        for key in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'memory_safety_claim', 'termination_claim'):
            self.assertFalse(self.manifest[key])
        self.assertEqual(self.manifest['numeric_operand_preconditions'], [])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'], [])
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure), {profile.quotient.UDIV, profile.ZERO})
        self.assertEqual(closure[profile.quotient.UDIV]['returns'], [0x08142B1C, 0x08142B26])
        self.assertEqual(closure[profile.ZERO]['returns'], [profile.ZERO])
        self.assertEqual(dict(self.manifest['native_runtime_frames'])[profile.quotient.UDIV]['maximum_additional_stack_bytes'], 4)
        self.assertEqual(self.manifest['frame']['maximum_frame_bytes'], 8)

    def test_original_fixture_has_only_two_exact_Thumb_call_relocations(self):
        image = match.elf_image(self.raw)
        relocations = []
        for number in image['relocations']:
            section = image['sections'][number]
            self.assertEqual(section[1], 9)
            for offset in range(0, len(image['section_data'][number]), 8):
                site, info = struct.unpack_from('<II', image['section_data'][number], offset)
                self.assertEqual(info & 255, 10)  # R_ARM_THM_CALL
                relocations.append((site, image['symbol_tables'][section[6]][info >> 8]['name']))
        self.assertEqual(sorted(name for _, name in relocations), ['__udivsi3', 'func_08020000'])
        raw_text = image['text'][:len(self.body)]
        masked_raw, masked_linked = bytearray(raw_text), bytearray(self.body)
        for offset, _ in relocations:
            masked_raw[offset:offset+4] = masked_linked[offset:offset+4] = b'\0'*4
        self.assertEqual(masked_raw, masked_linked)

    def test_standalone_CLI_explicit_profile(self):
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)
        (self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_previous_single_constant_policy_remains_unchanged(self):
        refinement = owner.refine(self.body, A, self.mapping)
        instructions, edges, branches, calls, _ = graph.graph(self.body, A, refinement)
        with self.assertRaisesRegex(ValueError, 'CFG-proven nonzero constant'):
            previous_policy.prove_divisors(instructions, edges, A, branches, calls,
                {site for site, target in calls.items() if target == profile.quotient.UDIV})

    def test_singletons_and_preserved_register_copy(self):
        for constant in (4, 8):
            with self.subTest(constant=constant):
                observed, _ = self.machine([0xB510, 'ordinary', 0x2400|constant, 0x1C21,
                                            'udiv', 0xBC10, 0xBC01, 0x4700])
                self.assertEqual([values for _, values in observed['derived_divisor_choices']], [[constant]])
        observed, _ = self.machine([0xB510, 0x2404, 'ordinary', 0x1C21, 'udiv', 0xBC10, 0xBC01, 0x4700])
        self.assertEqual([values for _, values in observed['derived_divisor_choices']], [[4]])

    def test_zero_other_constant_and_entry_unknown_divisors(self):
        for prefix in ([], [0x2100], [0x2102], [0x210C], [0x2104, 0x3104, 0x3104]):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
                self.machine([0xB510, 'ordinary', *prefix, 'udiv', 0xBC10, 0xBC01, 0x4700])

    def test_conditional_zero_other_unknown_and_uninitialized_joins(self):
        # cmp r0,#0; beq join; movs r1,#8; join: UDIV.
        for first in (0x2100, 0x2102, 0x1C11, 0x46C0):
            with self.subTest(first=first), self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
                self.machine([0xB510, 'ordinary', first, 0x2800, 0xD000, 0x2108,
                              'udiv', 0xBC10, 0xBC01, 0x4700])

    def test_call_clobbers_and_unsupported_arithmetic_kill_facts(self):
        for middle in ([0x2104, 'ordinary'], ['ordinary', 0x2104, 0x3100],
                       ['ordinary', 0x2104, 0x0049], ['ordinary', 0x2104, 0x4051]):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
                self.machine([0xB510, *middle, 'udiv', 0xBC10, 0xBC01, 0x4700])

    def test_every_UDIV_site_checked_and_call_result_has_no_numeric_fact(self):
        with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
            self.machine([0xB510, 'ordinary', 0x2104, 'udiv', 'udiv', 0xBC10, 0xBC01, 0x4700])
        observed, _ = self.machine([0xB510, 'ordinary', 0x2104, 'udiv', 0x2108,
                                   'udiv', 0xBC10, 0xBC01, 0x4700])
        self.assertEqual([values for _, values in observed['derived_divisor_choices']], [[4], [8]])

    def test_SP_writes_escapes_entry_words_saved_slots_and_bad_returns_refused(self):
        for sequence in ([0xB510, 0xB081, 'ordinary', 0x2104, 'udiv', 0xB001, 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x4668, 'ordinary', 0x2104, 'udiv', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x9800, 'ordinary', 0x2104, 'udiv', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x9000, 'ordinary', 0x2104, 'udiv', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 'ordinary', 0x2104, 'udiv', 0xBC20, 0xBC01, 0x4700],
                         [0xB510, 'ordinary', 0x2104, 'udiv', 0x2000, 0x4700]):
            with self.subTest(sequence=sequence), self.assertRaises(ValueError):
                self.machine(sequence)

    def test_complete_calls_reserved_runtime_thunks_and_exact_ordinary_entries(self):
        for target in (profile.quotient.UDIV+2, profile.ZERO, 0x081426B8, 0x08142950,
                       0x08142B28, thunks.START, thunks.START+2, ORDINARY+2, A+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, 'ordinary', ('call', target), 0x2104, 'udiv', 0xBC10, 0xBC01, 0x4700])
        for target in (profile.quotient.UDIV+1, ORDINARY+1):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: profile.quotient.UDIV, A+6: target}, self.mapping, A, 12, len(self.rom))
        for sequence in ([0xB510, 'ordinary', 0xBC10, 0xBC01, 0x4700],
                         [0xB510, 0x2104, 'udiv', 0xBC10, 0xBC01, 0x4700]):
            with self.assertRaises(ValueError):
                self.machine(sequence)
        with self.assertRaises(ValueError):
            self.native(calls={})
        with self.assertRaises(ValueError):
            self.native(bindings={})

    def test_runtime_hashes_zero_body_and_exact_dual_index_counts(self):
        for site in (profile.quotient.UDIV, 0x08142B20, 0x08142B26, profile.ZERO):
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
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(b'59 return', b'60 return'))

    def test_selector_default_off_and_strict_manifest(self):
        for selector in (None, False, 'udivsi3-v1', 'div-only-ordinary-target-state-inventory-v1'):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        for field, value in (('derived_divisor_choices', []), ('numeric_operand_preconditions', ['invented']),
                             ('mapping_sha256', '0'*64), ('frame', {})):
            manifest = copy.deepcopy(self.manifest)
            manifest[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.native(manifest=manifest)


if __name__ == '__main__':
    unittest.main()
