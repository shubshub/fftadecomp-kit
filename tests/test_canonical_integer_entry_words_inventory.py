"""Natural multiple-incoming-argument integer fixture and strict versioned ABI contracts."""
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
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import canonical_integer_entry_words_inventory as profile
import canonical_integer_scalar_inventory as strict
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned int func_08020000(int, int, unsigned int, unsigned int,
    int, int, int, unsigned int);
unsigned int func_08010000(int value, int divisor, unsigned int other, unsigned int other_divisor,
                          int fifth, unsigned int sixth)
{
    int first = (value + fifth) / divisor;
    int second = (value + 7) % (divisor + fifth);
    unsigned int third = other / (other_divisor + sixth);
    unsigned int fourth = (other + 11) % (other_divisor + 5);
    return func_08020000(first, second, third, fourth, value, divisor, fifth, sixth);
}
'''

POLICY = {'schema': profile.entry.SCHEMA, 'words': [0, 1]}


class CanonicalIntegerEntryWordsInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        mapping = (json.dumps(rows, indent=2)+'\n').encode()
        index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                        for row in rows).encode()
        return mapping, index

    @classmethod
    def setUpClass(cls):
        approved = Path(os.environ['FFTA_ROM']).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='entry_words_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_ENTRY_WORDS_RETAIN'])
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
            assert not (cls.retained/'original.o').exists(), 'one natural compile only; reuse retained fixture'
            (cls.retained/'caller.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
            with runner.workspace() as workspace:
                cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                symbol, offset = match.function_record(original, 'func_08010000', A, True)
                assert offset == 0
                # Typed absolute symbol bindings contain no instructions. This
                # standalone fixture link grants no source/ELF admission profile.
                targets = dict(profile.OPERATIONS, func_08020000=ORDINARY)
                definitions = ['.syntax unified', '.thumb']
                for name, target in sorted(targets.items()):
                    definitions.extend((f'.global {name}', f'.type {name}, %function',
                                        f'.thumb_set {name}, 0x{target|1:08X}'))
                runner.write_text(f'{workspace}/f.known.s', '\n'.join(definitions)+'\n')
                script = (f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
                    '.data 0 : { *(.data) } .bss 0 : { *(.bss) } '
                    '.ARM.attributes 0 : { *(.ARM.attributes) } '
                    '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
                    '.rel.iplt 0 : { *(.rel.iplt) } '
                    'ASSERT(SIZEOF(.unexpected) == 0, "unexpected linker stubs") '
                    'ASSERT(SIZEOF(.rel.iplt) == 0, "unexpected dynamic relocations") '
                    '/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }')
                runner.write_text(f'{workspace}/f.ld', script)
                q = shlex.quote(workspace)
                runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
                runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax '
                          f'--orphan-handling=error -T {q}/f.ld -e func_08010000 '
                          f'{q}/f.o {q}/f.known.o -o {q}/f.elf')
                linked_bytes = runner.read_binary(f'{workspace}/f.elf')
                (cls.retained/'linked.elf').write_bytes(linked_bytes)
                linked = match.elf_image(linked_bytes)
                linked_symbol, linked_offset = match.function_record(linked, 'func_08010000', A, True)
                assert linked_symbol['size'] == symbol['size'] and linked_offset == 0
                assert len(linked['text']) == len(original['text'])
                cls.body = linked['text'][:symbol['size']]
                (cls.retained/'section-end-padding.bin').write_bytes(original['text'][symbol['size']:])
                (cls.retained/'typed-symbols.s').write_text('\n'.join(definitions)+'\n')
                (cls.retained/'fixture.ld').write_text(script)
            cls.rows = [
                {'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
                {'rom': f'0x{ORDINARY:08X}', 'end': f'0x{ORDINARY+2:08X}', 'mode': 'thumb', 'instrs': 1},
                {'rom': '0x081426B8', 'end': '0x0814274A', 'mode': 'thumb', 'instrs': 72},
                {'rom': '0x08142950', 'end': '0x08142A1E', 'mode': 'thumb', 'instrs': 102},
                {'rom': '0x08142AB0', 'end': '0x08142B28', 'mode': 'thumb', 'instrs': 59},
                {'rom': '0x08142B28', 'end': '0x08142BE8', 'mode': 'thumb', 'instrs': 95},
                {'rom': '0x0814274C', 'end': '0x0814274E', 'mode': 'thumb', 'instrs': 1}]
            mapping, _ = cls.indexes(cls.rows)
            cls.rows[0]['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
            cls.mapping, cls.index = cls.indexes(cls.rows)
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained/name).write_bytes(data)
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        _, _, _, cls.calls, _ = graph.graph(cls.body, A, owner.refine(cls.body, A, cls.mapping))
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1' and (cls.retained/'native-inventory.json').exists():
            cls.manifest = json.loads((cls.retained/'native-inventory.json').read_text())
            assert cls.manifest['producer_source_sha256'][Path(profile.__file__).name] == profile.sha(Path(profile.__file__).read_bytes())
        else:
            cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                cls.calls, cls.bindings, selector=profile.SELECTOR, entry_stack_policy=POLICY)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')
        (cls.retained/'fixture-evidence.json').write_text(json.dumps({
            'ELF_type': match.elf_image(cls.raw)['type'], 'compiler': match.DEFAULT_CC,
            'flags': match.DEFAULT_FLAGS, 'fixture_compile_invocations': 1,
            'natural_source': True, 'no_asm_volatile_pragmas_or_steering': True,
            'genuine_two_incoming_words_four_runtime_families_and_ordinary': True,
            'source_or_ELF_admission': False, 'entry_stack_policy': POLICY,
            'entry_ABI_preconditions': [profile.entry.CONTRACT],
            'linked_function_symbol_bytes': len(cls.body), 'calls': sorted(cls.bindings.values()),
            'section_end_padding_bytes': len((cls.retained/'section-end-padding.bin').read_bytes())}, indent=2)+'\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR, entry_stack_policy=POLICY)
        values.update(changes)
        return profile.verify(**values)

    def machine(self, sequence, policy=POLICY):
        """Synthetic boundary instructions are distinct from the natural ELF fixture."""
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H', value)
            else:
                target = profile.OPERATIONS[value] if value in profile.OPERATIONS else ORDINARY if value == 'ordinary' else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF), 0xF800|((delta >> 1)&0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, _ = self.indexes(rows)
        rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
        mapping, index = self.indexes(rows)
        _, _, _, calls, _ = graph.graph(data, A, owner.refine(data, A, mapping))
        bindings = profile.bind_calls(calls, mapping, A, len(data), len(self.rom))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings, entry_stack_policy=policy)

    def test_natural_two_incoming_words_four_families_and_conditional_ordinary(self):
        self.assertEqual(match.elf_image(self.raw)['type'], 1)
        self.assertEqual(match.elf_image((self.retained/'linked.elf').read_bytes())['type'], 2)
        self.assertEqual(set(self.bindings.values()), {*profile.OPERATIONS, 'func_08020000'})
        incoming = self.manifest['frame']['entry_stack']
        self.assertEqual(incoming['schema'], profile.entry.SCHEMA)
        self.assertEqual(incoming['words'], [0, 1])
        self.assertEqual({row[1] for row in incoming['reads']}, {0, 4})
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual(self.manifest['entry_stack_policy'], POLICY)
        self.assertEqual(self.manifest['entry_loaded_value_facts'], [])
        self.assertEqual(self.manifest['numeric_operand_preconditions'], [])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'], [])
        self.assertEqual(set(self.manifest['runtime_families']), set(profile.OPERATIONS))
        self.assertTrue(self.manifest['shared_zero_native_and_frame_agreement'])
        self.assertIn('conditional:', self.manifest['ordinary_call_premise'])
        for field in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'termination_claim',
                      'memory_safety_claim', 'physical_caller_stack_nonalias_proof'):
            self.assertFalse(self.manifest[field])

    def test_genuine_ET_REL_relocations_linked_exact_symbol_and_no_instruction_steering(self):
        image, linked = match.elf_image(self.raw), match.elf_image((self.retained/'linked.elf').read_bytes())
        raw, relocated = bytearray(image['text'][:len(self.body)]), bytearray(self.body)
        names = []
        for number in image['relocations']:
            section = image['sections'][number]
            self.assertEqual(section[1], 9)
            for offset in range(0, len(image['section_data'][number]), 8):
                site, info = struct.unpack_from('<II', image['section_data'][number], offset)
                self.assertEqual(info & 255, 10)
                symbol = image['symbol_tables'][section[6]][info >> 8]
                self.assertEqual(symbol['section'], 0)
                names.append(symbol['name'])
                target = ORDINARY if symbol['name'] == 'func_08020000' else profile.OPERATIONS[symbol['name']]
                self.assertEqual(self.calls[A+site], target)
                raw[site:site+4] = relocated[site:site+4] = b'\0'*4
        self.assertEqual(set(names), {*profile.OPERATIONS, 'func_08020000'})
        self.assertEqual(len(names), 5)
        self.assertEqual(raw, relocated)
        symbol, _ = match.function_record(image, 'func_08010000', A, True)
        self.assertEqual(symbol['size'], len(self.body))
        self.assertEqual(len(linked['text']), len(image['text']))

    def test_explicit_API_contract_and_CLI_entry_word_count(self):
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--entry-stack-words', '2', '--rom', str(self.root/'baserom.bin'),
            '--mapping', str(self.root/'config/functions.json'), '--index', str(self.root/'symbols/functions.txt'),
            f'{A:08X}'], capture_output=True, text=True)
        (self.retained/'cli.stdout').write_text(run.stdout)
        (self.retained/'cli.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)
        # Invalid CLI counts and missing explicit flag fail before native work.
        for count in ('1', '7'):
            changed = run.args.copy()
            changed[changed.index('--entry-stack-words')+1] = count
            rejected = subprocess.run(changed, capture_output=True, text=True)
            self.assertEqual(rejected.returncode, 2)
        changed = run.args.copy()
        position = changed.index('--entry-stack-words')
        del changed[position:position+2]
        self.assertEqual(subprocess.run(changed, capture_output=True, text=True).returncode, 2)

    def test_helper_strict_prefix_policy_and_exact_Thumb_SP_LDR_authentication(self):
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        def decode(raw, address=A):
            return next(decoder.disasm(raw, address))
        for count in range(2, 7):
            policy = {'schema': profile.entry.SCHEMA, 'words': list(range(count))}
            self.assertIs(profile.entry.validate(policy), policy)
            for word in range(count):
                instruction = decode(struct.pack('<H', 0x9A00 | (10+word)))
                self.assertEqual(profile.entry.read_word(instruction, 10, policy), 4*word)
            profile.entry.validate_reads([4*word for word in range(count)], policy)
        for policy in (None, {}, {'schema': profile.entry.SCHEMA, 'words': [0]},
                       {'schema': profile.entry.SCHEMA, 'words': list(range(7))},
                       {'schema': profile.entry.SCHEMA, 'words': [False, 1]},
                       {'schema': profile.entry.SCHEMA, 'words': [0, True]},
                       {'schema': profile.entry.SCHEMA, 'words': [0, 1.0]},
                       {'schema': profile.entry.SCHEMA, 'words': [0, 2]},
                       {'schema': profile.entry.SCHEMA, 'words': [1, 0]},
                       {'schema': profile.entry.SCHEMA, 'words': (0, 1)},
                       {'schema': profile.entry.SCHEMA, 'words': [0, 1], 'write': False},
                       {'schema': 'thumb-readonly-entry-stack-word-v1', 'words': [0, 1]},
                       {'schema': 'future', 'words': [0, 1]}):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                profile.entry.validate(policy)
        for raw, address in ((bytes.fromhex('0a90'), A), (bytes.fromhex('0868'), A),
                             (bytes.fromhex('0048'), A), (bytes.fromhex('0aa8'), A),
                             (bytes.fromhex('ddf82800'), A), (bytes.fromhex('0a98'), A+1),
                             (bytes.fromhex('0c98'), A), (bytes.fromhex('0998'), A)):
            with self.subTest(raw=raw.hex(), address=address), self.assertRaises(ValueError):
                profile.entry.read_word(decode(raw, address), 10, POLICY)
        for depth in (True, -1, 1.0):
            with self.subTest(depth=depth), self.assertRaises(ValueError):
                profile.entry.read_word(decode(bytes.fromhex('0a98')), depth, POLICY)
        for offsets in ([0], [0, 0], [0, 4, 8], [0, 2], [False, 4]):
            with self.subTest(offsets=offsets), self.assertRaises(ValueError):
                profile.entry.validate_reads(offsets, POLICY)

    def test_each_declared_word_must_be_actually_read_two_through_six(self):
        for count in range(2, 7):
            policy = {'schema': profile.entry.SCHEMA, 'words': list(range(count))}
            reads = [0x9803+word for word in range(count)]
            observed, _ = self.machine([0xB510, 0xB081, *reads, '__udivsi3',
                0xB001, 0xBC10, 0xBC01, 0x4700], policy=policy)
            self.assertEqual(observed['entry_stack_contract']['words'], list(range(count)))
            self.assertEqual({row[1] for row in observed['entry_stack_contract']['reads']}, {4*word for word in range(count)})
            self.assertEqual(observed['entry_loaded_value_facts'], [])
        for reads in ([], [0x9803], [0x9803, 0x9903], [0x9803, 0x9904, 0x9A05]):
            with self.subTest(reads=reads), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, *reads, '__udivsi3', 0xB001, 0xBC10, 0xBC01, 0x4700])

    def test_writes_outside_entry_aliases_blocks_and_wrong_restoration_rejected(self):
        for extra in ([0x9003], [0x9104], [0x4668], [0xA800], [0xC001], [0xC801], [0x9A05], [0x9001]):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, 0x9803, 0x9904, *extra,
                    '__divsi3', 0xB001, 0xBC10, 0xBC01, 0x4700])
        for suffix in ([0xBC10, 0xBC01, 0x4700], [0xB001, 0xBC20, 0xBC01, 0x4700],
                       [0xB001, 0xBC10, 0xBC01, 0x4708]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, 0x9803, 0x9904, '__divsi3', *suffix])

    def test_cycles_direct_locals_and_unknown_zero_values_grant_no_numeric_facts(self):
        observed, _ = self.machine([0xB510, 0xB081, 0x9803, 0x9904, 0x9000, 0x9800,
            0x2800, 0xD1FD, 0x2100, '__divsi3', '__modsi3', '__udivsi3', '__umodsi3',
            0xB001, 0xBC10, 0xBC01, 0x4700])
        self.assertTrue(observed['backward_edges'])
        self.assertEqual(observed['numeric_operand_preconditions'], [])
        self.assertEqual(observed['runtime_numeric_return_facts'], [])
        self.assertEqual(observed['entry_loaded_value_facts'], [])
        self.assertEqual(observed['ordinary_calls'], [])

    def test_selector_types_manifest_and_explicit_policy_required(self):
        for selector in (None, False, 'canonical-integer-entry-word0-inventory-v1'):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        for changes in ({'data': bytearray(self.body)}, {'rom': bytearray(self.rom)},
                        {'mapping': bytearray(self.mapping)}, {'index': bytearray(self.index)},
                        {'address': True}, {'calls': []}, {'bindings': {}}, {'entry_stack_policy': None}):
            with self.subTest(changes=list(changes)), self.assertRaises(ValueError):
                self.native(**changes)
        for field, value in (('entry_stack_policy', {'schema': profile.entry.SCHEMA, 'words': [0, 1, 2]}),
                             ('entry_loaded_value_facts', ['invented']), ('entry_ABI_preconditions', []),
                             ('frame', {}), ('mapping_sha256', '0'*64)):
            manifest = copy.deepcopy(self.manifest)
            manifest[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)

    def test_exact_calls_mappings_thunks_helper_identity_and_index_counts(self):
        targets = [profile.ZERO, thunks.START, ORDINARY+2, A+2, 0x08144378]
        targets += [target+2 for target in profile.OPERATIONS.values()]
        for target in targets:
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, 0x9802, 0x9903, '__divsi3', ('call', target), 0xBC10, 0xBC01, 0x4700])
        for target in (ORDINARY+1, profile.OPERATIONS['__divsi3']+1):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: target}, self.mapping, A, 10, len(self.rom))
        for number in (0, 2, 3, 4, 5, 6):
            rows = copy.deepcopy(self.rows)
            rows[number]['instrs'] -= 1
            mapping, index = self.indexes(rows)
            with self.subTest(number=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        rows = copy.deepcopy(self.rows)
        rows.append(copy.deepcopy(rows[1]))
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)
        for target in [profile.ZERO, *profile.OPERATIONS.values()]:
            rom = bytearray(self.rom)
            rom[target-match.ROM_BASE] ^= 1
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))

    def test_affected_old_default_and_word0_frame_outputs_exact_on_retained_fixtures(self):
        import local_long_branch_profile as frame
        import readonly_entry_stack_profile as word0
        old_root = Path(os.environ['FFTA_OLD_FIXTURE_ROOT'])
        receipts = []
        for dirname, policy in (('canonical-integer-scalar-inventory-implementation', None),
                                ('canonical-integer-entry-word0-inventory-implementation', {'schema': word0.SCHEMA, 'words': [0]})):
            selected = old_root/dirname/'fixture'
            manifest = json.loads((selected/'native-inventory.json').read_bytes())
            body, mapping = (selected/'body.bin').read_bytes(), (selected/'functions.json').read_bytes()
            instructions, edges, branches, calls, _ = graph.graph(body, A, owner.refine(body, A, mapping))
            actual = frame.prove_frame(instructions, edges, A, branches, calls, entry_stack_policy=policy)
            self.assertEqual(profile.text(actual), profile.text(manifest['frame']))
            receipts.append({'fixture': str(selected), 'entry_policy': policy,
                             'frame_output_byte_identical_to_retained': True, 'new_compiler_jobs': 0,
                             'new_original_owner_API_calls': 0, 'new_targeted_frame_calls': 1})
        (self.retained/'affected-old-frame-regressions.json').write_text(json.dumps(receipts, indent=2)+'\n')

    def test_affected_old_default_word0_and_unknown_schema_refusals_unchanged(self):
        import local_long_branch_profile as frame
        import readonly_entry_stack_profile as word0
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        instructions, edges, branches, calls, _ = graph.graph(
            self.body, A, owner.refine(self.body, A, self.mapping))
        for policy in (None, {'schema': word0.SCHEMA, 'words': [0]},
                       {'schema': 'future', 'words': [0, 1]},
                       {'schema': word0.SCHEMA, 'words': [0, 1]}):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                frame.prove_frame(instructions, edges, A, branches, calls, entry_stack_policy=policy)
        # Direct old helper still accepts only [0], independently of dispatch.
        instruction = next(decoder.disasm(bytes.fromhex('0298'), A))
        self.assertEqual(word0.read_word(instruction, 2, {'schema': word0.SCHEMA, 'words': [0]}), 0)
        with self.assertRaises(ValueError):
            word0.validate({'schema': word0.SCHEMA, 'words': [0, 1]})
        # The unchanged strict inventory and old word0 inventory both still
        # reject the new genuine two-word fixture before canonical closures.
        import canonical_integer_entry_word0_inventory as old
        with self.assertRaises(ValueError):
            strict.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings, selector=strict.SELECTOR)
        with self.assertRaises(ValueError):
            old.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings,
                       selector=old.SELECTOR, entry_stack_policy={'schema': word0.SCHEMA, 'words': [0]})


if __name__ == '__main__':
    unittest.main()
