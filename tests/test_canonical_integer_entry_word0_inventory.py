"""Natural fifth-argument integer fixture and explicit read-only entry contract checks."""
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
import canonical_integer_entry_word0_inventory as profile
import canonical_integer_scalar_inventory as strict
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int);
int func_08010000(int value, int divisor, int third, int fourth, int fifth)
{
    return func_08020000((value + third + fourth + fifth) / divisor);
}
'''
POLICY = {'schema': profile.entry.SCHEMA, 'words': [0]}


class CanonicalIntegerEntryWord0InventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='entry_word0_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_ENTRY_WORD0_RETAIN'])
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
            'genuine_fifth_argument_word0_runtime_and_ordinary': True,
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

    def machine(self, sequence):
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
        return self.native(data=data, rom=bytes(rom), mapping=mapping, index=index, calls=calls, bindings=bindings)

    def test_natural_fifth_argument_runtime_ordinary_and_exact_ET_REL(self):
        self.assertEqual(match.elf_image(self.raw)['type'], 1)
        self.assertEqual(match.elf_image((self.retained/'linked.elf').read_bytes())['type'], 2)
        self.assertEqual(sorted(self.bindings.values()), ['__divsi3', 'func_08020000'])
        self.assertEqual(self.manifest['runtime_families'], ['__divsi3'])
        self.assertEqual(self.manifest['entry_stack_policy'], POLICY)
        incoming = self.manifest['entry_stack_contract']
        self.assertEqual(incoming, self.manifest['frame']['entry_stack'])
        self.assertEqual(incoming['words'], [0])
        self.assertEqual(incoming['contract'], profile.entry.CONTRACT)
        self.assertTrue(incoming['reads'])
        self.assertTrue(all(offset == 0 and size == 4 for _, offset, size, _ in incoming['reads']))
        self.assertEqual(incoming['loaded_value'], 'unknown scalar; no provenance facts')
        self.assertEqual(self.manifest['entry_ABI_preconditions'], [profile.entry.CONTRACT])
        self.assertEqual(self.manifest['entry_loaded_value_facts'], [])
        self.assertEqual(self.manifest['numeric_input_preconditions'], [])
        self.assertTrue(self.manifest['ordinary_call_premise'].startswith('conditional:'))
        for key in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'memory_safety_claim',
                    'termination_claim', 'physical_caller_stack_nonalias_proof', 'physical_frame_preservation_claim'):
            self.assertFalse(self.manifest[key])
        image = match.elf_image(self.raw)
        original, linked = bytearray(image['text'][:len(self.body)]), bytearray(self.body)
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
                original[site:site+4] = linked[site:site+4] = b'\0'*4
        self.assertEqual(sorted(names), ['__divsi3', 'func_08020000'])
        self.assertEqual(original, linked)

    def test_explicit_selector_and_entry_contract_CLI(self):
        command = [sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--entry-stack-word0', '--rom', str(self.root/'baserom.bin'),
            '--mapping', str(self.root/'config/functions.json'), '--index', str(self.root/'symbols/functions.txt'),
            f'{A:08X}']
        run = subprocess.run(command, capture_output=True, text=True)
        (self.retained/'CLI.stdout').write_text(run.stdout)
        (self.retained/'CLI.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)
        omitted = subprocess.run([part for part in command if part != '--entry-stack-word0'], capture_output=True, text=True)
        (self.retained/'CLI-missing-premise.stderr').write_text(omitted.stderr)
        self.assertEqual(omitted.returncode, 2)
        self.assertIn('--entry-stack-word0', omitted.stderr)

    def test_each_actual_family_uses_unchanged_native_closure_only(self):
        from contextlib import ExitStack
        factories = {'__divsi3': (profile.core.canonical, 'prove_division_closure'),
                     '__modsi3': (profile.core.canonical, 'prove_remainder_closure'),
                     '__udivsi3': (profile.core.quotient, 'prove_quotient_closure'),
                     '__umodsi3': (profile.core.unsigned_remainder, 'runtime_closure')}
        for selected in profile.OPERATIONS:
            with self.subTest(family=selected), ExitStack() as stack:
                for other, (module, name) in factories.items():
                    if other != selected:
                        stack.enter_context(patch.object(module, name, side_effect=AssertionError('uncalled family dispatched')))
                observed, _ = self.machine([0xB510, 0x9802, selected, 0xBC10, 0xBC01, 0x4700])
                self.assertEqual(observed['runtime_families'], [selected])
                self.assertEqual(observed['ordinary_calls'], [])
                self.assertEqual(set(dict(observed['native_runtime_closure'])), {profile.ZERO, profile.OPERATIONS[selected]})
                self.assertEqual(observed['runtime_component_accounting'], [{'family': selected,
                    'closure_factory_invocations': 1, 'native_runtime_components': 2, 'strict_runtime_frame_components': 2}])
                self.assertEqual(observed['runtime_numeric_return_facts'], [])

    def test_explicit_typed_word0_premise_and_actual_read_required(self):
        invalid = [None, False, {}, {'schema': profile.entry.SCHEMA, 'words': []},
            {'schema': profile.entry.SCHEMA, 'words': [False]}, {'schema': profile.entry.SCHEMA, 'words': [4]},
            {'schema': profile.entry.SCHEMA, 'words': [0, 4]}, {'schema': 'other', 'words': [0]},
            {'schema': profile.entry.SCHEMA, 'words': [0], 'initialized': True}]
        for policy in invalid:
            with self.subTest(policy=policy), self.assertRaisesRegex(ValueError, 'word0 ABI contract'):
                self.native(entry_stack_policy=policy)
        with self.assertRaisesRegex(ValueError, 'actual incoming word0 read'):
            self.machine([0xB510, '__divsi3', 0xBC10, 0xBC01, 0x4700])
        # The previous selector and strict frame still reject this same new fixture.
        with self.assertRaises(ValueError):
            strict.verify(self.body, A, self.rom, self.mapping, self.index,
                          self.calls, self.bindings, selector=strict.SELECTOR)

    def test_only_declared_read_no_extra_entry_write_or_saved_slot_access(self):
        for middle in ([0x9803], [0x9002], [0x9003], [0x9001], [0x4668], [0xA800]):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                self.machine([0xB510, 0x9802, *middle, '__divsi3', 0xBC10, 0xBC01, 0x4700])
        # Writing word0 is refused even after an otherwise valid incoming read.
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x9802, 0x9002, '__modsi3', 0xBC10, 0xBC01, 0x4700])

    def test_allocated_scalar_local_initialization_cycles_and_unknown_value(self):
        observed, _ = self.machine([0xB510, 0xB081, 0x9803, 0x9000, 0x9800, 0x2800, 0xD1FD,
            '__divsi3', 'ordinary', 0xB001, 0xBC10, 0xBC01, 0x4700])
        self.assertEqual(observed['frame']['maximum_frame_bytes'], 12)
        self.assertEqual(len(observed['backward_edges']), 1)
        self.assertEqual(observed['entry_stack_contract']['reads'][0][1:3], [0, 4])
        self.assertEqual(observed['entry_loaded_value_facts'], [])
        self.assertEqual(observed['numeric_operand_preconditions'], [])
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0xB081, 0x9803, 0x9001, '__divsi3', 0xB001, 0xBC10, 0xBC01, 0x4700])

    def test_blocks_dynamic_SP_call_clobber_saved_restore_and_entry_LR_refused(self):
        for middle in ([0xC801], [0xC001], [0x4485], [0x4685], [0xA800]):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                self.machine([0xB510, 0x9802, *middle, '__divsi3', 0xBC10, 0xBC01, 0x4700])
        for suffix in ([0xBC20, 0xBC01, 0x4700], [0xBC10, 0xBC02, '__divsi3', 0x4708],
                       [0xBC10, 0xBC02, 0x468E, 0x4700], [0xB001, 0xBC10, 0xBC01, 0x4700]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.machine([0xB510, 0x9802, '__divsi3', *suffix])
        # Loaded incoming scalar cannot become fabricated entry-LR provenance.
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x9902, '__divsi3', 0xBC10, 0xBC01, 0x4708])

    def test_call_completeness_families_and_reserved_targets(self):
        for target in [profile.ZERO, thunks.START, thunks.START+2, ORDINARY+2, A+2, 0x08144378,
                       *[value+2 for value in profile.OPERATIONS.values()]]:
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, 0x9802, '__divsi3', ('call', target), 0xBC10, 0xBC01, 0x4700])
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x9802, 'ordinary', 0xBC10, 0xBC01, 0x4700])
        for changes in ({'calls': {}}, {'bindings': {}}, {'calls': []}, {'bindings': []}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.native(**changes)

    def test_exact_maps_runtime_bytes_counts_and_shared_zero(self):
        for changed in ('duplicate', 'overlap', 'caller_count', 'caller_end', 'DIV_count'):
            rows = copy.deepcopy(self.rows)
            if changed == 'duplicate':
                rows.append(copy.deepcopy(rows[1]))
            elif changed == 'overlap':
                rows[1]['end'] = '0x08142C00'
            elif changed == 'caller_count':
                rows[0]['instrs'] -= 1
            elif changed == 'DIV_count':
                rows[2]['instrs'] -= 1
            else:
                rows[0]['end'] = f'0x{A+len(self.body)+2:08X}'
            mapping, index = self.indexes(rows)
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(b'72 return', b'71 return'))
        for site in (profile.ZERO, profile.OPERATIONS['__divsi3']):
            rom = bytearray(self.rom)
            rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for field, value in (('returns', []), ('writes', [1]), ('stack_reads', [1])):
            closure = copy.deepcopy(dict(self.manifest['native_runtime_closure']))
            closure[profile.OPERATIONS['__divsi3']][field] = value
            with self.subTest(field=field), patch.object(profile.core.canonical, 'prove_division_closure', return_value=closure), self.assertRaises(ValueError):
                self.native()
        original = profile.core.canonical.prove_remainder_closure
        def wrong_zero(*args):
            result = original(*args)
            result[profile.ZERO]['invented'] = True
            return result
        with patch.object(profile.core.canonical, 'prove_remainder_closure', side_effect=wrong_zero), self.assertRaisesRegex(ValueError, 'shared zero'):
            self.machine([0xB510, 0x9802, '__divsi3', '__modsi3', 0xBC10, 0xBC01, 0x4700])

    def test_selector_immutable_types_and_manifest_premise_forgery(self):
        for selector in (None, False, strict.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        for changes in ({'data': bytearray(self.body)}, {'rom': bytearray(self.rom)},
                        {'mapping': bytearray(self.mapping)}, {'index': bytearray(self.index)}, {'address': True}):
            with self.subTest(changes=list(changes)), self.assertRaises(ValueError):
                self.native(**changes)
        for field, value in (('entry_ABI_preconditions', []), ('entry_stack_policy', None),
                ('entry_stack_contract', {}), ('entry_loaded_value_facts', ['zero']),
                ('numeric_operand_preconditions', ['invented']), ('frame', {}), ('native_runtime_frames', [])):
            manifest = copy.deepcopy(self.manifest)
            manifest[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)


if __name__ == '__main__':
    unittest.main()
