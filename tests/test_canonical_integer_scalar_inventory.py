"""Natural four-family integer fixture and fail-closed scalar inventory checks."""
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
import canonical_integer_scalar_inventory as profile
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import pure_div_inventory as old_div
import owner_runtime_profile as old_numeric

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned int func_08020000(int, int, unsigned int, unsigned int,
    int, int, unsigned int, unsigned int);
unsigned int func_08010000(int value, int divisor, unsigned int other, unsigned int other_divisor)
{
    int first = value / divisor;
    int second = (value + 7) % (divisor + 3);
    unsigned int third = other / other_divisor;
    unsigned int fourth = (other + 11) % (other_divisor + 5);
    return func_08020000(first, second, third, fourth, value, divisor, other, other_divisor);
}
'''


class CanonicalIntegerScalarInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='canonical_integer_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        cls.retained = Path(os.environ['FFTA_CANONICAL_INTEGER_RETAIN'])
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
                cls.calls, cls.bindings, selector=profile.SELECTOR)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest, indent=2)+'\n')
        (cls.retained/'fixture-evidence.json').write_text(json.dumps({
            'ELF_type': match.elf_image(cls.raw)['type'], 'compiler': match.DEFAULT_CC,
            'flags': match.DEFAULT_FLAGS, 'fixture_compile_invocations': 1,
            'natural_source': True, 'source_or_ELF_admission': False,
            'linked_function_symbol_bytes': len(cls.body), 'calls': sorted(cls.bindings.values()),
            'section_end_padding_bytes': len((cls.retained/'section-end-padding.bin').read_bytes())}, indent=2)+'\n')
        for name, data in (('config/functions.json', cls.mapping), ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root/name).write_bytes(data)

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
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

    def test_natural_four_families_allocated_scalar_frame_and_outgoing_words(self):
        self.assertEqual(match.elf_image(self.raw)['type'], 1)
        self.assertEqual(match.elf_image((self.retained/'linked.elf').read_bytes())['type'], 2)
        self.assertEqual(set(self.bindings.values()), {*profile.OPERATIONS, 'func_08020000'})
        instructions, _, _, _, _ = graph.graph(self.body, A, owner.refine(self.body, A, self.mapping))
        from capstone.arm import ARM_OP_MEM, ARM_REG_SP
        stores = [op.mem.disp for item in instructions.values() for op in item.operands
                  if item.mnemonic == 'str' and op.type == ARM_OP_MEM and op.mem.base == ARM_REG_SP]
        self.assertTrue({0, 4, 8, 12} <= set(stores))
        self.assertTrue(match.uses_stack_frame(instructions.values()))
        self.assertEqual(set(self.manifest['runtime_families']), set(profile.OPERATIONS))
        self.assertEqual(set(dict(self.manifest['native_runtime_closure'])), {profile.ZERO, *profile.OPERATIONS.values()})
        self.assertTrue(self.manifest['shared_zero_native_and_frame_agreement'])
        self.assertEqual(sum(row['native_runtime_components'] for row in self.manifest['runtime_component_accounting']), 8)
        self.assertEqual(sum(row['strict_runtime_frame_components'] for row in self.manifest['runtime_component_accounting']), 8)
        self.assertEqual(self.manifest['numeric_operand_preconditions'], [])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'], [])
        for key in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'memory_safety_claim',
                    'termination_claim', 'physical_caller_stack_nonalias_proof'):
            self.assertFalse(self.manifest[key])
        closure, frames = dict(self.manifest['native_runtime_closure']), dict(self.manifest['native_runtime_frames'])
        for site, proof in closure.items():
            self.assertFalse(proof['writes'] or proof['stack_reads'])
            self.assertEqual(proof['returns'], frames[site]['frame']['returns'])

    def test_exact_original_relocations_and_no_linker_instruction_changes(self):
        image, linked = match.elf_image(self.raw), match.elf_image((self.retained/'linked.elf').read_bytes())
        relocated = bytearray(image['text'][:len(self.body)])
        masked = bytearray(self.body)
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
                relocated[site:site+4] = masked[site:site+4] = b'\0'*4
        self.assertEqual(set(names), {*profile.OPERATIONS, 'func_08020000'})
        self.assertEqual(len(names), 5)
        self.assertEqual(relocated, masked)
        symbol, _ = match.function_record(image, 'func_08010000', A, True)
        self.assertEqual(symbol['size'], len(self.body))
        self.assertEqual(len(linked['text']), len(image['text']))
        for name, target in dict(profile.OPERATIONS, func_08020000=ORDINARY).items():
            definitions = [row for row in linked['symbols'] if row['name'] == name]
            self.assertEqual(len(definitions), 1)
            self.assertEqual(definitions[0]['value'], target | 1)

    def test_standalone_explicit_selector_CLI(self):
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        (self.retained/'cli.stdout').write_text(run.stdout)
        (self.retained/'cli.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), self.manifest)

    def test_each_actual_family_only_dispatches_its_own_closure(self):
        factories = {'__divsi3': (profile.canonical, 'prove_division_closure'),
                     '__modsi3': (profile.canonical, 'prove_remainder_closure'),
                     '__udivsi3': (profile.quotient, 'prove_quotient_closure'),
                     '__umodsi3': (profile.unsigned_remainder, 'runtime_closure')}
        from contextlib import ExitStack
        for selected in profile.OPERATIONS:
            with self.subTest(family=selected), ExitStack() as stack:
                for other, (module, name) in factories.items():
                    if other != selected:
                        stack.enter_context(patch.object(module, name, side_effect=AssertionError('uncalled family dispatched')))
                observed, _ = self.machine([0xB510, selected, 0xBC10, 0xBC01, 0x4700])
                self.assertEqual(observed['runtime_families'], [selected])
                self.assertEqual(observed['ordinary_calls'], [])
                self.assertIsNone(observed['ordinary_call_premise'])

    def test_cycle_local_reload_unknown_and_zero_inputs_are_structural(self):
        # Conditional local backedge is retained and has a checked exit path.
        for middle in ([], [0x2100], [0x2800, 0xD1FD]):
            with self.subTest(middle=middle):
                observed, _ = self.machine([0xB510, 0xB081, 0x9000, 0x9800, *middle,
                    '__divsi3', 0xB001, 0xBC10, 0xBC01, 0x4700])
                self.assertEqual(observed['numeric_operand_preconditions'], [])
                self.assertEqual(observed['runtime_numeric_return_facts'], [])
                self.assertEqual(bool(observed['backward_edges']), bool(middle and middle[0] == 0x2800))
        for prefix in ([0x4668], [0xA800], [0x9803], [0x9001], [0x9003], [0x8800, 0x8000, 0xC001], [0xC801]):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, *prefix, '__divsi3', 0xB001, 0xBC10, 0xBC01, 0x4700])

    def test_wrong_stack_restoration_saved_registers_and_returns_rejected(self):
        for suffix in ([0xBC10, 0xBC01, 0x4700], [0xB001, 0xBC20, 0xBC01, 0x4700],
                       [0xB001, 0xBC10, 0xBC01, 0x4708]):
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.machine([0xB510, 0xB081, '__divsi3', *suffix])

    def test_runtime_and_thunk_aliases_interior_unmapped_and_odd_calls_rejected(self):
        targets = [profile.ZERO, thunks.START, thunks.START+2, ORDINARY+2, A+2, 0x08144378]
        targets += [target+2 for target in profile.OPERATIONS.values()]
        for target in targets:
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.machine([0xB510, '__divsi3', ('call', target), 0xBC10, 0xBC01, 0x4700])
        for target in [ORDINARY+1, *[value+1 for value in profile.OPERATIONS.values()]]:
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+2: target}, self.mapping, A, 10, len(self.rom))
        for changes in ({'calls': {}}, {'bindings': {}}, {'calls': []}, {'bindings': []}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.native(**changes)
        with self.assertRaises(ValueError):
            self.machine([0xB510, 'ordinary', 0xBC10, 0xBC01, 0x4700])

    def test_mapping_duplicates_overlaps_and_caller_dual_counts_rejected(self):
        for changed in ('duplicate', 'overlap', 'caller_count', 'caller_end'):
            rows = copy.deepcopy(self.rows)
            if changed == 'duplicate':
                rows.append(copy.deepcopy(rows[1]))
            elif changed == 'overlap':
                rows[1]['end'] = '0x08142C00'
            elif changed == 'caller_count':
                rows[0]['instrs'] -= 1
            else:
                rows[0]['end'] = f'0x{A+len(self.body)+2:08X}'
            mapping, index = self.indexes(rows)
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(b'72 return', b'71 return'))

    def test_each_runtime_identity_zero_and_exact_runtime_counts_rejected(self):
        for site in [profile.ZERO, *profile.OPERATIONS.values()]:
            rom = bytearray(self.rom)
            rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for number in range(2, len(self.rows)):
            rows = copy.deepcopy(self.rows)
            rows[number]['instrs'] -= 1
            mapping, index = self.indexes(rows)
            with self.subTest(row=number), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)

    def test_runtime_complete_returns_effects_and_shared_zero_agreement_rejected(self):
        closure = dict(self.manifest['native_runtime_closure'])
        div = {site: copy.deepcopy(closure[site]) for site in (profile.ZERO, profile.OPERATIONS['__divsi3'])}
        for field, value in (('returns', []), ('writes', [1]), ('stack_reads', [1])):
            changed = copy.deepcopy(div)
            changed[profile.OPERATIONS['__divsi3']][field] = value
            with self.subTest(field=field), patch.object(profile.canonical, 'prove_division_closure', return_value=changed), self.assertRaises(ValueError):
                self.native()
        changed = {site: copy.deepcopy(closure[site]) for site in (profile.ZERO, profile.OPERATIONS['__modsi3'])}
        changed[profile.ZERO]['invented'] = True
        with patch.object(profile.canonical, 'prove_remainder_closure', return_value=changed), self.assertRaisesRegex(ValueError, 'shared zero'):
            self.native()
        original = profile.remainder_frames
        def wrong_frames(*args):
            changed = original(*args)
            dict(changed)[profile.ZERO]['maximum_additional_stack_bytes'] = 4
            return changed
        with patch.object(profile, 'remainder_frames', side_effect=wrong_frames), self.assertRaisesRegex(ValueError, 'shared zero'):
            self.native()

    def test_explicit_selector_immutable_types_and_manifest_rejected(self):
        for selector in (None, False, 'pure-div-saved-only-structural-inventory-v1'):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        for changes in ({'data': bytearray(self.body)}, {'rom': bytearray(self.rom)},
                        {'mapping': bytearray(self.mapping)}, {'index': bytearray(self.index)}, {'address': True}):
            with self.subTest(changes=list(changes)), self.assertRaises(ValueError):
                self.native(**changes)
        for field, value in (('numeric_operand_preconditions', ['invented']), ('mapping_sha256', '0'*64),
                             ('frame', {}), ('native_runtime_frames', [])):
            manifest = copy.deepcopy(self.manifest)
            manifest[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=manifest)

    def test_existing_saved_only_and_numeric_policies_stay_closed(self):
        with self.assertRaises(ValueError):
            old_div.bind_calls(self.calls, self.mapping, A, len(self.body), len(self.rom))
        instructions, edges, branches, calls, _ = graph.graph(self.body, A, owner.refine(self.body, A, self.mapping))
        with self.assertRaisesRegex(ValueError, 'CFG-proven nonzero constant'):
            old_numeric.prove_divisors(instructions, edges, A, branches, calls,
                {site for site, target in calls.items() if target == profile.OPERATIONS['__udivsi3']})
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, A, True, self.calls)


if __name__ == '__main__':
    unittest.main()
