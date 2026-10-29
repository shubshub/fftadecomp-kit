"""Natural agbcc scalar-frame switch and focused inventory contract checks."""
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
if os.environ.get('FFTA_BASE_TOOLS'):
    sys.path.insert(1, os.environ['FFTA_BASE_TOOLS'])
import framed_switch_inventory as profile
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants

A, B = 0x08010000, 0x08020000
SOURCE = '''extern unsigned int func_08020000(unsigned int, unsigned int,
    unsigned int, unsigned int, unsigned int);
unsigned int func_08010000(unsigned int selector, unsigned int value)
{
    unsigned int result;
    switch (selector) {
    case 0: result = func_08020000(value + 1, 0, 0, 0, 1); break;
    case 1: result = func_08020000(value - 2, 0, 0, 0, 2); break;
    case 2: result = func_08020000(value * 3, 0, 0, 0, 3); break;
    case 3: result = func_08020000(value | 4, 0, 0, 0, 4); break;
    case 4: result = func_08020000(value & 5, 0, 0, 0, 5); break;
    case 5: result = func_08020000(value ^ 6, 0, 0, 0, 6); break;
    default: result = value; break;
    }
    return result;
}
'''


class FramedSwitchInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
            ''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                f'{int(r["end"], 16)-int(r["rom"], 16)} {r["instrs"]} return\n'
                for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH',
            Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='framed_switch_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_FRAMED_SWITCH_RETAIN']) \
            if os.environ.get('FFTA_FRAMED_SWITCH_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args,
                cls.root, A, 'src/08010000.c')
            if cls.retained:
                (cls.retained / 'caller.c').write_text(SOURCE)
                (cls.retained / 'compiler.s').write_bytes(runner.read_binary(workspace + '/f.s'))
                (cls.retained / 'original.o').write_bytes(cls.raw)
            script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
            script += '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
            script += '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
            script += '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
            script += 'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }'
            runner.write_text(workspace + '/f.ld', script)
            # Linker-only typed absolute symbol, never an assembly body fixture.
            runner.write_text(workspace + '/f.known.s', '.syntax unified\n.thumb\n'
                '.global func_08020000\n.type func_08020000, %function\n'
                f'.thumb_set func_08020000, 0x{B|1:08X}\n')
            q = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
                f'-T {q}/f.ld -e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            cls.linked = runner.read_binary(workspace + '/f.elf')
            image = match.elf_image(cls.linked)
            match.allocated_text_only(image)
            symbol, offset = match.function_record(image, 'func_08010000', A, True)
            assert original['type'] == 1 and image['type'] == 2 and not image['relocations'] and offset == 0
            cls.body = image['text'][:symbol['size']]
            assert len(image['text']) == len(original['text'])
            assert image['text'][symbol['size']:] == original['text'][symbol['size']:] in (b'', b'\xc0\x46')
            expected = bytearray(original['text'][:symbol['size']])
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            decoder.detail = True
            relocations = []
            for section_index in original['relocations']:
                section = original['sections'][section_index]
                symbols = original['symbol_tables'][section[6]]
                for position in range(0, section[5], 8):
                    site, info = struct.unpack_from('<II', original['section_data'][section_index], position)
                    target = symbols[info >> 8]
                    if info & 255 == 10:
                        assert target['name'] == 'func_08020000' and not target['section']
                        ins = next(decoder.disasm(cls.body[site:site+4], A + site))
                        assert ins.mnemonic == 'bl' and ins.size == 4 and ins.operands[0].imm == B
                        expected[site:site+4] = cls.body[site:site+4]
                    else:
                        assert info & 255 == 2 and target['section'] == original['text_index']
                        addend = struct.unpack_from('<I', original['text'], site)[0]
                        struct.pack_into('<I', expected, site, A + addend)
                    relocations.append([site, info & 255])
            assert bytes(expected) == cls.body
            if cls.retained:
                (cls.retained / 'linked.elf').write_bytes(cls.linked)
                (cls.retained / 'compiler-evidence.json').write_text(json.dumps({
                    'ET_REL': original['type'], 'linked_type': image['type'],
                    'compiler': args.cc, 'flags': args.flags, 'relocations': relocations,
                    'only_standard_linker_relocations_changed': True,
                    'source_or_ELF_admission': False}, indent=2) + '\n')
        cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A+len(cls.body):08X}', 'mode': 'thumb', 'instrs': 0},
            {'rom': f'0x{B:08X}', 'end': f'0x{B+2:08X}', 'mode': 'thumb', 'instrs': 1}]
        mapping, _ = cls.indexes(cls.rows)
        cls.refinement = owner.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(B-match.ROM_BASE+2)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping,
            cls.index, cls.calls, cls.bindings, selector=profile.SELECTOR)
        for name, data in (('config/functions.json', cls.mapping),
                ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root / name).write_bytes(data)
        if cls.retained:
            (cls.retained / 'fixture-proof.json').write_text(json.dumps(cls.manifest, indent=2) + '\n')

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
            index=self.index, calls=self.calls, bindings=self.bindings, selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def changed(self, data, **changes):
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=bytes(data), rom=bytes(rom), **changes)

    def test_natural_compiler_API_CLI_and_unchanged_old_profiles(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertTrue(self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertFalse(self.manifest['arithmetic_C_equivalence'])
        self.assertFalse(self.manifest['termination_claim'])
        self.assertFalse(self.manifest['ordinary_callee_native_proof'])
        self.assertTrue(self.manifest['word_switches'])
        self.assertGreater(self.manifest['frame']['maximum_frame_bytes'], 0)
        self.assertEqual(self.manifest['runtime_calls'], [])
        self.assertEqual(self.manifest['numeric_input_preconditions'], [])
        switch = self.refinement['word_switches'][0]
        with self.assertRaises(ValueError):
            constants.layout(self.body, A, dict(switch['relocations']))
        with self.assertRaisesRegex(ValueError, 'switch evidence excludes fixed frames'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                switch_relocations=dict(switch['relocations']))
        with self.assertRaises(ValueError):
            self.native(selector='two-constants-frame-v1')
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), json.loads(json.dumps(self.manifest)))
        if self.retained:
            (self.retained / 'fixture-cli.json').write_text(run.stdout)

    def test_guard_comparison_and_table_target_authentication(self):
        switch = self.refinement['word_switches'][0]
        for off, raw in ((switch['guard'], b'\xc0\x46'),
                (switch['comparison'], b'\x00\x28'),
                (switch['table'], struct.pack('<I', A + switch['table']))):
            data = bytearray(self.body)
            data[off:off+len(raw)] = raw
            with self.subTest(offset=off), self.assertRaises(ValueError):
                self.changed(data)

    def test_guard_bypass_and_cycle_are_not_accepted(self):
        switch = self.refinement['word_switches'][0]
        site = next(site for site, i in self.ins.items() if site >= A+4 and
            site < A+switch['comparison'] and i.mnemonic not in ('push', 'sub'))
        data = bytearray(self.body)
        struct.pack_into('<H', data, site-A, 0xD000 | ((A+switch['dispatch']-site-4)//2 & 255))
        with self.assertRaises(ValueError):
            self.changed(data)
        data = bytearray(self.body)
        struct.pack_into('<H', data, site-A, 0xD1FE)
        with self.assertRaisesRegex(ValueError, 'CFG cycles'):
            self.changed(data)

    def test_every_call_and_binding_is_required(self):
        for site in self.calls:
            calls = dict(self.calls)
            calls.pop(site)
            with self.subTest(site=site), self.assertRaises(ValueError):
                self.native(calls=calls)
        bindings = dict(self.bindings)
        bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaisesRegex(ValueError, 'bindings differ'):
            self.native(bindings=bindings)
        with self.assertRaises(ValueError):
            profile.bind_calls({A+1: B}, self.mapping, A, len(self.body), len(self.rom))

    def test_runtime_thunk_alias_unknown_and_overlapping_callee_reject(self):
        for target in (0x081426B8, 0x081426BA, 0x08142950, 0x08142952,
                0x08142244, 0x08142246, B+1, B+4):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+4: target}, self.mapping, A, len(self.body), 0x1000000)
        rows = copy.deepcopy(self.rows)
        rows.append(dict(rows[1], rom=f'0x{B+1:08X}'))
        mapping, _ = self.indexes(rows)
        with self.assertRaises(ValueError):
            profile.bind_calls(self.calls, mapping, A, len(self.body), len(self.rom))

    def test_dead_and_live_SP_materialization_and_dynamic_SP_reject(self):
        store = next(site for site, i in self.ins.items() if i.mnemonic == 'str' and '[sp' in i.op_str)
        for raw in (b'\x68\x46', b'\x85\x46', b'\x01\xc8'):
            data = bytearray(self.body)
            data[store-A:store-A+2] = raw
            with self.subTest(raw=raw.hex()), self.assertRaisesRegex(ValueError, 'materialization|block transfers'):
                self.changed(data)

    def test_saved_slot_store_and_unbalanced_release_reject(self):
        allocation = -next(value for _, value in self.manifest['stack_adjustments'] if value < 0)
        store = next(site for site, i in self.ins.items() if i.mnemonic == 'str' and '[sp' in i.op_str)
        data = bytearray(self.body)
        struct.pack_into('<H', data, store-A, 0x9000 | allocation//4)
        with self.assertRaisesRegex(ValueError, 'saved register'):
            self.changed(data)
        release = next(off for off, value in self.manifest['stack_adjustments'] if value > 0)
        data = bytearray(self.body)
        data[release:release+2] = b'\xc0\x46'
        with self.assertRaises(ValueError):
            self.changed(data)

    def test_original_LR_and_preserved_registers_are_required(self):
        data = bytearray(self.body)
        # Replace PUSH {LR} with PUSH {R0}, keeping the same frame shape and
        # recognized return sequence while removing the entry-return token.
        self.assertEqual(self.body[:2], b'\x00\xb5')
        data[:2] = b'\x01\xb4'
        with self.assertRaisesRegex(ValueError, 'original entry LR'):
            self.changed(data)
        data = bytearray(self.body)
        data[4:6] = b'\x00\x24'
        with self.assertRaisesRegex(ValueError, 'r4-r11'):
            self.changed(data)

    def test_exact_owner_dual_counts_ROM_and_partition_boundaries(self):
        for field, value in (('mode', 'arm'), ('instrs', len(self.ins)+1),
                ('end', f'0x{A+len(self.body)-2:08X}')):
            rows = copy.deepcopy(self.rows)
            rows[0][field] = value
            mapping, index = self.indexes(rows)
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(f' {len(self.ins)} return'.encode(), b' 1 return', 1))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.native(rom=bytes(rom))
        data = self.body+b'\0\0\0\0'
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping, index = self.indexes(rows)
        with self.assertRaisesRegex(ValueError, 'unowned complete-owner'):
            self.changed(data, mapping=mapping, index=index)

    def test_manifest_and_explicit_selector_cannot_be_substituted(self):
        manifest, _ = self.native(manifest=json.loads(json.dumps(self.manifest)))
        self.assertEqual(manifest, self.manifest)
        for key in ('frame', 'partition', 'word_switches', 'calls', 'producer_source_sha256', 'ordinary_call_premise'):
            damaged = copy.deepcopy(self.manifest)
            damaged[key] = []
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=damaged)
        for selector in (None, True, 'ordinary', constants.FRAME_POLICY.selector):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)


if __name__ == '__main__':
    unittest.main()
