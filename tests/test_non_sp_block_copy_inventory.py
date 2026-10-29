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
import non_sp_block_copy_inventory as profile
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants

A, B = 0x08010000, 0x08020000
SOURCE = 'struct record { unsigned int a, b, c, d, e; };\nextern unsigned int func_08020000(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);\nunsigned int func_08010000(unsigned int selector, struct record *destination, const struct record *source, unsigned int value)\n{\n    unsigned int left = value & 0xFF00FF00;\n    unsigned int right = value & 0x0F0F0F0F;\n    switch (selector) {\n    case 0: *destination = *source; return func_08020000(left, right, 0, 0, 1);\n    case 1: return func_08020000(left + right, 0, 0, 0, 2);\n    case 2: return func_08020000(left - right, 0, 0, 0, 3);\n    case 3: return func_08020000(left * right, 0, 0, 0, 4);\n    case 4: return func_08020000(left ^ right, 0, 0, 0, 5);\n    case 5: return func_08020000(left | right, 0, 0, 0, 6);\n    default: return left & right;\n    }\n}\n'

class NonSPBlockCopyInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='non_sp_copy_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_BLOCK_COPY_RETAIN']) \
            if os.environ.get('FFTA_BLOCK_COPY_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        reuse = os.environ.get('FFTA_BLOCK_COPY_REUSE')
        if reuse:
            retained = Path(reuse)
            assert (retained / 'caller.c').read_text() == SOURCE
            pins = json.loads((retained / 'retained-pins.json').read_text())
            for name, digest in pins.items():
                assert hashlib.sha256((retained / name).read_bytes()).hexdigest() == digest
            cls.raw = (retained / 'original.o').read_bytes()
            cls.linked = (retained / 'linked.elf').read_bytes()
            image = match.elf_image(cls.linked)
            symbol, offset = match.function_record(image, 'func_08010000', A, True)
            assert offset == 0
            cls.body = image['text'][:symbol['size']]
        else:
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
        cls.refinement = profile.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(B-match.ROM_BASE+2)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, two_constant_word_switch=True)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
        if reuse:
            cls.manifest = json.loads((Path(reuse) / 'fixture-proof.json').read_text())
            assert cls.manifest['producer_source_sha256'][Path(profile.__file__).name] == profile.sha(Path(profile.__file__).read_bytes())
            cls.instructions = [cls.ins[site] for site in sorted(cls.ins)]
        else:
            cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping,
                cls.index, cls.calls, cls.bindings, selector=profile.SELECTOR)
        for name, data in (('config/functions.json', cls.mapping),
                ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
            (cls.root / name).write_bytes(data)
        if cls.retained and not reuse:
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

    def test_natural_API_CLI(self):
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertEqual(self.manifest['interposed_constant_words'], 2)
        self.assertTrue(self.manifest['copy_pairs'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), json.loads(json.dumps(self.manifest)))
        if self.retained:
            (self.retained / 'fixture-cli.json').write_text(run.stdout)

    def mutate(self, offset, raw, **changes):
        data = bytearray(self.body)
        data[offset:offset+len(raw)] = raw
        return self.changed(data, **changes)

    def test_old_defaults_and_false_keyword_boundaries(self):
        import analyze
        old = owner.refine(self.body, A, self.mapping)
        self.assertFalse(old['cfg_closed'])
        with self.assertRaises(ValueError):
            graph.graph(self.body, A, self.refinement)
        with self.assertRaisesRegex(ValueError, 'block transfers'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                switch_relocations=dict(self.refinement['word_switches'][0]['relocations']),
                allow_switch_constants=True, allow_switch_scalar_frame=True)
        with self.assertRaises(ValueError):
            constants._manifest(self.body, A, self.calls,
                dict(self.refinement['word_switches'][0]['relocations']), constants.FRAME_POLICY)
        for value in (None, 1, 'yes'):
            with self.subTest(value=value):
                bad = analyze.refine_function(self.body, A, json.loads(self.mapping),
                    two_constant_word_switch=value)
                self.assertFalse(bad['cfg_closed'])
                with self.assertRaisesRegex(ValueError, 'Boolean'):
                    graph.graph(self.body, A, self.refinement, two_constant_word_switch=value)

    def test_raw_base_overlap_empty_list_and_writeback_hazards(self):
        for offset, raw in ((0x48, b'\x69\xc8'), (0x4a, b'\x6a\xc1'),
                            (0x48, b'\x00\xc8'), (0x4a, b'\x00\xc1')):
            with self.subTest(offset=offset, raw=raw.hex()), self.assertRaises(ValueError):
                self.mutate(offset, raw)

    def test_copy_pair_list_identity_and_required_actual_operations(self):
        with self.assertRaisesRegex(ValueError, 'copy pair'):
            self.mutate(0x4a, b'\x28\xc1')
        data = bytearray(self.body)
        for offset in (0x48, 0x4a, 0x4c, 0x4e):
            data[offset:offset+2] = b'\x00\x20'
        with self.assertRaisesRegex(ValueError, 'actual non-SP'):
            self.changed(data)
        rows = copy.deepcopy(self.manifest['block_transfers'])
        edges = dict(self.edges)
        edges[A+0x46] = (A+0x4a,)
        with self.assertRaisesRegex(ValueError, 'unbypassable'):
            profile.copy_pairs(rows, edges)

    def test_SP_base_and_stored_SP_lineage_reject(self):
        for offset, raw in ((0x46, b'\x68\x46'), (0x44, b'\x6b\x46')):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'stack-address'):
                self.mutate(offset, raw)
        # Thumb2 SP/PC register lists are outside the authenticated Thumb16 form.
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        for raw in (b'\xbd\xe8\x03\x00', b'\xb0\xe8\x01\x80'):
            instruction = next(decoder.disasm(raw, A, count=1))
            with self.subTest(raw=raw.hex()), self.assertRaisesRegex(ValueError, 'Thumb16'):
                profile.transfer(instruction)

    def test_saved_slot_release_entryLR_and_preserved_origins_reject(self):
        for offset, raw in ((0x52, b'\x01\x90'), (0x92, b'\x02\xb0'),
                            (0x98, b'\x00\x47'), (0x94, b'\xb0\xbc')):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.mutate(offset, raw)
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        self.assertEqual(self.manifest['frame']['maximum_frame_bytes'], 20)
        # r5/r6 overwritten by actual LDM; restoring saved tokens is essential.
        self.assertIn('r5', self.manifest['block_transfers'][0]['origin_kills'])
        self.assertIn('r6', self.manifest['block_transfers'][0]['origin_kills'])

    def test_guard_table_constant_and_unowned_alignment_reject(self):
        for offset, raw in ((0x10, b'\x04\x28'), (0x12, b'\x3c\xdc'),
                            (0x28, struct.pack('<I', A+0x30)),
                            (0x2c, struct.pack('<I', A+0x49)),
                            (0x1e, b'\x01\x00'), (0x08, b'\x00\x22')):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.mutate(offset, raw)
        with self.assertRaisesRegex(ValueError, 'runtime/thunk/function'):
            self.mutate(0x20, struct.pack('<I', match.divsi3.ADDRESS))
        edges = dict(self.edges)
        edges[A+0x46] = (A+0x16,)
        with self.assertRaisesRegex(ValueError, 'bound is bypassed'):
            profile.guard_predecessors(self.ins, edges, A, self.refinement['word_switches'][0])

    def test_cycles_indirect_call_and_local_overlap_reject(self):
        for offset, raw in ((0x58, b'\xf4\xe7'), (0x88, b'\x80\x47\x00\x20')):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.mutate(offset, raw)
        rows = copy.deepcopy(self.rows)
        rows[1]['rom'] = f'0x{A+0x48:08X}'
        rows[1]['end'] = f'0x{A+0x4c:08X}'
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)

    def test_all_ordinary_calls_mapping_binding_and_reserved_exclusions(self):
        with self.assertRaises(ValueError):
            self.native(calls={})
        with self.assertRaises(ValueError):
            self.native(bindings={})
        for target in (match.divsi3.ADDRESS, match.modsi3.ADDRESS, match.UDIVSI3_ADDRESS,
                       next(iter(match.function_thunk.ALIASES.values())), B+2):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({A+0x88:target}, self.mapping, A, len(self.body), len(self.rom))
        rows = copy.deepcopy(self.rows)
        rows[1]['mode'] = 'arm'
        mapping, _ = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping)

    def test_source_ROM_dual_counts_and_manifest_hashes_are_exact(self):
        rows = copy.deepcopy(self.rows)
        rows[0]['instrs'] += 1
        mapping, index = self.indexes(rows)
        with self.assertRaisesRegex(ValueError, 'instruction counts'):
            self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(data=b'\x00'+self.body[1:])
        for field in ('body_sha256', 'mapping_sha256', 'index_sha256', 'producer_source_sha256', 'block_transfers'):
            bad = copy.deepcopy(self.manifest)
            bad[field] = [] if isinstance(bad[field], list) else {}
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=bad)
        for selector in ('two-constants-frame-v1', 'scalar-frame-ordinary-switch-inventory-v1', None):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)

if __name__ == '__main__':
    unittest.main()
