"""Natural cyclic struct-value LDM caller and focused read-only inventory checks."""
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
from types import SimpleNamespace

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
if os.environ.get('FFTA_BASE_TOOLS'):
    sys.path.insert(1, os.environ['FFTA_BASE_TOOLS'])
import readonly_non_sp_ldm_cycle_inventory as profile
import non_sp_block_copy_inventory as old_profile
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants

A, B = 0x08010000, 0x08020000
SOURCE = 'struct scalar { unsigned int value; };\nextern unsigned int func_08020000(struct scalar, unsigned int,\n    unsigned int, unsigned int, unsigned int);\ntypedef unsigned int (*callback_t)(struct scalar, unsigned int,\n    unsigned int, unsigned int, unsigned int);\nunsigned int func_08010000(unsigned int selector, const struct scalar *items,\n    unsigned int count, callback_t callback)\n{\n    unsigned int result = 0;\n    switch (selector) {\n    case 0:\n        while (count != 0) {\n            result += callback(*items++, result, 0, 0, count);\n            count--;\n        }\n        break;\n    case 1:\n        while (count != 0) {\n            result = func_08020000(*items++, result, 0, 0, count);\n            count--;\n        }\n        break;\n    case 2: result = func_08020000(*items, 2, 0, 0, count); break;\n    case 3: result = func_08020000(*items, 3, 0, 0, count); break;\n    case 4: result = func_08020000(*items, 4, 0, 0, count); break;\n    case 5: result = func_08020000(*items, 5, 0, 0, count); break;\n    case 6: result = func_08020000(*items, 6, 0, 0, count); break;\n    case 7: result = func_08020000(*items, 7, 0, 0, count); break;\n    default: result = count; break;\n    }\n    return result;\n}\n'


class ReadonlyNonSPLDMCycleInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='readonly_ldm_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_READONLY_LDM_RETAIN']) \
            if os.environ.get('FFTA_READONLY_LDM_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        if os.environ.get('FFTA_REUSE_FIXTURE') == '1':
            assert cls.retained and (cls.retained / 'caller.c').read_text() == SOURCE
            cls.raw = (cls.retained / 'original.o').read_bytes()
            cls.linked = (cls.retained / 'linked.elf').read_bytes()
            cls.body = (cls.retained / 'body.bin').read_bytes()
            cls.mapping = (cls.retained / 'functions.json').read_bytes()
            cls.index = (cls.retained / 'functions.txt').read_bytes()
            cls.rows = json.loads(cls.mapping)
            cls.refinement = owner.refine(cls.body, A, cls.mapping)
            cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement)
            rom = bytearray(thunks.END-match.ROM_BASE)
            for target in cls.calls.values():
                if target in thunks.ALIASES.values():
                    struct.pack_into('<HH', rom, target-match.ROM_BASE,
                        0x4700+(((target-thunks.START)//4)<<3), 0x46c0)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
            cls.rom = bytes(rom)
            cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(cls.rom))
            cls.manifest = json.loads((cls.retained / 'fixture-proof.json').read_text())
            assert cls.manifest['producer_source_sha256'][Path(profile.__file__).name] == profile.sha(Path(profile.__file__).read_bytes())
            for name, data in (('config/functions.json', cls.mapping),
                    ('symbols/functions.txt', cls.index), ('baserom.bin', cls.rom)):
                (cls.root / name).write_bytes(data)
            return
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
                f'.thumb_set func_08020000, 0x{B|1:08X}\n' + ''.join(
                    f'.global {name}\n.type {name}, %function\n.thumb_set {name}, 0x{target|1:08X}\n'
                    for name, target in thunks.ALIASES.items()))
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
                        assert target['name'] in ('func_08020000', *thunks.ALIASES) and not target['section']
                        ins = next(decoder.disasm(cls.body[site:site+4], A + site))
                        expected_target = B if target['name'] == 'func_08020000' else thunks.ALIASES[target['name']]
                        assert ins.mnemonic == 'bl' and ins.size == 4 and ins.operands[0].imm == expected_target
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
        cls.rows += [{'rom': f'0x{target:08X}', 'end': f'0x{target+2:08X}',
            'mode': 'thumb', 'instrs': 1} for target in thunks.ALIASES.values()]
        mapping, _ = cls.indexes(cls.rows)
        cls.refinement = owner.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement)
        cls.helper_targets = {target for target in cls.calls.values() if target in thunks.ALIASES.values()}
        assert cls.helper_targets
        rom = bytearray(thunks.END-match.ROM_BASE)
        for target in cls.helper_targets:
            register = (target-thunks.START)//4
            struct.pack_into('<HH', rom, target-match.ROM_BASE, 0x4700+(register<<3), 0x46c0)
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
            for name, data in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained / name).write_bytes(data)
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

    @staticmethod
    def decoded(data, address=A):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return list(decoder.disasm(data, address))

    def first_load(self):
        return next(item for item in self.ins.values() if item.mnemonic == 'ldm')

    def test_natural_struct_value_cycle_switch_frame_API_CLI(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertTrue(self.manifest['inventory_only'])
        self.assertTrue(self.manifest['cycles_present'])
        self.assertEqual(self.manifest['readonly_LDM_policy'], profile.LDM_POLICY)
        self.assertGreater(len(self.manifest['readonly_LDM_loads']), 0)
        self.assertEqual(self.manifest['interposed_constant_words'], 0)
        self.assertEqual(len(self.manifest['word_switches']), 1)
        self.assertGreater(self.manifest['frame']['maximum_frame_bytes'], 0)
        self.assertTrue(any(name in thunks.ALIASES for _, name in self.manifest['calls']))
        self.assertTrue(any(name not in thunks.ALIASES for _, name in self.manifest['calls']))
        for field in ('source_or_ELF_admission', 'arithmetic_C_equivalence',
                'memory_safety_claim', 'nonalias_claim', 'termination_claim'):
            self.assertFalse(self.manifest[field])
        environment = dict(os.environ)
        environment['PYTHONPATH'] = os.pathsep.join([str(Path(profile.__file__).parent),
            str(Path(match.__file__).parent)])
        result = subprocess.run([sys.executable, profile.__file__, '--profile', profile.SELECTOR,
            '--rom', str(self.root/'baserom.bin'), '--mapping', str(self.root/'config/functions.json'),
            '--index', str(self.root/'symbols/functions.txt'), hex(A)],
            text=True, capture_output=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), self.manifest)
        if self.retained:
            (self.retained/'fixture-CLI.json').write_text(result.stdout)

    def test_exact_original_C901_decoder_and_unknown_origin_kills(self):
        observed = profile.readonly_load(self.decoded(bytes.fromhex('01c9'))[0])
        self.assertEqual(observed['bytes'], '01c9')
        self.assertEqual(observed['base'], 'r1')
        self.assertEqual(observed['registers'], ['r0'])
        self.assertEqual(observed['origin_kills'], ['r0', 'r1'])
        self.assertEqual(observed['writeback_bytes'], 4)
        self.assertFalse(observed['flags_written'])

    def test_raw_encoding_operand_list_and_writeback_must_agree(self):
        item = self.decoded(bytes.fromhex('01c9'))[0]
        def forged(**changes):
            fields = {name: getattr(item, name) for name in
                ('bytes', 'size', 'mnemonic', 'cc', 'writeback', 'operands', 'address', 'reg_name', 'regs_access')}
            fields.update(changes)
            return SimpleNamespace(**fields)
        for changes in ({'bytes': bytes.fromhex('00c9')},
                {'bytes': bytes.fromhex('03c9')}, {'writeback': False},
                {'operands': item.operands[:-1]},
                {'regs_access': lambda: ([match.ARM_REG_R1], [match.ARM_REG_R0])}):
            with self.subTest(changes=tuple(changes)), self.assertRaises(ValueError):
                profile.readonly_load(forged(**changes))

    def test_STM_base_in_list_SP_LR_PC_and_other_forms_reject(self):
        for encoded in ('01c1', '03c9', '01bd', '0147', '0868'):
            with self.subTest(encoded=encoded), self.assertRaises(ValueError):
                profile.readonly_load(self.decoded(bytes.fromhex(encoded))[0])
        item = self.decoded(bytes.fromhex('01c9'))[0]
        fields = {name: getattr(item, name) for name in
            ('bytes', 'size', 'mnemonic', 'cc', 'writeback', 'operands', 'address', 'reg_name', 'regs_access')}
        fields['regs_access'] = lambda: ([match.ARM_REG_SP], [match.ARM_REG_R0, match.ARM_REG_SP])
        with self.assertRaises(ValueError):
            profile.readonly_load(SimpleNamespace(**fields))

    def test_actual_STM_substitution_rejects_in_complete_API(self):
        item = self.first_load()
        data = bytearray(self.body)
        value = int.from_bytes(item.bytes, 'little') & ~0x0800
        struct.pack_into('<H', data, item.address-A, value)
        with self.assertRaises(ValueError):
            self.changed(data)

    def test_loaded_preserved_register_loses_entry_origin(self):
        # push {lr}; ldmia r1!,{r4}; pop {r0}; bx r0.
        # An opaque loaded r4 cannot retain its incoming saved-register token.
        items = self.decoded(bytes.fromhex('00b510c901bc0047'))
        profile.readonly_load(items[1])
        instructions = {item.address: item for item in items}
        edges = {item.address: (() if item is items[-1] else (item.address+item.size,))
            for item in items}
        with self.assertRaisesRegex(ValueError, 'restore SP, r4-r11'):
            profile.frame.prove_frame(instructions, edges, A, {}, {})

    def test_SP_materialization_and_dynamic_SP_reject(self):
        for encoded in ('6846', '8544'):
            data = bytearray(self.body)
            data[2:4] = bytes.fromhex(encoded)
            with self.subTest(encoded=encoded), self.assertRaises(ValueError):
                self.changed(data)

    def test_saved_slots_incoming_words_and_release_require_strict_frame(self):
        for raw in ('00b5009001bc0047', '019800477047', '00b501b001bc0047'):
            items = self.decoded(bytes.fromhex(raw))
            instructions = {item.address: item for item in items}
            edges = {item.address: (() if item is items[-1] else (item.address+item.size,))
                for item in items}
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                profile.frame.prove_frame(instructions, edges, A, {}, {})

    def test_guard_tamper_and_nonreturning_cycle_reject(self):
        switch = self.refinement['word_switches'][0]
        data = bytearray(self.body)
        struct.pack_into('<H', data, switch['guard'], 0x46c0)
        with self.assertRaises(ValueError):
            self.changed(data)
        site = self.manifest['actual_cycle_back_edges'][0][0]
        data = bytearray(self.body)
        struct.pack_into('<H', data, site-A, 0xe7fe)
        with self.assertRaises(ValueError):
            self.changed(data)

    def test_every_call_binding_helper_identity_and_reserved_class_reject(self):
        calls = dict(self.calls)
        calls.pop(next(iter(calls)))
        with self.assertRaises(ValueError):
            self.native(calls=calls)
        bindings = dict(self.bindings)
        bindings[next(iter(bindings))] = 'func_08142250'
        with self.assertRaises(ValueError):
            self.native(bindings=bindings)
        target = next(target for target in self.calls.values() if target in thunks.ALIASES.values())
        rom = bytearray(self.rom)
        rom[target-match.ROM_BASE+2:target-match.ROM_BASE+4] = b'\0\0'
        with self.assertRaises(ValueError):
            self.native(rom=bytes(rom))

    def test_dual_counts_owner_bytes_and_partition_must_be_exact(self):
        rows = copy.deepcopy(self.rows)
        rows[0]['instrs'] += 1
        mapping, index = self.indexes(rows)
        with self.assertRaises(ValueError):
            self.native(mapping=mapping, index=index)
        with self.assertRaises(ValueError):
            self.native(index=self.index.replace(str(self.rows[0]['instrs']).encode(), b'9999', 1))
        rom = bytearray(self.rom)
        rom[A-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.native(rom=bytes(rom))

    def test_policy_selector_and_manifest_are_explicit(self):
        for selector in (None, old_profile.SELECTOR, True):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        manifest = copy.deepcopy(self.manifest)
        manifest['readonly_LDM_policy'] = 'arbitrary-loads'
        with self.assertRaises(ValueError):
            self.native(manifest=manifest)


if __name__ == '__main__':
    unittest.main()

