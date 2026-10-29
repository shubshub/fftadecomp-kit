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
import one_constant_scalar_switch_inventory as profile
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants
import analyze
import one_object_ordinary_acyclic_inventory as objects

A, B = 0x08010000, 0x08020000
SOURCE = 'extern unsigned int func_08020000(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);\nunsigned int func_08010000(const unsigned char *object, unsigned int value)\n{\n    unsigned int result;\n    switch (object[0x797]) {\n    case 0: result = func_08020000(value + 1, 0, 0, 0, 1); break;\n    case 1: result = func_08020000(value - 2, 0, 0, 0, 2); break;\n    case 2: result = func_08020000(value * 3, 0, 0, 0, 3); break;\n    case 3: result = func_08020000(value | 4, 0, 0, 0, 4); break;\n    case 4: result = func_08020000(value & 5, 0, 0, 0, 5); break;\n    case 5: result = func_08020000(value ^ 6, 0, 0, 0, 6); break;\n    default: result = value; break;\n    }\n    return result;\n}\n'

class OneConstantScalarSwitchInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='one_numeric_switch_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_NUMERIC_SWITCH_RETAIN']) \
            if os.environ.get('FFTA_NUMERIC_SWITCH_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        reuse = os.environ.get('FFTA_NUMERIC_SWITCH_REUSE')
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
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_numeric_word_switch=True)
        cls.switch = cls.refinement['word_switches'][0]
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
        self.assertEqual(self.manifest['interposed_constant_words'], 1)
        self.assertEqual(self.manifest['numeric_word']['value'], 0x797)
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        run = subprocess.run([sys.executable, str(Path(profile.__file__)), '--profile', profile.SELECTOR,
            '--rom', str(self.root / 'baserom.bin'), '--mapping', str(self.root / 'config/functions.json'),
            '--index', str(self.root / 'symbols/functions.txt'), f'{A:08X}'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), json.loads(json.dumps(self.manifest)))
        if self.retained:
            (self.retained / 'fixture-cli.json').write_text(run.stdout)

    def mutate(self, site, raw, **changes):
        data = bytearray(self.body)
        offset = site-A
        data[offset:offset+len(raw)] = raw
        return self.changed(data, **changes)

    def test_default_old_selectors_and_ambiguous_optins_reject(self):
        self.assertFalse(owner.refine(self.body, A, self.mapping)['cfg_closed'])
        with self.assertRaises(ValueError):
            graph.graph(self.body, A, self.refinement)
        with self.assertRaises(ValueError):
            objects.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,
                selector=objects.SELECTOR)
        with self.assertRaises(ValueError):
            constants.layout(self.body,A,dict(self.switch['relocations']))
        for other in ('one_object_word_switch','two_constant_word_switch'):
            options={'one_numeric_word_switch':True,other:True}
            with self.subTest(other=other):
                self.assertFalse(analyze.refine_function(self.body,A,json.loads(self.mapping),**options)['cfg_closed'])
                with self.assertRaisesRegex(ValueError,'cannot combine'):
                    graph.graph(self.body,A,self.refinement,**options)
                with self.assertRaisesRegex(ValueError,'isolated Boolean'):
                    analyze.refinement_word_switch(self.body,A,A+8,A+len(self.body),None,**options)
        for value in (None,1,'yes'):
            with self.subTest(value=value):
                self.assertFalse(analyze.refine_function(self.body,A,json.loads(self.mapping),one_numeric_word_switch=value)['cfg_closed'])
                with self.assertRaisesRegex(ValueError,'Boolean'):
                    graph.graph(self.body,A,self.refinement,one_numeric_word_switch=value)

    def test_literal_category_rejects_objects_functions_and_wide_values(self):
        site=self.manifest['numeric_word']['address']
        for value in (0x10000,0x02000000,0x03002810,A,B,match.divsi3.ADDRESS,match.UDIVSI3_ADDRESS):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.mutate(site,struct.pack('<I',value))
        self.assertEqual(self.manifest['numeric_input_preconditions'],[])
        self.assertFalse(self.manifest['arithmetic_C_equivalence'])
        self.assertIn('literal category',self.manifest['numeric_word_policy'])

    def test_guard_table_pointer_target_and_bypass_reject(self):
        comparison=A+self.switch['comparison']
        encoded=int.from_bytes(self.ins[comparison].bytes,'little')
        with self.assertRaises(ValueError):
            self.mutate(comparison,struct.pack('<H',encoded^1))
        guard=A+self.switch['guard']
        encoded=int.from_bytes(self.ins[guard].bytes,'little')
        with self.assertRaises(ValueError):
            self.mutate(guard,struct.pack('<H',(encoded&0xff)|0xdc00))
        for offset,value in ((self.switch['literal'],A+self.switch['table']+4),
                (self.switch['table'],A+self.switch['table']),
                (self.switch['table'],A+self.switch['dispatch']+1)):
            with self.subTest(offset=offset,value=value), self.assertRaises(ValueError):
                self.mutate(A+offset,struct.pack('<I',value))
        edges=dict(self.edges)
        edges[A]=(A+self.switch['dispatch']+2,)
        with self.assertRaisesRegex(ValueError,'bound is bypassed'):
            profile.guard_predecessors(self.ins,edges,A,self.switch)

    def test_SP_materialization_alias_export_and_block_operations_reject(self):
        site=A+self.switch['comparison']-2
        for raw in (b'\x68\x46',b'\x00\xa8',b'\x02\xc8',b'\x02\xc0'):
            with self.subTest(raw=raw.hex()), self.assertRaises(ValueError):
                self.mutate(site,raw)

    def test_frame_saved_slots_entry_words_unbalanced_release_and_LR_reject(self):
        stores=[i for i in self.instructions if i.mnemonic=='str' and any(
            op.type==match.ARM_OP_MEM and op.mem.base==match.ARM_REG_SP for op in i.operands)]
        self.assertTrue(stores)
        allocation=-next(value for _,value in self.manifest['stack_adjustments'] if value<0)
        store=stores[0]
        reg=store.operands[0].reg-match.ARM_REG_R0
        for raw in (struct.pack('<H',0x9000+(reg<<8)+allocation//4),struct.pack('<H',0x9800+0xff)):
            with self.subTest(raw=raw.hex()), self.assertRaises(ValueError):
                self.mutate(store.address,raw)
        release=next(A+offset for offset,value in self.manifest['stack_adjustments'] if value>0)
        with self.assertRaises(ValueError):
            self.mutate(release,struct.pack('<H',0xb000+allocation//4+1))
        ret=next(i for i in reversed(self.instructions) if i.mnemonic=='bx')
        with self.assertRaises(ValueError):
            self.mutate(ret.address,b'\x10\x47')
        # This natural fixture saves LR only. A real r4 write without any save
        # must still lose its entry token and fail the reached-return proof.
        with self.assertRaises(ValueError):
            self.mutate(A+4,b'\x00\x24')

    def test_every_call_binding_and_runtime_thunk_unknown_exclusions(self):
        with self.assertRaises(ValueError):self.native(calls={})
        with self.assertRaises(ValueError):self.native(bindings={})
        site=next(iter(self.calls))
        for target in (B+2,match.divsi3.ADDRESS,match.modsi3.ADDRESS,match.UDIVSI3_ADDRESS,
                       next(iter(match.function_thunk.ALIASES.values()))):
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls({site:target},self.mapping,A,len(self.body),len(self.rom))
        rows=copy.deepcopy(self.rows);rows[1]['mode']='arm'
        mapping,_=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping)
        rows=copy.deepcopy(self.rows);rows[1]['rom']=f'0x{A+4:08X}';rows[1]['end']=f'0x{A+8:08X}'
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)

    def test_cycles_indirect_calls_and_nonreturning_regions_reject(self):
        branch=next(i for i in self.instructions if i.mnemonic=='b' and i.address>A+self.switch['table'])
        with self.assertRaises(ValueError):self.mutate(branch.address,b'\xfe\xe7')
        site=next(iter(self.calls))
        with self.assertRaises(ValueError):self.mutate(site,b'\x80\x47\x00\x20')
        with self.assertRaises(ValueError):self.mutate(site,b'\x70\x47\x00\x20')

    def test_reached_literal_alignment_and_complete_extent_required(self):
        load=self.manifest['numeric_word']['load_sites'][0]
        with self.assertRaises(ValueError):self.mutate(load,b'\x00\x22')
        alignment=self.manifest['partition']['alignment'][0][0]
        with self.assertRaises(ValueError):self.mutate(alignment,b'\x01\x00')
        rows=copy.deepcopy(self.rows);rows[0]['end']=f'0x{A+len(self.body)-2:08X}'
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        with self.assertRaises(ValueError):self.native(data=self.body[:-2])

    def test_dual_counts_source_ROM_manifest_and_selector_binding(self):
        rows=copy.deepcopy(self.rows);rows[0]['instrs']+=1
        mapping,index=self.indexes(rows)
        with self.assertRaisesRegex(ValueError,'instruction counts'):
            self.native(mapping=mapping,index=index)
        with self.assertRaises(ValueError):self.native(data=bytes([self.body[0]^1])+self.body[1:])
        for field in ('body_sha256','mapping_sha256','index_sha256','producer_source_sha256','numeric_word'):
            bad=copy.deepcopy(self.manifest);bad[field]={}
            with self.subTest(field=field), self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=bad)
        for selector in (None,'scalar-frame-ordinary-switch-inventory-v1','non-sp-block-copy-inventory-v1'):
            with self.subTest(selector=selector), self.assertRaises(ValueError):self.native(selector=selector)

if __name__ == '__main__':
    unittest.main()
