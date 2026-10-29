"""Natural agbcc conditional-thunk scalar-frame switch and focused inventory contract checks."""
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
import one_numeric_thunk_scalar_switch_inventory as profile
import one_constant_scalar_switch_inventory as numeric
import one_object_thunk_switch_inventory as objects
import zero_word_thunk_switch_inventory as old_profile
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants

A, B, D = 0x08010000, 0x08020000, 0x02001000
SOURCE = 'extern unsigned int func_08020000(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int);\ntypedef unsigned int (*callback_t)(unsigned int, unsigned int);\nunsigned int func_08010000(const unsigned char *object, unsigned int value, callback_t callback)\n{\n    unsigned int result;\n    switch (object[0x1089]) {\n    case 0: result = callback(value + 1, 0); break;\n    case 1: result = func_08020000(value - 2, 0, 0, 0, 2); break;\n    case 2: result = func_08020000(value * 3, 0, 0, 0, 3); break;\n    case 3: result = func_08020000(value | 4, 0, 0, 0, 4); break;\n    case 4: result = func_08020000(value & 5, 0, 0, 0, 5); break;\n    case 5: result = func_08020000(value ^ 6, 0, 0, 0, 6); break;\n    default: result = value; break;\n    }\n    return result;\n}\n'

class OneNumericThunkScalarSwitchInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='numeric_r2_switch_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_NUMERIC_R2_SWITCH_RETAIN']) \
            if os.environ.get('FFTA_NUMERIC_R2_SWITCH_RETAIN') else None
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
                        assert info & 255 == 2
                        addend = struct.unpack_from('<I', original['text'], site)[0]
                        assert target['section'] == original['text_index']
                        value = A + addend
                        struct.pack_into('<I', expected, site, value)
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
        cls.refinement = profile.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_numeric_word_switch=True)
        cls.helper_targets = {target for target in cls.calls.values() if target in thunks.ALIASES.values()}
        assert cls.helper_targets == {thunks.ALIASES['_call_via_r2']}
        rom = bytearray(thunks.END-match.ROM_BASE)
        approved = Path(os.environ.get('FFTA_ROM',
            '/home/user/Downloads/Final Fantasy Tactics Advance (USA, Australia).gba')).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        for target in cls.helper_targets:
            rom[target-match.ROM_BASE:target-match.ROM_BASE+4] = approved[target-match.ROM_BASE:target-match.ROM_BASE+4]
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_numeric_word_switch=True)
        cls.switch = cls.refinement['word_switches'][0]
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

    def mutate(self, site, raw, **changes):
        data=bytearray(self.body);offset=site-A
        data[offset:offset+len(raw)]=raw
        return self.changed(data,**changes)

    def test_natural_O2_API_CLI_and_explicit_conditional_boundary(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertEqual(set(self.bindings.values()),{profile.THUNK,'func_08020000'})
        self.assertEqual(self.manifest['numeric_word']['value'],0x1089)
        self.assertEqual(len(self.manifest['canonical_thunk_dependencies']),1)
        self.assertEqual(self.manifest['canonical_thunk_dependencies'][0][0],profile.THUNK)
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertFalse(self.manifest['indirect_callee_native_proof'])
        self.assertFalse(self.manifest['indirect_callee_effect_proof'])
        self.assertFalse(self.manifest['arithmetic_C_equivalence'])
        self.assertFalse(self.manifest['termination_claim'])
        self.assertEqual(self.manifest['numeric_input_preconditions'],[])
        run=subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'fixture-cli.json').write_text(run.stdout)

    def test_exact_r2_helper_identity_and_dependency_manifest(self):
        target=thunks.ALIASES[profile.THUNK]
        for offset in (0,2):
            changed=bytearray(self.rom);changed[target-match.ROM_BASE+offset]^=1
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError,'identity'):
                self.native(rom=bytes(changed))
        bad=copy.deepcopy(self.manifest);bad['canonical_thunk_dependencies'][0][3]='0'*64
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=bad)
        self.assertIn('target-state validity are not proved',self.manifest['indirect_call_premise'])

    def test_every_call_and_only_canonical_r2_binding(self):
        with self.assertRaises(ValueError):self.native(calls={})
        with self.assertRaises(ValueError):self.native(bindings={})
        site=next(iter(self.calls))
        for target in (thunks.ALIASES['_call_via_r0'],thunks.ALIASES['_call_via_r3'],
                thunks.ALIASES[profile.THUNK]+2,match.divsi3.ADDRESS,match.modsi3.ADDRESS,
                match.UDIVSI3_ADDRESS,B+2):
            calls=dict(self.calls);calls[site]=target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))
        only_ordinary={s:t for s,t in self.calls.items() if t==B}
        only_runtime={s:t for s,t in self.calls.items() if t==thunks.ALIASES[profile.THUNK]}
        for calls in (only_ordinary,only_runtime):
            with self.subTest(calls=calls),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))

    def test_old_numeric_object_and_zero_thunk_selectors_stay_closed(self):
        for module in (numeric,objects,old_profile):
            with self.subTest(selector=module.SELECTOR),self.assertRaises(ValueError):
                module.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,
                    selector=module.SELECTOR)
        with self.assertRaises(ValueError):self.native(selector=numeric.SELECTOR)
        with self.assertRaises(ValueError):self.native(selector=None)

    def test_numeric_word_and_code_literal_provenance_are_separate(self):
        site=self.manifest['numeric_word']['address']
        for value in (0x10000,0x02001000,0x03005e79,A,B,thunks.ALIASES[profile.THUNK]):
            with self.subTest(value=value),self.assertRaises(ValueError):
                self.mutate(site,struct.pack('<I',value))
        load=self.manifest['numeric_word']['load_sites'][0]
        with self.assertRaises(ValueError):self.mutate(load,b'\x00\x22')

    def test_guard_table_partition_and_bypassed_bounds_reject(self):
        site=A+self.switch['comparison'];encoded=int.from_bytes(self.ins[site].bytes,'little')
        with self.assertRaises(ValueError):self.mutate(site,struct.pack('<H',encoded^1))
        for offset,value in ((self.switch['literal'],A+self.switch['table']+4),
                (self.switch['table'],A+self.switch['table']),
                (self.switch['table'],A+self.switch['dispatch']+1)):
            with self.subTest(offset=offset,value=value),self.assertRaises(ValueError):
                self.mutate(A+offset,struct.pack('<I',value))
        alignment=self.manifest['partition']['alignment'][0][0]
        with self.assertRaises(ValueError):self.mutate(alignment,b'\x01\x00')
        edges=dict(self.edges);edges[A]=(A+self.switch['dispatch']+2,)
        with self.assertRaisesRegex(ValueError,'bound is bypassed'):
            profile.guard_predecessors(self.ins,edges,A,self.switch)

    def test_scalar_frame_saved_slots_entry_words_SP_exports_and_returns(self):
        site=A+self.switch['comparison']-2
        for raw in (b'\x68\x46',b'\x00\xa8',b'\x02\xc8',b'\x02\xc0'):
            with self.subTest(raw=raw.hex()),self.assertRaises(ValueError):self.mutate(site,raw)
        allocation=-next(value for _,value in self.manifest['stack_adjustments'] if value<0)
        store=next(i for i in self.instructions if i.mnemonic=='str' and any(
            op.type==match.ARM_OP_MEM and op.mem.base==match.ARM_REG_SP for op in i.operands))
        reg=store.operands[0].reg-match.ARM_REG_R0
        for raw in (struct.pack('<H',0x9000+(reg<<8)+allocation//4),struct.pack('<H',0x98ff)):
            with self.subTest(raw=raw.hex()),self.assertRaises(ValueError):self.mutate(store.address,raw)
        release=next(A+off for off,value in self.manifest['stack_adjustments'] if value>0)
        with self.assertRaises(ValueError):self.mutate(release,struct.pack('<H',0xb000+allocation//4+1))
        ret=next(i for i in reversed(self.instructions) if i.mnemonic=='bx')
        with self.assertRaises(ValueError):self.mutate(ret.address,b'\x10\x47')

    def test_cycles_indirect_calls_bad_maps_counts_ROM_and_manifest(self):
        branch=next(i for i in self.instructions if i.mnemonic=='b' and i.address>A+self.switch['table'])
        with self.assertRaises(ValueError):self.mutate(branch.address,b'\xfe\xe7')
        site=next(iter(self.calls))
        with self.assertRaises(ValueError):self.mutate(site,b'\x80\x47\x00\x20')
        rows=copy.deepcopy(self.rows);rows[0]['instrs']+=1;mapping,index=self.indexes(rows)
        with self.assertRaisesRegex(ValueError,'instruction counts'):self.native(mapping=mapping,index=index)
        rows=copy.deepcopy(self.rows);rows[1]['mode']='arm';mapping,_=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping)
        with self.assertRaises(ValueError):self.native(data=bytes([self.body[0]^1])+self.body[1:])
        for field in ('body_sha256','mapping_sha256','index_sha256','producer_source_sha256','runtime_calls'):
            bad=copy.deepcopy(self.manifest);bad[field]={}
            with self.subTest(field=field),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=bad)

if __name__=='__main__':unittest.main()
