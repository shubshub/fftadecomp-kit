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
import one_object_zero_local_thunk_inventory as profile
import one_object_thunk_switch_inventory as old_profile
import function_thunk_profile as thunks
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import switch_constants_profile as constants

A, B, D = 0x08010000, 0x08020000, 0x02001000
SOURCE = '''extern const unsigned char data_02001000[];
extern unsigned int func_08020000(unsigned int, unsigned int);
typedef unsigned int (*callback_t)(void);
extern callback_t callbacks_08393918[];
unsigned int func_08010000(unsigned int selector, unsigned int index)
{
    unsigned int value = data_02001000[index & 7];
    unsigned int result = 0;
    switch (selector) {
    case 0: result = func_08020000(value, 23); break;
    case 1: result = func_08020000(value, 24); break;
    case 2: result = func_08020000(value, 26); break;
    case 3: result = func_08020000(value, 27); break;
    case 4: result = func_08020000(value, 28); break;
    case 5: result = func_08020000(value, 29); break;
    case 6: result = func_08020000(value, 31); break;
    }
    return result + callbacks_08393918[selector]();
}
'''


class OneObjectZeroLocalThunkInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
            ''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                f'{int(r["end"], 16)-int(r["rom"], 16)} {r["instrs"]} return\n'
                for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        approved = Path(os.environ['FFTA_ROM']).read_bytes()
        assert profile.sha(approved) == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH',
            Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='thunk_switch_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_ZERO_LOCAL_THUNK_RETAIN']) \
            if os.environ.get('FFTA_ZERO_LOCAL_THUNK_RETAIN') else None
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
                    for name, target in thunks.ALIASES.items()) +
                '.global data_02001000\n.type data_02001000, %object\n.set data_02001000, 0x02001000\n'
                '.global callbacks_08393918\n.type callbacks_08393918, %object\n.set callbacks_08393918, 0x08393918\n')
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
                        if target['section'] == original['text_index']:
                            value = A + addend
                        else:
                            assert target['name'] in ('data_02001000','callbacks_08393918') and not target['section']
                            value = {'data_02001000':D,'callbacks_08393918':0x08393918}[target['name']] + addend
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
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_object_word_switch=True)
        cls.helper_targets = {target for target in cls.calls.values() if target in thunks.ALIASES.values()}
        assert cls.helper_targets
        rom = bytearray(approved)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_object_word_switch=True)
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

    def site(self):
        switch = self.refinement['word_switches'][0]
        return next(site for site,i in sorted(self.ins.items())
                    if site > A+switch['table'] and i.mnemonic == 'movs')

    def test_natural_O2_ET_REL_API_CLI_and_explicit_boundary(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertEqual(self.manifest['interposed_constant_words'],1)
        self.assertEqual(self.manifest['object_word']['value'],D)
        self.assertEqual(self.manifest['local_bytes'],0)
        self.assertEqual(self.manifest['stack_adjustments'],[])
        self.assertFalse(self.manifest['cycles_present'])
        self.assertEqual({name for _,name in self.manifest['runtime_calls']},{'_call_via_r0'})
        self.assertIn('func_08020000',self.bindings.values())
        self.assertEqual(self.manifest['frame']['preserved'],'r4-r11,sp,entry-lr')
        for key in ('source_or_ELF_admission','arithmetic_C_equivalence','memory_safety_claim',
                    'termination_claim','indirect_callee_native_proof','indirect_callee_effect_proof'):
            self.assertFalse(self.manifest[key])
        with self.assertRaises(ValueError):
            old_profile.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=old_profile.SELECTOR)
        self.assertFalse(owner.selected(f'* verification: `{profile.SCHEMA}`\n'))
        self.assertFalse(thunks.selected(f'* verification: `{profile.SCHEMA}`\n'))
        run=subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True,
            env=dict(os.environ,PYTHONPATH=os.pathsep.join(sys.path)))
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'fixture-cli.json').write_text(run.stdout)

    def test_guard_table_and_actual_object_word_are_bound(self):
        switch=self.refinement['word_switches'][0]
        for off,raw in ((switch['guard'],b'\xc0\x46'),(switch['comparison'],b'\x00\x28'),
                (switch['table'],struct.pack('<I',A+switch['table'])),
                (switch['literal'],struct.pack('<I',A+switch['table']+4)),
                (switch['literal']-4,struct.pack('<I',0x797)),
                (switch['literal']-4,struct.pack('<I',B|1)),
                (switch['literal']-4,struct.pack('<I',thunks.START))):
            data=bytearray(self.body);data[off:off+len(raw)]=raw
            with self.subTest(offset=off,raw=raw.hex()),self.assertRaises(ValueError):self.changed(data)
        site=self.manifest['object_word']['load_sites'][0]
        data=bytearray(self.body);data[site-A:site-A+2]=b'\xc0\x46'
        with self.assertRaises(ValueError):self.changed(data)

    def test_guard_bypass_and_real_cycle_reject(self):
        switch=self.refinement['word_switches'][0];site=self.site()
        data=bytearray(self.body)
        # A conditional jump into the dispatch creates an actual additional
        # predecessor, retaining the original path and complete instruction set.
        delta=(A+switch['dispatch']-site-4)//2
        self.assertTrue(-128<=delta<=127)
        struct.pack_into('<H',data,site-A,0xD000|(delta&255))
        with self.assertRaisesRegex(ValueError,'bypass|predecessor|closed'):
            self.changed(data)
        data=bytearray(self.body);struct.pack_into('<H',data,site-A,0xD0FE)
        with self.assertRaisesRegex(ValueError,'CFG cycles'):self.changed(data)

    def test_SP_allocations_accesses_exports_and_block_transfer_reject(self):
        site=self.site()
        for raw in (b'\x81\xb0',b'\x01\xb0',b'\x00\x90',b'\xff\x98',
                    b'\x68\x46',b'\x85\x46',b'\x01\xc1',b'\x01\xc9'):
            data=bytearray(self.body);data[site-A:site-A+2]=raw
            with self.subTest(raw=raw.hex()),self.assertRaisesRegex(ValueError,'allocation|SP|materialization|block transfers'):
                self.changed(data)

    def test_saved_register_and_entry_LR_restoration_reject(self):
        data=bytearray(self.body);first=struct.unpack_from('<H',data)[0]
        self.assertTrue(first&0x100)
        struct.pack_into('<H',data,0,first&~0x100|1)
        with self.assertRaises(ValueError):self.changed(data)
        data=bytearray(self.body);site=self.site();data[site-A:site-A+2]=b'\x82\x46'
        with self.assertRaises(ValueError):self.changed(data)

    def test_only_exact_r0_helper_and_both_halfwords_are_authenticated(self):
        self.assertEqual(self.helper_targets,{thunks.START})
        for off in (0,2):
            rom=bytearray(self.rom);rom[thunks.START-match.ROM_BASE+off]^=8
            with self.subTest(offset=off),self.assertRaisesRegex(ValueError,'identity differs'):
                self.native(rom=bytes(rom))
        site=next(site for site,target in self.calls.items() if target==thunks.START)
        for target in (thunks.START+4,thunks.START+2,thunks.START|1):
            calls=dict(self.calls);calls[site]=target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))
        bindings=dict(self.bindings);bindings[site]=f'func_{thunks.START:08X}'
        with self.assertRaisesRegex(ValueError,'bindings differ'):self.native(bindings=bindings)

    def test_runtime_alias_unknown_overlap_and_missing_call_reject(self):
        for target in (0x081426B8,0x081426BA,0x08142950,0x08142952,B+1,B+4):
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls({A+4:target,A+8:thunks.START},self.mapping,A,len(self.body),len(self.rom))
        for site in self.calls:
            calls=dict(self.calls);calls.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(calls=calls)
        rows=copy.deepcopy(self.rows);rows.append(dict(rows[1],rom=f'0x{B+1:08X}'))
        mapping,_=self.indexes(rows)
        with self.assertRaises(ValueError):profile.bind_calls(self.calls,mapping,A,len(self.body),len(self.rom))

    def test_exact_dual_counts_ROM_complete_extent_and_selector_required(self):
        for field,value in (('mode','arm'),('instrs',len(self.ins)+1),('end',f'0x{A+len(self.body)-2:08X}')):
            rows=copy.deepcopy(self.rows);rows[0][field]=value;mapping,index=self.indexes(rows)
            with self.subTest(field=field),self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        with self.assertRaises(ValueError):self.native(index=self.index.replace(f' {len(self.ins)} return'.encode(),b' 1 return',1))
        rom=bytearray(self.rom);rom[A-match.ROM_BASE]^=1
        with self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for selector in (None,True,old_profile.SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):self.native(selector=selector)
        data=self.body+b'\0\0\0\0';rows=copy.deepcopy(self.rows);rows[0]['end']=f'0x{A+len(data):08X}'
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.changed(data,mapping=mapping,index=index)

    def test_manifest_cannot_omit_frame_dependencies_or_conditional_ABI(self):
        for key in ('frame','partition','calls','runtime_calls','canonical_thunk_dependencies',
                    'ordinary_call_premise','indirect_call_premise','producer_source_sha256','object_word','frame_policy'):
            damaged=copy.deepcopy(self.manifest);damaged[key]=[]
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=damaged)

if __name__=='__main__':
    unittest.main()
