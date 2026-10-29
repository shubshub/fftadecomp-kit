"""Natural one-object-word switch and structural-only native closure gates."""
import argparse
import copy
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
import one_object_mixed_switch_inventory as profile
import owner_admission_profile as owner
import owner_graph_profile as graph
import match

A, B, D = 0x08010000, 0x08020000, 0x083A8260
SOURCE = '''extern const unsigned char data_083A8260[];
extern unsigned int func_08020000(unsigned int, unsigned int);
unsigned int func_08010000(unsigned int selector, unsigned int value, unsigned int index)
{
    unsigned int divisor = data_083A8260[index & 7];
    unsigned int result = 0;
    switch (selector) {
    case 0: result = func_08020000(value, 23) / divisor; break;
    case 1: result = func_08020000(value, 24) / divisor; break;
    case 2: result = func_08020000(value, 26) / divisor; break;
    case 3: result = func_08020000(value, 27) / divisor; break;
    case 4: result = func_08020000(value, 28) / divisor; break;
    case 5: result = func_08020000(value, 29) / divisor; break;
    case 6: result = (int)value / (int)divisor; break;
    }
    return result;
}
'''


class OneObjectMixedSwitchInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2)+'\n').encode(), ''.join(
            f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert profile.sha(approved) == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='one_object_switch_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_ONE_OBJECT_RETAIN']) if os.environ.get('FFTA_ONE_OBJECT_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
            (cls.retained/'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            if cls.retained:
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(workspace+'/f.s'))
            script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
            script += '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
            script += '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
            script += '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
            script += 'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }'
            runner.write_text(workspace+'/f.ld', script)
            aliases = '.syntax unified\n.thumb\n'
            targets = {'func_08020000':B, '__udivsi3':0x08142AB0, '__divsi3':0x081426B8}
            for name, target in targets.items():
                aliases += f'.global {name}\n.type {name}, %function\n.thumb_set {name}, 0x{target|1:08X}\n'
            aliases += f'.global data_083A8260\n.type data_083A8260, %object\n.set data_083A8260, 0x{D:08X}\n'
            runner.write_text(workspace+'/f.known.s', aliases)
            q = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
                f'-T {q}/f.ld -e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            linked = runner.read_binary(workspace+'/f.elf')
            image = match.elf_image(linked)
            match.allocated_text_only(image)
            symbol, offset = match.function_record(image, 'func_08010000', A, True)
            assert original['type'] == 1 and image['type'] == 2 and not image['relocations'] and offset == 0
            cls.body = image['text'][:symbol['size']]
            assert image['text'][symbol['size']:] == original['text'][symbol['size']:] in (b'', b'\xc0\x46')
            expected = bytearray(original['text'][:symbol['size']])
            cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB); cs.detail = True
            relocations = []
            for section_index in original['relocations']:
                section = original['sections'][section_index]
                symbols = original['symbol_tables'][section[6]]
                for position in range(0, section[5], 8):
                    site, info = struct.unpack_from('<II', original['section_data'][section_index], position)
                    target = symbols[info >> 8]
                    if info & 255 == 10:
                        assert target['name'] in targets and not target['section']
                        i = next(cs.disasm(cls.body[site:site+4], A+site))
                        assert i.mnemonic == 'bl' and i.size == 4 and i.operands[0].imm == targets[target['name']]
                        expected[site:site+4] = cls.body[site:site+4]
                    elif info & 255 == 2:
                        addend = struct.unpack_from('<I', original['text'], site)[0]
                        if target['section'] == original['text_index']:
                            value = A+addend
                        else:
                            assert target['name'] == 'data_083A8260' and not target['section']
                            value = D+addend
                        struct.pack_into('<I', expected, site, value)
                    else:
                        raise AssertionError('unexpected natural fixture relocation')
                    relocations.append([site, info & 255, target['name']])
            assert bytes(expected) == cls.body
            if cls.retained:
                (cls.retained/'linked.elf').write_bytes(linked)
                (cls.retained/'compiler-evidence.json').write_text(json.dumps({'ET_REL':original['type'],
                    'linked_type':image['type'], 'compiler':args.cc, 'flags':args.flags,
                    'relocations':relocations, 'only_standard_linker_relocations_changed':True,
                    'source_or_ELF_admission':False}, indent=2)+'\n')
        cls.rows = [{'rom':f'0x{A:08X}', 'end':f'0x{A+len(cls.body):08X}', 'mode':'thumb', 'instrs':0},
            {'rom':f'0x{B:08X}', 'end':f'0x{B+2:08X}', 'mode':'thumb', 'instrs':1},
            {'rom':'0x081426B8', 'end':'0x0814274A', 'mode':'thumb', 'instrs':72},
            {'rom':'0x08142AB0', 'end':'0x08142B28', 'mode':'thumb', 'instrs':59},
            {'rom':'0x0814274C', 'end':'0x0814274E', 'mode':'thumb', 'instrs':1}]
        mapping, _ = cls.indexes(cls.rows)
        cls.refinement = profile.refine(cls.body, A, mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, A, cls.refinement, one_object_word_switch=True)
        rom = bytearray(approved); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.bindings = profile.bind_calls(cls.calls, cls.mapping, A, len(cls.body), len(rom))
        cls.manifest, _ = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
            cls.calls, cls.bindings, selector=profile.SELECTOR)
        for name, value in (('baserom.bin',cls.rom), ('config/functions.json',cls.mapping), ('symbols/functions.txt',cls.index)):
            (cls.root/name).write_bytes(value)
        if cls.retained:
            (cls.retained/'body.bin').write_bytes(cls.body)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')

    def native(self, **changes):
        values = dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
            calls=self.calls,bindings=self.bindings,selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def changed(self, data, **changes):
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=bytes(data),rom=bytes(rom),**changes)

    def test_natural_O2_API_CLI_and_explicit_structural_boundary(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(self.refinement['word_switches'][0]['interposed_words'],1)
        self.assertEqual(set(self.bindings.values()),{'__udivsi3','__divsi3','func_08020000'})
        self.assertTrue(self.manifest['complete_native_structural_proof'] and self.manifest['inventory_only'])
        for key in ('source_or_ELF_admission','arithmetic_C_equivalence','termination_claim'):
            self.assertFalse(self.manifest[key])
        self.assertEqual(self.manifest['numeric_input_preconditions'],[])
        self.assertEqual(self.manifest['nonzero_facts'],[])
        self.assertEqual(set(dict(self.manifest['native_runtime_closure'])),{0x081426B8,0x08142AB0,0x0814274C})
        self.assertEqual(self.manifest['object_word']['value'],D)
        self.assertTrue(self.manifest['object_word']['load_sites'])
        old = owner.refine(self.body,A,self.mapping)
        self.assertFalse(old['cfg_closed'])
        with self.assertRaises(ValueError):graph.graph(self.body,A,self.refinement)
        with self.assertRaises(ValueError):self.native(selector='zero-aware-mixed-byte-switch-inventory-v1')
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_guard_bypass_table_pointer_object_ownership_and_indirect_reject(self):
        sw=self.refinement['word_switches'][0]
        for off, raw in ((sw['comparison'],b'\x00\x28'),(sw['guard'],b'\xc0\x46'),
                (sw['table'],struct.pack('<I',A+sw['table'])),
                (sw['literal'],struct.pack('<I',A+sw['table']+4)),
                (sw['literal']-4,struct.pack('<I',A)),
                (sw['literal']-4,struct.pack('<I',0x081426B8)),
                (sw['dispatch']+8,b'\x00\x47')):
            data=bytearray(self.body);data[off:off+len(raw)]=raw
            with self.subTest(offset=off,raw=raw.hex()),self.assertRaises(ValueError):self.changed(data)
        load=self.manifest['object_word']['load_sites'][0]
        data=bytearray(self.body);data[load-A:load-A+2]=b'\xc0\x46'
        with self.assertRaises(ValueError):self.changed(data)
        site=next(s for s,i in self.ins.items() if A+2<=s<A+sw['comparison'] and i.mnemonic=='movs')
        for target in (A+sw['dispatch'],site):
            data=bytearray(self.body);struct.pack_into('<H',data,site-A,0xD000|((target-site-4)//2&255))
            with self.subTest(target=target),self.assertRaises(ValueError):self.changed(data)

    def test_every_canonical_closure_zero_edge_frame_and_count_is_bound(self):
        for site in (0x081426BA,0x0814273C,0x08142742,0x08142748,0x0814274C,
                0x08142AB2,0x08142B1A,0x08142B20,0x08142B26):
            rom=bytearray(self.rom);rom[site-match.ROM_BASE]^=1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        # Ordinary callees have a conditional ABI premise, not a native count proof.
        for number in (0, 2, 3, 4):
            rows=copy.deepcopy(self.rows);rows[number]['instrs']-=1
            mapping,index=self.indexes(rows)
            with self.subTest(number=number),self.assertRaises(ValueError):self.native(mapping=mapping,index=index)

    def test_missing_calls_reserved_aliases_unknown_and_overlapping_maps_reject(self):
        for site in self.calls:
            calls=dict(self.calls);calls.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(calls=calls)
        for target in (0x081426BA,0x08142AB2,0x08142950,0x0814274C,0x08142244,B+1,B+4,A+2):
            calls=dict(self.calls);calls[next(s for s,t in calls.items() if t==B)]=target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))
        rows=copy.deepcopy(self.rows);rows.append(dict(rows[1]))
        mapping,index=self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        bindings=dict(self.bindings);bindings[next(iter(bindings))]='__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)

    def test_saved_frame_SP_materialization_exports_and_wrong_return_reject(self):
        for site,raw in ((A,b'\xc0\x46'),
                (next(s for s,i in self.ins.items() if i.mnemonic=='movs'),b'\x68\x46'),
                (next(s for s,i in self.ins.items() if i.mnemonic=='pop'),b'\x00\x90'),
                (max(self.ins),b'\x70\x47')):
            data=bytearray(self.body);data[site-A:site-A+2]=raw
            with self.subTest(site=site),self.assertRaises(ValueError):self.changed(data)

    def test_manifest_hash_effects_and_inventory_source_admission_are_strict(self):
        for key in ('body_sha256','mapping_sha256','index_sha256','producer_source_sha256',
                'object_word','word_switches','native_runtime_closure','dependencies','frame','calls'):
            manifest=copy.deepcopy(self.manifest);manifest[key]=[]
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)
        data=bytearray(self.body);data[2]^=1
        with self.assertRaises(ValueError):self.native(data=bytes(data))
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        self.assertNotIn(profile.SCHEMA,Path(match.__file__).read_text())
        self.assertNotIn(profile.SELECTOR,Path(match.__file__).read_text())
        import status
        self.assertNotIn(profile.SCHEMA,Path(status.__file__).read_text())


if __name__=='__main__':unittest.main()
