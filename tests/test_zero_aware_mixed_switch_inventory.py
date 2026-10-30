"""Natural fixed-compiler switch/DIV/MOD composition and strict refusals."""
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
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import zero_aware_mixed_runtime_inventory as old
import zero_aware_mixed_switch_inventory as profile

A, B = 0x08010000,0x08020000
SOURCE = '''extern int func_08020000(int value, int a, int b, int c, int d);
int func_08010000(unsigned int selector, signed char *values, int divisor, int *output)
{
    int result;
    switch (selector) {
    case 0: result = func_08020000(values[0] + 1, 0, 0, 0, 0); break;
    case 1: result = func_08020000(values[0] - 2, 0, 0, 0, 0); break;
    case 2: result = func_08020000(values[0] * 3, 0, 0, 0, 0); break;
    case 3: result = func_08020000(values[0] | 4, 0, 0, 0, 0); break;
    case 4: result = func_08020000(values[0] & 5, 0, 0, 0, 0); break;
    case 5: result = func_08020000(values[0] ^ 6, 0, 0, 0, 0); break;
    case 6: result = func_08020000(values[0] + 7, 0, 0, 0, 0); break;
    default: result = func_08020000(values[0], 0, 0, 0, 0); break;
    }
    output[0] = values[1] / divisor;
    output[1] = values[2] % divisor;
    return result;
}
'''


class MixedSwitchInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows,indent=2)+'\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected:raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH',Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='mixed_switch_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):(cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_MIXED_SWITCH_RETAIN']) if os.environ.get('FFTA_MIXED_SWITCH_RETAIN') else None
        if cls.retained:cls.retained.mkdir(parents=True,exist_ok=True)
        args = argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC,root=cls.root,timeout=120)
        with runner.workspace() as workspace:
            cls.raw,_,original = match.compile_object(runner,workspace,args,cls.root,A,'src/08010000.c')
            if cls.retained:
                (cls.retained/'caller.c').write_text(SOURCE)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(workspace+'/f.s'))
                (cls.retained/'original.o').write_bytes(cls.raw)
            # Fixture-only standard linking resolves natural compiler relocations.
            # The inventory API accepts neither source nor ELF/linker inputs.
            script = f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} '
            script += '.data 0 : { *(.data) } .bss 0 : { *(.bss) } .ARM.attributes 0 : { *(.ARM.attributes) } '
            script += '.unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } '
            script += '.rel.iplt 0 : { *(.rel.iplt) } ASSERT(SIZEOF(.unexpected)==0,"unexpected stubs") '
            script += 'ASSERT(SIZEOF(.rel.iplt)==0,"unexpected relocations") /DISCARD/ : { *(.comment) *(.note.GNU-stack) } }'
            runner.write_text(workspace+'/f.ld',script)
            definitions = ['.syntax unified','.thumb']
            for name,address in (('__divsi3',0x081426B8),('__modsi3',0x08142950),('func_08020000',B)):
                definitions += [f'.global {name}',f'.type {name}, %function',f'.thumb_set {name}, 0x{address|1:08X}']
            runner.write_text(workspace+'/f.known.s','\n'.join(definitions)+'\n')
            quoted = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax --orphan-handling=error '
                f'-T {quoted}/f.ld -e func_08010000 {quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf')
            cls.linked = runner.read_binary(workspace+'/f.elf')
            image = match.elf_image(cls.linked)
            match.allocated_text_only(image)
            symbol,offset = match.function_record(image,'func_08010000',A,True)
            assert original['type'] == 1 and image['type'] == 2 and not image['relocations'] and offset == 0
            cls.body = image['text'][:symbol['size']]
            assert len(image['text']) == len(original['text'])
            assert original['text'][symbol['size']:] in (b'',b'\xc0\x46')
            assert image['text'][symbol['size']:] == original['text'][symbol['size']:]
            expected = bytearray(original['text'][:symbol['size']])
            decoder = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail = True
            targets = {'__divsi3':0x081426B8,'__modsi3':0x08142950,'func_08020000':B}
            for section_index in original['relocations']:
                section = original['sections'][section_index]
                symbols = original['symbol_tables'][section[6]]
                for position in range(0,section[5],8):
                    site,info = struct.unpack_from('<II',original['section_data'][section_index],position)
                    target = symbols[info >> 8]
                    if info & 255 == 10:
                        assert target['name'] in targets and not target['section']
                        ins = next(decoder.disasm(cls.body[site:site+4],A+site))
                        assert ins.mnemonic == 'bl' and ins.size == 4 and ins.operands[0].imm == targets[target['name']]
                        expected[site:site+4] = cls.body[site:site+4]
                    else:
                        assert info & 255 == 2 and target['section'] == original['text_index']
                        addend = struct.unpack_from('<I',original['text'],site)[0]
                        struct.pack_into('<I',expected,site,A+addend)
            assert bytes(expected) == cls.body
            if cls.retained:
                (cls.retained/'caller.c').write_text(SOURCE)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(workspace+'/f.s'))
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'linked.elf').write_bytes(cls.linked)
        cls.rows = [{'rom':f'0x{A:08X}','end':f'0x{A+len(cls.body):08X}','mode':'thumb','instrs':0},
            {'rom':f'0x{B:08X}','end':f'0x{B+2:08X}','mode':'thumb','instrs':1},
            {'rom':'0x081426B8','end':'0x0814274A','mode':'thumb','instrs':72},
            {'rom':'0x08142950','end':'0x08142A1E','mode':'thumb','instrs':102},
            {'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1}]
        mapping,_ = cls.indexes(cls.rows)
        cls.refinement = owner.refine(cls.body,A,mapping)
        cls.rows[0]['instrs'] = cls.refinement['instrs']
        cls.mapping,cls.index = cls.indexes(cls.rows)
        rom = bytearray(approved);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.ins,cls.edges,_,cls.calls,_ = graph.graph(cls.body,A,cls.refinement)
        cls.bindings = profile.bind_calls(cls.calls,cls.mapping,A,len(cls.body),len(cls.rom))
        cls.manifest,cls.instructions = profile.verify(cls.body,A,cls.rom,cls.mapping,cls.index,
            cls.calls,cls.bindings,selector=profile.SELECTOR)
        for name,data in (('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),('baserom.bin',cls.rom)):
            (cls.root/name).write_bytes(data)
        if cls.retained:
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
            (cls.retained/'fixture.json').write_text(json.dumps({'original_ELF_type':original['type'],
                'linked_ELF_type':image['type'],'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS],
                'source_or_ELF_admission':False,'synthetic_only':True,'relocations':original['relocations'],
                'natural_word_switches':cls.refinement['word_switches']},indent=2)+'\n')

    def native(self,**changes):
        values = dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
            calls=self.calls,bindings=self.bindings,selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def changed(self,data,*,rebind=False,**changes):
        rom = bytearray(self.rom);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        if rebind:
            refinement = owner.refine(bytes(data),A,self.mapping)
            _,_,_,calls,_ = graph.graph(bytes(data),A,refinement)
            changes.update(calls=calls,bindings=profile.bind_calls(calls,self.mapping,A,len(data),len(rom)))
        return self.native(data=bytes(data),rom=bytes(rom),**changes)

    def test_natural_dense_switch_DIV_MOD_ordinary_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertTrue(self.manifest['word_switches'])
        self.assertEqual(set(name for _,name in self.manifest['runtime_calls']),{'__divsi3','__modsi3'})
        self.assertEqual(len(self.manifest['operand_ranges']),2)
        self.assertTrue(self.manifest['ordinary_calls'])
        self.assertFalse(self.manifest['ordinary_callee_native_proof'])
        self.assertEqual(self.manifest['frame']['external_calls'],'existing-direct-call-ABI-summary')
        self.assertEqual(set(dict(self.manifest['native_runtime_closure'])),{0x081426B8,0x08142950,0x0814274C})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])),persisted)
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),persisted)
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_guard_and_table_words_require_exact_closed_native_layout(self):
        switch = self.refinement['word_switches'][0]
        for offset,replacement in ((switch['guard'],b'\xc0\x46'),
                (switch['comparison'],b'\x00\x28'),
                (switch['table'],struct.pack('<I',A+switch['table']))):
            data = bytearray(self.body);data[offset:offset+len(replacement)] = replacement
            with self.subTest(offset=offset),self.assertRaises(ValueError):self.changed(data)

    def test_all_call_bindings_and_reserved_ordinary_target_exclusions(self):
        for site in self.calls:
            calls = dict(self.calls);calls.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(calls=calls)
        for target in (0x081426BA,0x08142952,0x08142244,0x08030000):
            calls = dict(self.calls);calls[next(site for site,target in calls.items() if target == B)] = target
            with self.subTest(target=target),self.assertRaises(ValueError):
                profile.bind_calls(calls,self.mapping,A,len(self.body),len(self.rom))
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = 'func_08020000'
        if bindings == self.bindings:bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)

    def test_unknown_dividend_and_call_result_do_not_supply_BYTE_origin(self):
        for row in self.manifest['operand_ranges']:
            origin = row[3][0]
            for replacement in (b'\x00\x20',b'\x00\x68'):
                data = bytearray(self.body);data[origin:origin+2] = replacement
                with self.subTest(origin=origin,replacement=replacement),self.assertRaisesRegex(ValueError,'signed16 r0'):
                    self.changed(data)

    def test_bypassed_load_call_kill_and_local_cycle_remain_refused(self):
        origin = self.manifest['operand_ranges'][0][3][0]
        call = self.manifest['operand_ranges'][0][0]
        data = bytearray(self.body)
        struct.pack_into('<H',data,origin-2,0xD000 | ((call-(origin-2)-4)//2 & 0xFF))
        with self.assertRaisesRegex(ValueError,'signed16 r0'):self.changed(data)
        data = bytearray(self.body);delta = B-(A+origin)-4
        struct.pack_into('<HH',data,origin,0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
        with self.assertRaisesRegex(ValueError,'signed16 r0'):self.changed(data,rebind=True)
        site = next(site for site,ins in self.ins.items() if ins.mnemonic == 'b')
        data = bytearray(self.body);struct.pack_into('<H',data,site-A,0xD0FE)
        with self.assertRaisesRegex(ValueError,'CFG cycles'):self.changed(data)

    def test_stack_arguments_and_saved_slot_writes_remain_refused(self):
        site = next(site for site,target in self.calls.items() if target == B)
        data = bytearray(self.body);data[site-A-2:site-A] = b'\x68\x46'
        with self.assertRaisesRegex(ValueError,'aliases crossing calls'):self.changed(data)
        # Replace a non-control instruction immediately after the fixed prologue
        # with STR r0,[SP,#allocation]. It writes the first saved frame word.
        allocation = sum(ins.operands[-1].imm for ins in self.ins.values()
            if ins.mnemonic == 'sub' and ins.op_str.startswith('sp,'))
        candidate = self.manifest['operand_ranges'][0][3][0]-2
        data = bytearray(self.body);data[candidate:candidate+2] = struct.pack('<H',0x9000 | (allocation//4))
        with self.assertRaisesRegex(ValueError,'overwrites a saved register'):self.changed(data)

    def test_complete_zero_nonzero_runtime_identity_and_manifest_boundaries(self):
        for address in (0x081426BA,0x08142742,0x08142746,0x0814274C,0x08142A16,0x08142A1A):
            rom = bytearray(self.rom);rom[address-match.ROM_BASE] ^= 1
            with self.subTest(address=address),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for key in ('native_runtime_closure','runtime_cases','frame','word_switches','partition','operand_ranges','ordinary_call_premise'):
            manifest = copy.deepcopy(self.manifest);manifest[key] = []
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)

    def test_default_old_selector_and_owner_ownership_boundaries(self):
        with self.assertRaises(ValueError):self.native(selector=old.SELECTOR)
        with self.assertRaises(ValueError):
            old.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=old.SELECTOR)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        for name in ('rom','end','mode'):
            rows = copy.deepcopy(self.rows)
            rows[0][name] = {'rom':'0x08010001','end':f'0x{A+len(self.body)-2:08X}','mode':'arm'}[name]
            mapping,index = self.indexes(rows)
            with self.subTest(name=name),self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        rows = copy.deepcopy(self.rows);rows.append(dict(rows[1],rom=f'0x{B:08X}'))
        mapping,index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)


if __name__ == '__main__':unittest.main()
