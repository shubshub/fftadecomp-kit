"""Full-width structural runtime inventory makes no arithmetic equivalence claim."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner
import status
import zero_aware_remainder_inventory as pure
import zero_aware_remainder_ordinary_inventory as ordinary
import signed_divmod_profile as numeric
import software_double_profile as canonical
import zero_aware_remainder_shift_inventory as shift
import zero_aware_mixed_runtime_inventory as bounded
import full_width_signed_runtime_inventory as unframed
import full_width_signed_framed_inventory as strict
import local_alias_slot_inventory as profile
import local_alias_slot_profile as slots
import local_long_branch_profile as frame
import owner_graph_profile as graph

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = """extern int func_08020000(int a, int b, int c, int d);
int func_08010000(int value, int divisor, int extra, int other_divisor)
{
    unsigned char local[8];
    unsigned char *first = local;
    unsigned char *second = local + 1;
    unsigned char *third = local + 2;
    unsigned char *fourth = local + 3;
    int a = func_08020000(value, divisor, extra, other_divisor);
    int b = func_08020000(extra, divisor, extra, other_divisor);
    int c = func_08020000(value + extra, divisor, extra, other_divisor);
    int d = func_08020000(value - extra, divisor, extra, other_divisor);
    int e = func_08020000(value ^ extra, divisor, extra, other_divisor);
    int f = func_08020000(value & extra, divisor, extra, other_divisor);
    *first = a / divisor;
    *second = b % other_divisor;
    *third = c;
    *fourth = d;
    return func_08020000(*first + *second + *third + *fourth, e, f, value);
}
"""



class LocalAliasSlotInventoryTests(unittest.TestCase):
    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows,indent=2)+'\n').encode(),
            ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())

    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        approved = Path(selected).read_bytes()
        assert hashlib.sha256(approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH',Path(__file__).resolve().parents[1]/'build/tests'))
        scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='alias_slot_tests_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_ALIAS_SLOT_RETAIN']) if os.environ.get('FFTA_ALIAS_SLOT_RETAIN') else None
        if cls.retained:
            cls.retained.mkdir(parents=True,exist_ok=True)
            (cls.retained/'caller.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC,cpp=match.DEFAULT_CPP,assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY,linker=match.DEFAULT_LD,flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC,root=cls.root,timeout=120)
        with runner.workspace() as workspace:
            cls.raw,_,original = match.compile_object(runner,workspace,args,cls.root,A,'src/08010000.c')
            if cls.retained:
                (cls.retained/'original.o').write_bytes(cls.raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
            cls.rows = [{'rom':f'0x{A:08X}','end':f'0x{A+len(original["text"]):08X}','mode':'thumb','instrs':0},
                {'rom':'0x081426B8','end':'0x0814274A','mode':'thumb','instrs':72},
                {'rom':'0x08142950','end':'0x08142A1E','mode':'thumb','instrs':102},
                {'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1},
                {'rom':f'0x{ORDINARY:08X}','end':f'0x{ORDINARY+2:08X}','mode':'thumb','instrs':1}]
            mapping,_ = cls.indexes(cls.rows)
            mod,div = {},{}
            cls.body,cls.calls,literals = match.link_calls(runner,workspace,args,original,A,mapping,
                len(approved),approved,modsi3_bindings=mod,divsi3_bindings=div,signed_runtime_profile=numeric.SELECTOR)
            assert not literals and set(mod.values()) == {'__modsi3'} and set(div.values()) == {'__divsi3'}
            if cls.retained:
                (cls.retained/'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
        cls.rows[0]['end'] = f'0x{A+len(cls.body):08X}'
        mapping,_ = cls.indexes(cls.rows)
        cls.rows[0]['instrs'] = owner.refine(cls.body,A,mapping)['instrs']
        cls.mapping,cls.index = cls.indexes(cls.rows)
        rom = bytearray(approved); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        cls.bindings = profile.bind_calls(cls.calls,cls.mapping,A,len(cls.body),len(cls.rom))
        for name,data in (('config/functions.json',cls.mapping),('symbols/functions.txt',cls.index),('baserom.bin',cls.rom)):
            (cls.root/name).write_bytes(data)
        (cls.root/'config/data_symbols.json').write_text('{}\n')
        cls.manifest,cls.instructions = profile.verify(cls.body,A,cls.rom,cls.mapping,cls.index,
            cls.calls,cls.bindings,selector=profile.SELECTOR)
        if cls.retained:
            for name,data in (('body.bin',cls.body),('baserom.bin',cls.rom),('functions.json',cls.mapping),('functions.txt',cls.index)):
                (cls.retained/name).write_bytes(data)
            (cls.retained/'native-inventory.json').write_text(json.dumps(cls.manifest,indent=2)+'\n')
            (cls.retained/'fixture.json').write_text(json.dumps({'ELF_type':original['type'],
                'calls':cls.calls,'bindings':cls.bindings,'synthetic_only':True,
                'conditional_ordinary_call_ABI':True,'source_or_ELF_admission':False,
                'compiler':[match.DEFAULT_CC,match.DEFAULT_FLAGS]},indent=2)+'\n')

    def native(self,**changes):
        values = dict(data=self.body,address=A,rom=self.rom,mapping=self.mapping,index=self.index,
            calls=self.calls,bindings=self.bindings,selector=profile.SELECTOR)
        values.update(changes)
        return profile.verify(**values)

    def machine(self,sequence):
        data = bytearray()
        for value in sequence:
            if type(value) is int:
                data += struct.pack('<H',value)
            else:
                target = pure.remainder.ADDRESS if value == 'mod' else profile.quotient.ADDRESS if value == 'div' else ORDINARY if value == 'ordinary' else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows); rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping,_ = self.indexes(rows)
        refinement = owner.refine(data,A,mapping)
        rows[0]['instrs'] = refinement['instrs']
        mapping,index = self.indexes(rows)
        calls = {int(row['site'],16):int(row['target'],16) for row in refinement['calls']}
        bindings = profile.bind_calls(calls,mapping,A,len(data),len(self.rom))
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data,rom=bytes(rom),mapping=mapping,index=index,calls=calls,bindings=bindings)

    def test_natural_O2_API_CLI_and_old_default_refusal(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__divsi3','__modsi3','func_08020000'})
        proof = self.manifest['frame']['local_alias_slots']
        self.assertTrue(proof['stores'] and proof['loads'])
        self.assertTrue(self.manifest['complete_native_structural_proof'])
        self.assertFalse(self.manifest['source_or_ELF_admission'] or self.manifest['arithmetic_C_equivalence'] or self.manifest['termination_claim'])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'],[])
        with self.assertRaisesRegex(ValueError,'cannot be stored or spilled'):
            strict.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=strict.SELECTOR)
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),json.loads(json.dumps(self.manifest)))
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def local(self,sequence,policy=slots.SELECTOR):
        data = b''.join(struct.pack('<H',word) for word in sequence)
        md = match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);md.detail=True
        instructions = {i.address:i for i in md.disasm(data,A)}
        edges = {}
        for site,i in instructions.items():
            if i.mnemonic == 'bx':edges[site] = ()
            elif i.mnemonic == 'b':edges[site] = (i.operands[0].imm,)
            elif i.mnemonic.startswith('b') and i.mnemonic != 'bl':edges[site] = (i.operands[0].imm,site+i.size)
            else:edges[site] = (site+i.size,)
        return frame.prove_frame(instructions,edges,A,{}, {},stack_aliases=True,local_alias_slot_policy=policy)

    HEAD = [0xB510,0xB084]
    TAIL = [0x2000,0xB004,0xBC10,0xBC02,0x4708]

    def test_exact_spill_reload_small_SP_add_and_byte_index(self):
        sequence = self.HEAD+[0x466C,0x9403,0x9C03,0x2101,0x4469,0x2207,0x700A,
            0x2301,0x56E0,0x2400]+self.TAIL
        proof = self.local(sequence)['local_alias_slots']
        self.assertEqual(len(proof['stores']),1);self.assertEqual(len(proof['loads']),1)
        self.assertEqual(len(proof['small_SP_additions']),1);self.assertEqual(len(proof['small_index_byte_loads']),1)
        with self.assertRaisesRegex(ValueError,'cannot be stored or spilled'):self.local(sequence,None)
        with self.assertRaisesRegex(ValueError,'versioned policy'):self.local(sequence,'other')

    def test_whole_scalar_overwrite_kills_slot_alias(self):
        proof = self.local(self.HEAD+[0x466C,0x9403,0x2100,0x9103,0x9803,0x2400]+self.TAIL)
        self.assertEqual(proof['local_alias_slots']['loads'],[])

    def test_slot_bounds_saved_words_and_partial_overlap(self):
        for middle in ([0x466C,0x9404],[0x466C,0x9405],[0x466C,0x9403,0x230D,0x446B,0x2100,0x7019,0x9803,0x7800],
                [0x466C,0x9403,0x466B,0x7B18]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.local(self.HEAD+middle+self.TAIL)

    def test_alias_slot_join_unknown_or_different_provenance_stays_refused(self):
        for middle in ([0x466C,0x2800,0xD000,0x9403,0x9803,0x7800],
                [0x466C,0x2800,0xD001,0x9403,0xE001,0x2000,0x9003,0x9803,0x7800],
                [0x466C,0x2800,0xD001,0x9403,0xE001,0x3401,0x9403,0x9803,0x7800]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.local(self.HEAD+middle+self.TAIL)

    def test_release_reallocation_cannot_revive_pointer_register_or_slot(self):
        for middle in ([0x466C,0x9403,0xB001,0xB081,0x9C03,0x7820],
                [0x466C,0x9403,0x9C03,0xB004,0xB084,0x7820],
                [0x466C,0x9403,0xB004,0xB084,0x9803,0x7800]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.local(self.HEAD+middle+self.TAIL)

    def test_constants_require_exact_all_path_MOVS_and_writes_kill(self):
        for middle in ([0x466C,0x9403,0x56E0],[0x466C,0x9403,0x2304,0x56E0],
                [0x466C,0x9403,0x2301,0x3300,0x56E0],
                [0x466C,0x9403,0x2800,0xD000,0x2301,0x56E0],
                [0x466C,0x9403,0x2301,0x9B00,0x56E0],
                [0x466C,0x9403,0x2104,0x4469]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.local(self.HEAD+middle+self.TAIL)

    def test_calls_kill_constants_and_reject_loaded_alias_arguments(self):
        for middle in ([0x466C,0x9403,0x9803,'ordinary'],
                [0x466C,0x9403,0x2301,'ordinary',0x56E0]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):
                self.machine(self.HEAD+middle+['div','mod',0x2400]+self.TAIL)

    def test_return_saved_register_origin_dynamic_SP_and_numeric_boundary(self):
        for middle in ([0x466C,0x9403,0xB0A0],[0x466C,0x9403,0x4685],
                [0x466C,0x9403,0x9803,0x9004]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.local(self.HEAD+middle+self.TAIL)
        with self.assertRaisesRegex(ValueError,'original entry LR'):
            self.local(self.HEAD+[0x466C,0x9403]+self.TAIL[:-1]+[0x4686,0x4770])
        with self.assertRaises(ValueError):self.native(selector=strict.SELECTOR)
        with self.assertRaises(ValueError):self.native(bindings={})
        manifest = copy.deepcopy(self.manifest);manifest['frame']['local_alias_slots']['loads'] = []
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=manifest)
        with self.assertRaises(ValueError):numeric.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)

if __name__ == '__main__':unittest.main()
