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
import full_width_signed_framed_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int value);
int func_08010000(int value, int divisor, int extra, int other_divisor)
{
    int first = func_08020000(value);
    int second = func_08020000(extra);
    int third = func_08020000(value + extra);
    int fourth = func_08020000(value - extra);
    int fifth = func_08020000(value ^ extra);
    int sixth = func_08020000(value & extra);
    return first / divisor + second % other_divisor + third + fourth + fifth + sixth + value + extra;
}
'''



class FullWidthSignedFramedInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='full_width_runtime_tests_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_FULL_WIDTH_FRAMED_RETAIN']) if os.environ.get('FFTA_FULL_WIDTH_FRAMED_RETAIN') else None
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

    def test_natural_unrestricted_O2_native_structural_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__divsi3','__modsi3','func_08020000'})
        self.assertTrue(self.manifest['complete_native_structural_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertFalse(self.manifest['arithmetic_C_equivalence'] or self.manifest['termination_claim'])
        self.assertEqual(self.manifest['runtime_numeric_return_facts'],[])
        self.assertEqual(self.manifest['nonzero_facts'],[])
        self.assertEqual(self.manifest['frame']['external_calls'],'existing-direct-call-ABI-summary')
        self.assertTrue(any((match.thumb_stack_adjustment(item) or 0)<0 for item in self.instructions))
        self.assertEqual(set(dict(self.manifest['native_runtime_frames'])),{0x081426B8,0x08142950,0x0814274C})
        self.assertIsNone(self.manifest['ordinary_call_stack_bound'])
        self.assertNotIn('signed16',self.manifest['runtime_entry_domain'])
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure),{0x081426B8,0x08142950,0x0814274C})
        self.assertEqual(closure[0x081426B8]['returns'],[0x0814273E,0x08142748])
        self.assertEqual(closure[0x08142950]['returns'],[0x08142A12,0x08142A1C])
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])),persisted)
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),persisted)
        self.assertNotIn('MATCH',run.stdout)
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_arbitrary_runtime_entry_registers_and_zero_have_structural_claim_only(self):
        for sequence in ([0xB510,0xB081,0x9000,'div','mod',0x9800,0xB001,0xBC10,0xBC02,0x4708],
                [0xB510,0xB081,0x2100,'div',0x2100,'mod',0xB001,0xBC10,0xBC02,0x4708],
                [0xB510,0xB081,'ordinary','div','ordinary','mod',0xB001,0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence):
                manifest,_ = self.machine(sequence)
                self.assertTrue(manifest['complete_native_structural_proof'])
                self.assertEqual(manifest['runtime_numeric_return_facts'],[])
                self.assertEqual(manifest['nonzero_facts'],[])
                self.assertFalse(manifest['arithmetic_C_equivalence'] or manifest['termination_claim'])

    def test_exact_helpers_zero_edges_counts_effects_and_reference_source_pins(self):
        for site in (0x081426BA,0x08142742,0x08142748,0x0814273C,
                0x0814274C,0x08142A16,0x08142A1A,0x08142A1C):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for number in (0,1,2,3):
            rows = copy.deepcopy(self.rows);rows[number]['instrs'] -= 1
            mapping,index = self.indexes(rows)
            with self.subTest(number=number),self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        for key in ('native_runtime_closure','dependencies','frame','calls','runtime_calls','ordinary_calls',
                'producer_source_sha256','runtime_input_semantics','native_runtime_frames'):
            manifest = copy.deepcopy(self.manifest);manifest[key] = []
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)
        manifest = copy.deepcopy(self.manifest);manifest['arithmetic_C_equivalence'] = True
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=manifest)

    def test_every_call_requires_canonical_or_unique_ordinary_mapping(self):
        for target in (0x08142952,0x081426BA,0x0814274C,thunks.START,match.UDIVSI3_ADDRESS,
                0x08142B28,ORDINARY+2,A+2):
            with self.subTest(target=target),self.assertRaises(ValueError):
                self.machine([0xB510,'div','mod',('call',target),0xBC10,0xBC02,0x4708])
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        for site in self.calls:
            calls = dict(self.calls);calls.pop(site)
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(calls=calls)
        rows = copy.deepcopy(self.rows);rows.append(dict(rows[-1]))
        mapping,index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        with self.assertRaises(ValueError):self.native(selector=numeric.SELECTOR)

    def test_saved_slots_SP_alias_escapes_bad_returns_and_system_operations(self):
        head = [0xB510,0xB081]
        tail = ['div','mod',0xB001,0xBC10,0xBC02,0x4708]
        for middle in ([0x9001],[0x9002],[0x9003],[0x9803],
                [0x4668],[0x4668,0x9000],[0xDF00],[0x466C,0x6024]):
            with self.subTest(middle=middle),self.assertRaises(ValueError):self.machine(head+middle+tail)
        for sequence in ([0xB510,'div','mod',0xBC10,0xBC02,0x4708],
                head+['div','mod',0xBC10,0xBC02,0x4708],
                head+['div','mod',0xB002,0xBC10,0xBC02,0x4708],
                head+['div','mod',0xB001,0xBC02,0x4708],
                head+['div','mod',0xB001,0xBC10,0xBC02,0x4770],
                head+['div','mod',0x2A00,0xD000,0xB001,0xBC10,0xBC02,0x4708],
                head+['div','mod',0x4668,0xB001,0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.machine(sequence)

    def test_old_numeric_defaults_and_source_report_status_boundary(self):
        with self.assertRaisesRegex(ValueError,'without local stack allocation'):
            unframed.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=unframed.SELECTOR)
        with self.assertRaises(ValueError):
            numeric.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings)
        with self.assertRaises(ValueError):
            bounded.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=bounded.SELECTOR)
        with self.assertRaises(ValueError):match.verify_leaf_instructions(self.body,A,True,self.calls)
        for option in ('--signed-runtime-profile','--owner-runtime-profile'):
            run = subprocess.run([sys.executable,str(Path(match.__file__)),'--root',str(self.root),
                option,profile.SELECTOR,f'{A:08X}'],capture_output=True,text=True)
            self.assertNotEqual(run.returncode,0)
            self.assertNotIn('verdict MATCH - byte identical',run.stdout)
        report = f'# {A:08X}\n* verification: `{profile.SCHEMA}`\n**MATCH - byte identical**\n'
        self.assertFalse(evidence.report_matches(report,self.root,A))
        destination = self.root/'docs/match/08010000.md';destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_text(report)
        try:
            collected = status.collect(str(self.root),verify=False)
            self.assertEqual((collected[1],collected[3]),(0,0));self.assertTrue(collected[4])
        finally:destination.unlink()


if __name__ == '__main__':unittest.main()
