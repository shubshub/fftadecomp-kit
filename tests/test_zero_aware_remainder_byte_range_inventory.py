"""Exact architectural byte and signed load intervals remain inventory-only."""
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
import zero_aware_remainder_shift_inventory as shift
import zero_aware_remainder_framed_inventory as framed
import zero_aware_remainder_byte_range_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern unsigned char *func_08020000(unsigned char *bytes);
int func_08010000(unsigned char *bytes, int divisor)
{
    unsigned char *pointer = func_08020000(bytes);
    return (*pointer - 1) % divisor;
}
'''


class ByteRangeRemainderTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='byte_range_mod_tests_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_BYTE_RANGE_REMAINDER_RETAIN']) if os.environ.get('FFTA_BYTE_RANGE_REMAINDER_RETAIN') else None
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
                {'rom':f'0x{ORDINARY:08X}','end':f'0x{ORDINARY+2:08X}','mode':'thumb','instrs':1},
                {'rom':'0x08142950','end':'0x08142A1E','mode':'thumb','instrs':102},
                {'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1}]
            mapping,_ = cls.indexes(cls.rows)
            runtime = {}
            cls.body,cls.calls,literals = match.link_calls(runner,workspace,args,original,A,mapping,
                len(approved),approved,modsi3_bindings=runtime)
            assert not literals and set(runtime.values()) == {'__modsi3'}
            if cls.retained:
                (cls.retained/'linked.elf').write_bytes(runner.read_binary(f'{workspace}/f.elf'))
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
                target = pure.remainder.ADDRESS if value == 'mod' else ORDINARY if value == 'ordinary' else value[1]
                delta = target-(A+len(data))-4
                data += struct.pack('<HH',0xF000|((delta>>12)&0x7FF),0xF800|((delta>>1)&0x7FF))
        data = bytes(data)
        rows = copy.deepcopy(self.rows); rows[0]['end'] = f'0x{A+len(data):08X}'
        mapping,_ = self.indexes(rows)
        refinement = owner.refine(data,A,mapping)
        rows[0]['instrs'] = refinement['instrs']
        mapping,index = self.indexes(rows)
        calls = {int(row['site'],16):int(row['target'],16) for row in refinement['calls']}
        bindings = {site:'__modsi3' if target == pure.remainder.ADDRESS else f'func_{target:08X}'
                    for site,target in calls.items()}
        rom = bytearray(self.rom); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        return self.native(data=data,rom=bytes(rom),mapping=mapping,index=index,calls=calls,bindings=bindings)

    def test_natural_byte_minus_one_native_API_CLI_and_negative_range(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__modsi3','func_08020000'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertEqual(self.manifest['load_transfers'][0][1:5],['ldrb','r0',0,255])
        self.assertEqual(self.manifest['immediate_arithmetic_transfers'][0][1:6],['subs','r0',-1,-1,254])
        self.assertEqual(self.manifest['operand_ranges'][0][1:3],[-1,254])
        self.assertEqual(self.manifest['frame']['external_calls'],'existing-direct-call-ABI-summary')
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])),persisted)
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),persisted)
        self.assertNotIn('MATCH',run.stdout)
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_exact_architectural_load_forms_and_signed_ranges(self):
        for encoded,expected in ((0x7810,(0,255)),(0x5CD0,(0,255)),
                (0x56D0,(-128,127)),(0x5ED0,(-32768,32767))):
            with self.subTest(encoded=encoded):
                manifest,_ = self.machine([0xB510,'ordinary',encoded,'mod',0xBC10,0xBC02,0x4708])
                self.assertEqual(manifest['operand_ranges'][0][1:3],list(expected))
                self.assertEqual(len(manifest['operand_ranges'][0][3]),1)

    def test_exact_small_and_large_immediate_arithmetic_and_copies(self):
        for load,arithmetic,expected in ((0x7810,0x3001,(1,256)),(0x7810,0x3801,(-1,254)),
                (0x781A,0x1DD0,(7,262)),(0x781A,0x1E50,(-1,254)),
                (0x56D0,0x3001,(-127,128)),(0x56D0,0x3801,(-129,126))):
            with self.subTest(load=load,arithmetic=arithmetic):
                manifest,_ = self.machine([0xB510,'ordinary',load,arithmetic,'mod',0xBC10,0xBC02,0x4708])
                self.assertEqual(manifest['operand_ranges'][0][1:3],list(expected))
                self.assertEqual(len(manifest['operand_ranges'][0][4]),1)
        self.machine([0xB510,'ordinary',0x7810,0x4604,'ordinary',0x4620,'mod',0xBC10,0xBC02,0x4708])

    def test_unknown_word_unsigned_halfword_shifts_and_excess_ranges_refused(self):
        for instruction in (0x6810,0x8810,0x5AD0,0x4108,0x4088,0x1410,0x0C10):
            with self.subTest(instruction=instruction),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine([0xB510,'ordinary',instruction,'mod',0xBC10,0xBC02,0x4708])
        for sequence in ([0x5ED0,0x3001],[0x5ED0,0x3801],[0x7810]+[0x30FF]*128,
                [0x7810,0x1880],[0x3001],[0x7810,0x4108],[0x7810,0x4088],
                [0x7810,0x8810],[0x7810,0x6810]):
            with self.subTest(sequence=sequence),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine([0xB510,'ordinary']+sequence+['mod',0xBC10,0xBC02,0x4708])

    def test_skipped_load_unknown_join_and_each_call_kill_caller_saved_facts(self):
        tail = ['mod',0xBC10,0xBC02,0x4708]
        for sequence in ([0xB510,'ordinary',0x2A00,0xD000,0x7810],
                [0xB510,'ordinary',0x7810,'ordinary'],[0xB510,'ordinary',0x7810,'mod'],
                [0xB510,'ordinary',0x7810,0x4684,'ordinary',0x4660],
                [0xB510,'ordinary',0x2A00,0xD001,0x7810,0xE000,0x6810]):
            with self.subTest(sequence=sequence),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine(sequence+tail)
        manifest,_ = self.machine([0xB510,'ordinary',0x2A00,0xD001,0x7810,0xE000,0x56D0]+tail)
        self.assertEqual(manifest['operand_ranges'][0][1:3],[-128,255])
        self.assertEqual(len(manifest['operand_ranges'][0][3]),2)
        # A bounded widening loop must terminate by refusal, never an invented iteration count.
        with self.assertRaisesRegex(ValueError,'state budget exceeded'):
            self.machine([0xB510,'ordinary',0x7810,0x3001,0x2A00,0xD1FC]+tail)

    def test_helper_identity_binding_and_every_manifest_provenance_field(self):
        for site in (0x08142954,0x0814274C,0x08142A1A,0x08142A12):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for key in ('native_runtime_closure','runtime_cases','frame','calls','ordinary_calls','runtime_calls',
                'load_transfers','immediate_arithmetic_transfers','operand_ranges','dividend_policy'):
            manifest = copy.deepcopy(self.manifest);manifest[key] = []
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)
        manifest = copy.deepcopy(self.manifest);manifest['operand_ranges'][0][1] = 0
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=manifest)
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        with self.assertRaises(ValueError):
            self.machine([0xB510,('call',thunks.START+2),0x7810,'mod',0xBC10,0xBC02,0x4708])

    def test_existing_memory_stack_frame_and_return_gates(self):
        for sequence in ([0xB510,0x9000,'ordinary',0x7810,'mod',0xBC10,0xBC02,0x4708],
                [0xB510,'ordinary',0x7810,'mod',0xBC02,0x4708],
                [0xB510,0x4668,'ordinary',0x7810,'mod',0xBC10,0xBC02,0x4708],
                [0xB510,0xB081,'ordinary',0x7810,'mod',0xB001,0xBC10,0xBC02,0x4708],
                [0xB510,0x4668,0x7800,'ordinary',0x7810,'mod',0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.machine(sequence)

    def test_prior_selectors_and_source_report_status_boundary(self):
        for previous in (ordinary,shift):
            with self.subTest(selector=previous.SELECTOR),self.assertRaises(ValueError):
                previous.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=previous.SELECTOR)
        with self.assertRaises(ValueError):
            pure.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=pure.SELECTOR)
        with self.assertRaises(ValueError):
            framed.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=framed.SELECTOR)
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

    def test_isolated_fresh_context(self):
        context = (self.rom,self.mapping,self.index,self.bindings,{},profile.SELECTOR)
        for options in ({'double_context':()},{'signed_runtime_context':()},{'buffer_proof':object()},
                {'remainder_inventory_context':context},{'remainder_ordinary_inventory_context':context},
                {'remainder_shift_inventory_context':context},{'remainder_framed_shift_inventory_context':context}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body,A,True,self.calls,
                    remainder_byte_range_inventory_context=context,**options)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,A,True,self.calls,
                remainder_byte_range_inventory_context=context[:4]+({'invented':True},profile.SELECTOR))
        with self.assertRaises(ValueError):self.native(selector=ordinary.SELECTOR)


if __name__ == '__main__':unittest.main()
