"""Exact signed and unsigned immediate shifts remain inventory-only."""
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
import zero_aware_remainder_shift_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''extern int func_08020000(int value);
int func_08010000(int value, int divisor)
{
    int adjusted = func_08020000(value);
    return (short)adjusted % divisor;
}
'''


class ShiftRemainderTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='shift_mod_tests_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_SHIFT_REMAINDER_RETAIN']) if os.environ.get('FFTA_SHIFT_REMAINDER_RETAIN') else None
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

    @staticmethod
    def encoded_shift(operation,amount,destination=0,source=2):
        return operation | ((amount & 31) << 6) | (source << 3) | destination

    def test_natural_signed_cast_negative_range_native_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__modsi3','func_08020000'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertNotIn('mask_transfers',self.manifest)
        self.assertEqual(self.manifest['shift_transfers'][0][1],'asrs')
        self.assertEqual(self.manifest['shift_transfers'][0][4:7],[16,-32768,32767])
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

    def test_exact_ASR_LSR_bounds_include_negative_signed_values_and_32_encoding(self):
        for operation,amounts in ((0x1000,(16,17,31,32)),(0x0800,(17,18,31,32))):
            for amount in amounts:
                encoded = self.encoded_shift(operation,amount)
                with self.subTest(operation=operation,amount=amount):
                    manifest,_ = self.machine([0xB510,'ordinary',encoded,'mod',0xBC10,0xBC02,0x4708])
                    transfer = manifest['shift_transfers'][0]
                    self.assertEqual(transfer[4],amount)
                    low,high = transfer[5:7]
                    self.assertLessEqual(-32768,low); self.assertLessEqual(high,32767)
                    values = (-0x80000000,-0x7FFFFFFF,-65536,-32769,-1,0,1,32767,0x7FFFFFFF)
                    for value in values:
                        actual = value >> amount if operation == 0x1000 else (value & 0xFFFFFFFF) >> amount
                        self.assertLessEqual(low,actual); self.assertLessEqual(actual,high)
                    if operation == 0x1000:
                        self.assertLess(low,0)
                        self.assertEqual((-0x80000000) >> amount,low)
                    else:self.assertEqual(low,0)

    def test_unsigned16_small_signed_shift_register_shift_loads_and_arithmetic_refused(self):
        bad = [self.encoded_shift(0x0800,16),self.encoded_shift(0x1000,15),
               self.encoded_shift(0x0000,16),0x4108,0x4088,0x7810,0x5610,0x5E10,0x8810,0x6810]
        for instruction in bad:
            with self.subTest(instruction=instruction),self.assertRaises(ValueError):
                self.machine([0xB510,'ordinary',instruction,'mod',0xBC10,0xBC02,0x4708])
        with self.assertRaisesRegex(ValueError,'signed16 r0'):
            self.machine([0xB510,'ordinary',self.encoded_shift(0x1000,16),0x3001,
                          'mod',0xBC10,0xBC02,0x4708])

    def test_skipped_shift_join_arms_and_calls_kill_caller_saved_origins(self):
        shift = self.encoded_shift(0x1000,16)
        tail = ['mod',0xBC10,0xBC02,0x4708]
        for sequence in ([0xB510,'ordinary',0x2A00,0xD000,shift],
                         [0xB510,'ordinary',shift,'ordinary'],
                         [0xB510,'ordinary',shift,'mod'],
                         [0xB510,'ordinary',shift,0x4684,'ordinary',0x4660],
                         [0xB510,'ordinary',0x2A00,0xD001,shift,0xE000,self.encoded_shift(0x0800,16)]):
            with self.subTest(sequence=sequence),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine(sequence+tail)
        # Both independent shift origins are retained at the join.
        manifest,_ = self.machine([0xB510,'ordinary',0x2A00,0xD001,shift,0xE000,
            self.encoded_shift(0x0800,17)]+tail)
        self.assertEqual(len(manifest['operand_shift_origins'][0][1]),2)
        # Caller-saved facts die; saved r4 follows only the existing conditional ABI.
        self.machine([0xB510,'ordinary',shift,0x4604,'ordinary',0x4620]+tail)

    def test_helper_identity_all_bindings_and_forged_shift_origins_refused(self):
        for site in (0x08142954,0x0814274C,0x08142A1A,0x08142A12):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        for key in ('native_runtime_closure','runtime_cases','frame','calls','ordinary_calls',
                    'runtime_calls','shift_transfers','operand_shift_origins','dividend_policy'):
            manifest = copy.deepcopy(self.manifest);manifest[key] = []
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)
        manifest = copy.deepcopy(self.manifest);manifest['shift_transfers'][0][5] = 0
        with self.assertRaisesRegex(ValueError,'manifest differs'):self.native(manifest=manifest)
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        with self.assertRaises(ValueError):
            self.machine([0xB510,('call',thunks.START+2),self.encoded_shift(0x1000,16),
                          'mod',0xBC10,0xBC02,0x4708])

    def test_existing_frame_stack_alias_and_return_gates_are_retained(self):
        shift = self.encoded_shift(0x1000,16)
        for sequence in ([0xB510,0x9000,'ordinary',shift,'mod',0xBC10,0xBC02,0x4708],
                         [0xB510,'ordinary',shift,'mod',0xBC02,0x4708],
                         [0xB510,0x4668,'ordinary',shift,'mod',0xBC10,0xBC02,0x4708],
                         [0xB510,0xB081,'ordinary',shift,'mod',0xB001,0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.machine(sequence)

    def test_old_AND_profiles_and_source_report_status_boundary_unchanged(self):
        with self.assertRaisesRegex(ValueError,'every call to be canonical MOD'):
            pure.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=pure.SELECTOR)
        with self.assertRaisesRegex(ValueError,'signed16 r0'):
            ordinary.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=ordinary.SELECTOR)
        runtime = {site:name for site,name in self.bindings.items() if name == '__modsi3'}
        with self.assertRaisesRegex(ValueError,'signed16 r0 and nonzero r1'):
            match.verify_leaf_instructions(self.body,A,True,self.calls,modsi3_context=(self.rom,self.mapping,runtime))
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

    def test_new_selector_requires_isolated_fresh_context(self):
        context = (self.rom,self.mapping,self.index,self.bindings,{},profile.SELECTOR)
        for options in ({'double_context':()},{'signed_runtime_context':()},{'buffer_proof':object()},
                        {'remainder_inventory_context':context},{'remainder_ordinary_inventory_context':context}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body,A,True,self.calls,
                    remainder_shift_inventory_context=context,**options)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,A,True,self.calls,
                remainder_shift_inventory_context=context[:4]+({'invented':True},profile.SELECTOR))
        with self.assertRaises(ValueError):self.native(selector=ordinary.SELECTOR)


if __name__ == '__main__':
    unittest.main()

