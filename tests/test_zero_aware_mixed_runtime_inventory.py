"""Complete canonical DIV/MOD zero cases compose only for explicit inventory."""
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
import zero_aware_mixed_runtime_inventory as profile

A, ORDINARY = 0x08010000, 0x08020000
SOURCE = '''void func_08010000(int *output, int value, int divisor)
{
    int adjusted = (short)value;
    output[0] = adjusted / divisor;
    output[1] = adjusted % divisor;
}
'''


class MixedRuntimeInventoryTests(unittest.TestCase):
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
        cls.temporary = tempfile.TemporaryDirectory(prefix='mixed_runtime_tests_',dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src','include','config','symbols','build'):
            (cls.root/name).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        cls.retained = Path(os.environ['FFTA_MIXED_RUNTIME_RETAIN']) if os.environ.get('FFTA_MIXED_RUNTIME_RETAIN') else None
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
                {'rom':'0x0814274C','end':'0x0814274E','mode':'thumb','instrs':1}]
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
                'conditional_ordinary_call_ABI':False,'source_or_ELF_admission':False,
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
                target = pure.remainder.ADDRESS if value == 'mod' else profile.quotient.ADDRESS if value == 'div' else value[1]
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

    @staticmethod
    def asr(destination=0,source=2,amount=16):
        return 0x1000 | ((amount & 31) << 6) | (source << 3) | destination

    def test_natural_O2_variable_divisor_full_native_API_and_CLI(self):
        self.assertEqual(struct.unpack_from('<H',self.raw,16)[0],1)
        self.assertEqual(set(self.bindings.values()),{'__divsi3','__modsi3'})
        self.assertTrue(self.manifest['complete_native_proof'] and self.manifest['inventory_only'])
        self.assertFalse(self.manifest['source_or_ELF_admission'])
        self.assertEqual(self.manifest['ordinary_calls'],[])
        self.assertEqual(self.manifest['frame']['external_calls'],'complete-native-callee-preservation-v1')
        closure = dict(self.manifest['native_runtime_closure'])
        self.assertEqual(set(closure),{0x081426B8,0x08142950,0x0814274C})
        self.assertEqual(closure[0x081426B8]['returns'],[0x0814273E,0x08142748])
        self.assertEqual(closure[0x08142950]['returns'],[0x08142A12,0x08142A1C])
        self.assertTrue(all(not proof['writes'] and not proof['stack_reads'] for proof in closure.values()))
        self.assertEqual(len(self.manifest['operand_shift_origins']),2)
        persisted = json.loads(json.dumps(self.manifest))
        self.assertEqual(json.loads(json.dumps(self.native(manifest=persisted)[0])),persisted)
        run = subprocess.run([sys.executable,str(Path(profile.__file__)),'--profile',profile.SELECTOR,
            '--rom',str(self.root/'baserom.bin'),'--mapping',str(self.root/'config/functions.json'),
            '--index',str(self.root/'symbols/functions.txt'),f'{A:08X}'],capture_output=True,text=True)
        self.assertEqual(run.returncode,0,run.stderr)
        self.assertEqual(json.loads(run.stdout),persisted)
        self.assertNotIn('MATCH',run.stdout)
        if self.retained:(self.retained/'native-inventory-cli.json').write_text(run.stdout)

    def test_actual_zero_divisor_and_negative_signed16_inputs_need_no_nonzero_premise(self):
        manifest,_ = self.machine([0xB510,self.asr(),0x2100,'div',self.asr(),0x2100,'mod',0xBC10,0xBC02,0x4708])
        self.assertEqual(manifest['divisor_partition'],['r1 == 0','r1 != 0'])
        self.assertEqual(manifest['shift_transfers'][0][5:7],[-32768,32767])
        for name in ('quotient','remainder'):
            self.assertEqual(manifest['runtime_cases'][name]['zero']['return_r0'],0)
        self.assertEqual(manifest['operand_shift_origins'],[[6,[2]],[14,[10]]])

    def test_each_runtime_needs_independent_producer_and_every_call_clobbers(self):
        tail = [0xBC10,0xBC02,0x4708]
        for sequence in ([0xB510,'div',self.asr(),'mod'],[0xB510,self.asr(),'div','mod'],
                [0xB510,self.asr(),'div',0x4684,'mod'],
                [0xB510,self.asr(0,2,15),'div',self.asr(),'mod'],
                [0xB510,0x0C10,'div',self.asr(),'mod'],
                [0xB510,self.asr(),'div',self.asr(),0x4108,'mod']):
            with self.subTest(sequence=sequence),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine(sequence+tail)
        # Callee-saved origin survives only because both complete runtime closures prove preservation.
        self.machine([0xB510,self.asr(),0x4604,'div',0x4620,'mod']+tail)

    def test_skipped_shift_unknown_arm_and_all_path_origins(self):
        tail = ['mod',0xBC10,0xBC02,0x4708]
        for arm in (0x6810,0x0C10,0x4108):
            with self.subTest(arm=arm),self.assertRaisesRegex(ValueError,'signed16 r0'):
                self.machine([0xB510,self.asr(),'div',0x2A00,0xD001,self.asr(),0xE000,arm]+tail)
        with self.assertRaisesRegex(ValueError,'signed16 r0'):
            self.machine([0xB510,self.asr(),'div',0x2A00,0xD000,self.asr()]+tail)
        manifest,_ = self.machine([0xB510,self.asr(),'div',0x2A00,0xD001,self.asr(),0xE000,self.asr(0,3,17)]+tail)
        self.assertEqual(len(manifest['operand_shift_origins'][1][1]),2)

    def test_all_canonical_call_sites_required_and_bad_targets_or_relocations_refused(self):
        for sequence in ([0xB510,self.asr(),'mod',0xBC10,0xBC02,0x4708],
                [0xB510,self.asr(),'div',0xBC10,0xBC02,0x4708],
                [0xB510,self.asr(),'div',self.asr(),('call',0x08142952),0xBC10,0xBC02,0x4708],
                [0xB510,self.asr(),'div',self.asr(),'mod',('call',ORDINARY),0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.machine(sequence)
        bindings = dict(self.bindings);bindings[next(iter(bindings))] = '__modsi3'
        with self.assertRaises(ValueError):self.native(bindings=bindings)
        calls = dict(self.calls);calls[next(iter(calls))] += 2
        with self.assertRaises(ValueError):self.native(calls=calls)
        for key in self.calls:
            reduced = dict(self.calls);reduced.pop(key)
            with self.assertRaises(ValueError):self.native(calls=reduced)

    def test_DIV_MOD_zero_hook_return_and_identity_evidence_are_exact(self):
        for site in (0x081426BA,0x08142742,0x08142746,0x08142748,0x0814273C,
                0x0814274C,0x08142A16,0x08142A1A,0x08142A1C):
            rom = bytearray(self.rom);rom[site-match.ROM_BASE] ^= 1
            with self.subTest(site=site),self.assertRaises(ValueError):self.native(rom=bytes(rom))
        rows = copy.deepcopy(self.rows);rows[1]['instrs'] -= 1
        mapping,index = self.indexes(rows)
        with self.assertRaises(ValueError):self.native(mapping=mapping,index=index)
        for key in ('native_runtime_closure','runtime_cases','dependencies','frame','calls','runtime_calls',
                'shift_transfers','operand_shift_origins','dividend_policy','caller_facts'):
            manifest = copy.deepcopy(self.manifest);manifest[key] = []
            with self.subTest(key=key),self.assertRaisesRegex(ValueError,'manifest differs'):
                self.native(manifest=manifest)

    def test_frame_saved_slots_entry_LR_and_runtime_return_alternatives(self):
        for sequence in ([0xB510,0x9000,self.asr(),'div',self.asr(),'mod',0xBC10,0xBC02,0x4708],
                [0xB510,self.asr(),'div',self.asr(),'mod',0xBC02,0x4708],
                [0xB510,0xB081,self.asr(),'div',self.asr(),'mod',0xB001,0xBC10,0xBC02,0x4708],
                [0xB510,0x4668,self.asr(),'div',self.asr(),'mod',0xBC10,0xBC02,0x4708]):
            with self.subTest(sequence=sequence),self.assertRaises(ValueError):self.machine(sequence)

    def test_old_profiles_and_source_report_status_boundary_remain_closed(self):
        with self.assertRaises(ValueError):
            numeric.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings)
        with self.assertRaises(ValueError):
            canonical.verify_context(self.body,A,self.calls,(self.rom,self.mapping,self.index,self.bindings))
        with self.assertRaises(ValueError):
            shift.verify(self.body,A,self.rom,self.mapping,self.index,self.calls,self.bindings,selector=shift.SELECTOR)
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

    def test_new_selector_needs_isolated_fresh_context(self):
        context = (self.rom,self.mapping,self.index,self.bindings,{},profile.SELECTOR)
        for options in ({'double_context':()},{'signed_runtime_context':()},{'buffer_proof':object()},
                {'remainder_inventory_context':context},{'remainder_ordinary_inventory_context':context},
                {'remainder_shift_inventory_context':context},{'remainder_framed_shift_inventory_context':context},
                {'remainder_byte_range_inventory_context':context},{'bounded_stack_output_inventory_context':context},
                {'bounded_stack_output_zero_index_inventory_context':context}):
            with self.subTest(options=options),self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body,A,True,self.calls,
                    zero_aware_mixed_inventory_context=context,**options)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,A,True,self.calls,
                zero_aware_mixed_inventory_context=context[:4]+({'invented':True},profile.SELECTOR))
        with self.assertRaises(ValueError):self.native(selector=numeric.SELECTOR)


if __name__ == '__main__':unittest.main()
