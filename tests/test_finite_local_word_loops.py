"""Finite local-array caller proof, failure boundaries and independent CPU oracle."""
import copy
import json
from pathlib import Path
import struct
import importlib.util
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import finite_local_word_loop_profile as finite
from test_nested_known_query import assemble

A, B, T = 0x08010000, 0x08011000, 0x08142250
TABLE, EXTERNAL = 0x08300000, 0x02001000


def fixture():
    tokens = [0xb570,0xb082,0x2400,0x4d10,0x4e10,0x1c28,B,
              0x00a1,0x4469,0x6008,0x6833,0x490d,0x1c2a,T,
              0x3401,0x2c01,0xddf1,0x2400,0x4e08,0x466d,
              0xcd02,0x6833,0x4807,0x4a05,T,0x3401,0x2c01,
              0xddf6,0x2000,0xb002,0xbc70,0xbc02,0x4708]
    raw = assemble(A,tokens)+struct.pack('<III',16,TABLE,EXTERNAL)
    assert len(raw) == 84
    rom = bytearray(0x300004)
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(raw)] = raw
    rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = b'\x70\x47'
    rom[T-match.ROM_BASE:T-match.ROM_BASE+4] = bytes.fromhex('1847c046')
    rows = [dict(rom=f'0x{a:08X}',end=f'0x{a+n:08X}',mode='thumb',instrs=count)
            for a,n,count in [(A,84,36),(B,2,1),(T,4,1)]]
    mapping = json.dumps(rows).encode()
    rows[0]['instrs'] = owner.refine(raw,A,mapping)['instrs']
    mapping = json.dumps(rows).encode()
    refinement = owner.refine(raw,A,mapping)
    _,_,_,calls,_ = graph.graph(raw,A,refinement)
    return dict(data=raw,address=A,rom=bytes(rom),mapping=mapping,
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                     f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode(),
        objects=json.dumps({'data_08300000':'0x08300000','data_02001000':'0x02001000'}).encode(),
        bindings=dict(calls=[[site-A,'_call_via_r3' if target==T else f'func_{target:08X}']
                             for site,target in sorted(calls.items())],
                      functions=[],switches=[],data=[[76,'data_08300000',0],[80,'data_02001000',0]]),
        selector=finite.SELECTOR)


def changed(offset, halfword):
    f=fixture();raw=bytearray(f['data']);struct.pack_into('<H',raw,offset,halfword)
    f['data']=bytes(raw);rom=bytearray(f['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(raw)]=raw
    f['rom']=bytes(rom)
    return f


class FiniteLoopTests(unittest.TestCase):
    def test_two_word_store_and_cursor_load_loops(self):
        manifest,_=owner.verify(**fixture())
        self.assertEqual(manifest['profile'],finite.SCHEMA)
        p=manifest['proof']['finite_local_words']
        self.assertEqual(p['frame_bytes'],24)
        self.assertEqual([x[2]for x in p['accesses']if x[1]=='write'],[-24,-20])
        self.assertEqual([x[2]for x in p['accesses']if x[1]=='read'],[-24,-20])
        self.assertEqual(len(p['calls']),6)

    @unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
    def test_raw_cpu_oracle_varied_allocator_values(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        f=fixture();manifest,_=owner.verify(**f)
        for returned in [(0,0),(0x02002000,0x02002040),(0xffffffff,0x12345678)]:
            cpu=Uc(UC_ARCH_ARM,UC_MODE_THUMB);cpu.mem_map(0x08000000,0x150000)
            cpu.mem_map(0x08300000,0x1000);cpu.mem_map(0x02000000,0x10000)
            cpu.mem_write(A,f['data']);cpu.mem_write(TABLE,struct.pack('<I',0x08140001))
            sp=0x02008000;stop=0x08008000;calls=[];writes=[];allocation=iter(returned)
            cpu.reg_write(arm.UC_ARM_REG_SP,sp);cpu.reg_write(arm.UC_ARM_REG_LR,stop|1)
            saved={getattr(arm,f'UC_ARM_REG_R{n}'):0x1000+n for n in range(4,12)}
            for r,v in saved.items():cpu.reg_write(r,v)
            def hook(uc,pc,size,user):
                if pc==stop:uc.emu_stop();return
                if pc not in (B,T):return
                args=[uc.reg_read(getattr(arm,f'UC_ARM_REG_R{n}'))for n in range(4)]
                calls.append((pc,args))
                value=next(allocation) if pc==B else 0xabcdef00
                for n in (1,2,3,12):uc.reg_write(getattr(arm,f'UC_ARM_REG_R{n}'),0x7000+n)
                uc.reg_write(arm.UC_ARM_REG_R0,value)
                uc.reg_write(arm.UC_ARM_REG_PC,uc.reg_read(arm.UC_ARM_REG_LR))
            def write(uc,access,at,size,value,user):
                if sp-24<=at<sp-16:writes.append((at-sp,size,value))
            cpu.hook_add(UC_HOOK_CODE,hook);cpu.hook_add(UC_HOOK_MEM_WRITE,write)
            cpu.emu_start(A|1,stop,count=256)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC),stop)
            self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP),sp)
            self.assertEqual(writes,[(-24,4,returned[0]),(-20,4,returned[1])])
            self.assertEqual([args[1]for pc,args in calls if pc==T][-2:],list(returned))
            self.assertEqual(len(calls),len(manifest['proof']['finite_local_words']['calls']))
            for r,v in saved.items():self.assertEqual(cpu.reg_read(r),v)

    def test_unknown_loop_counter_refuses(self):
        with self.assertRaisesRegex(ValueError,'constant offset|exact scalar'):
            owner.verify(**changed(4,0x1c04))

    def test_extra_iteration_hits_protected_word(self):
        with self.assertRaisesRegex(ValueError,'protected save'):
            owner.verify(**changed(34,0x2c02))

    def test_missing_local_initialization_refuses(self):
        with self.assertRaisesRegex(ValueError,'uninitialized'):
            owner.verify(**changed(20,0x1c00))

    def test_local_argument_to_callback_refuses(self):
        with self.assertRaisesRegex(ValueError,'scratch registers'):
            owner.verify(**changed(24,0x4669))

    def test_local_pointer_store_refuses(self):
        with self.assertRaisesRegex(ValueError,'stored private pointers'):
            owner.verify(**changed(20,0x6009))

    def test_cursor_overrun_hits_protected_word(self):
        with self.assertRaisesRegex(ValueError,'protected save'):
            owner.verify(**changed(58,0x2c02))

    def test_repeated_loop_state_refuses(self):
        with self.assertRaisesRegex(ValueError,'repeats'):
            owner.verify(**changed(32,0x3400))

    def test_entry_frame_release_cannot_discard_saves(self):
        with self.assertRaisesRegex(ValueError,'protected saved words'):
            owner.verify(**changed(64,0xb003))

    def test_unknown_flags_refuse(self):
        with self.assertRaisesRegex(ValueError,'unknown or stale flags'):
            owner.verify(**changed(34,0x2400))

    def test_changed_original_call_binding_refuses(self):
        f=fixture();f['bindings']['calls'][0][1]='func_08012000'
        with self.assertRaisesRegex(ValueError,'call identities'):
            owner.verify(**f)

    def test_changed_thunk_bytes_refuse(self):
        f=fixture();rom=bytearray(f['rom']);rom[T-match.ROM_BASE]=0x10;f['rom']=bytes(rom)
        with self.assertRaises(ValueError):owner.verify(**f)

    def test_saved_manifest_tamper_refuses(self):
        f=fixture();manifest,_=owner.verify(**f);manifest['proof']['finite_local_words']['frame_bytes']=8
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            owner.verify(**f,manifest=manifest)

    def test_step_budget_refuses(self):
        f=fixture();refinement=owner.refine(f['data'],A,f['mapping'])
        ins,edges,_,calls,_=graph.graph(f['data'],A,refinement)
        with self.assertRaisesRegex(ValueError,'budget exhausted'):
            finite.execute(f['data'],A,ins,edges,calls,step_limit=10)

    def test_signed_and_unsigned_cmp_predicates(self):
        self.assertTrue(finite.CONDITIONS['blt'](*finite.compare(0xffffffff,1)))
        self.assertFalse(finite.CONDITIONS['blo'](*finite.compare(0xffffffff,1)))
        self.assertTrue(finite.CONDITIONS['bge'](*finite.compare(0x7fffffff,0xffffffff)))

    def test_old_selector_and_report_markers_remain_distinct(self):
        f=fixture();f['selector']='bounded-buffer-conditional-thunks-v1'
        with self.assertRaises(ValueError):owner.verify(**f)
        self.assertEqual(owner.selector_for_report(f'* verification: `{finite.SCHEMA}`\n* owner runtime: {finite.SELECTOR}'),finite.SELECTOR)


if __name__=='__main__':unittest.main()
