"""Both original task constructors at one call, including their zero-phase callbacks."""
import copy
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import effect_or_delay_task as choice
import match


class FrameTests(unittest.TestCase):
    def test_each_call_keeps_its_own_descriptor_payload_and_size(self):
        base = -108
        stack = [(False, False, True)] * 20 + [(False, True, False)] * 7
        proof = SimpleNamespace(observations={}, access=match.BufferCallProof.access)
        for desc, payload, size in [(12, 0, 56), (40, 68, 12)]:
            r2, r1 = match.ARM_REG_R2, match.ARM_REG_R1
            args = [{r2:base+desc}, stack, {base+desc+4:base+payload}, {r1:size}, choice.CREATE]
            choice.check_call(proof, *args)
            for index, value in [(0, {r2:base+desc,match.ARM_REG_R3:base+payload}),
                                 (0, {r2:base+desc+4}), (1,stack[:-1]), (2,{base+desc+4:base+12}),
                                 (2,{base+desc+4:base+80}), (2,{base+desc+8:base+payload}),
                                 (3,{r1:12 if size==56 else 56}), (4,choice.CREATE+2)]:
                changed = list(args)
                changed[index] = value
                with self.subTest(desc=desc,index=index,value=value), self.assertRaises(ValueError):
                    choice.check_call(proof,*changed)
        self.assertEqual(set(proof.observations[choice.CREATE]),{choice.EFFECT,choice.DELAY})


@unittest.skipUnless(os.environ.get('FFTA_EFFECT_OR_DELAY_ROOT'), 'requires reviewed source and original USA ROM')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from inert_spin_profile import index_snapshot
        from rompath import rom_path
        cls.root = Path(os.environ['FFTA_EFFECT_OR_DELAY_ROOT']).resolve()
        cls.rom = Path(rom_path(str(cls.root))).read_bytes()
        cls.mapping,cls.index,cls.objects = match.mapping_snapshot(cls.root),index_snapshot(cls.root),match.data_snapshot(cls.root)
        cls.report = (cls.root/'docs/match/080DCFE4.md').read_text()

    def test_native_linked_report_and_mutations(self):
        import match_evidence
        self.assertTrue(match_evidence.report_matches(self.report,str(self.root),choice.OWNER))
        for old,new in [('"initialized_parameter_bytes":10','"initialized_parameter_bytes":12'),
                        ('"destination_payload_interval":[16,36]','"destination_payload_interval":[16,37]'),
                        ('"private_pointer_retained":false','"private_pointer_retained":true')]:
            changed=self.report.replace(old,new)
            self.assertNotEqual(changed,self.report)
            self.assertFalse(match_evidence.report_matches(changed,str(self.root),choice.OWNER))

    def test_changed_original_callbacks_copier_join_and_bindings(self):
        import owner_admission_profile as owner
        import conditional_local_buffer_profile as local
        def verify(rom,bindings):
            off=choice.OWNER-match.ROM_BASE
            return owner.verify(rom[off:off+184],choice.OWNER,rom,self.mapping,self.index,self.objects,
                                selector=local.SCHEDULER_PAYLOAD,bindings=bindings)
        verify(self.rom,choice.BINDINGS)
        for site in (0x080DD024,0x080DD048,0x080DD050,0x080DD078,0x080DD07A,0x080DD088,
                     0x080DC58C,0x080DC5A8,0x080DC5AC,0x080DC5B4,0x080DCB04,0x080DCB10,
                     0x08005A02,0x08142250,0x0836D4BC,0x08A38A9C):
            data=bytearray(self.rom)
            data[site-match.ROM_BASE]^=2
            with self.subTest(site=hex(site)), self.assertRaises(ValueError):
                verify(bytes(data),choice.BINDINGS)
        for key,index,pos,value in [('calls',0,0,156),('functions',0,1,'func_080DCAD4'),
                                   ('functions',1,0,160)]:
            bindings=copy.deepcopy(choice.BINDINGS)
            bindings[key][index][pos]=value
            with self.subTest(bindings=bindings),self.assertRaises(ValueError):
                verify(self.rom,bindings)

    def run_game(self,flag,record,amount,parent,allocation=None):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE
        import unicorn.arm_const as reg
        from scheduler_zero_descriptor import IMAGE,DESTINATION
        r=reg
        uc=Uc(UC_ARCH_ARM,UC_MODE_THUMB)
        uc.mem_map(0x08000000,len(self.rom));uc.mem_write(0x08000000,self.rom)
        uc.mem_map(0x02000000,0x40000);uc.mem_map(0x03000000,0x8000)
        uc.mem_write(DESTINATION,self.rom[IMAGE-match.ROM_BASE:IMAGE-match.ROM_BASE+176])
        entry_sp=0x03007300
        target=0x02006000 if allocation is None else allocation
        actor,manager,object_value=0x02004000,0x02005000,0x02014000
        done=0x080000D0
        put=lambda p,v:uc.mem_write(p,struct.pack('<I',v))
        word=lambda p:struct.unpack('<I',uc.mem_read(p,4))[0]
        put(actor,object_value);put(actor+12,flag<<7);put(0x02008FF0,manager)
        put(entry_sp,0x92);put(entry_sp+4,parent);put(entry_sp+8,amount&0xffffffff)
        if record:
            uc.mem_write(record,bytes(range(1,21)))
        for register,value in [(r.UC_ARM_REG_R0,actor),(r.UC_ARM_REG_R1,record),(r.UC_ARM_REG_R2,7),
                               (r.UC_ARM_REG_R3,0x21),(r.UC_ARM_REG_SP,entry_sp),(r.UC_ARM_REG_LR,done|1)]:
            uc.reg_write(register,value)
        records=[]
        def hook(u,pc,size,context):
            if pc==0x08007138:
                count=u.reg_read(r.UC_ARM_REG_R1)
                records.append(('allocate',count))
                u.reg_write(r.UC_ARM_REG_R0,target)
                u.reg_write(r.UC_ARM_REG_PC,u.reg_read(r.UC_ARM_REG_LR))
            elif pc in (choice.EFFECT,choice.DELAY):
                desc=u.reg_read(r.UC_ARM_REG_R1); payload=u.reg_read(r.UC_ARM_REG_R2)
                records.append(('phase',pc,word(desc)&0xffff,word(desc+4),payload))
            elif pc==0x03005EE8:
                records.append(('copy20',u.reg_read(r.UC_ARM_REG_R0),u.reg_read(r.UC_ARM_REG_R1),u.reg_read(r.UC_ARM_REG_R2)))
        uc.hook_add(UC_HOOK_CODE,hook)
        uc.emu_start(choice.OWNER|1,done,count=2000)
        self.assertEqual(uc.reg_read(r.UC_ARM_REG_PC),done)
        self.assertEqual(uc.reg_read(r.UC_ARM_REG_SP),entry_sp)
        return uc.reg_read(r.UC_ARM_REG_R0),records,bytes(uc.mem_read(target,80))

    def test_machine_runs_both_callbacks_and_both_early_returns(self):
        target, record, sp = 0x02006000, 0x0200C000, 0x03007300
        for parent in (0,0x02007000):
            result,log,mem=self.run_game(1,record,40,parent)
            self.assertEqual(result,target)
            self.assertEqual(log,[('allocate',84),('phase',choice.EFFECT,0,sp-108,target+24),
                                  ('copy20',target+40,record,20)])
            self.assertEqual(mem[40:60],bytes(range(1,21)))
            self.assertEqual(mem[26:34],b'\x21\x00\x92\x00\x07\x06\x04\x06')
            self.assertEqual(struct.unpack_from('<I',mem,36)[0],0x02004000)
            result,log,mem=self.run_game(0,0,31,parent)
            self.assertEqual(result,target)
            self.assertEqual(log,[('allocate',40),('phase',choice.DELAY,0,sp-108+68,target+24)])
            self.assertEqual(mem[24:36],struct.pack('<IBBHHH',0x02014000,21,30,0,31,0x92))
            for flag,record_value,value in ((1,0,30),(0,0,-1)):
                result,log,_=self.run_game(flag,record_value,value,parent)
                self.assertEqual((result,log),(0,[]))
        # The real zero helper overwrites an aliased external record before
        # the copy. This is a genuine counterexample to dropping separation.
        _,_,mem=self.run_game(1,target+40,40,0)
        self.assertEqual(mem[40:60],bytes(20))

if __name__=='__main__':
    unittest.main()
