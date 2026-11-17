"""Named three-output composition, strict mutations and an independent raw oracle."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import importlib.util
import sys
import unittest
from unittest.mock import patch

import test_buffer_discarded_return_scratch as fixtures
import named_three_halfword_output_buffer_profile as policy
import three_halfword_output_buffer_profile as prior

match,owner=fixtures.match,fixtures.owner
A,B,C=0x08010000,0x08010100,0x08010200
GLOBAL=0x02007F40
LEAF='''push {r4,r5,r6,r7,lr}
mov r7,r8
push {r7}
ldr r4,[sp,#24]
mov r8,r4
ldr r7,[sp,#28]
lsls r0,r0,#16
asrs r0,r0,#16
lsls r2,r2,#16
asrs r2,r2,#16
subs r4,r0,r2
asrs r4,r4,#1
strh r4,[r3]
ldr r6,state
ldrh r5,[r6,#32]
adds r4,r4,r5
strh r4,[r3]
adds r0,r0,r2
asrs r2,r0,#2
lsls r1,r1,#16
asrs r1,r1,#17
subs r2,r2,r1
mov r1,r8
strh r2,[r1]
ldrh r1,[r6,#34]
adds r2,r2,r1
mov r4,r8
strh r2,[r4]
strh r0,[r7]
pop {r3}
mov r8,r3
pop {r4,r5,r6,r7}
pop {r0}
bx r0
.align 2
state: .word 0x02007F40
'''
WRAPPER='''push {r4,r5,r6,r7,lr}
sub sp,#8
adds r6,r1,#0
movs r1,#8
ldrsh r4,[r0,r1]
movs r5,#10
ldrsh r1,[r0,r5]
movs r7,#12
ldrsh r5,[r0,r7]
str r2,[sp]
str r3,[sp,#4]
adds r0,r4,#0
adds r2,r5,#0
adds r3,r6,#0
bl leaf
add sp,#8
pop {r4,r5,r6,r7}
pop {r0}
bx r0
'''


class NamedThreeOutputTests(unittest.TestCase):
    setUp=fixtures.DiscardedReturnScratchTests.setUp

    def fixture(self,leaf=LEAF,wrapper=WRAPPER):
        source=self.root/'fixture.s'
        source.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
            '.global leaf,leaf_end,wrapper,wrapper_end,func_08010200,caller_end\n'
            '.thumb_func\nleaf:\n'+leaf+'leaf_end:\n.org 0x100\n.thumb_func\nwrapper:\n'+wrapper+
            'wrapper_end:\n.org 0x200\n.thumb_func\nfunc_08010200:\n'
            'push {lr}\nsub sp,#8\nmov r1,sp\nadd r2,sp,#4\nmovs r3,#6\nadd r3,sp\n'
            'bl wrapper\nadd sp,#8\npop {r0}\nbx r0\ncaller_end:\n')
        subprocess.run(['arm-none-eabi-as','-mthumb-interwork',str(source),'-o',str(self.root/'f.o')],check=True,capture_output=True)
        subprocess.run(['arm-none-eabi-ld',f'-Ttext=0x{A:08X}','-e','func_08010200',str(self.root/'f.o'),'-o',str(self.root/'f.elf')],check=True,capture_output=True)
        image=match.elf_image((self.root/'f.elf').read_bytes());symbols={r['name']:r['value']for r in image['symbols']}
        rows=[];bodies={}
        for name,start in [('leaf',A),('wrapper',B),('caller',C)]:
            end=symbols[name+'_end'];bodies[name]=image['text'][start-A:end-A]
            rows.append(dict(rom=hex(start),end=hex(end),mode='thumb',instrs=0))
        inputs=dict(rom=b'\0'*(A-match.ROM_BASE)+image['text'],mapping=json.dumps(rows).encode(),
            index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} 0 return\n'for r in rows).encode(),
            objects=json.dumps({'g_state_02007F40':f'0x{GLOBAL:08X}'}).encode())
        changed=patch.multiple(policy,LEAF=(A,len(bodies['leaf']),hashlib.sha256(bodies['leaf']).hexdigest()),
            WRAPPER=(B,len(bodies['wrapper']),hashlib.sha256(bodies['wrapper']).hexdigest()))
        changed.start();self.addCleanup(changed.stop)
        return inputs,bodies

    def apply(self,inputs,**changes):
        r=match.ARM_REG_R0
        args=dict(aliases={r+1:-8,r+2:-6,r+3:-4,r+8:-2,r+12:-12},stack=[(False,False,True)]*8,site=C+12)
        args.update(changes);proof=policy.NamedThreeOutputBufferProof(**inputs)
        return proof,proof.check_call(B,**args)

    def test_five_writes_three_bounds_and_actual_entryR8_return(self):
        inputs,_=self.fixture();p,r=self.apply(inputs);r0=match.ARM_REG_R0
        self.assertEqual(r,{r0+3:-2,r0+12:-12})
        m=p.nested_manifest();self.assertEqual(m['calls'][0]['writes_entry_SP_offsets'],[[-8,2],[-6,2],[-4,2]])
        leaf=m['native_helpers']['leaf']['structure']['effects']
        self.assertEqual(len(leaf['formal_writes']),5)
        self.assertEqual(leaf['return_entry_origins'],[[3,8],[12,12]])
        self.assertEqual(m['named_read_policy']['reads'],[[32,2],[34,2]])
        self.assertFalse(m['physical_nonalias_claim'])

    @unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
    def test_independent_raw_oracle_values_write_order_and_restoration(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        inputs,bodies=self.fixture();self.apply(inputs)
        cases=[(10,4,6,7,11,False),(-32768,32767,32767,65535,65535,False),
               (32767,-32768,-32768,1,2,False),(-7,-3,4,13,17,True)]
        for x,y,z,gx,gy,alias in cases:
            u=Uc(UC_ARCH_ARM,UC_MODE_THUMB);u.mem_map(A,0x2000);u.mem_write(A,inputs['rom'][A-match.ROM_BASE:])
            u.mem_map(0x02000000,0x10000);u.mem_map(0x03000000,0x10000)
            obj=0x02001000;sp=0x03008000;out=[sp+16,sp+18,sp+20]
            if alias:out=[sp+16]*3
            u.mem_write(obj+8,struct.pack('<hhh',x,y,z));u.mem_write(GLOBAL+32,struct.pack('<HH',gx,gy))
            saved={getattr(arm,'UC_ARM_REG_R'+str(n)):0x1200+n for n in range(4,12)}
            for r,v in saved.items():u.reg_write(r,v)
            r8=saved[arm.UC_ARM_REG_R8]
            for n,v in enumerate([obj,*out]):u.reg_write(getattr(arm,'UC_ARM_REG_R'+str(n)),v)
            stop=A+0x1000;u.reg_write(arm.UC_ARM_REG_SP,sp);u.reg_write(arm.UC_ARM_REG_LR,stop|1)
            writes=[]
            def code(uc,pc,size,_):
                if pc==stop:uc.emu_stop()
            def write(uc,access,at,size,value,_):
                if at in out:writes.append((at,size,value&0xffff))
            u.hook_add(UC_HOOK_CODE,code);u.hook_add(UC_HOOK_MEM_WRITE,write);u.emu_start(B|1,stop,count=200)
            a=(x-z)>>1;b=((x+z)>>2)-(y>>1)
            expected=[(out[0],2,a&65535),(out[0],2,(a+gx)&65535),(out[1],2,b&65535),(out[1],2,(b+gy)&65535),(out[2],2,(x+z)&65535)]
            self.assertEqual(writes,expected);self.assertEqual(u.reg_read(arm.UC_ARM_REG_SP),sp)
            self.assertEqual(u.reg_read(arm.UC_ARM_REG_R3),r8)
            for r,v in saved.items():self.assertEqual(u.reg_read(r),v)
            self.assertEqual(u.reg_read(arm.UC_ARM_REG_PC),stop)

    def test_output_requires_live_aligned_unprotected_bounds(self):
        inputs,_=self.fixture();r=match.ARM_REG_R0
        for offset in (-1,-34,0):
            with self.subTest(offset=offset),self.assertRaisesRegex(ValueError,'local|output|pointer|stack|bounds|aligned'):self.apply(inputs,aliases={r+1:-8,r+2:-6,r+3:offset})
        with self.assertRaisesRegex(ValueError,'local|protected|saved|frame'):self.apply(inputs,stack=[(False,True,False)]*8)

    def test_all_three_outputs_and_nonlocal_object_required(self):
        inputs,_=self.fixture();r=match.ARM_REG_R0
        for aliases in ({r+1:-8,r+2:-6},{r:-16,r+1:-8,r+2:-6,r+3:-4}):
            with self.subTest(aliases=aliases),self.assertRaisesRegex(ValueError,'local|output|pointer|stack|bounds|aligned'):self.apply(inputs,aliases=aliases)

    def test_caller_pointer_slots_remain_rejected(self):
        inputs,_=self.fixture()
        with self.assertRaisesRegex(ValueError,'no pointer slots'):self.apply(inputs,slots={-4:-8})

    def test_outgoing_word_is_initialized_at_exact_offset(self):
        for value in ('movs r3,#0','str r3,[sp,#8]','str r2,[sp,#4]'):
            with self.subTest(value=value),self.assertRaisesRegex(ValueError,'pointer store|transport'):
                inputs,_=self.fixture(wrapper=WRAPPER.replace('str r3,[sp,#4]',value));self.apply(inputs)

    def test_leaf_extra_incoming_word_refused(self):
        inputs,_=self.fixture(leaf=LEAF.replace('ldr r7,[sp,#28]','ldr r7,[sp,#32]'))
        with self.assertRaisesRegex(ValueError,'incoming|entry|word'):self.apply(inputs)

    def test_named_read_extent_remains_exact(self):
        inputs,_=self.fixture(leaf=LEAF.replace('ldrh r5,[r6,#32]','ldrh r5,[r6,#36]'))
        with self.assertRaisesRegex(ValueError,'named output read'):self.apply(inputs)

    def test_formal_pointer_is_not_a_scalar_store_value(self):
        inputs,_=self.fixture(leaf=LEAF.replace('strh r0,[r7]','strh r3,[r7]'))
        with self.assertRaisesRegex(ValueError,'scalar source'):self.apply(inputs)

    def test_leaf_saved_high_register_restoration_required(self):
        inputs,_=self.fixture(leaf=LEAF.replace('mov r8,r3','mov r8,r0'))
        with self.assertRaisesRegex(ValueError,'restore|restoring|saved|entry'):self.apply(inputs)

    def test_wrapper_actual_input_offsets_and_return_required(self):
        for src in (WRAPPER.replace('movs r7,#12','movs r7,#14'),WRAPPER.replace('bx r0','bx lr')):
            with self.subTest(src=src),self.assertRaisesRegex(ValueError,'offsets|restore|restoration'):
                inputs,_=self.fixture(wrapper=src);self.apply(inputs)

    def test_canonical_named_binding_required(self):
        inputs,_=self.fixture();inputs['objects']=b'{}'
        with self.assertRaisesRegex(ValueError,'typed data binding'):self.apply(inputs)

    def test_whole_helper_body_identity_required(self):
        inputs,_=self.fixture();raw=bytearray(inputs['rom']);raw[B-match.ROM_BASE]^=1
        with self.assertRaisesRegex(ValueError,'complete immutable indexed helper'):self.apply(dict(inputs,rom=bytes(raw)))

    def test_original_binding_report_and_manifest_are_closed(self):
        inputs,bodies=self.fixture();args=dict(bindings=dict(calls=[[12,'func_08010100']],data=[],functions=[],switches=[]),selector=policy.SELECTOR)
        m,ins=owner.verify(bodies['caller'],C,**inputs,**args)
        self.assertEqual(m['profile'],policy.SCHEMA)
        forged=copy.deepcopy(m);forged['proof']['buffers']['three_halfword_outputs']['calls']=[]
        with self.assertRaisesRegex(ValueError,'manifest differs'):owner.verify(bodies['caller'],C,**inputs,manifest=forged,**args)
        self.assertEqual(owner.selector_for_report(f'* verification: `{policy.SCHEMA}`'),policy.SELECTOR)
        with self.assertRaises(ValueError):owner.verify(bodies['caller'],C,**inputs,**dict(args,selector=prior.SELECTOR))

    def test_native_cli_exposes_explicit_selector(self):
        r=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--help'],check=True,capture_output=True,text=True)
        self.assertIn(policy.SELECTOR,r.stdout)

if __name__=='__main__':unittest.main(verbosity=2)
