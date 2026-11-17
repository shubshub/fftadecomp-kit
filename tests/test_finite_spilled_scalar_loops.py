"""Independent synthetic assembly and raw CPU checks for spilled scalar loops."""
import functools
import json
from pathlib import Path
import struct
import subprocess
import importlib.util
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import finite_spilled_scalar_loop_profile as policy
import finite_local_word_loop_profile as prior

A,B,C,T=0x08010000,0x08011000,0x08012000,0x08300000

@functools.lru_cache(None)
def assembled(source,address):
    with tempfile.TemporaryDirectory(prefix='scalar-loop-fixture-') as temporary:
        p=Path(temporary);(p/'input.s').write_text('.syntax unified\n.arch armv4t\n.thumb\n'+source)
        subprocess.run(['arm-none-eabi-as','-mthumb-interwork',str(p/'input.s'),'-o',str(p/'input.o')],check=True,capture_output=True)
        subprocess.run(['arm-none-eabi-ld','-Ttext',hex(address),'-e','start',str(p/'input.o'),'-o',str(p/'input.elf')],check=True,capture_output=True)
        subprocess.run(['arm-none-eabi-objcopy','-O','binary','-j','.text',str(p/'input.elf'),str(p/'input.bin')],check=True,capture_output=True)
        names={line.split()[2]:int(line.split()[0],16)&~1 for line in subprocess.check_output(['arm-none-eabi-nm',str(p/'input.elf')],text=True).splitlines() if len(line.split())==3}
        return (p/'input.bin').read_bytes(),names

ROOT='''
.global start
.type start,%function
.thumb_func
start:
push {r4,r5,r6,lr}
sub sp,#24
counter: movs r4,#0
mov r5,sp
loop:
lsls r6,r4,#2
adds r2,r5,r6
str r2,[sp,#12]
movs r0,#136
initialize: str r0,[r2]
adds r1,r2,#0
bl leaf
recover: ldr r1,[sp,#12]
movs r3,#0
read_scalar: ldrsh r0,[r1,r3]
negate: rsbs r0,r0,#0
movs r3,#2
muls r0,r3,r0
asrs r0,r0,#1
str r0,[r1]
adds r4,#1
bound: cmp r4,#2
bls loop
movs r0,#8
movs r1,#0
clear_r2: movs r2,#0
bl ordinary
movs r0,#0
add sp,#24
pop {r4,r5,r6}
pop {r1}
bx r1
.thumb_set leaf,0x08011001
.thumb_set ordinary,0x08012001
'''
LEAF='''
.global start
.type start,%function
.thumb_func
start:
kill: movs r1,#0
ldr r0,=0x08300000
ldrsh r0,[r0,r1]
bx lr
.balign 4
'''
ORDINARY='''
.global start
.type start,%function
.thumb_func
start:
push {lr}
pop {r0}
bx r0
'''

def fixture(root=ROOT,leaf=LEAF,ordinary=ORDINARY):
    raw,labels=assembled(root,A);leafraw,_=assembled(leaf,B);ordinaryraw,_=assembled(ordinary,C)
    rom=bytearray(T-match.ROM_BASE+4);rows=[]
    for address,data in [(A,raw),(B,leafraw),(C,ordinaryraw)]:
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)]=data
        rows.append(dict(rom=f'0x{address:08X}',end=f'0x{address+len(data):08X}',mode='thumb',instrs=1))
    mapping=json.dumps(rows).encode()
    for row in rows:
        address=int(row['rom'],16);data=bytes(rom[address-match.ROM_BASE:int(row['end'],16)-match.ROM_BASE])
        row['instrs']=owner.refine(data,address,mapping)['instrs']
    mapping=json.dumps(rows).encode();refinement=owner.refine(raw,A,mapping)
    _,_,_,calls,_=graph.graph(raw,A,refinement)
    values=dict(data=raw,address=A,rom=bytes(rom),mapping=mapping,
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode(),
        objects=json.dumps({'data_08300000':'0x08300000'}).encode(),
        bindings=dict(calls=[[site-A,f'func_{target:08X}']for site,target in sorted(calls.items())],data=[],functions=[],switches=[]),selector=policy.SELECTOR)
    return values,labels


class SpilledScalarLoopTests(unittest.TestCase):
    def test_complete_spill_leaf_and_private_frame_composition(self):
        f,_=fixture();m,_=owner.verify(**f);p=m['proof']
        self.assertEqual(m['profile'],policy.SCHEMA)
        self.assertEqual(p['finite_local_words']['frame_bytes'],40)
        self.assertEqual(len(p['finite_local_words']['calls']),4)
        self.assertEqual(len(p['call_effects']['readonly_leaves']),1)
        self.assertEqual(len(p['call_effects']['ordinary_private_frames']),1)
        self.assertTrue(all(x['effect']['retained_pointer_slots'] for x in p['finite_local_words']['calls']))

    @unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
    def test_raw_cpu_oracle_preserves_spilled_origins_and_values(self):
        from unicorn import Uc,UC_ARCH_ARM,UC_MODE_THUMB,UC_HOOK_CODE,UC_HOOK_MEM_WRITE
        from unicorn import arm_const as arm
        f,_=fixture();m,_=owner.verify(**f)
        for table in (0,0x7fff,0x8000,0xffff):
            u=Uc(UC_ARCH_ARM,UC_MODE_THUMB);u.mem_map(0x08000000,0x400000);u.mem_map(0x02000000,0x10000)
            for address,source in [(A,ROOT),(B,LEAF),(C,ORDINARY)]:u.mem_write(address,assembled(source,address)[0])
            u.mem_write(T,struct.pack('<H',table));sp=0x02008000;stop=0x08008000
            u.reg_write(arm.UC_ARM_REG_SP,sp);u.reg_write(arm.UC_ARM_REG_LR,stop|1)
            saved={getattr(arm,f'UC_ARM_REG_R{n}'):0xabc000+n for n in range(4,12)}
            for r,value in saved.items():u.reg_write(r,value)
            writes=[];calls=[]
            def code(uc,pc,size,_):
                if pc==stop:uc.emu_stop()
                if pc in (B,C):calls.append(pc)
            def write(uc,access,at,size,value,_):
                if sp-40<=at<sp-16:writes.append((at-sp,size,value))
            u.hook_add(UC_HOOK_CODE,code);u.hook_add(UC_HOOK_MEM_WRITE,write)
            u.emu_start(A|1,stop,count=1024)
            self.assertEqual(u.reg_read(arm.UC_ARM_REG_PC),stop)
            self.assertEqual(u.reg_read(arm.UC_ARM_REG_SP),sp)
            self.assertEqual(calls,[B,B,B,C])
            self.assertEqual([x[2]for x in writes if x[0]==-28],[sp-40,sp-36,sp-32])
            self.assertEqual([x[2]for x in writes if x[0] in (-40,-36,-32)],[136,0xffffff78]*3)
            self.assertEqual([(x[0],x[1])for x in writes],[(x[2],x[3])for x in m['proof']['finite_local_words']['accesses']if x[1]=='write'])
            for r,value in saved.items():self.assertEqual(u.reg_read(r),value)

    def test_readonly_leaf_observing_r2_refuses(self):
        f,_=fixture(leaf=LEAF.replace('kill: movs r1,#0','kill: adds r1,r2,#0'))
        with self.assertRaisesRegex(ValueError,'observes an incoming local alias'):owner.verify(**f)

    def test_partial_read_of_spilled_pointer_refuses(self):
        f,_=fixture(root=ROOT.replace('recover: ldr r1,[sp,#12]','recover: add r1,sp,#12'))
        with self.assertRaisesRegex(ValueError,'interpret a local pointer'):owner.verify(**f)

    def test_uninitialized_local_read_refuses(self):
        f,_=fixture(root=ROOT.replace('initialize: str r0,[r2]','initialize: movs r0,#1'))
        with self.assertRaisesRegex(ValueError,'uninitialized'):owner.verify(**f)

    def test_unknown_local_index_refuses(self):
        f,_=fixture(root=ROOT.replace('counter: movs r4,#0','counter: adds r4,r0,#0'))
        with self.assertRaisesRegex(ValueError,'constant offset'):owner.verify(**f)

    def test_loop_exceeding_array_corrupts_slot_and_refuses(self):
        f,_=fixture(root=ROOT.replace('bound: cmp r4,#2','bound: cmp r4,#3'))
        with self.assertRaisesRegex(ValueError,'external stores'):owner.verify(**f)

    def test_scalar_operation_on_pointer_refuses(self):
        f,_=fixture(root=ROOT.replace('negate: rsbs r0,r0,#0','negate: rsbs r0,r1,#0'))
        with self.assertRaisesRegex(ValueError,'scalar operation observes a local pointer'):owner.verify(**f)

    def test_ordinary_callee_incoming_stack_read_refuses(self):
        f,_=fixture(ordinary=ORDINARY.replace('push {lr}\npop {r0}\nbx r0','ldr r0,[sp]\nbx lr'))
        with self.assertRaisesRegex(ValueError,'stack|frame|incoming'):owner.verify(**f)

    def test_local_alias_cannot_pass_to_stack_callee(self):
        f,_=fixture(root=ROOT.replace('clear_r2: movs r2,#0','clear_r2: mov r2,sp'))
        with self.assertRaisesRegex(ValueError,'must not observe any stack'):owner.verify(**f)

    def test_byte_read_of_initialized_scalar(self):
        f,_=fixture(root=ROOT.replace('read_scalar: ldrsh r0,[r1,r3]','read_scalar: ldrb r0,[r1,r3]'))
        m,_=owner.verify(**f)
        self.assertEqual(sum(x[1]=='read' and x[3]==1 for x in m['proof']['finite_local_words']['accesses']),3)

    def test_manifest_cannot_erase_spill_effects(self):
        f,_=fixture();m,_=owner.verify(**f);m['proof']['call_effects']['readonly_leaves']=[]
        with self.assertRaisesRegex(ValueError,'manifest differs'):owner.verify(**f,manifest=m)

    def test_original_binding_identity_is_required(self):
        f,_=fixture();f['bindings']['calls'][0][1]='func_08013000'
        with self.assertRaisesRegex(ValueError,'call identities'):owner.verify(**f)

    def test_prior_word_only_selector_stays_strict(self):
        f,_=fixture();f['selector']=prior.SELECTOR
        with self.assertRaisesRegex(ValueError,'stored private pointers'):owner.verify(**f)

    def test_report_selector_stays_distinct(self):
        self.assertEqual(owner.selector_for_report(f'* verification: `{policy.SCHEMA}`\n* owner runtime: {policy.SELECTOR}'),policy.SELECTOR)

    def test_shift32_known_constant_is_supported(self):
        f,_=fixture(root=ROOT.replace('asrs r0,r0,#1','asrs r0,r0,#32'))
        m,_=owner.verify(**f);self.assertTrue(m['proof']['finite_local_words']['complete'])

    def test_strict_callee_uses_only_its_own_allocated_word(self):
        body=ORDINARY.replace('push {lr}\npop {r0}',
            'push {lr}\nsub sp,#4\nstr r0,[sp]\nldr r0,[sp]\nadd sp,#4\npop {r0}')
        f,_=fixture(ordinary=body);m,_=owner.verify(**f)
        frames=m['proof']['call_effects']['ordinary_private_frames']
        self.assertEqual(len(frames),1)
        self.assertTrue(frames[0]['frame'])
        self.assertTrue(frames[0]['nested_calls_remain_conditional'])

    def test_high_register_save_and_conditional_external_byte_read(self):
        source=ROOT.replace('sub sp,#24','mov r6,r8\npush {r6}\nsub sp,#24\nldrb r0,[r0]')
        source=source.replace('add sp,#24','add sp,#24\npop {r3}\nmov r8,r3')
        f,_=fixture(root=source);m,_=owner.verify(**f)
        p=m['proof']['finite_local_words']
        self.assertEqual(p['frame_bytes'],44)
        self.assertTrue(any(x[1:] == ['conditional-external-read',None,1] for x in p['accesses']))

    def test_native_cli_exposes_the_distinct_selector(self):
        result=subprocess.run([sys.executable,'-B',str(Path(owner.__file__).with_name('match.py')),'--help'],
                              check=True,text=True,capture_output=True)
        self.assertIn(policy.SELECTOR,result.stdout)

if __name__=='__main__':unittest.main()
