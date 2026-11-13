"""Narrow switch/fill composition and retained local-alias regression checks."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import local_long_branch_profile as frame
import bios_word_switch_buffer_profile as profile
import bios_cpuset_fill_profile as bios
import named_data_buffer_profile as named
A,B,C = 0x08010000,0x08020000,0x08020100


def fixture(*, control=0x01000008, source_offset=2, query=(0x2101,0x2000,0x4770), helper=None,
            restore=3, direction=False, table_target=None, bound=1, after_query=(), repeat_fill=1, saved_control=False, untracked_bios=False):
    body=bytearray(); labels={}; fix=[]; loads=[]; sites={}
    def emit(v): body.extend(struct.pack('<H',v))
    def label(n): labels[n]=len(body)
    def branch(op,n): fix.append((len(body),op,n));emit(0)
    def load(reg,n): loads.append((len(body),reg,n));emit(0)
    def call(target,n): sites[n]=len(body);body.extend(bl(A+len(body),target))
    for v in (0xB530,0xB083):emit(v)
    load(1,'state');emit(0x7808);emit(0x2800|bound);branch(0xD800,'default')
    emit(0x0080);load(1,'table_pointer')
    for v in (0x1840,0x6800,0x4687):emit(v)
    if len(body)%4:emit(0)
    label('state');body.extend(struct.pack('<I',0x02000020))
    label('table_pointer');body.extend(bytes(12))
    label('case0')
    for v in (0x4668,0x4669,0x3101):emit(v)
    call(B,'output');call(C,'query')
    for v in after_query:emit(v)
    if saved_control:load(5,'control')
    for number in range(repeat_fill):
        emit(0x4668);emit(0x3000|source_offset);emit(0x2400);emit(0x8004)
        load(1,'destination')
        if saved_control:emit(0x1C2A)
        else:load(2,'control')
        if direction:emit(0x4669)
        call(bios.ADDRESS,'bios'+str(number))
    emit(0x2000);branch(0xE000,'finish')
    label('case1');emit(0x2001)
    if untracked_bios:
        load(1,'destination');load(2,'control');call(bios.ADDRESS,'bios_external')
    branch(0xE000,'finish')
    label('default');emit(0x2002)
    label('finish')
    for v in (0xB000|restore,0xBC30,0xBC02,0x4708):emit(v)
    if len(body)%4:emit(0)
    label('destination');body.extend(struct.pack('<I',0x06000000))
    label('control');body.extend(struct.pack('<I',control))
    for off,op,name in fix:
        struct.pack_into('<H',body,off,op|(((labels[name]-off-4)//2)&(0x7ff if op==0xE000 else 255)))
    for off,reg,name in loads:
        struct.pack_into('<H',body,off,0x4800|(reg<<8)|((labels[name]-((off+4)&~3))//4))
    table=labels['table_pointer'];words={table:table+4,table+4:labels['case0'] if table_target is None else table_target,table+8:labels['case1']}
    for off,target in words.items():struct.pack_into('<I',body,off,A+target)
    helper=bytes.fromhex('024b1a780270587808707047')+struct.pack('<I',0x02000020) if helper is None else helper
    query=struct.pack('<'+'H'*len(query),*query)
    entries=((A,bytes(body)),(B,helper),(C,query),(bios.ADDRESS,bios.WRAPPER))
    rows=[dict(rom=hex(a),end=hex(a+len(data)),mode='thumb',instrs=0)for a,data in entries]
    mapping=json.dumps(rows).encode()
    for row,(a,data) in zip(rows,entries):
        if a!=bios.ADDRESS:
            row['instrs']=(profile.refine if a==A else owner.refine)(data,a,mapping)['instrs']
        else:row['instrs']=2
    mapping=json.dumps(rows).encode()
    index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'for r in rows).encode()
    rom=bytearray(bios.ADDRESS-match.ROM_BASE+4)
    for a,data in entries:rom[a-match.ROM_BASE:a-match.ROM_BASE+len(data)]=data
    bindings=dict(calls=sorted([[site,f'func_{B if n=="output" else C if n=="query" else bios.ADDRESS:08X}']for n,site in sites.items()]),
        data=[[labels['state'],'state',0],[labels['destination'],'destination',0]],functions=[],switches=[list(r)for r in words.items()])
    return dict(data=bytes(body),address=A,rom=bytes(rom),mapping=mapping,index=index,
        objects=b'{"state":"0x02000020","destination":"0x06000000"}',bindings=bindings,selector=profile.SELECTOR)


def bl(site,target):
    d=target-site-4
    return struct.pack('<HH',0xF000|((d>>12)&0x7ff),0xF800|((d>>1)&0x7ff))


class BiosWordSwitchTests(unittest.TestCase):
    def test_native_alias_return_survives_until_authenticated_query_kill(self):
        f=fixture();manifest,ins=owner.verify(**f)
        self.assertEqual(manifest['profile'],profile.SCHEMA)
        self.assertEqual(manifest['proof']['frame']['returned_local_alias_policy'],profile.RETURN_POLICY)
        root=manifest['proof']['buffers']['root_guarded_switch']
        self.assertEqual(root['returned_local_aliases'],[[A+f['bindings']['calls'][0][0],B,1,-23]])
        self.assertEqual(root['bios_fill']['sites'][0][2],2)
        self.assertEqual({row['address']for row in manifest['proof']['buffers']['dependencies']},{B,C,bios.ADDRESS})
        self.assertEqual(owner.preflight(*(f[k]for k in ('data','address','rom','mapping','index','objects')),selector=profile.SELECTOR)[0],manifest)

    def test_pointer_cannot_be_discarded_by_ordinary_next_call(self):
        # A preserved R1 must remain tainted until overwritten, including across BL.
        with self.assertRaises(ValueError):
            owner.verify(**fixture(query=(0x2000,0x4770),after_query=(0x6001,)))
        # Actual native overwrite by the helper makes this later store scalar.
        owner.verify(**fixture(after_query=(0x6001,)))
        for query in ((0x6001,0x2100,0x4770), (0x310C,0x7808,0x2100,0x4770), (0x0049,0x4770)):
            with self.subTest(query=query),self.assertRaises(ValueError):owner.verify(**fixture(query=query))

    def test_bios_mode_count_alignment_direction_and_wrapper(self):
        for control,width,offset in ((0x01000000,2,2),(0x01000008,2,2),(0x05000008,4,4)):
            m,_=owner.verify(**fixture(control=control,source_offset=offset))
            self.assertEqual(m['proof']['buffers']['root_guarded_switch']['bios_fill']['sites'][0][2],width)
        for changes in (dict(control=8),dict(control=0x04000008),dict(source_offset=1),
                        dict(control=0x05000008),dict(source_offset=12),dict(direction=True)):
            with self.subTest(changes=changes),self.assertRaises(ValueError):owner.verify(**fixture(**changes))
        f=fixture();rom=bytearray(f['rom']);rom[-4:]=bytes.fromhex('0cdf7047')
        with self.assertRaises(ValueError):owner.verify(**dict(f,rom=bytes(rom)))

    def test_all_bios_sites_require_fill_proof_and_saved_control_is_retained(self):
        m,_=owner.verify(**fixture(repeat_fill=4,saved_control=True))
        self.assertEqual(len(m['proof']['buffers']['root_guarded_switch']['bios_fill']['sites']),4)
        with self.assertRaisesRegex(ValueError,'every CpuSet site'):
            owner.verify(**fixture(untracked_bios=True))

    def test_dangling_alias_push_and_out_of_range_returns_fail(self):
        for changes in (dict(after_query=(0xB003,0x7808)),dict(after_query=(0xB402,)),
                        dict(query=(0x310C,0x4770)),dict(query=(0x1C0B,0x2100,0x2000,0x4770))):
            with self.subTest(changes=changes),self.assertRaises(ValueError):
                owner.verify(**fixture(query=(0x2000,0x4770),**changes) if 'query' not in changes else fixture(**changes))

    def test_switch_bounds_targets_frame_and_old_policies(self):
        for changes in (dict(table_target=0),dict(table_target=0x1000),dict(bound=2),dict(restore=2)):
            with self.subTest(changes=changes),self.assertRaises(ValueError):owner.verify(**fixture(**changes))
        f=fixture()
        for selector in (named.ROOT_SWITCH_SELECTOR,named.BIOS_FILL_SELECTOR,named.SELECTOR,owner.ACYCLIC_SELECTOR):
            with self.subTest(selector=selector),self.assertRaises(ValueError):owner.verify(**dict(f,selector=selector))

    def test_report_and_manifest_replay_are_exact(self):
        f=fixture();m,_=owner.verify(**f)
        altered=copy.deepcopy(m)
        altered['proof']['buffers']['root_guarded_switch']['returned_local_aliases'][0][3]=-1
        with self.assertRaises(ValueError):owner.verify(**f,manifest=altered)
        for role in ('calls','switches','data'):
            changed=copy.deepcopy(f);changed['bindings'][role]=[]
            with self.subTest(role=role),self.assertRaises(ValueError):owner.verify(**changed)
        report=f'* verification: `{profile.SCHEMA}`\n'
        self.assertTrue(owner.selected(report));self.assertEqual(owner.selector_for_report(report),profile.SELECTOR)

    def test_return_policy_requires_exact_fresh_class_and_bound_root(self):
        f=fixture();ref=profile.refine(f['data'],A,f['mapping'])
        ins,edges,branches,calls,words=graph.graph(f['data'],A,ref,one_object_word_switch=True)
        args=[f[k]for k in ('rom','mapping','index','objects')]
        proof=profile.BiosWordSwitchBufferProof(*args)
        with self.assertRaises(ValueError):frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,buffer_proof=proof,returned_local_alias_policy=profile.RETURN_POLICY)
        proof.bind_root(f['data'],A,calls,words)
        with self.assertRaises(ValueError):frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,buffer_proof=proof)
        class Forged(profile.BiosWordSwitchBufferProof):
            def check_call(self,*args,**kwargs):return {match.ARM_REG_R0:-1}
        forged=Forged(*args);forged.bind_root(f['data'],A,calls,words)
        with self.assertRaises(ValueError):frame.prove_frame(ins,edges,A,branches,calls,stack_aliases=True,buffer_proof=forged,returned_local_alias_policy=profile.RETURN_POLICY)
        wrong=dict(calls);wrong[A+f['bindings']['calls'][1][0]]=B
        with self.assertRaises(ValueError):frame.prove_frame(ins,edges,A,branches,wrong,stack_aliases=True,buffer_proof=proof,returned_local_alias_policy=profile.RETURN_POLICY)

if __name__=='__main__':unittest.main(verbosity=2)
