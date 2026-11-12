"""Three-per-path selection preserves per-call frame and identity obligations.

Full compiler fixtures are supplied by the private evidence driver through
FFTA_SCHEDULER_SEQUENTIAL_EVIDENCE. No original caller or fabricated assembly
is used. Pure DAG tests run without private data.
"""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import owner_admission_profile as owner
import scheduler_branch_profile as branch

SELECTOR = 'conditional-scheduler-three-per-path-calls-v1'
S = branch.SCHEDULER
B = 0x08020000
LOCAL, SAVED = (False, False, True), (False, True, False)


def phases(edges, calls, **flags):
    return branch.phases(edges, calls, three_per_path_calls=True, **flags)


def sequence(targets):
    edges = {i:(i+1,) for i in range(len(targets)-1)}
    edges[len(targets)-1] = ()
    return edges, dict(enumerate(targets))


class SequentialDAGTests(unittest.TestCase):
    def test_longest_path_survives_union_join_and_counts_each_invocation(self):
        edges={0:(1,4),1:(2,),2:(3,),3:(5,),4:(5,),5:(6,),6:(7,),7:()}
        calls={0:B,1:S,2:S,5:S,7:B}
        result=phases(edges,calls)
        self.assertEqual(result['maximum_scheduler_calls_per_path'],3)
        self.assertEqual(result['following_ordinary_sites'],[7])
        # A fourth scheduler after the join must fail even though the short
        # arm reaches it with only two calls. Reverse successor order as well.
        calls[6]=S
        for successors in ((1,4),(4,1)):
            with self.subTest(successors=successors),self.assertRaisesRegex(ValueError,'per-path'):
                phases({**edges,0:successors},calls)

    def test_four_static_sites_on_three_call_paths(self):
        result=phases({0:(1,),1:(2,3),2:(4,),3:(4,),4:(5,),5:()},
                      {0:B,1:S,2:S,3:S,4:S,5:B})
        self.assertEqual(len(result['scheduler_sites']),4)
        self.assertEqual(result['maximum_scheduler_calls_per_path'],3)
        self.assertEqual(result['scheduler_site_budget'],4)
        self.assertEqual(result['scheduler_calls_per_path_budget'],3)

    def test_target_and_call_budgets_are_separate(self):
        edges,calls=sequence([B+32*i for i in range(32)]+[S]+[B]*7)
        r=phases(edges,calls)
        self.assertEqual(r['ordinary_target_budget'],32)
        self.assertEqual(r['call_site_budget'],40)
        for targets in ([B+32*i for i in range(33)]+[S], [B]*40+[S]):
            with self.subTest(sites=len(targets)),self.assertRaisesRegex(ValueError,'bounds'):
                phases(*sequence(targets))

    def test_fifth_static_scheduler_site_refused(self):
        edges={0:(1,2,3,4,5),1:(6,),2:(6,),3:(6,),4:(6,),5:(6,),6:()}
        with self.assertRaisesRegex(ValueError,'bounds'):
            phases(edges,{0:B,1:S,2:S,3:S,4:S,5:S})

    def test_cycles_unknown_edges_and_unknown_call_sites_refused(self):
        for edges,calls in (({0:(1,),1:(0,)},{0:S,1:B}),
                            ({0:(1,),1:(2,)},{0:S,1:B}),
                            ({0:(1,),1:()},{0:S,2:B})):
            with self.subTest(edges=edges),self.assertRaises(ValueError):phases(edges,calls)

    def test_new_flag_is_boolean_and_exclusive_with_each_old_flag(self):
        edges,calls=sequence([B,S,B])
        for value in (None,0,1,'yes'):
            with self.subTest(value=value),self.assertRaises(ValueError):
                branch.phases(edges,calls,three_per_path_calls=value)
        for flag in ('following_calls','wide_targets','twenty_four_targets','twenty_four_following_calls'):
            with self.subTest(flag=flag),self.assertRaises(ValueError):phases(edges,calls,**{flag:True})

    def test_previous_flag_combinations_and_selector_limits_stay_closed(self):
        edges,calls=sequence([B,S,B])
        flags=('following_calls','wide_targets','twenty_four_targets','twenty_four_following_calls')
        for i,left in enumerate(flags):
            for right in flags[i+1:]:
                with self.subTest(left=left,right=right),self.assertRaises(ValueError):
                    branch.phases(edges,calls,**{left:True,right:True})
        for flag,budget in ((None,4),('following_calls',4),('wide_targets',8),
                            ('twenty_four_targets',24),('twenty_four_following_calls',24)):
            over=sequence([B+32*i for i in range(budget+1)]+[S,B])
            with self.subTest(flag=flag),self.assertRaises(ValueError):
                branch.phases(*over,**({flag:True} if flag else {}))

    def test_previous_manifests_keep_one_path_and_existing_shape(self):
        edges,calls=sequence([B,S,B])
        for flag in ('following_calls','twenty_four_following_calls'):
            result=branch.phases(edges,calls,**{flag:True})
            self.assertEqual(result['maximum_scheduler_calls_per_path'],1)
            self.assertNotIn('scheduler_calls_per_path_budget',result)
            self.assertEqual(result['following_ordinary_sites'],[2])
        for flag in (None,'wide_targets','twenty_four_targets'):
            with self.subTest(flag=flag),self.assertRaises(ValueError):
                branch.phases(edges,calls,**({flag:True} if flag else {}))


@unittest.skipUnless(os.environ.get('FFTA_SCHEDULER_SEQUENTIAL_EVIDENCE'),
                     'private synthetic compiler fixture not configured')
class SequentialNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.e=Path(os.environ['FFTA_SCHEDULER_SEQUENTIAL_EVIDENCE'])
        spec=importlib.util.spec_from_file_location('sequential_fixture',cls.e/'native_fixture.py')
        cls.fixture=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.fixture)
        cls.a=cls.fixture.A
        cls.root=cls.e/'prechange-fixture'
        cls.rom=(cls.root/'baserom.bin').read_bytes()
        cls.mapping=(cls.root/'config/functions.json').read_bytes()
        cls.index=(cls.root/'symbols/functions.txt').read_bytes()
        cls.objects=(cls.root/'config/data_symbols.json').read_bytes()
        cls.calls=dict(json.loads((cls.root/'fixture.json').read_text())['calls'])
        row=next(r for r in json.loads(cls.mapping) if int(r['rom'],16)==cls.a)
        cls.body=cls.rom[cls.a-match.ROM_BASE:int(row['end'],16)-match.ROM_BASE]

    def bound(self, body=None, calls=None, rom=None, mapping=None, index=None, policy=SELECTOR):
        p=local.ConditionalLocalBufferProof(self.rom if rom is None else rom,
            self.mapping if mapping is None else mapping,self.index if index is None else index,
            self.objects,policy=policy)
        p.bind_root(self.body if body is None else body,self.a,self.calls if calls is None else calls)
        return p

    def test_complete_four_sites_three_per_path_native_frame(self):
        p=self.bound()
        verified=match.verify_leaf_instructions(self.body,self.a,True,self.calls,buffer_proof=p)
        manifest=p.contract_manifest()
        self.assertEqual(len(manifest['observations']),8)
        self.assertEqual(manifest['branch_calls']['maximum_scheduler_calls_per_path'],3)
        self.assertEqual(len(manifest['branch_calls']['scheduler_sites']),4)
        self.assertEqual(p.dependency_budget,36)
        self.assertEqual(len(p.requested),8)
        self.assertEqual(len(verified),next(r['instrs'] for r in json.loads(self.mapping)
                         if int(r['rom'],16)==self.a))
        for field in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):
            self.assertFalse(manifest[field])
        assumptions=' '.join(manifest['assumptions'])
        self.assertIn('Every sequential scheduler invocation',assumptions)
        self.assertIn('copied R1',assumptions)
        self.assertIn('R9',assumptions)

    def test_each_ordinary_interface_before_between_and_after_retains_all_checks(self):
        ordinary=[s for s,t in self.calls.items() if t!=S]
        self.assertEqual(len(ordinary),4)
        for site in ordinary:
            for aliases,slots,words in (({match.ARM_REG_R0:-36},{},None),
                    ({match.ARM_REG_R0+4:-36},{},None),
                    ({},{-36:-32},None),({},{},{-36:'opaque'})):
                with self.subTest(site=site,aliases=aliases,slots=slots,words=words),self.assertRaises(ValueError):
                    self.bound().check_call(self.calls[site],aliases,[LOCAL]*7+[SAVED]*2,
                                           slots,site=site,words=words)

    def test_each_scheduler_requires_exact_descriptor_and_saved_word_safety(self):
        for site,target in self.calls.items():
            if target!=S:continue
            for aliases,slots in (({},{}),({match.ARM_REG_R0+2:-32},{}),
                    ({match.ARM_REG_R0+2:-36,match.ARM_REG_R0:-36},{}),
                    ({match.ARM_REG_R0+2:-36},{-36:-36})):
                with self.subTest(site=site,aliases=aliases),self.assertRaises(ValueError):
                    self.bound().check_call(S,aliases,[LOCAL]*7+[SAVED]*2,slots,site=site)

    def test_no_skipped_site_or_unknown_target_or_site(self):
        p=self.bound()
        with self.assertRaises(ValueError):p.contract_manifest()
        for target,site in ((B,self.a),(B+0x400,max(self.calls)),(S,min(self.calls))):
            with self.subTest(target=target,site=site),self.assertRaises(ValueError):
                p.check_call(target,{},[],site=site)
        changed=dict(self.calls);changed.pop(max(changed))
        with self.assertRaisesRegex(ValueError,'local BL and switches'):self.bound(calls=changed)

    def test_real_dependency_corruption_and_missing_body_refused(self):
        for target in (S,0x08005954,match.function_thunk.ALIASES['_call_via_r2'],
                       match.function_thunk.ALIASES['_call_via_r3']):
            changed=bytearray(self.rom);changed[target-match.ROM_BASE]^=1
            with self.subTest(target=target),self.assertRaises(ValueError):self.bound(rom=bytes(changed))
        rows=[r for r in json.loads(self.mapping) if int(r['rom'],16)!=B]
        with self.assertRaises(ValueError):self.bound(mapping=json.dumps(rows).encode())

    def test_default_and_old_selectors_still_refuse_sequential_fixture(self):
        for policy in (local.SCHEDULER,local.SCHEDULER_BRANCH,local.SCHEDULER_FOLLOWING,
                       local.SCHEDULER_WIDE,local.SCHEDULER_24,local.SCHEDULER_24_FOLLOWING):
            with self.subTest(policy=policy),self.assertRaises(ValueError):self.bound(policy=policy)
        p=named.NamedDataBufferProof(self.rom,self.mapping,self.index,self.objects)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body,self.a,True,self.calls,buffer_proof=p)

    def test_runtime_and_thunk_ordinary_targets_cannot_bypass_identity(self):
        # Bind to an actual graph whose ordinary call entry is changed, so
        # this checks the ordinary dependency classification directly.
        for target in (next(iter(match.RUNTIME_HELPERS.values())),
                       match.function_thunk.ALIASES['_call_via_r2']):
            p=local.ConditionalLocalBufferProof(self.rom,self.mapping,self.index,self.objects,policy=SELECTOR)
            with self.subTest(target=target),self.assertRaisesRegex(ValueError,'ordinary indexed'):
                branch.bind(p,*sequence([target,S]),three_per_path_calls=True)

    def test_wrong_return_and_unbalanced_frame_binary_corruption_refused(self):
        # Corrupt compiler-produced return/frame halfwords, keeping the ROM,
        # complete symbol span and input identities consistent for frame replay.
        import capstone
        decoder=capstone.Cs(capstone.CS_ARCH_ARM,capstone.CS_MODE_THUMB)
        ins=list(decoder.disasm(self.body,self.a))
        bx=next(i for i in reversed(ins) if i.mnemonic=='bx')
        adjust=next(i for i in reversed(ins) if i.mnemonic=='add' and i.op_str.startswith('sp,'))
        for offset,raw in ((bx.address-self.a,bytes([bx.bytes[0]^8,bx.bytes[1]])),
                           (adjust.address-self.a,bytes([adjust.bytes[0]^1,adjust.bytes[1]]))):
            bad=self.body[:offset]+raw+self.body[offset+2:]
            rom=bytearray(self.rom);rom[self.a-match.ROM_BASE:self.a-match.ROM_BASE+len(bad)]=bad
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                p=self.bound(body=bad,rom=bytes(rom))
                match.verify_leaf_instructions(bad,self.a,True,self.calls,buffer_proof=p)

    def test_real_compiler_full_32_target_40_site_boundary(self):
        root,body,calls=self.fixture.prepare('budget-fixture','budget')
        p=self.fixture.proof(root,body,calls)
        match.verify_leaf_instructions(body,self.a,True,calls,buffer_proof=p)
        manifest=p.contract_manifest()
        self.assertEqual(len(calls),40)
        self.assertEqual(len(manifest['branch_calls']['ordinary_targets']),32)
        self.assertEqual(len(p.requested),36)
        self.assertEqual(set(p.records),set(calls.values())|{0x08005954})
        (self.e/'budget-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')

    def test_real_compiler_four_per_path_and_cycle_refused(self):
        for variant,error in (('four-on-path','per-path'),('cycle','cycles')):
            root,body,calls=self.fixture.prepare(variant+'-fixture',variant)
            with self.subTest(variant=variant),self.assertRaisesRegex(ValueError,error):
                self.fixture.proof(root,body,calls)

    def test_genuine_ELF_native_CLI_and_source_bound_report_replay(self):
        os.environ['FFTA_ROM']=str(self.root/'baserom.bin')
        result=owner.build(self.root,self.a,selector=SELECTOR)
        report=owner.render(self.a,result)
        (self.e/'native-report.md').write_text(report)
        (self.e/'native-manifest.json').write_text(json.dumps(result[1],indent=2)+'\n')
        self.assertTrue(owner.report_matches(report,self.root,self.a))
        self.assertEqual(owner.selector_for_report(report),SELECTOR)
        command=[sys.executable,'-B',str(Path(match.__file__)),'--root',str(self.root),
                 '--owner-runtime-profile',SELECTOR,'--no-write','08010000']
        run=subprocess.run(command,capture_output=True,text=True)
        (self.e/'native-cli.stdout').write_text(run.stdout)
        (self.e/'native-cli.stderr').write_text(run.stderr)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertIn('MATCH',run.stdout)
        manifest=copy.deepcopy(result[1])
        manifest['proof']['buffers']['conditional_local_calls']['branch_calls']['maximum_scheduler_calls_per_path']=2
        with self.assertRaises(ValueError):owner.build(self.root,self.a,expected=manifest,selector=SELECTOR)
        self.assertFalse(owner.report_matches(report.replace(SELECTOR,local.SCHEDULER_24_FOLLOWING),self.root,self.a))
        for name in ('src/08010000.c','config/functions.json','symbols/functions.txt',
                     'config/data_symbols.json','baserom.bin'):
            path=self.root/name;old=path.read_bytes()
            changed=bytearray(old)
            if name=='baserom.bin':changed[S-match.ROM_BASE]^=1
            else:changed+=b'\n'
            path.write_bytes(changed)
            try:
                self.assertFalse(owner.report_matches(report,self.root,self.a),name)
            finally:path.write_bytes(old)


@unittest.skipUnless(os.environ.get('FFTA_SCHEDULER_SEQUENTIAL_EVIDENCE'),
                     'private synthetic compiler fixture not configured')
class SequentialAdditionalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        SequentialNativeTests.setUpClass.__func__(cls)

    bound = SequentialNativeTests.bound
    def test_actual_compiler_pointer_escapes_before_between_after_refused(self):
        refusals=[]
        for variant in ('alias-before','alias-between','alias-after'):
            root,body,calls=self.fixture.prepare(variant+'-fixture',variant)
            p=self.fixture.proof(root,body,calls)
            with self.subTest(variant=variant),self.assertRaisesRegex(ValueError,'every live local alias') as caught:
                match.verify_leaf_instructions(body,self.a,True,calls,buffer_proof=p)
            refusals.append(dict(variant=variant,error=str(caught.exception)))
        (self.e/'compiler-alias-refusals.json').write_text(json.dumps(refusals,indent=2)+'\n')

    def test_each_scheduler_admits_and_records_preserved_descriptor_alias_under_same_premises(self):
        p=self.bound()
        stack=[LOCAL]*7+[SAVED]*2
        for site,target in p.calls.items():
            aliases={match.ARM_REG_R0+2:-36,match.ARM_REG_R0+4:-36} if target==S else {}
            p.check_call(target,aliases,stack,site=site)
        manifest=p.contract_manifest()
        observations=[o for o in manifest['observations'] if o['target']==S]
        self.assertEqual(len(observations),4)
        self.assertTrue(all([match.ARM_REG_R0+4,-36] in [list(a) for a in o['aliases']]
                            for o in observations))
        self.assertFalse(manifest['nonescape_proved'])

    def test_manifest_omitted_final_scheduler_and_path_conflict_refused(self):
        p=self.bound();stack=[LOCAL]*7+[SAVED]*2
        final_scheduler=max(s for s,t in self.calls.items() if t==S)
        for site,target in self.calls.items():
            if site==final_scheduler:continue
            p.check_call(target,{match.ARM_REG_R0+2:-36} if target==S else {},stack,site=site)
        with self.assertRaisesRegex(ValueError,'every conditional'):p.contract_manifest()
        site=min(s for s,t in self.calls.items() if t==S)
        with self.assertRaisesRegex(ValueError,'incoming paths'):
            p.check_call(S,{match.ARM_REG_R0+2:-36,match.ARM_REG_R0+4:-36},stack,site=site)

    def test_changed_ordinary_dependency_is_identified_and_stale_manifest_refused(self):
        p=self.bound()
        match.verify_leaf_instructions(self.body,self.a,True,self.calls,buffer_proof=p)
        original=p.records[B]['body_sha256']
        changed=bytearray(self.rom);changed[B-match.ROM_BASE]^=1
        q=self.bound(rom=bytes(changed))
        self.assertNotEqual(q.records[B]['body_sha256'],original)
        self.assertNotEqual(q.identities['rom_sha256'],p.identities['rom_sha256'])
        # Identity is recorded, not a purity or nested-effect theorem.
        self.assertFalse(q.records[B]['structure']['callee_effects_proved'])
        report=(self.e/'native-report.md').read_text()
        os.environ['FFTA_ROM']=str(self.root/'baserom.bin')
        path=self.root/'baserom.bin';old=path.read_bytes();path.write_bytes(changed)
        try:self.assertFalse(owner.report_matches(report,self.root,self.a))
        finally:path.write_bytes(old)

    def test_stale_producer_environment_and_descriptor_observation_refused(self):
        manifest=json.loads((self.e/'native-manifest.json').read_text())
        os.environ['FFTA_ROM']=str(self.root/'baserom.bin')
        for change in ('producer','descriptor','scheduler-budget'):
            bad=copy.deepcopy(manifest)
            contract=bad['proof']['buffers']['conditional_local_calls']
            if change=='producer':contract['environment']['sources']['scheduler_branch_profile.py']='0'*64
            elif change=='descriptor':
                next(o for o in contract['observations'] if o['target']==S)['bytes']=24
            else:contract['branch_calls']['scheduler_calls_per_path_budget']=4
            with self.subTest(change=change),self.assertRaises(ValueError):
                owner.build(self.root,self.a,expected=bad,selector=SELECTOR)

    def test_overlapping_ordinary_body_and_bad_instruction_mode_refused(self):
        rows=json.loads(self.mapping)
        for variant in ('overlap','mode','extent'):
            changed=copy.deepcopy(rows)
            row=next(r for r in changed if int(r['rom'],16)==B)
            if variant=='overlap':
                changed.append(dict(rom='0x%08X'%B,end='0x%08X'%(B+2),mode='thumb',instrs=1))
            elif variant=='mode':row['mode']='arm'
            else:row['end']='0x%08X'%(B+4)
            with self.subTest(variant=variant),self.assertRaises(ValueError):
                self.bound(mapping=json.dumps(changed).encode())


if __name__=='__main__':unittest.main()
