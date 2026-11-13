"""Complete compiler leaf-output composition and hostile boundary checks."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import conditional_local_buffer_profile as local
import match
import owner_admission_profile as owner

SELECTOR = local.SCHEDULER_LEAF_OUTPUT
H = 0x08024000
LOCAL, SAVED = (False, False, True), (False, True, False)


@unittest.skipUnless(os.environ.get('FFTA_SCHEDULER_LEAF_OUTPUT_EVIDENCE'),
                     'private genuine compiler fixture not configured')
class SchedulerLeafOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.e = Path(os.environ['FFTA_SCHEDULER_LEAF_OUTPUT_EVIDENCE'])
        spec = importlib.util.spec_from_file_location('leaf_output_fixture', cls.e/'native_fixture.py')
        cls.f = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.f)
        cls.root = cls.e/'synthetic-game'
        cls.rom = (cls.root/'baserom.bin').read_bytes()
        cls.mapping = (cls.root/'config/functions.json').read_bytes()
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()
        cls.objects = (cls.root/'config/data_symbols.json').read_bytes()
        cls.a = cls.f.A
        row = next(r for r in json.loads(cls.mapping) if int(r['rom'],16)==cls.a)
        cls.body = cls.rom[cls.a-match.ROM_BASE:int(row['end'],16)-match.ROM_BASE]
        cls.calls = dict(json.loads((cls.root/'fixture.json').read_text())['calls'])
        cls.site = next(s for s,t in cls.calls.items() if t==H)

    def proof(self, *, mapping=None, index=None, rom=None, policy=SELECTOR):
        p=local.ConditionalLocalBufferProof(self.rom if rom is None else rom,
            self.mapping if mapping is None else mapping,
            self.index if index is None else index, self.objects, policy=policy)
        p.bind_root(self.body,self.a,self.calls)
        return p

    def replay(self, p=None):
        p=p or self.proof()
        match.verify_leaf_instructions(self.body,self.a,True,self.calls,buffer_proof=p)
        return p.contract_manifest()

    def test_complete_leaf_and_each_scheduler_observed(self):
        p=self.proof();manifest=self.replay(p)
        self.assertEqual(len(manifest['observations']),len(self.calls))
        obs=next(o for o in manifest['observations'] if o['target']==H)
        self.assertEqual(obs['kind'],'complete-leaf-buffer-alias-replay')
        self.assertEqual(obs['returned_aliases'],[])
        self.assertEqual(obs['helper']['body_sha256'],p.records[H]['body_sha256'])
        self.assertEqual(p.dependency_budget,36)
        self.assertEqual(manifest['branch_calls']['maximum_scheduler_calls_per_path'],3)
        for field in ('actual_callback_effects_proved','nonescape_proved','termination_proved'):
            self.assertFalse(manifest[field])

    def test_old_selectors_still_refuse(self):
        for policy in (local.SCHEDULER_SEQUENTIAL, local.SCHEDULER_24_FOLLOWING):
            with self.subTest(policy=policy),self.assertRaises(ValueError):
                self.replay(self.proof(policy=policy))

    def test_missing_or_wrong_actual_call_site_refused(self):
        for target,site in ((H,self.site+2),(H+2,self.site)):
            with self.subTest(target=target,site=site),self.assertRaises(ValueError):
                self.proof().check_call(target,{match.ARM_REG_R0:-16},[LOCAL]*4,site=site)

    def test_pointer_slots_and_opaque_words_refused(self):
        for slots,words in (({-16:-12},None),({}, {-16:'opaque'})):
            with self.subTest(slots=slots,words=words),self.assertRaises(ValueError):
                self.proof().check_call(H,{match.ARM_REG_R0:-16},[LOCAL]*4,slots,site=self.site,words=words)

    def test_preserved_register_aliases_and_lr_refused(self):
        for register in (match.ARM_REG_R0+4,match.ARM_REG_LR):
            with self.subTest(register=register),self.assertRaises(ValueError):
                self.proof().check_call(H,{match.ARM_REG_R0:-16,register:-16},[LOCAL]*4,site=self.site)

    def test_alignment_saved_word_and_frame_bounds_refused(self):
        for offset,stack in ((-15,[LOCAL]*4),(-8,[LOCAL]*4),(-16,[LOCAL]*2+[SAVED]*2)):
            with self.subTest(offset=offset,stack=stack),self.assertRaises(ValueError):
                self.proof().check_call(H,{match.ARM_REG_R0:offset},stack,site=self.site)

    def test_inconsistent_observations_refuse_both_orderings(self):
        for first,second in (({}, {match.ARM_REG_R0:-16}),({match.ARM_REG_R0:-16},{})):
            p=self.proof();p.check_call(H,first,[LOCAL]*4,site=self.site)
            with self.assertRaisesRegex(ValueError,'incoming call paths'):
                p.check_call(H,second,[LOCAL]*4,site=self.site)

    def test_changed_complete_helper_identity_is_bound(self):
        changed=bytearray(self.rom);changed[H-match.ROM_BASE+2]^=1
        q=self.proof(rom=bytes(changed))
        self.assertNotEqual(q.records[H]['body_sha256'],self.proof().records[H]['body_sha256'])

    def test_helper_missing_index_overlap_and_mode_refused(self):
        rows=json.loads(self.mapping)
        for kind in ('missing','overlap','mode'):
            altered=copy.deepcopy(rows)
            row=next(r for r in altered if int(r['rom'],16)==H)
            if kind=='missing':altered.remove(row)
            elif kind=='overlap':altered.append(dict(row))
            else:row['mode']='arm'
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                self.proof(mapping=json.dumps(altered).encode())
        index=b'\n'.join(line for line in self.index.splitlines() if not line.startswith(b'08024000'))+b'\n'
        with self.assertRaises(ValueError):self.proof(index=index)

    def test_genuine_compiler_hostile_helpers_refused(self):
        refusals=[]
        for variant in ('bounds','return','escape','nested'):
            root,body,calls=self.f.prepare('hostile-'+variant,helper_variant=variant)
            with self.subTest(variant=variant),self.assertRaises(ValueError) as caught:
                p=self.f.proof(root,body,calls)
                match.verify_leaf_instructions(body,self.a,True,calls,buffer_proof=p)
            refusals.append(dict(variant=variant,error=str(caught.exception)))
        (self.e/'compiler-hostile-refusals.json').write_text(json.dumps(refusals,indent=2)+'\n')

    def test_native_cli_report_replay_and_stale_evidence(self):
        os.environ['FFTA_ROM']=str(self.root/'baserom.bin')
        result=owner.build(self.root,self.a,selector=SELECTOR)
        report=owner.render(self.a,result)
        self.assertTrue(owner.report_matches(report,self.root,self.a))
        (self.e/'native-report.md').write_text(report)
        (self.e/'native-manifest.json').write_text(json.dumps(result[1],indent=2)+'\n')
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--root',str(self.root),
            '--owner-runtime-profile',SELECTOR,'--no-write','08010000'],capture_output=True,text=True)
        (self.e/'native-cli.log').write_text(run.stdout+run.stderr)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertIn('MATCH',run.stdout)
        for key in ('source_sha256','helper','aliases'):
            bad=copy.deepcopy(result[1]);obs=next(o for o in bad['proof']['buffers']['conditional_local_calls']['observations'] if o['target']==H)
            obs[key]='forged'
            with self.subTest(key=key),self.assertRaises(ValueError):
                owner.build(self.root,self.a,selector=SELECTOR,expected=bad)
        for name in ('src/08010000.c','config/functions.json','symbols/functions.txt','config/data_symbols.json','baserom.bin'):
            path=self.root/name;old=path.read_bytes();changed=bytearray(old)
            if name=='baserom.bin':changed[H-match.ROM_BASE]^=1
            else:changed+=b'\n'
            path.write_bytes(changed)
            try:self.assertFalse(owner.report_matches(report,self.root,self.a),name)
            finally:path.write_bytes(old)


if __name__=='__main__':unittest.main()
