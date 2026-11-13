"""Compiler-backed entry-kill composition and exact hostile boundaries."""
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
import scheduler_killed_alias_profile as killed

H = 0x08024100
LOCAL = (False, False, True)


@unittest.skipUnless(os.environ.get('FFTA_SCHEDULER_KILLED_ALIAS_EVIDENCE'),
                     'private genuine compiler fixture not configured')
class SchedulerKilledAliasTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.e = Path(os.environ['FFTA_SCHEDULER_KILLED_ALIAS_EVIDENCE'])
        spec = importlib.util.spec_from_file_location('kill_fixture', cls.e/'native_fixture.py')
        cls.f = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.f)
        cls.root = cls.e/'synthetic-game'
        cls.rom = (cls.root/'baserom.bin').read_bytes()
        cls.mapping = (cls.root/'config/functions.json').read_bytes()
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()
        cls.objects = (cls.root/'config/data_symbols.json').read_bytes()
        cls.calls = dict(json.loads((cls.root/'fixture.json').read_text())['calls'])
        cls.site = next(s for s,t in cls.calls.items() if t == H)
        row = next(r for r in json.loads(cls.mapping) if int(r['rom'],16) == cls.f.A)
        cls.body = cls.rom[cls.f.A-match.ROM_BASE:int(row['end'],16)-match.ROM_BASE]

    def proof(self, policy=local.SCHEDULER_KILLED_ALIAS, *, rom=None, mapping=None, index=None):
        p = local.ConditionalLocalBufferProof(self.rom if rom is None else rom,
            self.mapping if mapping is None else mapping,
            self.index if index is None else index, self.objects, policy=policy)
        p.bind_root(self.body, self.f.A, self.calls)
        return p

    def test_native_composition_records_exact_prefix_and_preserves_premises(self):
        p = self.proof()
        match.verify_leaf_instructions(self.body,self.f.A,True,self.calls,buffer_proof=p)
        manifest = p.contract_manifest()
        self.assertEqual(len(manifest['observations']),len(self.calls))
        observation = next(o for o in manifest['observations'] if o['target'] == H)
        self.assertEqual(observation['kind'],'complete-ordinary-entry-alias-overwrite')
        self.assertEqual(observation['incoming_registers'],[match.ARM_REG_R1])
        self.assertEqual(observation['prefix'][-1]['killed'],[match.ARM_REG_R1])
        self.assertEqual(observation['prefix'][-1]['remaining'],[])
        self.assertTrue(observation['nested_calls'])
        self.assertFalse(observation['nested_execution_proved'])
        self.assertFalse(manifest['actual_callback_effects_proved'])
        self.assertFalse(manifest['nonescape_proved'])
        self.assertFalse(manifest['termination_proved'])
        self.assertEqual(manifest['branch_calls']['maximum_scheduler_calls_per_path'],3)
        self.assertIn('R9', ' '.join(manifest['assumptions']))
        self.assertEqual(p.dependency_budget,36)
        (self.e/'native-composition.json').write_text(json.dumps(manifest,indent=2)+'\n')

    def test_old_leaf_and_sequential_profiles_refuse_new_composition(self):
        for policy in (local.SCHEDULER_LEAF_OUTPUT,local.SCHEDULER_SEQUENTIAL):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                match.verify_leaf_instructions(self.body,self.f.A,True,self.calls,
                    buffer_proof=self.proof(policy))

    def test_each_incoming_alias_must_die(self):
        with self.assertRaises(ValueError):
            self.proof().check_call(H,{match.ARM_REG_R1:-16,match.ARM_REG_R12:-16},
                [LOCAL]*4,site=self.site)

    def test_exact_call_site_pointer_slots_preserved_aliases_and_words_refused(self):
        for target,site,aliases,slots,words in (
                (H,self.site+2,{match.ARM_REG_R1:-16},{},None),
                (H+2,self.site,{match.ARM_REG_R1:-16},{},None),
                (H,self.site,{match.ARM_REG_R1:-16},{-16:-12},None),
                (H,self.site,{match.ARM_REG_R1:-16,(match.ARM_REG_R0+4):-16},{},None),
                (H,self.site,{match.ARM_REG_R1:-16},{},{-16:'opaque'})):
            with self.subTest(target=target,site=site,aliases=aliases,slots=slots),self.assertRaises(ValueError):
                self.proof().check_call(target,aliases,[LOCAL]*4,slots,site=site,words=words)

    def test_no_saved_or_outside_frame_pointer_admission(self):
        for offset,stack in ((4,[LOCAL]*4),(-20,[LOCAL]*4),(-16,[(False,True,False)]*4)):
            with self.subTest(offset=offset),self.assertRaises(ValueError):
                self.proof().check_call(H,{match.ARM_REG_R1:offset},stack,site=self.site)

    def test_cross_path_observation_must_be_identical(self):
        for first,second in (({}, {match.ARM_REG_R1:-16}),({match.ARM_REG_R1:-16},{})):
            p=self.proof();p.check_call(H,first,[LOCAL]*4,site=self.site)
            with self.assertRaisesRegex(ValueError,'incoming call paths'):
                p.check_call(H,second,[LOCAL]*4,site=self.site)

    def test_compiler_read_escape_conditional_and_surviving_alias_refused(self):
        refusals=[]
        for variant in ('read','escape','conditional','survives'):
            root,body,calls=self.f.prepare('hostile-'+variant,nested_variant=variant)
            with self.subTest(variant=variant),self.assertRaises(ValueError) as caught:
                p=self.f.proof(root,body,calls)
                match.verify_leaf_instructions(body,self.f.A,True,calls,buffer_proof=p)
            refusals.append(dict(variant=variant,error=str(caught.exception)))
        (self.e/'compiler-hostile-refusals.json').write_text(json.dumps(refusals,indent=2)+'\n')

    def test_prefix_raw_effects_ip_read_copy_partial_and_branch_refused(self):
        from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
        decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
        for raw,aliases in ((bytes.fromhex('6046'),{match.ARM_REG_R12:-16}),
                (bytes.fromhex('0191'),{match.ARM_REG_R1:-16}),
                (bytes.fromhex('0940'),{match.ARM_REG_R1:-16}),
                (bytes.fromhex('00d0'),{match.ARM_REG_R1:-16})):
            instructions={i.address:i for i in decoder.disasm(raw,0x08030000)}
            edges={0x08030000:(0x08030002,)}
            with self.subTest(raw=raw.hex()),self.assertRaises(ValueError):
                killed.overwrite(instructions,edges,0x08030000,aliases)

    def test_exact_ip_full_overwrite_supported(self):
        from capstone import Cs,CS_ARCH_ARM,CS_MODE_THUMB
        decoder=Cs(CS_ARCH_ARM,CS_MODE_THUMB);decoder.detail=True
        instructions={i.address:i for i in decoder.disasm(bytes.fromhex('a446'),0x08030000)}
        prefix=killed.overwrite(instructions,{0x08030000:(0x08030002,)},0x08030000,
            {match.ARM_REG_R12:-16})
        self.assertEqual(prefix[0]['killed'],[match.ARM_REG_R12])

    def test_complete_helper_dual_index_mode_and_overlap_binding(self):
        rows=json.loads(self.mapping)
        for kind in ('missing','mode','overlap'):
            changed=copy.deepcopy(rows);row=next(r for r in changed if int(r['rom'],16)==H)
            if kind=='missing':changed.remove(row)
            elif kind=='mode':row['mode']='arm'
            else:changed.append(dict(row))
            with self.subTest(kind=kind),self.assertRaises(ValueError):
                self.proof(mapping=json.dumps(changed).encode())
        changed=b'\n'.join(line for line in self.index.splitlines() if not line.startswith(b'08024100'))+b'\n'
        with self.assertRaises(ValueError):self.proof(index=changed)

    def test_corrupted_helper_kill_refused_through_native_api(self):
        # Replace the full immediate overwrite with a copy of the live alias.
        changed=bytearray(self.rom)
        changed[H-match.ROM_BASE+4:H-match.ROM_BASE+6]=bytes.fromhex('0846')
        p=self.proof(rom=bytes(changed))
        with self.assertRaisesRegex(ValueError,'live incoming alias'):
            match.verify_leaf_instructions(self.body,self.f.A,True,self.calls,buffer_proof=p)

    def test_root_wrong_return_provenance_refused(self):
        changed=self.body[:-2]+bytes.fromhex('0847')
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(changed,self.f.A,True,self.calls,buffer_proof=self.proof())

    def test_missing_observation_refused(self):
        with self.assertRaisesRegex(ValueError,'every conditional'):
            self.proof().contract_manifest()

    def test_native_api_cli_source_report_and_stale_proofs(self):
        os.environ['FFTA_ROM']=str(self.root/'baserom.bin')
        result=owner.build(self.root,self.f.A,selector=local.SCHEDULER_KILLED_ALIAS)
        report=owner.render(self.f.A,result)
        self.assertTrue(owner.report_matches(report,self.root,self.f.A))
        (self.e/'native-report.md').write_text(report)
        (self.e/'native-manifest.json').write_text(json.dumps(result[1],indent=2)+'\n')
        run=subprocess.run([sys.executable,'-B',str(Path(match.__file__)),'--root',str(self.root),
            '--owner-runtime-profile',local.SCHEDULER_KILLED_ALIAS,'--no-write','08010000'],
            capture_output=True,text=True)
        (self.e/'native-cli.log').write_text(run.stdout+run.stderr)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertIn('MATCH',run.stdout)
        for key in ('source_sha256','helper','prefix','incoming_registers','aliases','nested_calls'):
            bad=copy.deepcopy(result[1]);observation=next(o for o in
                bad['proof']['buffers']['conditional_local_calls']['observations'] if o['target']==H)
            observation[key]='forged'
            with self.subTest(key=key),self.assertRaises(ValueError):
                owner.build(self.root,self.f.A,selector=local.SCHEDULER_KILLED_ALIAS,expected=bad)
        for name in ('src/08010000.c','config/functions.json','symbols/functions.txt','config/data_symbols.json','baserom.bin'):
            path=self.root/name;old=path.read_bytes();changed=bytearray(old)
            if name=='baserom.bin':changed[H-match.ROM_BASE+4]^=1
            else:changed+=b'\n'
            path.write_bytes(changed)
            try:self.assertFalse(owner.report_matches(report,self.root,self.f.A),name)
            finally:path.write_bytes(old)


if __name__ == '__main__':unittest.main()
