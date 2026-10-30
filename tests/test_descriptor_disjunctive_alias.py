"""Exact finite alternatives, complete native gates and fresh compiler evidence."""
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import descriptor_disjunctive_alias_profile as profile
import test_descriptor_output_alias as fixtures
from test_descriptor_output_alias import A,B,C,D

WORKER = '''struct Output { unsigned int *words; };
extern void func_08012000(struct Output *);
unsigned int func_08011000(unsigned char *marker)
{
    unsigned int words[3];
    struct Output output;
    words[0] = 1;
    words[1] = 3;
    words[2] = 5;
    output.words = words;
    if (marker[0])
        output.words = words + 1;
    func_08012000(&output);
    return (words[0] + marker[0]) * (words[1] + marker[0]) + words[2];
}
'''
LEAF = '''struct Output { unsigned int *words; };
void func_08012000(struct Output *output)
{
    unsigned int *cursor = output->words;
    if (cursor[0])
        cursor++;
    *cursor++ = 7;
    output->words = cursor;
}
'''


def fixture(root, leaf=LEAF):
    with patch.object(fixtures,'WORKER',WORKER):
        return fixtures.fixture(root,leaf=leaf)


def malformed(result, body):
    ordinary=fixtures.NativeTests.malformed(type('Result',(),{'result':result})(),body)
    return profile.DescriptorDisjunctiveAliasProof(ordinary.rom,ordinary.mapping,ordinary.index,ordinary.objects)


class SelectionTests(unittest.TestCase):
    def test_isolated_schema(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        for report in (marker*2, marker+f'* verification: `{owner.single_store.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'),'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_alternatives_',dir=scratch)
        cls.root=Path(cls.temporary.name);cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=profile.SELECTOR);cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.temporary.cleanup()

    def proof(self):
        r=self.result
        return profile.DescriptorDisjunctiveAliasProof(r[6],r[3],r[4],r[5])

    def run_body(self, body, *, aliases=None, stack=None, words=None, **changes):
        proof=malformed(self.result,bytes.fromhex(body))
        values=dict(arguments=aliases or {match.ARM_REG_R2:-8},
            stack=stack or [(False,False,True)]*2,incoming={},protected=frozenset(),
            words=words or {},frame_base=-4*len(stack or [(False,False,True)]*2),root_frame=A)
        values.update(changes)
        return proof,values

    def test_natural_elf_join_all_arms_and_fresh_report(self):
        self.assertEqual(self.original,self.result[8]);self.assertEqual(match.elf_image(self.original)['type'],1)
        paths=self.result[1]['proof']['buffers']['alias_alternatives']
        self.assertTrue(any(len({tuple(state['state'][0]) for state in row['states'] if state['site']==site})>1
            for row in paths for site in {state['site'] for state in row['states']}))
        self.assertTrue(any(len(row['returns'])>1 for row in paths))
        for row in paths:
            ids={state['id'] for state in row['states']}
            self.assertTrue(all(first in ids and second in ids for first,second in row['edges']))
            self.assertTrue(all(result['state'] in ids for result in row['returns']))
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))
        command=[sys.executable,str(Path(match.__file__)), '--root',str(self.root),f'{A:08X}',
                 '--owner-runtime-profile',profile.SELECTOR]
        native=subprocess.run(command,capture_output=True,text=True)
        self.assertEqual(native.returncode,0,native.stdout+native.stderr)
        self.assertIn('verdict MATCH - byte identical',native.stdout)
        saved=(self.root/f'docs/match/{A:08X}.md').read_text()
        self.assertEqual(saved,self.report)
        import status
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(saved,self.root,A),
                         ['--owner-runtime-profile',profile.SELECTOR])
        totals=status.collect(str(self.root),True,quiet=True)
        self.assertEqual((totals[1],totals[3],totals[4]),(1,len(self.data),[]))

    def test_previous_selector_still_refuses_unequal_join(self):
        r=self.result
        with self.assertRaisesRegex(ValueError,'inconsistent possible pointer offsets|lacks an exact live stack base'):
            owner.verify(r[0],A,r[6],r[3],r[4],r[5],bindings=self.bindings,selector=owner.single_store.SELECTOR)

    def test_one_bad_arm_and_one_past_cursor_refuse(self):
        # cmp r3,#0; beq join; adds r2,#4; join: STMIA r2!,{r0}; bx lr.
        for alias in (-4,-12):
            proof,values=self.run_body('002b00d0043201c27047',aliases={match.ARM_REG_R2:alias},
                stack=[(False,False,True)]*3)
            if alias==-4:
                with self.assertRaisesRegex(ValueError,'outside the tracked frame|outside allocated'):
                    proof.check_arguments(D,**values)
                self.assertNotIn(D,proof.native_frames)
            else:
                result=proof.check_arguments(D,**values)
                self.assertEqual({dict(item)[match.ARM_REG_R2] for item in result.alternatives},{-8,-4})

    def test_branch_pointer_escape_refuses(self):
        # The nonzero arm stores the tracked pointer through an unknown base.
        proof,values=self.run_body('002b00d00a607047')
        with self.assertRaisesRegex(ValueError,'pointer use or escape'):
            proof.check_arguments(D,**values)

    def test_saved_slot_and_clobbered_origin_refuse(self):
        proof,values=self.run_body('002b00d0043201c27047',
            stack=[(False,False,True),(False,True,False)])
        with self.assertRaisesRegex(ValueError,'outside allocated'):
            proof.check_arguments(D,**values)
        # Only one arm clobbers the exact descriptor pointer word before reload.
        proof,values=self.run_body('002b00d0106000687047',aliases={match.ARM_REG_R0:-8,match.ARM_REG_R2:-8},
            words={-8:('pointer',-4)},protected=frozenset({-8}))
        with self.assertRaisesRegex(ValueError,'exact surviving word value|pointer-bearing argument slot'):
            proof.check_arguments(D,**values)

    def test_loop_hits_real_bounds_and_budget_is_refusal(self):
        proof,values=self.run_body('01c2002bfcd17047')
        with self.assertRaisesRegex(ValueError,'outside the tracked frame|outside allocated'):
            proof.check_arguments(D,**values)
        self.assertNotIn(D,proof.native_frames)
        proof,values=self.run_body('002b00d0043201c27047')
        proof.exact_alias_state_budget=1
        with self.assertRaisesRegex(ValueError,'state budget exhausted'):
            proof.check_arguments(D,**values)

    def test_final_native_return_and_callee_saved_clobber_refuse(self):
        for body,pattern in (('01c2864601207047','indirect control flow'),
                             ('01c201247047','preservation of a live alias register')):
            proof,values=self.run_body(body,watched=(match.ARM_REG_R0+4,))
            with self.assertRaisesRegex(ValueError,pattern):proof.check_arguments(D,**values)
            self.assertNotIn(D,proof.native_frames)

    def test_exact_frame_gate_budget_and_isolation_refuse(self):
        proof=self.proof()
        with self.assertRaisesRegex(ValueError,'isolated'):
            match.verify_leaf_instructions(bytes.fromhex('7047'),D,True,
                buffer_proof=proof,acyclic_state_budget=4096)
        proof.exact_alias_state_budget=1
        with self.assertRaisesRegex(ValueError,'state budget exhausted'):
            match.verify_leaf_instructions(bytes.fromhex('01207047'),D,True,buffer_proof=proof)
        proof=self.proof()
        with self.assertRaisesRegex(ValueError,'balance|saved stack depth'):
            match.verify_leaf_instructions(bytes.fromhex('002b00d081b07047'),D,True,buffer_proof=proof)

    def test_tampered_paths_returns_and_source_refuse(self):
        r=self.result
        for field in ('alias_alternatives','single_word_stores','native_frame_replays'):
            manifest=copy.deepcopy(r[1]);manifest['proof']['buffers'][field]=[]
            with self.assertRaisesRegex(ValueError,'fresh native replay'):
                owner.verify(r[0],A,r[6],r[3],r[4],r[5],manifest=manifest,selector=profile.SELECTOR)
        source=self.root/f'src/{A:08X}.c';raw=source.read_bytes()
        try:
            source.write_bytes(raw+b'\n');self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
        finally:source.write_bytes(raw)


if __name__=='__main__':unittest.main(verbosity=2)
