"""Exact one-word Thumb STMIA effects, provenance and mandatory native gates."""
import copy
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import descriptor_single_store_profile as profile
import test_descriptor_output_alias as fixtures
from test_descriptor_output_alias import A,B,C,D

WORKER = '''struct Output { unsigned int *words; };
extern void func_08012000(struct Output *);
unsigned int func_08011000(unsigned char *marker)
{
    unsigned int words[2];
    struct Output output;
    words[1] = 3;
    output.words = words;
    func_08012000(&output);
    return (words[0] + marker[0]) * (words[1] + marker[0]);
}
'''
LEAF = '''struct Output { unsigned int *words; };
void func_08012000(struct Output *output)
{
    *output->words++ = 7;
}
'''


def fixture(root, leaf=LEAF):
    with patch.object(fixtures,'WORKER',WORKER):
        return fixtures.fixture(root,leaf=leaf)


def instruction(raw):
    decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
    return next(decoder.disasm(bytes.fromhex(raw),C))


class SelectionTests(unittest.TestCase):
    def test_isolated_selector_and_mixed_schema_refusal(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        for report in (marker*2,marker+f'* verification: `{owner.output_alias.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'),'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_single_store_',dir=scratch)
        cls.root=Path(cls.temporary.name);cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=profile.SELECTOR);cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop();cls.temporary.cleanup()

    def proof(self):
        r=self.result
        return profile.DescriptorSingleStoreProof(r[6],r[3],r[4],r[5])

    def replay(self,**changes):
        r=self.result
        values=dict(data=r[0],address=A,rom=r[6],mapping=r[3],index=r[4],objects=r[5],
                    manifest=r[1],selector=profile.SELECTOR);values.update(changes)
        return owner.verify(**values)

    def leaf(self,proof,**changes):
        values=dict(arguments={match.ARM_REG_R0:-16},stack=[(False,False,True)]*4,
            incoming={},protected=frozenset(),words={-16:('pointer',-8)},constants={},
            frame_base=-16,root_frame=A,site=A+8)
        values.update(changes)
        return proof.check_arguments(C,**values)

    def test_natural_original_elf_actual_store_and_fresh_report(self):
        self.assertEqual(self.original,self.result[8]);self.assertEqual(match.elf_image(self.original)['type'],1)
        buffers=self.result[1]['proof']['buffers'];stores=buffers['single_word_stores']
        self.assertTrue(stores)
        self.assertTrue(all(row['writeback']==row['offset']+4 for row in stores))
        self.assertEqual({tuple(row['stored_value']) for row in stores},{('constant',7)})
        self.assertIn(C,{row['address'] for row in buffers['native_frame_replays']})
        self.assertTrue(match_evidence.report_matches(self.report,self.root,A))

    def test_previous_selector_retains_store_refusal(self):
        with self.assertRaisesRegex(ValueError,'append block-write'):
            self.replay(selector=owner.output_alias.SELECTOR,manifest=None,bindings=self.bindings)

    def test_exact_word_pointer_constant_unknown_and_writeback(self):
        proof=self.proof();stm=instruction('01c2') # stm r2!,{r0}, generic fixture
        for source,constant,expected in ((-4,None,('pointer',-4)),(None,9,('constant',9)),(None,None,None)):
            with self.subTest(expected=expected):
                aliases={match.ARM_REG_R2:-8};constants={};facts={-8:('constant',3),-4:('constant',1)}
                slots={-8:-4};stack=[(False,False,True)]*2
                if source is not None:aliases[match.ARM_REG_R0]=source
                if constant is not None:constants[match.ARM_REG_R0]=constant
                proof.apply_single_store(stm,aliases,constants,stack,facts,pointer_slots=slots,root_frame=A)
                self.assertEqual(aliases[match.ARM_REG_R2],-4)
                self.assertEqual(facts.get(-8),expected);self.assertEqual(facts[-4],('constant',1))
                self.assertEqual(slots,{-8:-4} if source is not None else {})

    def test_bounds_control_stale_and_unknown_base_refuse(self):
        proof=self.proof();stm=instruction('01c2')
        for base,stack,source in ((0,[(False,False,True)]*2,None),
                (-12,[(False,False,True)]*2,None),(-6,[(False,False,True)]*2,None),
                (-8,[(False,True,False),(False,False,True)],None),
                (-8,[(False,False,True)]*2,0),(None,[(False,False,True)]*2,None)):
            aliases={} if base is None else {match.ARM_REG_R2:base}
            if source is not None:aliases[match.ARM_REG_R0]=source
            with self.subTest(base=base,source=source),self.assertRaises(ValueError):
                proof.apply_single_store(stm,aliases,{},list(stack),{-8:('constant',1)})

    def test_unsupported_register_lists_and_base_in_list_refuse(self):
        proof=self.proof()
        for raw in ('03c2','04c2'):
            with self.subTest(raw=raw),self.assertRaisesRegex(ValueError,'one exact low register'):
                proof.apply_single_store(instruction(raw),{match.ARM_REG_R2:-8},{},
                    [(False,False,True)]*2,{})

    def test_two_contexts_wrong_origin_and_clobbered_word_cannot_reuse(self):
        proof=self.proof();self.leaf(proof)
        for facts in ({-16:('pointer',0)},{}):
            with self.subTest(facts=facts),self.assertRaises(ValueError):
                self.leaf(proof,words=facts)
        self.assertGreaterEqual(len(proof.contexts),3)
        facts={-16:('pointer',-8)};stack=[(False,False,True)]*4
        proof.word_memory(instruction('0860'),{}, {},stack,facts,-16,frozenset({-16}))
        self.assertEqual(facts,{})
        with self.assertRaisesRegex(ValueError,'exact surviving word value'):
            self.leaf(proof,words=facts,protected=frozenset({-16}))

    def test_unbounded_repeat_and_one_past_access_refuse(self):
        proof=self.proof();aliases={match.ARM_REG_R2:-4};stack=[(False,False,True)]
        proof.apply_single_store(instruction('01c2'),aliases,{},stack,{})
        self.assertEqual(aliases[match.ARM_REG_R2],0)
        with self.assertRaises(ValueError):proof.apply_single_store(instruction('01c2'),aliases,{},stack,{})
        # This generic closed loop repeats one STMIA with no finite trip bound.
        bad=bytes.fromhex('01c2002bfcd17047');ordinary=fixtures.NativeTests.malformed(self,bad)
        proof=profile.DescriptorSingleStoreProof(ordinary.rom,ordinary.mapping,ordinary.index,ordinary.objects)
        with self.assertRaisesRegex(ValueError,'inconsistent possible pointer offsets'):
            proof.check_arguments(D,{match.ARM_REG_R2:-8},[(False,False,True)]*2,{},frozenset(),
                words={},frame_base=-8,root_frame=A)
        self.assertNotIn(D,proof.native_frames)

    def test_completed_store_effects_still_require_native_return_gate(self):
        # STMIA succeeds, then a closed CFG replaces the saved return token.
        bad=bytes.fromhex('01c2864601207047');ordinary=fixtures.NativeTests.malformed(self,bad)
        proof=profile.DescriptorSingleStoreProof(ordinary.rom,ordinary.mapping,ordinary.index,ordinary.objects)
        with patch.object(proof,'complete_frame',wraps=proof.complete_frame) as complete:
            with self.assertRaisesRegex(ValueError,'indirect control flow'):
                proof.check_arguments(D,{match.ARM_REG_R2:-8},[(False,False,True)]*2,{},frozenset(),
                    words={},frame_base=-8,root_frame=A)
        self.assertTrue(proof.store_observations());complete.assert_called_once()
        self.assertNotIn(D,proof.native_frames)

    def test_expired_partial_and_changed_store_report_refuse(self):
        proof=self.proof();facts={-16:('pointer',-8)}
        proof.prune_words(facts,[]);proof.prune_words(facts,[(False,False,True)]*4)
        self.assertEqual(facts,{})
        with self.assertRaises(ValueError):self.leaf(proof,words=facts)
        with self.assertRaisesRegex(ValueError,'exact aligned full word'):
            proof.word_memory(instruction('0078'),{match.ARM_REG_R0:-16},{},
                [(False,False,True)]*4,{-16:('pointer',-8)},-16,frozenset({-16}))
        manifest=copy.deepcopy(self.result[1]);manifest['proof']['buffers']['single_word_stores']=[]
        with self.assertRaisesRegex(ValueError,'fresh native replay'):self.replay(manifest=manifest)


if __name__=='__main__':unittest.main(verbosity=2)
