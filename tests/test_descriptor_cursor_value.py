"""Exact cursor values remain separate from allocated-word memory access."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import match
import match_evidence
import owner_admission_profile as owner
import descriptor_cursor_value_profile as profile
import test_descriptor_callee_constant as fixtures
from test_static_callback_buffer import A,B,C,D

WORKER='''struct Output { unsigned int *words; };
struct Work { struct Output output; unsigned int words[5]; };
unsigned int func_08011000(unsigned char *marker, void (*callback)(struct Output *))
{
    struct Work work;
    work.words[0] = 1;
    work.words[1] = 3;
    work.words[2] = 5;
    work.words[3] = 7;
    work.words[4] = 9;
    work.output.words = work.words;
    if (marker[0])
        work.output.words = work.words + 1;
    callback(&work.output);
    callback(&work.output);
    return (work.words[0] + marker[0]) * (work.words[1] + marker[0]) + work.words[2];
}
'''


def fixture(root):
    with patch.object(fixtures,'WORKER',WORKER):
        return fixtures.fixture(root)


class SelectionTests(unittest.TestCase):
    def test_explicit_isolated_schema(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        for report in (marker*2,marker+f'* verification: `{owner.callee_constant.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-ld'),'fixed original compiler required')
class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch=Path(os.environ.get('TMPDIR',Path.cwd()/'build/tests'));scratch.mkdir(parents=True,exist_ok=True)
        cls.temporary=tempfile.TemporaryDirectory(prefix='descriptor_cursor_',dir=scratch)
        cls.root=Path(cls.temporary.name);cls.data,cls.bindings,cls.original=fixture(cls.root)
        cls.environment=patch.dict(os.environ,FFTA_ROM=str(cls.root/'baserom.bin'));cls.environment.start()
        cls.result=owner.build(cls.root,A,selector=profile.SELECTOR);cls.report=owner.render(A,cls.result)

    @classmethod
    def tearDownClass(cls):cls.environment.stop();cls.temporary.cleanup()

    def proof(self, body=None):
        r=self.result
        if body is None:
            return profile.DescriptorCursorValueProof(r[6],r[3],r[4],r[5])
        body=bytes.fromhex(body);rom=bytearray(r[6]);rom[D-match.ROM_BASE:D-match.ROM_BASE+len(body)]=body
        rows=json.loads(r[3]);row=next(row for row in rows if int(row['rom'],16)==D)
        row.update(end=f'0x{D+len(body):08X}',instrs=len(body)//2)
        index=''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode()
        return profile.DescriptorCursorValueProof(bytes(rom),json.dumps(rows).encode(),index,r[5])

    def call(self, body, *, pointer=-4, **changes):
        proof=self.proof(body)
        values=dict(arguments={match.ARM_REG_R0:-12},stack=[(False,False,True)]*2+[(False,True,False)],
                    incoming={},protected=frozenset(),constants={},words={-12:('pointer',pointer)},
                    frame_base=-12,root_frame=A)
        values.update(changes)
        return proof,values

    def test_natural_elf_native_match_report_status_and_cursor(self):
        r=self.result;self.assertEqual(r[8],self.original);self.assertEqual(match.elf_image(r[8])['type'],1)
        rows=r[1]['proof']['buffers']['cursor_values']['transfers']
        self.assertTrue(any(not row['pointee_is_local'] and row['operation']=='store' for row in rows))
        native=subprocess.run([sys.executable,str(Path(match.__file__)),'--root',str(self.root),
            f'{A:08X}','--owner-runtime-profile',profile.SELECTOR],capture_output=True,text=True)
        self.assertEqual(native.returncode,0,native.stdout+native.stderr)
        saved=(self.root/f'docs/match/{A:08X}.md').read_text();self.assertEqual(saved,self.report)
        self.assertTrue(match_evidence.report_matches(saved,self.root,A))
        import status
        totals=status.collect(str(self.root),True,quiet=True)
        self.assertEqual((totals[1],totals[3],totals[4]),(1,len(self.data),[]))

    def test_previous_selector_still_requires_local_pointee(self):
        r=self.result
        with self.assertRaisesRegex(ValueError,'outside allocated'):
            owner.verify(r[0],A,r[6],r[3],r[4],r[5],bindings=self.bindings,selector=owner.callee_constant.SELECTOR)

    def test_store_reload_and_return_exact_value_without_dereference(self):
        # ldr r2,[r0]; str r2,[r0]; bx lr. Descriptor is local, cursor is saved-slot address.
        for pointer in (-4,0):
            proof,values=self.call('026802607047',pointer=pointer)
            result=proof.check_arguments(D,**values)
            self.assertEqual({dict(item.words)[-12] for item in result.alternatives},{('pointer',pointer)})
            self.assertEqual({item[match.ARM_REG_R2] for item in result.alternatives},{pointer})
            self.assertTrue(any(not row['pointee_is_local'] for row in proof.cursor_observations()['transfers']))
        proof=self.proof();facts={-4:('pointer',-12)}
        proof.prune_words(facts,[(False,False,True)]*2);self.assertEqual(facts,{})
        facts={-4:('pointer',0)};proof.prune_words(facts,[]);self.assertEqual(facts,{})

    def test_actual_saved_and_outside_dereferences_refuse(self):
        for pointer in (-4,0):
            for operation in ('1368','1360'):  # ldr/str r3,[r2].
                proof,values=self.call('0268'+operation+'7047',pointer=pointer)
                with self.subTest(pointer=pointer,operation=operation),self.assertRaisesRegex(ValueError,'outside allocated'):
                    proof.check_arguments(D,**values)
                self.assertNotIn(D,proof.native_frames)
        # The native caller engine must not reinterpret a cursor load as a saved-register restore.
        proof=self.proof()
        with self.assertRaisesRegex(ValueError,'outside allocated'):
            match.verify_leaf_instructions(bytes.fromhex('00b581b068460430016801b002bc0847'),D,True,buffer_proof=proof)

    def test_unknown_base_pointer_escape_and_root_return_refuse(self):
        proof,values=self.call('02680a607047')  # str r2,[r1], unknown base.
        with self.assertRaisesRegex(ValueError,'pointer use or escape'):proof.check_arguments(D,**values)
        with self.assertRaisesRegex(ValueError,'escapes through a return'):
            match.verify_leaf_instructions(bytes.fromhex('81b0684601b07047'),D,True,buffer_proof=self.proof())
        with self.assertRaisesRegex(ValueError,'bounded live stack'):
            self.proof().validate_pointer_value(-16,[(False,False,True)]*3)

    def test_every_cursor_return_alternative_and_bad_arm(self):
        # cmp r3,#0; beq; adds r2,#4; STMIA r2!,{r1}; str r2,[r0]; bx lr.
        body='002b00d0043202c202607047'
        values=dict(arguments={match.ARM_REG_R0:-16,match.ARM_REG_R2:-12},
            stack=[(False,False,True)]*3+[(False,True,False)],incoming={},protected=frozenset(),
            constants={},words={-16:('pointer',-12)},frame_base=-16,root_frame=A)
        proof=self.proof(body);result=proof.check_arguments(D,**values)
        self.assertEqual({dict(item.words)[-16] for item in result.alternatives},{('pointer',-8),('pointer',-4)})
        self.assertEqual({item[match.ARM_REG_R2] for item in result.alternatives},{-8,-4})
        bad=body[:-4]+'11607047'  # Only the saved-slot arm fails the subsequent actual store.
        proof=self.proof(bad)
        with self.assertRaisesRegex(ValueError,'outside allocated'):proof.check_arguments(D,**values)
        self.assertNotIn(D,proof.native_frames)

    def test_unknown_callback_and_unproved_effect_refuse(self):
        proof=self.proof();thunk=self.result[1]['proof']['buffers']['callbacks'][0]['thunk']
        with self.assertRaisesRegex(ValueError,'not an exact Thumb'):
            proof.check_arguments(thunk,{match.ARM_REG_R0:-12},[(False,False,True)]*3,{},frozenset(),
                constants={},words={-12:('pointer',0)},frame_base=-12,root_frame=A)
        proof,values=self.call('026810477047')  # bx r2 is an unproved transfer through the cursor.
        with self.assertRaises(ValueError):proof.check_arguments(D,**values)
        self.assertNotIn(D,proof.native_frames)

    def test_tampered_provenance_alternatives_and_source_refuse(self):
        r=self.result
        for field in ('cursor_values','alias_alternatives','callee_constants','word_reads'):
            manifest=copy.deepcopy(r[1]);manifest['proof']['buffers'][field]={} if field in ('cursor_values','callee_constants') else []
            with self.assertRaisesRegex(ValueError,'fresh native replay'):
                owner.verify(r[0],A,r[6],r[3],r[4],r[5],manifest=manifest,selector=profile.SELECTOR)
        manifest=copy.deepcopy(r[1]);manifest['proof']['buffers']['cursor_values']['transfers'][0]['value']=0
        with self.assertRaisesRegex(ValueError,'fresh native replay'):
            owner.verify(r[0],A,r[6],r[3],r[4],r[5],manifest=manifest,selector=profile.SELECTOR)
        manifest=copy.deepcopy(r[1])
        path=next(row for row in manifest['proof']['buffers']['alias_alternatives'] if row['returns'])
        path['returns'].pop()
        with self.assertRaisesRegex(ValueError,'fresh native replay'):
            owner.verify(r[0],A,r[6],r[3],r[4],r[5],manifest=manifest,selector=profile.SELECTOR)
        source=self.root/f'src/{A:08X}.c';raw=source.read_bytes()
        try:
            source.write_bytes(raw+b'\n');self.assertFalse(match_evidence.report_matches(self.report,self.root,A))
        finally:source.write_bytes(raw)


if __name__=='__main__':unittest.main(verbosity=2)
