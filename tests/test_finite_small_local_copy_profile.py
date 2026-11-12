"""Bounded loop authentication, exact cursor states and unchanged defaults."""
import copy
import json
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
import finite_small_local_copy_profile as finite
import match
from test_small_local_copy_caller_profile import fixture as base_fixture, change_word
import small_local_copy_caller_profile as caller


def fixture(count=8, *, root=0x08000200, target=0x08000400, source=0x08000801):
    env=base_fixture(count,root=root,target=target,source=source)
    frame=(count+3)//4
    words=[0xB500,0xB080+frame,0x4907,0x4668,0x2200+count,0,0,
           0x2300,0x466A,0x8810,0x3202,0x3301,0x2B00+count//2-1,
           0xDDFA,0x2200,0xB000+frame,0xBC02,0x4708,0,0]
    data=bytearray(struct.pack('<20H',*words))
    delta=target-root-10-4
    struct.pack_into('<HH',data,10,0xF000|((delta>>12)&2047),0xF800|((delta>>1)&2047))
    # LDR at +4 reads the complete word at +36.
    struct.pack_into('<I',data,36,source)
    rom=bytearray(env['rom']);rom[root-match.ROM_BASE:root-match.ROM_BASE+len(data)]=data
    rows=json.loads(env['mapping']);rows[0].update(end=f'0x{root+len(data):08X}',instrs=17)
    env.update(data=bytes(data),rom=bytes(rom),mapping=json.dumps(rows).encode(),
        index=f'{root:08X} {root+len(data):08X} {len(data)} 17 bx\n{target:08X} {target+98:08X} 98 49 bx\n'.encode())
    return env


def verify(env,**changes):
    args={key:env[key] for key in ('data','rom','mapping','index','objects')}
    args.update(address=env['root'],selector=finite.SELECTOR);args.update(changes)
    return finite.verify(**args)


class FiniteCopyTests(unittest.TestCase):
    def test_all_counts_exact_iterations_and_initialized_addresses(self):
        for count in (2,4,8,10):
            with self.subTest(count=count):
                env=fixture(count);manifest,instructions=verify(env)
                self.assertEqual(manifest['loop']['iterations'],count//2)
                low=manifest['caller']['caller_sp_offset']
                self.assertEqual([row[1] for row in manifest['loop']['initialized_halfword_reads']],
                    list(range(low,low+count,2)))
                self.assertEqual(len(instructions),17)
                self.assertEqual(len(manifest['loop']['branch_observations']),count//2)
                self.assertFalse(manifest['source_or_ELF_admission'])
                self.assertFalse(manifest['physical_access_proved'])
                self.assertIn('nonalias',manifest['conditions'][-1])
                verify(env,manifest=json.loads(json.dumps(manifest)))

    def test_default_join_stays_strict_and_destination_alias_retained(self):
        env=fixture()
        args={key:env[key] for key in ('data','rom','mapping','index','objects')}
        with self.assertRaisesRegex(ValueError,'inconsistent possible pointer offsets'):
            caller.verify(**args,address=env['root'],selector=caller.SELECTOR)
        proof=finite.LoopProof(**args,address=env['root'],selector=finite.SELECTOR)
        stack=[(False,False,True)]*2+[(True,True,False)]
        result=proof.check_call(env['helper'],{match.ARM_REG_R0:-12},stack,site=env['root']+10)
        self.assertEqual(result,{match.ARM_REG_R0:-12})

    def test_changed_bounds_update_cursor_and_initialization_refused(self):
        for offset,word in ((14,0x2301),(22,0x3302),(24,0x2B04),
                            (26,0xD1F9),(20,0x3204),(16,0x466B),
                            (18,0x8850),(18,0x8813),(20,0x6002)):
            with self.subTest(offset=offset,word=word),self.assertRaises(ValueError):
                verify(change_word(fixture(),offset,word))

    def test_counter_flags_and_loop_entry_cannot_be_bypassed(self):
        for offset,word in ((22,0xE000),(24,0x2300),(26,0xDDF8),(16,0xE001)):
            with self.subTest(offset=offset,word=word),self.assertRaises(ValueError):
                verify(change_word(fixture(),offset,word))

    def test_context_forgery_and_cross_inputs_refused(self):
        env=fixture();args={key:env[key] for key in ('data','rom','mapping','index','objects')}
        proof=finite.LoopProof(**args,address=env['root'],selector=finite.SELECTOR)
        proof.bound=4
        with self.assertRaisesRegex(ValueError,'stale'):
            match.verify_leaf_instructions(env['data'],env['root'],True,proof.calls,
                buffer_proof=proof,finite_small_copy_context=proof)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(env['data'],env['root'],True,proof.calls,
                buffer_proof=proof,finite_small_copy_context=object())

    def test_exact_successor_requires_cursor_and_counter(self):
        env=fixture();args={key:env[key] for key in ('data','rom','mapping','index','objects')}
        proof=finite.LoopProof(**args,address=env['root'],selector=finite.SELECTOR)
        for value,offset in ((0,-12),(5,-2),(1,-12),(2,-6),(None,-10)):
            with self.subTest(value=value,offset=offset),self.assertRaises(ValueError):
                proof.successors(proof.latch,{proof.counter:value},{proof.cursor:offset})

    def test_suffix_escapes_and_unbalanced_frame_remain_rejected(self):
        for offset,word in ((28,0x6002),(30,0xB001),(34,0x4700)):
            with self.subTest(offset=offset,word=word),self.assertRaises(ValueError):
                verify(change_word(fixture(),offset,word))

    def test_stale_manifest_and_old_selector_refused(self):
        env=fixture();manifest,_=verify(env)
        for field in ('loop','caller','conditions'):
            stale=copy.deepcopy(manifest);stale[field]={}
            with self.subTest(field=field),self.assertRaises(ValueError):verify(env,manifest=stale)
        with self.assertRaises(ValueError):verify(env,selector=caller.SELECTOR)

    def test_relocated_loop_and_source(self):
        manifest,_=verify(fixture(root=0x08001000,target=0x08000600,source=0x08002003))
        self.assertEqual(manifest['loop']['header'],0x08001012)


if __name__=='__main__':unittest.main()
