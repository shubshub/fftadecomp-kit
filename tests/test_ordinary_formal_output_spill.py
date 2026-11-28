"""Synthetic Thumb-only fixed-slot formal output regression; no compiler or ROM fixture."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import owner_admission_profile as owner
if os.environ.get('FORMAL_SPILL_BASELINE'):
    import named_data_buffer_profile as profile
    Proof = profile.NamedDataBufferProof
else:
    import ordinary_formal_output_spill_profile as profile
    Proof = profile.FormalOutputSpillProof

A, H, N = 0x08000100, 0x08000200, 0x08000300
PREFIX = bytes.fromhex('10b581b00092072200990a80')
SUFFIX = bytes.fromhex('012001b010bc02bc0847')
HELPER = PREFIX + SUFFIX


def bl(site, target):
    delta = target - site - 4
    return struct.pack('<HH', 0xf000 | ((delta >> 12) & 0x7ff), 0xf800 | ((delta >> 1) & 0x7ff))


def fixture(helper=HELPER, child=None):
    root = bytes.fromhex('00b582b001aa00200221') + bl(A+10, H) + bytes.fromhex('01a9088802b002bc0847')
    bodies = {A:root,H:helper}
    if child is not None:bodies[N]=child
    rom=bytearray(0x400)
    rows=[]
    for address,body in bodies.items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(body)]=body
        rows.append(dict(rom=f'0x{address:08X}',end=f'0x{address+len(body):08X}',mode='thumb',instrs=0))
    mapping=json.dumps(rows).encode()
    for row in rows:
        address=int(row['rom'],16)
        row['instrs']=owner.refine(bodies[address],address,mapping)['instrs']
    mapping=json.dumps(rows).encode()
    index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} {int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    return root,bytes(rom),mapping,index


def direct(helper=HELPER, child=None):
    data,rom,mapping,index=fixture(helper,child)
    proof=Proof(rom,mapping,index,b'{}')
    match.verify_leaf_instructions(data,A,True,{A+10:H},buffer_proof=proof)
    return proof


class SpillTests(unittest.TestCase):
    def test_fixed_SP0_spill_reload_initializes_exact_u16_output(self):
        proof=direct()
        if not os.environ.get('FORMAL_SPILL_BASELINE'):
            record=proof.spill_manifest()
            self.assertEqual(record['output_width'],2)
            self.assertTrue(record['spills'])
            self.assertTrue(record['reloads'])
            self.assertTrue(record['writes'])
            self.assertEqual(set(proof.native_frames),{H})

    def test_uninitialized_reload_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:4]+bytes.fromhex('c046')+HELPER[6:])

    def test_scalar_overwrite_of_spill_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:8]+bytes.fromhex('0090')+HELPER[8:])

    def test_partial_overwrite_of_spill_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:8]+bytes.fromhex('6b461870')+HELPER[8:])

    def test_nonzero_spill_slot_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:4]+bytes.fromhex('0192')+HELPER[6:])

    def test_saved_frame_spill_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:2]+bytes.fromhex('c046')+HELPER[4:])

    def test_output_pointer_escape_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:6]+bytes.fromhex('0260')+HELPER[6:])

    def test_output_read_before_write_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:10]+bytes.fromhex('0a88')+HELPER[12:])

    def test_output_offset_two_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:10]+bytes.fromhex('4a80')+HELPER[12:])

    def test_pointer_result_reload_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:8]+bytes.fromhex('0098')+HELPER[10:])

    def test_branch_around_spill_refuses(self):
        # A conditional path reaches the reload without an initialized pointer word.
        with self.assertRaises(ValueError):direct(HELPER[:4]+bytes.fromhex('00d00092')+HELPER[6:])

    def test_corrupted_return_refuses(self):
        with self.assertRaises(ValueError):direct(HELPER[:-2]+bytes.fromhex('0047'))

    def test_nested_scalar_call_replayed_without_pointer_forwarding(self):
        helper=PREFIX+bytes.fromhex('0021')+bl(H+14,N)+SUFFIX
        proof=direct(helper,bytes.fromhex('02207047'))
        self.assertEqual(set(proof.native_frames),{H,N})

    def test_nested_unknown_memory_write_refuses(self):
        helper=PREFIX+bytes.fromhex('0021')+bl(H+14,N)+SUFFIX
        with self.assertRaises(ValueError):direct(helper,bytes.fromhex('08607047'))

    def test_nested_pointer_forwarding_refuses(self):
        helper=PREFIX+bl(H+12,N)+SUFFIX
        with self.assertRaises(ValueError):direct(helper,bytes.fromhex('02207047'))

    def test_scratch_pointer_return_refuses(self):
        # Reload R2; write through it; leave R2 as a pointer at return.
        helper=bytes.fromhex('10b581b00092009a07201080')+SUFFIX
        data,rom,mapping,index=fixture(helper)
        proof=Proof(rom,mapping,index,b'{}')
        with self.assertRaisesRegex(ValueError,'result register|scratch'):
            proof.check_arguments(H,{match.ARM_REG_R2:-4},[(False,False,True)]*2,{},frozenset(),
                                  frame_base=-8,root_frame=A,site=A+10)

    def test_one_branch_missing_output_write_refuses(self):
        helper=HELPER[:10]+bytes.fromhex('002800d0')+HELPER[10:]
        with self.assertRaisesRegex(ValueError,'normal return precedes'):
            direct(helper)

    def test_canonical_mov_PC_LR_return_preserves_output(self):
        # The existing independent frame engine already accepts this return.
        helper=HELPER[:-2]+bytes.fromhex('8e46f746')
        self.assertTrue(direct(helper).spill_manifest()['writes'])

    def test_mov_PC_LR_path_missing_output_refuses(self):
        helper=HELPER[:10]+bytes.fromhex('002800d0')+HELPER[10:-2]+bytes.fromhex('8e46f746')
        with self.assertRaisesRegex(ValueError,'normal return precedes'):
            direct(helper)

    def test_unknown_value_before_spill_refuses(self):
        with self.assertRaises(ValueError):
            direct(HELPER[:4]+bytes.fromhex('0022')+HELPER[4:])

    def test_output_outside_caller_allocated_words_refuses(self):
        data,rom,mapping,index=fixture()
        proof=Proof(rom,mapping,index,b'{}')
        with self.assertRaisesRegex(ValueError,'outside allocated'):
            proof.check_arguments(H,{match.ARM_REG_R2:0},[(False,False,True)]*2,{},frozenset(),
                                  frame_base=-8,root_frame=A,site=A+10)

    def test_DEFAULT_remains_closed(self):
        data,rom,mapping,index=fixture()
        for stack in (False,True):
            with self.subTest(stack=stack),self.assertRaises(ValueError):
                match.verify_leaf_instructions(data,A,True,{A+10:H},buffer_proof=match.BufferCallProof(rom,mapping,stack_arguments=stack))


class ConsumerTests(unittest.TestCase):
    def values(self):
        data,rom,mapping,index=fixture()
        return dict(data=data,address=A,rom=rom,mapping=mapping,index=index,objects=b'{}',
                    bindings=dict(calls=[[10,f'func_{H:08X}']],data=[],functions=[],switches=[]),selector=profile.SELECTOR)

    def test_match_CLI_selects_only_explicit_owner_route(self):
        argv=['match.py','--root','.', '--owner-runtime-profile',profile.SELECTOR,f'0x{A:08X}']
        with patch.object(sys,'argv',argv),patch.object(match,'repo_root',return_value=Path('.')), \
                patch.object(owner,'issue',return_value='explicit-route') as issue:
            self.assertEqual(match.main(),'explicit-route')
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile,profile.SELECTOR)

    def test_explicit_owner_selector_roundtrip(self):
        marker=f'* verification: `{profile.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),profile.SELECTOR)
        for report in (marker*2,marker+f'* verification: `{owner.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)

    def test_complete_owner_manifest_and_changed_evidence_refuse(self):
        values=self.values();manifest,verified=owner.verify(**values)
        self.assertEqual(manifest['profile'],profile.SCHEMA)
        self.assertTrue(manifest['proof']['buffers']['formal_output_spill']['writes'])
        stale=copy.deepcopy(manifest);stale['proof']['buffers']['formal_output_spill']['writes']=[]
        with self.assertRaises(ValueError):owner.verify(**values,manifest=stale)

    def test_changed_helper_body_and_index_refuse(self):
        values=self.values();manifest,_=owner.verify(**values)
        for key,data in [('rom',values['rom'][:H-match.ROM_BASE]+b'\0\0'+values['rom'][H-match.ROM_BASE+2:]),
                         ('index',values['index'].replace(b'08000216',b'08000218'))]:
            changed=dict(values);changed[key]=data
            with self.subTest(key=key),self.assertRaises(ValueError):owner.verify(**changed,manifest=manifest)

    def test_data_and_callback_composition_refuse(self):
        values=self.values()
        for field,row in [('data',[0,'data_02000000',0]),('functions',[0,'func_08000300']),('switches',[0,4])]:
            changed=copy.deepcopy(values);changed['bindings'][field].append(row)
            with self.subTest(field=field),self.assertRaises(ValueError):owner.verify(**changed)

    def test_report_fresh_replay_and_stale_source_refuse(self):
        import match_evidence
        values=self.values();manifest,verified=owner.verify(**values)
        result=(values['data'],manifest,'fresh-source',values['mapping'],values['index'],b'{}',values['rom'],len(verified),b'original-ELF')
        report=owner.render(A,result)
        report_fixtures.rom_image(self,values['rom'])
        with patch.object(owner,'build',return_value=result):
            self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, Path('.'), A), Path('.'), A))
        stale=list(result);stale[2]='different-source'
        with patch.object(owner,'build',return_value=tuple(stale)):
            self.assertFalse(report_fixtures.replay(report,Path('.'),A))
        self.assertIn('conditional returning ordinary ARM ABI',report)


if __name__=='__main__':unittest.main(verbosity=2)
