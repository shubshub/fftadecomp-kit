"""Opaque saved entry aliases need both non-observation and native restoration."""
import hashlib
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from test_guarded_bios_division import halfwords, call, A, B
import match
import owner_admission_profile as owner
import descriptor_disjunctive_alias_profile as policy

LEAF = halfwords(0xB510,0x2407,0x8014,0xBC10,0xBC02,0x4708)


def fixture(leaf=LEAF):
    body = (halfwords(0xB510,0xB082,0x466C,0x466A)+call(A+8,B)+
            halfwords(0x8820,0x2200,0xB002,0xBC10,0xBC02,0x4708))
    rom = bytearray(B-match.ROM_BASE+len(leaf))
    rows = []
    for address,data in ((A,body),(B,leaf)):
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
        rows.append(dict(rom=f'0x{address:08X}',end=f'0x{address+len(data):08X}',
                         mode='thumb',instrs=0))
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                    f'{int(r["end"],16)-int(r["rom"],16)} 0 return\n' for r in rows).encode()
    return dict(data=body,address=A,rom=bytes(rom),mapping=json.dumps(rows).encode(),
        index=index,objects=b'{}\n',selector=policy.RESTORING_SELECTOR,
        bindings=dict(calls=[[8,f'func_{B:08X}']],data=[],functions=[],switches=[]))


class RestoringDescriptorLeafTests(unittest.TestCase):
    def test_complete_leaf_restores_alias_and_binds_native_frame(self):
        f=fixture()
        proof=policy.RestoringLeafDisjunctiveProof(f['rom'],f['mapping'],f['index'],f['objects'])
        proof.check_arguments(B,{match.ARM_REG_R2:-8},[(False,False,True)]*2,
            {},frozenset(),site=A+8,words={},frame_base=-8,root_frame=A,
            watched=(match.ARM_REG_R0+4,))
        manifest=proof.restoring_leaf_manifest()
        self.assertEqual(manifest['schema'],policy.RESTORING_SCHEMA)
        rows=manifest['observations']
        self.assertTrue(rows)
        self.assertEqual(rows[0]['restoration']['registers'],[4])
        self.assertEqual(rows[0]['site'],A+8)
        self.assertEqual(rows[0]['restoration']['body_sha256'],hashlib.sha256(LEAF).hexdigest())
        self.assertTrue(rows[0]['restoration']['frame'])
        self.assertIn(B,proof.native_frames)
        # A leaf certificate cannot supply the separate descriptor origins,
        # pointer-word replay, STMIA and unequal-join policy prerequisites.
        with self.assertRaisesRegex(ValueError,'actual callee stack origin and pointer-word replay'):
            owner.verify(**f)

    def test_existing_policy_still_requires_unmodified_live_alias(self):
        with self.assertRaisesRegex(ValueError,'preservation of a live alias register'):
            owner.verify(**dict(fixture(),selector=policy.SELECTOR))

    def test_opaque_alias_read_and_private_stack_escape_refuse(self):
        for leaf in (halfwords(0xB510,0x1C21,0x2407,0x8014,0xBC10,0xBC02,0x4708),
                     halfwords(0xB510,0x9400,0x2407,0x8014,0xBC10,0xBC02,0x4708)):
            with self.subTest(leaf=leaf),self.assertRaisesRegex(ValueError,'observes an opaque|only private PUSH/POP'):
                owner.verify(**fixture(leaf))

    def test_frame_return_and_actual_output_bounds_remain_required(self):
        for leaf in (halfwords(0xB510,0x2407,0x8014,0xBC10,0xBC02,0x4700),
                     halfwords(0xB510,0x2407,0x8114,0xBC10,0xBC02,0x4708)):
            with self.subTest(leaf=leaf),self.assertRaises(ValueError):
                owner.verify(**fixture(leaf))

    def test_selector_is_explicit_and_reports_are_canonical(self):
        marker=f'* verification: `{policy.RESTORING_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),policy.RESTORING_SELECTOR)
        for report in (marker*2,marker+f'* verification: `{policy.SCHEMA}`\n'):
            with self.assertRaises(ValueError):owner.selected(report)
        with patch.object(sys,'argv',['match.py','0x08010000','--root',str(Path.cwd()),
                '--owner-runtime-profile',policy.RESTORING_SELECTOR]), \
                patch.object(match,'repo_root',return_value=str(Path.cwd())), \
                patch.object(owner,'issue',return_value=17)as issue:
            self.assertEqual(match.main(),17)
            self.assertEqual(issue.call_args.args[2].owner_runtime_profile,policy.RESTORING_SELECTOR)


if __name__=='__main__':
    unittest.main(verbosity=2)
