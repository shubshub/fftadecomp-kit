"""Exact local BIOS/scratch composition through complete untouched-register leaves."""
import argparse
import copy
import json
import struct
import sys
import unittest
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import bg_affine_transparent_leaf_profile as transparent
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_bg_affine_set_scratch as base

A, B, C = base.A, base.B, base.B + 0x100
LEAF = bytes.fromhex('00b500210222805e002800d10121081c02bc0847')


class TransparentLeafTests(unittest.TestCase):
    def setUp(self):
        environment = patch.object(transparent, 'environment_fingerprint', return_value={'synthetic': True})
        environment.start()
        self.addCleanup(environment.stop)
        self.base = base.BgAffineSetScratchTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, leaf=LEAF, after=(), helper=None):
        f = self.base.fixture(helper=helper)
        site = A + len(f['data']) - 6
        data = f['data'][:-6] + base.bl(site, C)
        data += b''.join(struct.pack('<H', word) for word in after) + f['data'][-6:]
        rows = json.loads(f['mapping'])
        rows[0]['end'] = f'0x{A+len(data):08X}'
        rows.append(dict(rom=f'0x{C:08X}', end=f'0x{C+len(leaf):08X}', mode='thumb', instrs=0))
        mapping, index = base.indexes(rows)
        rom = bytearray(f['rom'])
        rom[A-base.match.ROM_BASE:A-base.match.ROM_BASE+len(data)] = data
        rom[C-base.match.ROM_BASE:C-base.match.ROM_BASE+len(leaf)] = leaf
        return dict(f, data=data, rom=bytes(rom), mapping=mapping, index=index,
            selector=buffers.BG_AFFINE_TRANSPARENT_SELECTOR,
            bindings=dict(f['bindings'], calls=f['bindings']['calls'] + [[site-A,f'func_{C:08X}']]))

    def test_positive_both_paths_and_live_register_receipt(self):
        for after in ((), (0x2300,), (0x2800,0xD000,0x2001)):
            with self.subTest(after=after):
                f = self.fixture(after=after)
                manifest, _ = owner.verify(**f)
                row = manifest['proof']['buffers']['normal_return_scratch']['transparent_leaf_calls']['observations'][0]
                self.assertEqual(row['target'], C)
                self.assertEqual(row['selected'], [3])
                self.assertEqual(row['returned_live'], [3])
                self.assertEqual(row['callee']['instructions'], 10)
                self.assertEqual(row['callee']['calls'], [])
                self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)

    def test_old_selectors_and_missing_new_observation_refuse(self):
        for selector in (buffers.BG_AFFINE_SELECTOR,buffers.BG_AFFINE_SCRATCH_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(self.fixture(),selector=selector))
        f = self.base.fixture()
        with self.assertRaisesRegex(ValueError,'actual checked call observations'):
            owner.verify(**dict(f,selector=buffers.BG_AFFINE_TRANSPARENT_SELECTOR))

    def test_observed_written_spilled_returned_and_unknown_effects_refuse(self):
        for leaf in (bytes.fromhex(h) for h in (
            '181c7047', '002b7047', '00237047', '03607047', '08b408bc7047',
            '1847', '18467047', '00df7047', '00d170477047', 'fee7',
            '00b500210222835e002800d10121081c02bc0847')):
            with self.subTest(leaf=leaf.hex()), self.assertRaises(ValueError):
                owner.verify(**self.fixture(leaf=leaf))
        leaf = bytes.fromhex('00b5')+base.bl(C+2,B)+bytes.fromhex('01bc0047')
        with self.assertRaisesRegex(ValueError,'nested ordinary calls'):
            owner.verify(**self.fixture(leaf=leaf))

    def test_r3_is_still_live_after_call_and_r0_r1_are_not_projected(self):
        for after in ((0x6818,), (0x1C18,), (0x600B,), (0x2800,0xD000,0x2300,0x6818)):
            with self.subTest(after=after), self.assertRaises(ValueError):
                owner.verify(**self.fixture(after=after))
        for helper, leaf, epilogue in ((bytes.fromhex('031c7047'), bytes.fromhex('7047'), bytes.fromhex('02bc0847')),
                                       (bytes.fromhex('031c011c00207047'), bytes.fromhex('00207047'), bytes.fromhex('01bc0047'))):
            f=self.fixture(helper=helper,leaf=leaf)
            data=f['data'][:-4]+epilogue
            rom=bytearray(f['rom']);rom[A-base.match.ROM_BASE:A-base.match.ROM_BASE+len(data)]=data
            with self.subTest(helper=helper.hex()), self.assertRaisesRegex(ValueError,'escapes through a return register'):
                owner.verify(**dict(f,data=data,rom=bytes(rom)))

    def test_body_index_object_and_manifest_changes_refuse(self):
        f = self.fixture(); manifest,_ = owner.verify(**f)
        for field in ('consumer_sha256','producer_site','site','target','selected','returned_live','callee'):
            changed=copy.deepcopy(manifest)
            changed['proof']['buffers']['normal_return_scratch']['transparent_leaf_calls']['observations'][0][field]=None
            with self.subTest(field=field), self.assertRaises(ValueError):
                owner.verify(**f,manifest=changed)
        for field in ('rom','mapping','index','objects'):
            bad=dict(f)
            if field=='rom':
                rom=bytearray(f['rom']);rom[C-base.match.ROM_BASE+2:C-base.match.ROM_BASE+4]=bytes.fromhex('0121');bad[field]=bytes(rom)
            elif field=='mapping':
                rows=json.loads(f[field]);rows[-1]['end']=f'0x{C+18:08X}';bad[field]=json.dumps(rows).encode()
            elif field=='index': bad[field]=f[field].replace(f'{C+20:08X}'.encode(),f'{C+18:08X}'.encode())
            else: bad[field]=b'{"object":"0x02000000"}'
            with self.subTest(input=field), self.assertRaises(ValueError):
                owner.verify(**bad,manifest=manifest)

    def test_bound_context_and_decoder_disagreement(self):
        f=self.fixture();proof=transparent.BgAffineTransparentLeafProof(f['rom'],f['mapping'],f['index'],f['objects'])
        with self.assertRaisesRegex(ValueError,'exact active root'):
            proof.check_scratch_call(A,A,A,C,{base.match.ARM_REG_R3})
        # Feed only the known load encoding with inconsistent implicit effects.
        class Forged:
            size=2
            bytes=bytes.fromhex('805e')
            def regs_access(self): return (),()
        with self.assertRaisesRegex(ValueError,'inconsistent implicit'):
            transparent.effects(Forged())

    def test_explicit_selector_and_unambiguous_report(self):
        marker=f'* verification: `{buffers.BG_AFFINE_TRANSPARENT_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker),buffers.BG_AFFINE_TRANSPARENT_SELECTOR)
        self.assertTrue(owner.selected(marker))
        with self.assertRaises(ValueError):
            owner.selected(marker+f'* verification: `{buffers.BG_AFFINE_SCRATCH_SCHEMA}`\n')
        def capture(parser,*args,**kwargs):
            choices=next(a.choices for a in parser._actions if a.dest=='owner_runtime_profile')
            self.assertIn(buffers.BG_AFFINE_TRANSPARENT_SELECTOR,choices)
            raise RuntimeError('captured')
        with patch.object(argparse.ArgumentParser,'parse_args',capture), self.assertRaisesRegex(RuntimeError,'captured'):
            base.match.main()


if __name__=='__main__': unittest.main()
