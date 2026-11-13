"""Exact BIOS local spans composed with authenticated discarded helper scratch."""
import copy
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import json
import struct
import unittest
from unittest.mock import patch

import bios_bg_affine_set_profile as affine
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_bg_affine_set as legacy

A, B = legacy.A, legacy.B
match = legacy.match
bl = legacy.fixtures.fixtures.fixtures.bl
indexes = legacy.fixtures.fixtures.fixtures.indexes


class BgAffineSetScratchTests(legacy.BgAffineSetTests):
    # Reuse the existing frame/count/wrapper hostility tests against the composition.
    def fixture(self, after=(), helper=None, **kwargs):
        f = super().fixture(**kwargs)
        original = f['data']
        # Keep the real BIOS prefix, then pass its destination to an ordinary helper.
        cut = len(original) - 6
        helper = helper if helper is not None else bytes.fromhex('031c002018807047')
        body = original[:cut] + bytes.fromhex('05a8')
        call_site = A + len(body)
        body += bl(call_site, B)
        for token in after:
            body += bl(A+len(body), B) if token == 'call' else struct.pack('<H', token)
        body += original[cut:]
        rows = json.loads(f['mapping'])
        rows[0].update(end=f'0x{A+len(body):08X}', instrs=0)
        rows[1].update(end=f'0x{B+len(helper):08X}', instrs=0)
        mapping, index = indexes(rows)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[B-match.ROM_BASE:B-match.ROM_BASE+len(helper)] = helper
        calls = f['bindings']['calls'] + [[call_site-A, f'func_{B:08X}']]
        if 'call' in after:
            calls += [[call_site-A+4+2*after.index('call'), f'func_{B:08X}']]
        return dict(f, data=body, rom=bytes(rom), mapping=mapping, index=index,
            selector=buffers.BG_AFFINE_SCRATCH_SELECTOR,
            bindings=dict(f['bindings'], calls=calls))

    def test_positive_replay_and_report_selector(self):
        for after in ((), (0x2300,), (0xE7FF,)):
            with self.subTest(after=after):
                f = self.fixture(after=after)
                manifest, _ = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.BG_AFFINE_SCRATCH_SCHEMA)
                proof = manifest['proof']['buffers']
                self.assertEqual(proof['bios_bg_affine_set']['sites'][0][3], 1)
                row = proof['normal_return_scratch']['observations'][0]
                self.assertEqual(row['projected'][0][0], 3)
                self.assertEqual(row['consumer'], A)
                self.assertEqual(row['call_target'], B)
                self.assertGreater(row['continuation_states'], 0)
                self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)
        marker = f'* verification: `{buffers.BG_AFFINE_SCRATCH_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), buffers.BG_AFFINE_SCRATCH_SELECTOR)
        self.assertTrue(owner.selected(marker))
        with self.assertRaises(ValueError):
            owner.selected(marker + f'* verification: `{buffers.BG_AFFINE_SCHEMA}`\n')

    def test_legacy_refuses_identical_helper_return(self):
        with self.assertRaisesRegex(ValueError, 'local stack pointer escapes through a return register'):
            owner.verify(**dict(self.fixture(), selector=buffers.BG_AFFINE_SELECTOR))
        with self.assertRaisesRegex(ValueError, 'actual checked projections'):
            owner.verify(**self.fixture(helper=bytes.fromhex('00207047')))

    def test_reads_stores_calls_and_branch_observations_before_kill(self):
        for after in ((0x6818,), (0x600B,), (0x1C1A,), ('call', 0x2300),
                      (0x2800, 0xD000, 0x2300, 0x6818)):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, 'consumer observes'):
                owner.verify(**self.fixture(after=after))

    def test_r0_r1_return_aliases_are_never_projected(self):
        for helper in (bytes.fromhex('031c7047'), bytes.fromhex('011c00207047')):
            with self.subTest(helper=helper.hex()), self.assertRaisesRegex(ValueError, 'escapes through a return register'):
                f = self.fixture(helper=helper)
                if helper == bytes.fromhex('031c7047'):
                    data = f['data'][:-4] + bytes.fromhex('02bc0847')
                    rom = bytearray(f['rom'])
                    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
                    f = dict(f, data=data, rom=bytes(rom))
                owner.verify(**f)

    def test_exact_active_callee_site_and_context(self):
        f = self.fixture()
        proof = affine.BgAffineSetScratchProof(f['rom'], f['mapping'], f['index'], f['objects'])
        aliases = {match.ARM_REG_R3: -20}
        site = A + f['bindings']['calls'][-1][0]
        for contexts in ([], [(B+2, site)], [(B, None)], [(B, A)], [(B, site+2)]):
            proof._consumers = contexts
            with self.subTest(contexts=contexts), self.assertRaises(ValueError):
                proof.normal_return_aliases(B, B+6, aliases)
        proof.bind_root(f['data'], A, {A+offset:int(name[5:],16) for offset,name in f['bindings']['calls']})
        with self.assertRaisesRegex(ValueError, 'exact bound root call'):
            proof.check_call(B, {}, [], site=A)

    def test_scratch_manifest_tampering_and_stale_consumer(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        for field in ('call_site', 'consumer_sha256', 'projected', 'call_target'):
            changed = copy.deepcopy(manifest)
            changed['proof']['buffers']['normal_return_scratch']['observations'][0][field] = None
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**f, manifest=changed)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['normal_return_scratch']['source_sha256']['match.py'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**f, manifest=changed)
        stale = self.fixture(after=(0x2300,))
        with self.assertRaises(ValueError):
            owner.verify(**stale, manifest=manifest)

    def test_explicit_cli_choice(self):
        import argparse
        def capture(parser, *args, **kwargs):
            choices = next(a.choices for a in parser._actions if a.dest == 'owner_runtime_profile')
            self.assertIn(buffers.BG_AFFINE_SCRATCH_SELECTOR, choices)
            raise RuntimeError('captured')
        with patch.object(argparse.ArgumentParser, 'parse_args', capture):
            with self.assertRaisesRegex(RuntimeError, 'captured'):
                match.main()


if __name__ == '__main__':
    unittest.main()
