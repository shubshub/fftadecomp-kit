"""Incoming scratch dies at real writes before any effectful continuation."""
import copy
import json
import unittest

from test_r6_scratch_leaf_kill import fixture as leaf_fixture, N
from test_r6_target_external_alignment import A, W, bl
import match
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy
import test_static_callback_r6_target as target

SELECTOR = 'static-callback-restoring-scratch-prefix-aligned-v1'
M = N + 0x1000
PREFIX = bytes.fromhex('10b500220023') + bl(N+6, M) + bytes.fromhex('10bc01bc0047')


def fixture(body=PREFIX, helper=bytes.fromhex('07207047')):
    values = leaf_fixture(body)
    rom = bytearray(values['rom'])
    rom[M-match.ROM_BASE:M-match.ROM_BASE+len(helper)] = helper
    rows = json.loads(values['mapping'])
    rows.append(dict(rom=f'0x{M:08X}', end=f'0x{M+len(helper):08X}', mode='thumb', instrs=0))
    values.update(rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=values['index']+f'{M:08X} {M+len(helper):08X} {len(helper)} 0 return\n'.encode(),
        selector=SELECTOR)
    return values


class ScratchPrefixKillTests(unittest.TestCase):
    def test_framed_prefix_and_exact_fresh_effects_and_frame_are_required(self):
        values = fixture()
        manifest, instructions = owner.verify(**values)
        self.assertTrue(instructions)
        evidence = manifest['proof']['buffers']['r6_restoration']
        rows = evidence['scratch_prefix_kills']
        self.assertTrue(rows)
        self.assertTrue(all(row['consumer'] == W and row['site'] == W+10 and row['address'] == N for row in rows))
        self.assertTrue(all(row['complete_effects_and_frames'] for row in rows))
        observed = {row['target'] for row in evidence['observations']}
        self.assertTrue({N, M}.issubset(observed))
        self.assertEqual(evidence['policy']['selector'], SELECTOR)
        for selector in (policy.ENTRY_ALIAS_SELECTOR, policy.COMPACT_CLOSURE_SELECTOR, policy.QUARANTINE_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'no-call no-frame'):
                owner.verify(**dict(values, selector=selector))

    def test_missing_kill_and_conditional_missing_kill_are_rejected(self):
        for body in ('10b5002310bc01bc0047', '10b50023002800d0002210bc01bc0047'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                owner.verify(**fixture(bytes.fromhex(body)))

    def test_copy_save_store_and_escape_before_kill_are_rejected(self):
        for prefix in ('111c', '04b4', '0a60', '1268'):
            body = bytes.fromhex('10b5'+prefix+'00220023')
            body += bl(N+len(body), M) + bytes.fromhex('10bc01bc0047')
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_call_before_kill_and_path_without_eventual_kill_are_rejected(self):
        body = bytes.fromhex('10b5') + bl(N+2, M) + bytes.fromhex('0022002310bc01bc0047')
        for encoded in (body, bytes.fromhex('10b5002800d0fce70022002310bc01bc0047')):
            with self.subTest(body=encoded.hex()), self.assertRaises(ValueError):
                owner.verify(**fixture(encoded))

    def test_both_incoming_scratch_values_are_tracked_until_their_actual_kills(self):
        for body in (bytes.fromhex('10b5002210bc01bc0047'),
                     bytes.fromhex('10b5191c0022002310bc01bc0047'),
                     bytes.fromhex('10b508b40022002310bc01bc0047'),
                     bytes.fromhex('10b50022')+bl(N+4, M)+bytes.fromhex('002310bc01bc0047')):
            values = fixture(body)
            proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                values['objects'], policy=SELECTOR)
            with self.subTest(body=body.hex()), self.assertRaisesRegex(ValueError, 'scratch prefix'):
                proof._scratch_prefix_kill(N, {match.ARM_REG_R0+2, match.ARM_REG_R0+3}, consumer=W, site=W+10)

    def test_complete_frame_and_post_prefix_effects_still_reject(self):
        for body in (bytes.fromhex('00220023')+bl(N+4, M)+bytes.fromhex('7047'),
                     bytes.fromhex('10b5002200230020009010bc01bc0047'),
                     bytes.fromhex('10b581b00022002368460121906001b010bc02bc0847')):
            with self.subTest(body=body.hex()), self.assertRaises(ValueError):
                owner.verify(**fixture(body))
        with self.assertRaises(ValueError):
            owner.verify(**fixture(helper=bytes.fromhex('00267047')))

    def test_prefix_alone_or_copied_completion_does_not_discharge_replay(self):
        values = fixture()
        proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
            values['objects'], policy=SELECTOR)
        proof._scratch_prefix_kill(N, {match.ARM_REG_R0+2}, consumer=W, site=W+10)
        with self.assertRaisesRegex(ValueError, 'same-instance fresh complete effects'):
            proof.scratch_prefix_observations()
        constants = {policy.REGISTER: target.C+1}
        result = proof.check_arguments(N, {}, [(False, False, True)], {}, frozenset(),
            constants=constants, site=W+10, frame_base=-4)
        with self.assertRaisesRegex(ValueError, 'same-instance fresh complete effects'):
            proof.scratch_prefix_observations()
        proof.finish_call_constants(dict(constants), dict(result), site=W+10, target=N)
        with self.assertRaisesRegex(ValueError, 'same-instance fresh complete effects'):
            proof.scratch_prefix_observations()
        other = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
            values['objects'], policy=SELECTOR)
        other._scratch_prefix_kill(N, {match.ARM_REG_R0+2}, consumer=W, site=W+10)
        other.finish_call_constants(dict(constants), result, site=W+10, target=N)
        with self.assertRaisesRegex(ValueError, 'same-instance fresh complete effects'):
            other.scratch_prefix_observations()
        proof.finish_call_constants(dict(constants), result, site=W+10, target=N)
        self.assertTrue(proof.scratch_prefix_observations()[0]['complete_effects_and_frames'])

    def test_prefix_and_completed_frame_receipts_are_report_bound(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        for field, value in (('body_sha256', '0'*64), ('complete_effects_and_frames', []), ('registers', [])):
            changed = copy.deepcopy(manifest)
            changed['proof']['buffers']['r6_restoration']['scratch_prefix_kills'][0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**values, manifest=changed)
        result = (values['data'], manifest, 'synthetic source', values['mapping'], values['index'],
            values['objects'], values['rom'], 0, b'synthetic original identity')
        report = owner.render(A, result)
        self.assertEqual(owner.selector_for_report(report), SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(report+f'* verification: `{policy.ENTRY_ALIAS_SCHEMA}`\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
