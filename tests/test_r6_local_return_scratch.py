"""Local R2/R3 scratch needs the actual complete unobserving consumer."""
import copy
import json
import unittest

from test_r6_target_external_alignment import aligned_fixture, A, W, bl
import test_static_callback_r6_target as target
import static_callback_r6_frame_profile as policy
import owner_admission_profile as owner
import match

L = target.L
LOCAL = bytes.fromhex('00b581b06a4601b001bc0047')


def fixture(leaf=LOCAL, continuation='0022'):
    worker = bytes.fromhex('70b50e1c151c') + bl(W+6, L)
    worker += bytes.fromhex(continuation+'291c') + bl(W+14, target.THUNK)
    worker += bytes.fromhex('70bc01bc0047')
    values = aligned_fixture(worker=worker, leaf=leaf)
    values['selector'] = policy.LOCAL_SCRATCH_SELECTOR
    return values


class LocalScratchTests(unittest.TestCase):
    def test_complete_local_frame_and_actual_consumer_are_replayed(self):
        values = fixture()
        manifest, instructions = owner.verify(**values)
        self.assertTrue(instructions)
        self.assertEqual(manifest['profile'], policy.LOCAL_SCRATCH_SCHEMA)
        evidence = manifest['proof']['buffers']['r6_restoration']
        self.assertIn('local_return_scratch', evidence['policy'])
        self.assertTrue(any(row['address'] == L and row['consumer'] == W
                            for row in evidence['normal_return_scratch']))
        row = next(row for row in evidence['observations'] if row['target'] == L)
        self.assertEqual(row['frame']['discarded_exit_scratch']['registers'], [2, 3])
        for selector in policy.ALIGNED_POLICIES:
            if selector in policy.LOCAL_SCRATCH_POLICIES:
                continue
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'local stack pointer escapes'):
                owner.verify(**dict(values, selector=selector))

    def test_actual_consumer_cannot_read_scratch_or_call_before_killing_it(self):
        with self.assertRaisesRegex(ValueError, 'consumer observes'):
            owner.verify(**fixture(continuation='111c'))
        with self.assertRaisesRegex(ValueError, 'consumer observes'):
            owner.verify(**fixture(continuation='291c'))

    def test_result_registers_cannot_export_local_aliases(self):
        for leaf in ('00b581b0684601b002bc0847', '00b581b0694601b001bc0047'):
            with self.subTest(leaf=leaf), self.assertRaisesRegex(ValueError, 'local stack pointer escapes'):
                owner.verify(**fixture(bytes.fromhex(leaf)))

    def test_bounds_and_restoration_remain_required(self):
        for leaf in ('00b581b06a460120906001b001bc0047',
                     '00b581b06a46002401b001bc0047',
                     '00b581b06a4601bc0047'):
            with self.subTest(leaf=leaf), self.assertRaises(ValueError):
                owner.verify(**fixture(bytes.fromhex(leaf)))

    def test_hook_is_closed_to_exact_active_preliminary_callee(self):
        values = fixture()
        aliases = {match.ARM_REG_R0+2: -4}
        old = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                        values['objects'], policy=policy.LEAF_ALIAS_SELECTOR)
        self.assertIs(policy.structural_return_aliases(old, LOCAL, L, L+10, aliases), aliases)
        new = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                        values['objects'], policy=policy.LOCAL_SCRATCH_SELECTOR)
        with self.assertRaisesRegex(ValueError, 'exact active preliminary'):
            policy.structural_return_aliases(new, LOCAL, L, L+10, aliases)
        class Forged(policy.R6FrameCallbackProof):
            pass
        forged = Forged(values['rom'], values['mapping'], values['index'], values['objects'],
                        policy=policy.LOCAL_SCRATCH_SELECTOR)
        self.assertIs(policy.structural_return_aliases(forged, LOCAL, L, L+10, aliases), aliases)

    def test_report_and_manifest_bind_the_explicit_new_policy(self):
        values = fixture()
        manifest, _ = owner.verify(**values)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['r6_restoration']['policy']['local_return_scratch']['registers'] = [0, 1, 2, 3]
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, manifest=changed)
        result = (values['data'], manifest, 'synthetic source', values['mapping'], values['index'],
                  values['objects'], values['rom'], 0, b'synthetic original identity')
        report = owner.render(A, result)
        self.assertEqual(owner.selector_for_report(report), policy.LOCAL_SCRATCH_SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(report+f'* verification: `{policy.LEAF_ALIAS_SCHEMA}`\n')

    def test_nested_local_output_uses_the_exact_completed_effect_certificate(self):
        helper = target.C + 0x1000
        leaf = bytes.fromhex('00b581b06946') + bl(L+6, helper)
        leaf += bytes.fromhex('00216a4601b001bc0047')
        values = fixture(leaf)
        body = bytes.fromhex('01220a6000207047')
        rom = bytearray(values['rom'])
        rom[helper-match.ROM_BASE:helper-match.ROM_BASE+len(body)] = body
        rows = json.loads(values['mapping'])
        rows.append(dict(rom=f'0x{helper:08X}', end=f'0x{helper+len(body):08X}', mode='thumb', instrs=4))
        values.update(rom=bytes(rom), mapping=json.dumps(rows).encode(),
                      index=values['index']+f'{helper:08X} {helper+len(body):08X} {len(body)} 4 return\n'.encode())
        manifest, _ = owner.verify(**values)
        rows = manifest['proof']['buffers']['r6_restoration']['observations']
        row = next(row for row in rows if row['target'] == L)
        self.assertEqual(row['calls'][0]['target'], helper)
        self.assertEqual(row['calls'][0]['return_aliases'], [])
        self.assertTrue(row['frame']['local_aliases']['buffer_calls'])
        self.assertTrue(row['frame']['local_aliases']['buffer_fingerprint'])
        bad = bytearray(values['rom'])
        bad[helper-match.ROM_BASE+2:helper-match.ROM_BASE+4] = bytes.fromhex('4a60')
        with self.assertRaisesRegex(ValueError, 'outside allocated'):
            owner.verify(**dict(values, rom=bytes(bad)))

    def test_frame_adapter_requires_the_same_completed_active_replay(self):
        values = fixture()
        proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                          values['objects'], policy=policy.LOCAL_SCRATCH_SELECTOR)
        context = dict(address=L, calls={}, effects_complete=True)
        with self.assertRaisesRegex(ValueError, 'same completed effects'):
            policy.RestoringLocalBufferProof(proof, context)
        context['effects_complete'] = False
        proof._frames.append(context)
        with self.assertRaisesRegex(ValueError, 'same completed effects'):
            policy.RestoringLocalBufferProof(proof, context)


if __name__ == '__main__':
    unittest.main(verbosity=2)
