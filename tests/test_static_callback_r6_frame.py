"""New synthetic composition boundaries; no extracted ROM or compiler workflow."""
import argparse
import copy
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

CASE = Path(__file__).resolve().parents[1]
BASE = CASE.parents[1]
sys.dont_write_bytecode = True
sys.path[:0] = [str(CASE/'tools'), str(BASE/'repos/fftadecomp-kit/tools')]

import match
import owner_admission_profile as owner
import function_thunk_profile as thunk
import static_callback_target_preservation_profile as r7
import static_callback_r6_frame_profile as policy

A, W, L, C, U = 0x08008000, 0x08010000, 0x08011000, 0x08012000, 0x08013000


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xf000 | ((delta >> 12) & 0x7ff),
                       0xf800 | ((delta >> 1) & 0x7ff))


def fixture(*, worker=None, callback=None, leaf=None):
    # Initialized local output, hoisted callback in R6, two worker uses with
    # an intervening ordinary no-buffer leaf call. The worker saves R6 before
    # replacing it with the root-local payload, and restores R6 on return.
    root = bytearray.fromhex('50b581b0004e00200090311c6a46')
    calls = []
    def call(target):
        calls.append([len(root), f'func_{target:08X}'])
        root.extend(bl(A+len(root), target))
    call(W)
    root.extend(bytes.fromhex('0099'))
    call(L)
    root.extend(bytes.fromhex('311c6a46'))
    call(W)
    root.extend(bytes.fromhex('009901b050bc01bc0047'))
    if len(root) % 4:
        root.extend(b'\0\0')
    literal = len(root)
    root.extend(struct.pack('<I', C+1))
    struct.pack_into('<H', root, 4, 0x4e00 | ((A+literal-((A+8) & ~3))//4))
    worker = worker if worker is not None else (bytes.fromhex('d0b50f1c161c311c') +
        bl(W+8, r7.THUNK) + bytes.fromhex('d0bc01bc0047'))
    bodies = {A: bytes(root), W: worker,
              L: leaf if leaf is not None else bytes.fromhex('07207047'),
              C: callback if callback is not None else bytes.fromhex('01220a6000207047')}
    rom = bytearray(thunk.END-match.ROM_BASE)
    for number, address in enumerate(thunk.ALIASES.values()):
        struct.pack_into('<HH', rom, address-match.ROM_BASE, 0x4700+(number << 3), 0x46c0)
    for address, data in bodies.items():
        rom[address-match.ROM_BASE:address-match.ROM_BASE+len(data)] = data
    rows = [dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}',
                 mode='thumb', instrs=0) for address, data in bodies.items()]
    rows += [dict(rom=f'0x{address:08X}', end=f'0x{address+2:08X}', mode='thumb', instrs=1)
             for address in thunk.ALIASES.values()]
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                    f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                    for row in rows).encode()
    return dict(data=bytes(root), address=A, rom=bytes(rom), mapping=json.dumps(rows).encode(),
                index=index, objects=b'{}', selector=policy.SELECTOR,
                bindings=dict(calls=calls, data=[], functions=[[literal, f'func_{C:08X}']], switches=[]))


def replay(**changes):
    return owner.verify(**fixture(**changes))


class CompositionTests(unittest.TestCase):
    def test_complete_saved_frame_and_intervening_no_buffer_call(self):
        manifest, instructions = replay()
        self.assertTrue(instructions)
        self.assertEqual(manifest['profile'], policy.SCHEMA)
        evidence = manifest['proof']['buffers']['r6_restoration']
        observations = evidence['observations']
        self.assertEqual({row['target'] for row in observations}, {W, L})
        self.assertEqual(len(observations), 3)
        self.assertTrue(all(row['value'] == C+1 for row in observations))
        worker = next(row for row in observations if row['target'] == W)
        self.assertEqual(worker['frame']['external_calls'], 'complete-native-callee-preservation-v1')
        self.assertEqual(worker['calls'][0]['target'], r7.THUNK)
        self.assertEqual(worker['calls'][0]['certificate']['address'], C)

    def test_loop_replays_same_callback_site_without_numeric_postcondition(self):
        # The callback's actual scalar result stays unknown. Both the exit and
        # backwards edge are checked; preservation is not a termination claim.
        body = (bytes.fromhex('d0b50f1c161c311c') + bl(W+8, r7.THUNK) +
                bytes.fromhex('002800d0f9e7d0bc01bc0047'))
        manifest, _ = replay(worker=body)
        evidence = manifest['proof']['buffers']['r6_restoration']['observations']
        self.assertEqual({row['target'] for row in evidence}, {W, L})
        self.assertEqual(len([row for row in evidence if row['target'] == W]), 2)

    def test_structural_phase_restored_after_error_and_descriptor_words_refused(self):
        values = fixture()
        proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                            values['objects'], policy=policy.SELECTOR)
        with self.assertRaisesRegex(ValueError, 'no verified return'):
            proof.inspect(W, bytes.fromhex('c046'))
        self.assertTrue(match._ordinary_call_replay(proof))
        self.assertEqual(proof._frames, [])
        with self.assertRaisesRegex(ValueError, 'without descriptor words'):
            proof.check_arguments(L, {}, [], {}, frozenset(), site=A, words={0: ('pointer', -4)})
        with self.assertRaisesRegex(ValueError, 'active ordinary caller'):
            proof.check_arguments(r7.THUNK, {}, [], {}, frozenset(), site=A,
                                  constants={r7.REGISTER: C+1})

    def test_old_selector_keeps_its_r6_constant_loss(self):
        values = fixture(); values['selector'] = r7.SELECTOR
        with self.assertRaisesRegex(ValueError, 'exact Thumb function pointer'):
            owner.verify(**values)

    def test_wrong_policy_and_subclass_do_not_gain_replay_hook(self):
        values = fixture()
        with self.assertRaises(ValueError):
            policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                        values['objects'], policy=r7.SELECTOR)
        class Other(policy.R6FrameCallbackProof):
            pass
        other = Other(values['rom'], values['mapping'], values['index'], values['objects'], policy=policy.SELECTOR)
        self.assertFalse(match._ordinary_call_replay(other))

    def test_callback_saved_register_or_sp_write_is_refused(self):
        for body in ('002601220a6000207047', '81b001220a6001b000207047'):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, 'unwritten register or SP'):
                replay(callback=bytes.fromhex(body))

    def test_buffer_bounds_and_escape_guards_remain(self):
        for body, error in [('01228a6000207047', 'outside allocated'),
                            ('016000207047', 'pointer use or escape')]:
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, error):
                replay(callback=bytes.fromhex(body))

    def test_unbound_nested_call_refused(self):
        body = bytes.fromhex('00b5') + bl(C+2, L) + bytes.fromhex('01bc0047')
        with self.assertRaisesRegex(ValueError, 'no-call callback'):
            replay(callback=body)

    def test_saved_slot_corruption_and_missing_restore_refused(self):
        for body in ('d0b500200090d0bc01bc0047', '00267047'):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, 'saved register|restore SP'):
                replay(leaf=bytes.fromhex(body))

    def test_unwritten_replay_guard_and_original_lr_return_remain_required(self):
        for body, error in [('83467047', 'live alias register'),
                            ('0047', 'indirect control flow')]:
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, error):
                replay(leaf=bytes.fromhex(body))

    def test_incomplete_owner_overlap_and_stale_text_refused(self):
        values = fixture()
        rows = json.loads(values['mapping'])
        mutations = []
        short = copy.deepcopy(rows); short[1]['end'] = f'0x{W+14:08X}'
        mutations.append(dict(mapping=json.dumps(short).encode()))
        overlap = copy.deepcopy(rows); overlap.append(dict(rom=f'0x{W+2:08X}', end=f'0x{W+4:08X}', mode='thumb', instrs=1))
        mutations.append(dict(mapping=json.dumps(overlap).encode()))
        mutations.append(dict(index=values['index'].replace(f'{W:08X} {W+18:08X}'.encode(), f'{W:08X} {W+16:08X}'.encode())))
        for changes in mutations:
            with self.subTest(changes=tuple(changes)), self.assertRaises(ValueError):
                owner.verify(**dict(values, **changes))

    def test_result_identity_aliases_site_value_and_one_use(self):
        values = fixture()
        stack = [(False, False, True)]
        for mutation in ('copy', 'aliases', 'site', 'target', 'value', 'reuse'):
            proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                                                values['objects'], policy=policy.SELECTOR)
            constants = {policy.REGISTER: C+1}
            result = proof.check_arguments(L, {}, stack, {}, frozenset(), constants=constants, site=A)
            finish = dict(site=A, target=L)
            if mutation == 'copy': result = dict(result)
            elif mutation == 'aliases': result[match.ARM_REG_R0] = -4
            elif mutation == 'site': finish['site'] += 2
            elif mutation == 'target': finish['target'] = W
            elif mutation == 'value': constants[policy.REGISTER] = C+3
            if mutation in ('aliases', 'site', 'target', 'value'):
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    proof.finish_call_constants(constants, result, **finish)
            else:
                proof.finish_call_constants(constants, result, **finish)
                if mutation == 'reuse':
                    self.assertEqual(constants[policy.REGISTER], C+1)
                    proof.finish_call_constants(constants, result, **finish)
                self.assertNotIn(policy.REGISTER, constants)

    def test_selector_cli_report_and_private_source_binding(self):
        argv = ['match.py', '--root', str(CASE/'scratch'), '--owner-runtime-profile', policy.SELECTOR, f'0x{A:08X}']
        with patch.object(sys, 'argv', argv), patch.object(owner, 'issue', return_value=19) as issue:
            self.assertEqual(match.main(), 19)
        self.assertEqual(issue.call_args.args[2].owner_runtime_profile, policy.SELECTOR)
        marker = f'* verification: `{policy.SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), policy.SELECTOR)
        manifest = policy.policy_manifest()
        self.assertIn('static_callback_r6_frame_profile.py', manifest['source_sha256'])
        self.assertIn('match.py', manifest['source_sha256'])
        for malformed in (marker*2, marker+f'* verification: `{r7.SCHEMA}`\n'):
            with self.assertRaises(ValueError): owner.selected(malformed)


if __name__ == '__main__':
    unittest.main(verbosity=2)
