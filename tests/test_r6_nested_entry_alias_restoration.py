"""Nested opaque entry values require killing writes and complete native frames."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import unittest

from test_r6_target_external_alignment import aligned_fixture, A, W, C, bl
from test_static_callback_r6_frame import L, U
import match
import owner_admission_profile as owner
import static_callback_r6_frame_profile as policy

SELECTOR = 'static-callback-restoring-entry-aliases-aligned-v1'
BODY = bytes.fromhex('60b50025161c') + bl(L+6, U) + bytes.fromhex('60bc02bc0847')


def fixture(body=BODY):
    callback = bytes.fromhex('10b50c1c0021') + bl(C+6, L)
    callback += bytes.fromhex('211c01220a60002010bc02bc0847')
    values = aligned_fixture(callback=callback, leaf=body)
    helper = bytes.fromhex('07207047')
    rom = bytearray(values['rom'])
    rom[U-match.ROM_BASE:U-match.ROM_BASE+len(helper)] = helper
    rows = json.loads(values['mapping'])
    rows.append(dict(rom=f'0x{U:08X}', end=f'0x{U+len(helper):08X}', mode='thumb', instrs=2))
    values.update(rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=values['index']+f'{U:08X} {U+len(helper):08X} {len(helper)} 2 return\n'.encode(),
        selector=SELECTOR)
    return values


class NestedEntryAliasTests(unittest.TestCase):
    def test_nested_killed_entry_alias_is_restored_by_authenticated_complete_frame(self):
        values = fixture()
        manifest, instructions = owner.verify(**values)
        self.assertTrue(instructions)
        evidence = manifest['proof']['buffers']['r6_restoration']
        rows = [row['entry_alias_restoration'] for row in evidence['observations']
                if 'entry_alias_restoration' in row]
        self.assertTrue(any(row['address'] == L and 6 in row['registers'] for row in rows))
        self.assertTrue(all(row['calls_with_live_entry_values'] == [] for row in rows))
        self.assertEqual(evidence['policy']['selector'], SELECTOR)
        self.assertEqual(evidence['policy']['source_sha256']['static_callback_r6_frame_profile.py'],
            hashlib.sha256(Path(policy.__file__).read_bytes()).hexdigest())
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['r6_restoration']['observations'][0]['body_sha256'] = '0'*64
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, manifest=changed)

    def test_old_profile_retains_instruction_wide_watches(self):
        with self.assertRaisesRegex(ValueError, 'live alias register'):
            owner.verify(**dict(fixture(), selector=policy.COMPACT_CLOSURE_SELECTOR))

    def test_unsaved_clobber_is_rejected(self):
        body = bytes.fromhex('00b5161c') + bl(L+4, U) + bytes.fromhex('01bc0047')
        with self.assertRaisesRegex(ValueError, 'restore'):
            owner.verify(**fixture(body))

    def test_altered_restore_registers_are_rejected(self):
        body = BODY[:-6] + bytes.fromhex('30bc02bc0847')
        with self.assertRaises(ValueError):
            owner.verify(**fixture(body))

    def test_missing_restoration_on_one_return_path_is_rejected(self):
        # BEQ selects the second return; it pops the saved values into R4/R5.
        body = BODY[:-6] + bytes.fromhex('002802d060bc02bc084730bc02bc0847')
        with self.assertRaises(ValueError):
            owner.verify(**fixture(body))

    def test_saved_slot_corruption_reload_and_escape_are_rejected(self):
        for access in ('00200090', '0098', '6846'):
            body = BODY[:6] + bytes.fromhex(access) + bl(L+6+len(bytes.fromhex(access)), U) + BODY[-6:]
            with self.subTest(access=access), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_observed_entry_or_live_entry_across_call_is_rejected(self):
        for prefix in ('60b5301c00250026', '60b50025'):
            body = bytes.fromhex(prefix) + bl(L+len(bytes.fromhex(prefix)), U)
            body += bytes.fromhex('002660bc02bc0847')
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                owner.verify(**fixture(body))

    def test_saved_entry_value_cannot_return_in_an_untracked_result_register(self):
        for register in range(4):
            body = bytes.fromhex('60b540b40025161c') + bl(L+8, U)
            epilogue = '60bc08bc1847' if register == 1 else '60bc02bc0847'
            body += struct.pack('<H', 0xbc00 | (1 << register)) + bytes.fromhex(epilogue)
            values = fixture(body)
            proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                values['objects'], policy=SELECTOR)
            with self.subTest(register=register), self.assertRaisesRegex(ValueError, 'entry alias.*return|opaque live entry alias'):
                proof._restore_entry_aliases(L, (policy.REGISTER,), {})

    def test_saved_entry_cannot_be_restored_into_pc_or_copied_to_r12(self):
        for suffix in ('00bd', '01bc844660bc02bc0847'):
            body = bytes.fromhex('60b540b40025161c') + bl(L+8, U) + bytes.fromhex(suffix)
            values = fixture(body)
            proof = policy.R6FrameCallbackProof(values['rom'], values['mapping'], values['index'],
                values['objects'], policy=SELECTOR)
            with self.subTest(suffix=suffix), self.assertRaisesRegex(ValueError, 'entry alias.*return|opaque live entry alias'):
                proof._restore_entry_aliases(L, (policy.REGISTER,), {})


if __name__ == '__main__':
    unittest.main(verbosity=2)
