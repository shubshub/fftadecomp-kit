"""Dead return scratch can be projected while live pointers remain checked."""
import copy
import json
import struct
import unittest

from test_conditional_thunk_buffers import A, B, T, bl, fixture
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

C = B + 0x40


def selective(extra=(0x2200, 0x7819, 0x2300), **kwargs):
    leaf = (0x2101, 0x7001, 0x1C02, 0x1C03, 0x2000, 0x4770)
    return dict(fixture(extra=extra, leaf=leaf, **kwargs),
                selector=buffers.THUNK_PARTIAL_SELECTOR)


def nested(leaf=(0x2001, 0x4770)):
    words = struct.unpack('<HH', bl(A + 14, C))
    f = selective(extra=(*words, 0x2200, 0x2300))
    raw = struct.pack('<' + 'H' * len(leaf), *leaf)
    rom = bytearray(f['rom'])
    rom[C-match.ROM_BASE:C-match.ROM_BASE+len(raw)] = raw
    rows = json.loads(f['mapping'])
    rows.append(dict(rom=f'0x{C:08X}', end=f'0x{C+len(raw):08X}',
                     mode='thumb', instrs=len(leaf)))
    f.update(rom=bytes(rom), mapping=json.dumps(rows).encode(),
             index=f['index'] + f'{C:08X} {C+len(raw):08X} {len(raw)} {len(leaf)} return\n'.encode())
    f['bindings']['calls'].insert(1, [14, f'func_{C:08X}'])
    return f


class SelectiveScratchTests(unittest.TestCase):
    def test_dead_r2_projected_live_r3_read_stays_bounded(self):
        manifest, _ = owner.verify(**selective())
        evidence = manifest['proof']['buffers']['normal_return_scratch']
        observation, = evidence['observations']
        self.assertEqual(observation['projected'], [[2, -16]])
        self.assertEqual(observation['retained'], [[3, -16]])
        self.assertEqual(manifest['profile'], buffers.THUNK_PARTIAL_SCHEMA)
        self.assertIn('observed aliases remain tracked', evidence['selection'])

    def test_retained_r3_protected_save_write_is_rejected(self):
        # Local allocation is eight bytes; offset eight reaches saved R4.
        with self.assertRaisesRegex(ValueError, 'bounds|frame|saved|outside|local'):
            owner.verify(**selective(extra=(0x2200, 0x7219, 0x2300)))

    def test_live_aliases_cross_only_an_actually_checked_ordinary_helper(self):
        manifest, _ = owner.verify(**nested())
        records = manifest['proof']['buffers']['normal_return_scratch']['observations']
        first = [r for r in records if r['address'] == B]
        second = [r for r in records if r['address'] == C]
        self.assertEqual(len(first), 1)
        self.assertEqual(first[0]['projected'], [])
        self.assertEqual(first[0]['retained'], [[2, -16], [3, -16]])
        self.assertEqual(second[0]['projected'], [[2, -16], [3, -16]])
        self.assertEqual(second[0]['retained'], [])

    def test_nested_helper_access_and_return_escape_are_not_summarized_away(self):
        for leaf, message in (((0x2001, 0x7210, 0x4770), 'outside allocated local words'),
                              ((0x1C10, 0x4770), 'local argument aliases')):
            with self.subTest(leaf=leaf), self.assertRaisesRegex(ValueError, message):
                owner.verify(**nested(leaf))

    def test_live_indirect_argument_is_still_rejected(self):
        with self.assertRaisesRegex(ValueError, 'local argument aliases'):
            owner.verify(**selective(extra=(0x2200,)))

    def test_one_branch_with_live_scratch_keeps_the_alias(self):
        # cmp; beq skips the R3 kill, so the callback can receive the pointer.
        with self.assertRaises(ValueError):
            owner.verify(**selective(extra=(0x2200, 0x2800, 0xD000, 0x2300)))

    def test_read_copy_to_argument_remains_tracked(self):
        with self.assertRaisesRegex(ValueError, 'local argument aliases'):
            owner.verify(**selective(extra=(0x2200, 0x1C19, 0x2300)))

    def test_old_selectors_retain_their_distinct_contracts(self):
        f = selective()
        with self.assertRaisesRegex(ValueError, 'observes discarded return scratch'):
            owner.verify(**dict(f, selector=buffers.THUNK_SCRATCH_SELECTOR))
        base, _ = owner.verify(**dict(f, selector=buffers.THUNK_SELECTOR))
        self.assertNotIn('normal_return_scratch', base['proof']['buffers'])

    def test_manifest_report_and_exact_type_authenticate_the_selection(self):
        f = selective()
        manifest, _ = owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['normal_return_scratch']['observations'][0]['retained'] = []
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, manifest=changed))
        rendered = owner.render(A, (f['data'], manifest, 'synthetic', f['mapping'],
                                   f['index'], f['objects'], f['rom'], 2, b'synthetic'))
        self.assertEqual(owner.selector_for_report(rendered), buffers.THUNK_PARTIAL_SELECTOR)
        self.assertTrue(owner.selected(rendered))
        self.assertIn('* control flow: ' + buffers.THUNK_PARTIAL_CONTROL_FLOW, rendered)
        class Unregistered(buffers.ConditionalThunkSelectiveScratchBufferProof):
            pass
        args = f['rom'], f['mapping'], f['index'], f['objects']
        self.assertTrue(match._ordinary_call_replay(buffers.ConditionalThunkSelectiveScratchBufferProof(*args), T))
        self.assertFalse(match._ordinary_call_replay(Unregistered(*args), T))

    def test_wrong_consumer_context_is_not_a_retention_fallback(self):
        f = selective()
        proof = buffers.ConditionalThunkSelectiveScratchBufferProof(
            f['rom'], f['mapping'], f['index'], f['objects'])
        with self.assertRaisesRegex(ValueError, 'active exact callee'):
            proof.normal_return_aliases(B, B + 10, {match.ARM_REG_R0 + 2: -16})
        proof._consumers.append((B, A + 8))
        with self.assertRaisesRegex(ValueError, 'exact ordinary consumer'):
            proof.normal_return_aliases(B, B + 10, {match.ARM_REG_R0 + 2: -16})

    def test_guarded_root_byte_halfword_word_and_multiple_accesses(self):
        # Local R3 is preserved until these actual accesses and then killed.
        for opcode in (0x7819, 0x8819, 0x6819, 0x7019, 0x8019, 0x6019,
                       0xCB02, 0xC302):
            with self.subTest(opcode=opcode):
                f = selective(extra=(0x2200, opcode, 0x2300))
                manifest, _ = owner.verify(**f)
                observations = manifest['proof']['buffers']['normal_return_scratch']['observations']
                self.assertEqual(observations[0]['retained'], [[3, -16]])
        for opcode in (0x7819, 0x7019, 0xCB02, 0xC302):
            # adds r3,#8 reaches the protected save, not a local allocation.
            with self.subTest(protected=opcode), self.assertRaisesRegex(ValueError, 'allocated local'):
                owner.verify(**selective(extra=(0x2200, 0x3308, opcode, 0x2300)))

    def test_guarded_mode_composes_early_return_and_nested_aliases(self):
        f = selective(extra=(0x2800, 0xD003, 0x2200, 0x2300))
        manifest, _ = owner.verify(**f)
        projected = manifest['proof']['buffers']['normal_return_scratch']['observations'][0]['projected']
        self.assertEqual(projected, [[2, -16], [3, -16]])
        manifest, _ = owner.verify(**nested((0x7810, 0x4770)))
        self.assertEqual(len(manifest['proof']['buffers']['dependencies']), 2)


if __name__ == '__main__':
    unittest.main(verbosity=2)
