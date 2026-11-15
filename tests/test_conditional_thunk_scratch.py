"""Indirect calls remain closed until actual scratch pointers are killed."""
import copy
import unittest

from test_conditional_thunk_buffers import A, B, T, fixture
import match
import named_data_buffer_profile as buffers
import owner_admission_profile as owner


def scratch_fixture(extra=(0x2200,), register=2, **kwargs):
    # Store one bounded byte, leave R2/R3 as a local alias, return scalar R0.
    leaf = (0x2101, 0x7001, 0x1C00 | register, 0x2000, 0x4770)
    return dict(fixture(extra=extra, leaf=leaf, **kwargs),
                selector=buffers.THUNK_SCRATCH_SELECTOR)


class ConditionalThunkScratchTests(unittest.TestCase):
    def test_killed_r2_and_r3_have_both_independent_certificates(self):
        for register in (2, 3):
            with self.subTest(register=register):
                f = scratch_fixture(extra=(0x2000 | register << 8,), register=register)
                manifest, _ = owner.verify(**f)
                proof = manifest['proof']['buffers']
                self.assertEqual(manifest['profile'], buffers.THUNK_SCRATCH_SCHEMA)
                observations = proof['normal_return_scratch']['observations']
                self.assertEqual(len(observations), 1)
                self.assertEqual(observations[0]['projected'], [[register, -16]])
                self.assertEqual(observations[0]['consumer'], A)
                self.assertEqual(observations[0]['call_target'], B)
                self.assertEqual(proof['conditional_thunks']['observations'][0]['target'], T)
                self.assertEqual(proof['conditional_thunks']['observations'][0]['local_argument_aliases'], [])

    def test_unkilled_scratch_cannot_cross_the_callback(self):
        with self.assertRaisesRegex(ValueError, 'observes discarded return scratch'):
            owner.verify(**scratch_fixture(extra=()))

    def test_reading_scratch_before_kill_is_not_projection(self):
        # mov r1,r2 observes the returned pointer, even if R2 is killed later.
        with self.assertRaisesRegex(ValueError, 'observes discarded return scratch'):
            owner.verify(**scratch_fixture(extra=(0x1C11, 0x2200)))

    def test_one_branch_avoiding_kill_is_rejected(self):
        # cmp r0,#0; beq callback; movs r2,#0.
        with self.assertRaisesRegex(ValueError, 'observes discarded return scratch'):
            owner.verify(**scratch_fixture(extra=(0x2800, 0xD000, 0x2200)))

    def test_unobserved_early_return_and_killed_callback_path_compose(self):
        # The taken branch reaches add sp at +24; the other path kills R2
        # before the call at +20. Neither path interprets the stale pointer.
        f = scratch_fixture(extra=(0x2800, 0xD002, 0x2200))
        with self.assertRaisesRegex(ValueError, 'local stack pointer escapes'):
            owner.verify(**dict(f, selector=buffers.THUNK_SELECTOR))
        manifest, _ = owner.verify(**f)
        self.assertEqual(len(manifest['proof']['buffers']['normal_return_scratch']['observations']), 1)

    def test_old_selectors_and_result_aliases_do_not_gain_permission(self):
        f = scratch_fixture()
        # The base policy already tracks R2 until its killing write here.
        # It must retain that acceptance without receiving a projection claim.
        base, _ = owner.verify(**dict(f, selector=buffers.THUNK_SELECTOR))
        self.assertNotIn('normal_return_scratch', base['proof']['buffers'])
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, selector=buffers.SELECTOR))
        for leaf in ((0x2101, 0x7001, 0x4770),
                     (0x2101, 0x7001, 0x1C01, 0x2000, 0x4770)):
            with self.subTest(leaf=leaf), self.assertRaises(ValueError):
                owner.verify(**dict(fixture(extra=(0x2200,), leaf=leaf),
                                    selector=buffers.THUNK_SCRATCH_SELECTOR))

    def test_killed_scratch_does_not_allow_fresh_local_escape(self):
        for extra in ((0x2200, 0x4668), (0x2200, 0x466C),
                      (0x2200, 0x4668, 0x9000, 0x2000)):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                owner.verify(**scratch_fixture(extra=extra))

    def test_manifest_and_report_keep_the_new_policy_explicit(self):
        f = scratch_fixture()
        manifest, _ = owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['normal_return_scratch']['observations'][0]['projected'] = []
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, manifest=changed))
        rendered = owner.render(A, (f['data'], manifest, 'synthetic', f['mapping'],
                                   f['index'], f['objects'], f['rom'], 2, b'synthetic'))
        self.assertEqual(owner.selector_for_report(rendered), buffers.THUNK_SCRATCH_SELECTOR)
        self.assertIn('* control flow: ' + buffers.THUNK_SCRATCH_CONTROL_FLOW, rendered)
        self.assertTrue(owner.selected(rendered))

    def test_unregistered_subclass_cannot_request_call_replay(self):
        class Unregistered(buffers.ConditionalThunkScratchBufferProof):
            pass
        f = scratch_fixture()
        args = (f['rom'], f['mapping'], f['index'], f['objects'])
        self.assertTrue(match._ordinary_call_replay(buffers.ConditionalThunkScratchBufferProof(*args), T))
        self.assertFalse(match._ordinary_call_replay(Unregistered(*args), T))
        self.assertFalse(match._ordinary_call_replay(buffers.ConditionalThunkScratchBufferProof(*args), B))


if __name__ == '__main__':
    unittest.main(verbosity=2)
