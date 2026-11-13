"""Expired root-frame R2/R3 at the root's own normal return, and nowhere else."""
import argparse
import copy
import unittest
from unittest.mock import patch

import test_buffer_discarded_return_scratch as fixtures

buffers, owner, match = fixtures.buffers, fixtures.owner, fixtures.match
A = fixtures.A
ESCAPE = 'escapes through a return register'


class RootReturnScratchTests(unittest.TestCase):
    setUp = fixtures.DiscardedReturnScratchTests.setUp
    fixture = fixtures.DiscardedReturnScratchTests.fixture

    def owner(self, selector=buffers.ROOT_SCRATCH_SELECTOR, **changes):
        # The callee leaves the caller's buffer pointer in R3; the caller never
        # rewrites R3, so the root returns with its expired frame address there.
        return dict(self.fixture(**changes), selector=selector)

    def test_existing_selectors_keep_refusing_the_root_scratch(self):
        for selector in (buffers.DATAFREE_SELECTOR,):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, ESCAPE):
                owner.verify(**self.owner(selector))

    def test_root_return_projection_and_fresh_manifest(self):
        f = self.owner()
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['profile'], buffers.ROOT_SCRATCH_SCHEMA)
        scratch = manifest['proof']['buffers']['root_return_scratch']
        self.assertEqual(scratch['registers'], [2, 3])
        self.assertEqual(scratch['address'], A)
        self.assertEqual(scratch['observations'], [[scratch['return_sites'][0], 3, -16]])
        self.assertEqual(scratch['dead_joins'], [])
        self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)
        altered = copy.deepcopy(manifest)
        altered['proof']['buffers']['root_return_scratch']['observations'] = []
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**f, manifest=altered)

    def test_selector_requires_an_actual_projection(self):
        with self.assertRaisesRegex(ValueError, 'actual projected root-frame alias'):
            owner.verify(**self.owner(after='movs r3, #0'))

    def test_result_registers_still_refuse(self):
        # A pointer returned in R0 (or the R1 half of a 64-bit result) is a real escape.
        for after, register in (('adds r0, r3, #0', 'r1'), ('adds r1, r3, #0', 'r0')):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, ESCAPE):
                owner.verify(**self.owner(after=after, return_register=register))

    def test_root_uses_before_return_stay_checked(self):
        f = self.owner(after='ldr r0, [r3]')
        self.assertTrue(owner.verify(**f)[0]['proof']['buffers']['root_return_scratch']['observations'])
        for after, error in (('str r3, [r1]', 'escape'),
                             ('ldr r0, [r3, #16]', 'outside'),
                             ('push {r3}\npop {r3}', 'pushed')):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, error):
                owner.verify(**self.owner(after=after))

    def test_scratch_passed_to_a_later_call_is_replayed_not_discarded(self):
        f = self.owner(after='bl child')
        manifest, _ = owner.verify(**f)
        self.assertIn(fixtures.C, {row['address'] for row in manifest['proof']['buffers']['dependencies']})
        with self.assertRaisesRegex(ValueError, 'escape'):
            owner.verify(**self.owner(after='bl child\nstr r3, [r1]'))

    def test_callee_own_frame_pointer_at_callee_return_still_refuses(self):
        callee = 'push {lr}\nsub sp, #8\nmov r2, sp\nstrh r0, [r3]\nadd sp, #8\npop {r0}\nbx r0'
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08010100: local stack pointer ' + ESCAPE):
            owner.verify(**self.owner(callee=callee))

    def test_dead_join_reaching_root_return_and_observed_joins(self):
        join = 'cmp r0, #0\nbeq done\nadd r3, sp, #4\ndone:\n'
        with self.assertRaisesRegex(ValueError, 'inconsistent possible pointer offsets'):
            owner.verify(**self.owner(buffers.DATAFREE_SELECTOR, after=join))
        # The join drop alone leaves no final-state projection. An observation made
        # from an intermediate fixpoint state must not satisfy the guard.
        with self.assertRaisesRegex(ValueError, 'actual projected root-frame alias'):
            owner.verify(**self.owner(after=join))
        f = self.owner(after=join + 'mov r2, sp')
        manifest, _ = owner.verify(**f)
        scratch = manifest['proof']['buffers']['root_return_scratch']
        self.assertTrue(scratch['dead_joins'])
        self.assertTrue(all(row[1:] == [3, -16, -12] for row in scratch['dead_joins']))
        self.assertEqual(scratch['observations'], [[scratch['return_sites'][0], 2, -16]])
        self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)
        for tail in ('ldr r0, [r3]', 'bl child', 'adds r0, r3, #0'):
            with self.subTest(tail=tail), self.assertRaisesRegex(ValueError, 'inconsistent possible pointer offsets'):
                owner.verify(**self.owner(after=join + tail))

    def test_final_state_projection_is_overwritten_per_return_site(self):
        f = self.owner()
        r3 = match.ARM_REG_R0 + 3
        proof = buffers.RootReturnScratchBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        proof.bind_return_root(A, f['data'])
        site = next(iter(proof._return_root[2]))
        proof.root_return_aliases(f['data'], A, site, {r3: -16})   # intermediate state
        proof.root_return_aliases(f['data'], A, site, {})          # final state: nothing left
        with self.assertRaisesRegex(ValueError, 'actual projected root-frame alias'):
            proof.root_scratch_manifest()

    def test_hooks_are_closed_to_other_proofs_and_contexts(self):
        f = self.owner()
        r2, r3 = match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3
        plain = buffers.NamedDataBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        self.assertEqual(buffers.root_return_scratch_aliases(plain, f['data'], A, A, {r3: -16}), {r3: -16})
        proof = buffers.RootReturnScratchBufferProof(f['rom'], f['mapping'], f['index'], f['objects'])
        with self.assertRaisesRegex(ValueError, 'bound root context'):
            proof.root_return_aliases(f['data'], A, A, {r3: -16})
        proof.bind_return_root(A, f['data'])
        site = next(iter(proof._return_root[2]))
        self.assertEqual(proof.root_return_aliases(f['data'], A, site, {r2: -8, r3: -16}), {})
        for args in ((f['data'], A, site + 2, {r3: -16}),          # not a return site
                     (f['data'], fixtures.B, site, {r3: -16}),     # another function
                     (f['data'], A, site, {r3: 0}),               # not the expired frame
                     (f['data'], A, site, {r3: 4})):
            with self.subTest(args=args):
                self.assertEqual(proof.root_return_aliases(*args), args[3])
        self.assertEqual(proof.root_return_aliases(f['data'], A, site, {match.ARM_REG_R0: -16, r3: -16}),
                         {match.ARM_REG_R0: -16})
        proof.active.add(fixtures.B)
        self.assertEqual(proof.root_return_aliases(f['data'], A, site, {r3: -16}), {r3: -16})
        with self.assertRaisesRegex(ValueError, 'exact unique complete body'):
            proof.bind_return_root(A, f['data'])

    def test_selector_report_and_render(self):
        for selector, schema, flow in (
                (buffers.ROOT_SCRATCH_SELECTOR, buffers.ROOT_SCRATCH_SCHEMA, buffers.ROOT_SCRATCH_CONTROL_FLOW),
                (buffers.THUNK_ROOT_SCRATCH_SELECTOR, buffers.THUNK_ROOT_SCRATCH_SCHEMA,
                 buffers.THUNK_ROOT_SCRATCH_CONTROL_FLOW)):
            marker = f'* verification: `{schema}`\n'
            self.assertEqual(owner.selector_for_report(marker), selector)
            for report in (marker * 2, marker + f'* verification: `{buffers.SCHEMA}`\n'):
                with self.subTest(report=report), self.assertRaises(ValueError):
                    owner.selected(report)
        f = self.owner()
        manifest, instructions = owner.verify(**f)
        report = owner.render(f['address'], (f['data'], manifest, 'source', f['mapping'],
            f['index'], f['objects'], f['rom'], len(instructions), b'original ELF identity'))
        self.assertIn(f'* owner runtime: {buffers.ROOT_SCRATCH_SELECTOR}', report)
        self.assertIn(f'* control flow: {buffers.ROOT_SCRATCH_CONTROL_FLOW}', report)
        self.assertEqual(owner.selector_for_report(report), buffers.ROOT_SCRATCH_SELECTOR)

    def test_function_and_switch_bindings_are_excluded(self):
        f = self.owner()
        for field, value in (('functions', [[0, 'func_08010100']]), ('switches', [[0, 4]])):
            bindings = copy.deepcopy(f['bindings'])
            bindings[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                owner.verify(**dict(f, bindings=bindings))

    def test_cli_selects_both_profiles(self):
        parse = argparse.ArgumentParser.parse_args
        class Parsed(Exception):
            pass
        for selector in (buffers.ROOT_SCRATCH_SELECTOR, buffers.THUNK_ROOT_SCRATCH_SELECTOR):
            def capture(parser, *args, **kwargs):
                parsed = parse(parser, ['0x08010000', '--owner-runtime-profile', selector])
                self.assertEqual(parsed.owner_runtime_profile, selector)
                raise Parsed
            with self.subTest(selector=selector), \
                    patch.object(argparse.ArgumentParser, 'parse_args', capture), self.assertRaises(Parsed):
                buffers.match.main()


class ConditionalThunkRootScratchTests(unittest.TestCase):
    """End-to-end thunk composition on the conditional-thunk fixture."""

    def thunk(self, **kwargs):
        from test_conditional_thunk_scratch import scratch_fixture
        return dict(scratch_fixture(**kwargs), selector=buffers.THUNK_ROOT_SCRATCH_SELECTOR)

    def test_uncleared_alias_crossing_the_callback_is_refused(self):
        with self.assertRaises(ValueError):
            owner.verify(**self.thunk(extra=()))

    def test_scratch_cleared_before_the_callback_projects_nothing(self):
        with self.assertRaisesRegex(ValueError, 'actual projected root-frame alias'):
            owner.verify(**self.thunk())

    def test_early_return_alias_is_projected_and_manifest_replays(self):
        for register in (2, 3):
            with self.subTest(register=register):
                f = self.thunk(register=register, extra=(0x2800, 0xD002, 0x2000 | register << 8))
                with self.assertRaisesRegex(ValueError, ESCAPE):
                    owner.verify(**dict(f, selector=buffers.THUNK_SELECTOR))
                manifest, _ = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.THUNK_ROOT_SCRATCH_SCHEMA)
                scratch = manifest['proof']['buffers']['root_return_scratch']
                self.assertEqual([row[1:] for row in scratch['observations']], [[register, -16]])
                self.assertTrue(manifest['proof']['buffers']['conditional_thunks']['observations'])
                self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)

    def test_copy_to_r0_before_early_return_is_refused(self):
        # mov r0, r2 makes the result register a root-frame address on the early path;
        # the callback path clears both R0 and R2 so only the return can refuse.
        with self.assertRaisesRegex(ValueError, ESCAPE):
            owner.verify(**self.thunk(extra=(0x4610, 0x2800, 0xD003, 0x2200, 0x2000)))
        # Control: the same shape without the copy is admitted through R2 alone.
        manifest, _ = owner.verify(**self.thunk(extra=(0x2800, 0xD003, 0x2200, 0x2000)))
        self.assertEqual([row[1:] for row in manifest['proof']['buffers']['root_return_scratch']['observations']],
                         [[2, -16]])


if __name__ == '__main__':
    unittest.main()
