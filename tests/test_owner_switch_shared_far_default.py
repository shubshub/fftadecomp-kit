"""Further far BLs to the owner switch's far default target (owner_switch_buffer_profile).

agbcc reaches a shared tail (the far default block, here a `return 0`) by far BL from
anywhere beyond a narrow branch's reach, a case or the code before the switch, not only from
the guard.  Every same-owner BL to that target, and only those, is walked as a jump that
loses LR, as the guard's own arm is.
"""
import contextlib
import io
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import owner_switch_buffer_profile as owner_switch
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_interposed_pool_switch as pool_tests
import test_owner_switch_far_default as far

A = far.A
FAR = far.FAR
SHARED = dict(guard=FAR, case1='movs r0, #1\nbl default')


class SharedFarDefaultTests(pool_tests.PoolFixture):
    """Unit walks over assembled owners (the far-default fixture)."""

    linked = far.FarDefaultTests.linked
    walk = far.FarDefaultTests.walk

    def sites(self, f):
        # The guard's BL sits right before the dispatch; case1's is its only other BL.
        guard = f['symbols']['dispatch'] - 4
        case1 = next(site for site, target in self.linked_branches(f).items() if site != guard)
        return guard, case1

    def linked_branches(self, f):
        import owner_graph_profile as graph
        _, _, branches, _, _ = graph.graph(f['data'], A, self.placed(f)[0])
        return dict(branches)

    def test_a_prologue_bl_to_the_default_target_is_walked(self):
        # Not only an arm: a BL before the switch to the same target is the same jump.
        f = self.fixture(guard=FAR, prelude='cmp r0, #7\nbne 1f\nbl default\n1:\n')
        proof = self.walk(f)
        arm = proof.owner_switch.evidence()['shared_far_default']
        self.assertEqual(len(arm['sites']), 2)
        self.assertEqual(arm['target'], f['symbols']['default'])
        self.assertIn(f['symbols']['dispatch'] - 4, arm['sites'])

    def test_a_case_bl_to_the_default_target_is_walked(self):
        f = self.fixture(**SHARED)
        proof = self.walk(f)
        record = proof.owner_switch.evidence()
        guard, case1 = self.sites(f)
        target = f['symbols']['default']
        self.assertNotIn('far_default', record)
        self.assertEqual(record['shared_far_default'],
                         dict(policy=owner_switch.SHARED_FAR_DEFAULT_NAME, target=target, sites=sorted((guard, case1))))
        self.assertEqual(proof.owner_switch.branches, {guard: target, case1: target})
        line, = proof.loop_replay_lines()
        self.assertIn('; ' + owner_switch.SHARED_FAR_DEFAULT_RULE.format(
            name=owner_switch.SHARED_FAR_DEFAULT_NAME, target=target,
            sites=', '.join(f'0x{site:08X}' for site in sorted((guard, case1)))), line)
        self.assertNotIn(owner_switch.FAR_DEFAULT_NAME + ')', line)

    def test_disabled_keeps_one_arm_only(self):
        with patch.object(owner_switch.SHARED_FAR_DEFAULT, 'enabled', False), \
                self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
            self.walk(self.fixture(**SHARED))
        # The single arm is unaffected by the switch.
        with patch.object(owner_switch.SHARED_FAR_DEFAULT, 'enabled', False):
            self.assertIn('far_default', self.walk(self.fixture(guard=FAR)).owner_switch.evidence())

    def test_a_single_arm_record_and_line_are_unchanged(self):
        f = self.fixture(guard=FAR)
        record = self.walk(f).owner_switch.evidence()
        self.assertNotIn('shared_far_default', record)
        self.assertEqual(set(record['far_default']), {'policy', 'site', 'target'})

    def test_bls_to_another_block_refuse(self):
        for name, change in (('case to done', dict(guard=FAR, case1='movs r0, #1\nbl done')),
                             ('one shared, one elsewhere',
                              dict(guard=FAR, case1='movs r0, #1\nbl default', case0='mov r0, sp\nbl callee\nbl done')),
                             ('case to the default without the far guard', dict(case1='movs r0, #1\nbl default'))):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
                self.walk(self.fixture(**change))

    def test_the_far_guard_is_required_even_when_targets_agree(self):
        # Two case BLs to one block, with a near guard: no far default arm, so no shared tail.
        f = self.fixture(case1='movs r0, #1\nbl far', case0='mov r0, sp\nbl callee\nbl far',
                         extra='far: movs r0, #2\nb done\n')
        with self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
            self.walk(f)

    def test_a_shared_jump_cannot_return_through_its_own_lr(self):
        # Every shared BL loses LR: a `bx lr` in the shared target is no return.
        f = self.fixture(guard='bls dispatch\nbl far', case1='movs r0, #1\nbl far', extra='far: movs r0, #0\nbx lr\n')
        with self.assertRaisesRegex(ValueError, 'non-leaf indirect control flow requires linked CFG verification'):
            self.walk(f)

    def test_the_walk_rederives_every_shared_arm(self):
        f = self.fixture(**SHARED)
        calls, words = self.linked(f)
        real = owner_switch.OwnerSwitch.__init__
        guard, case1 = self.sites(f)
        for name, change in (('moved target', lambda b: {**b, case1: b[case1] + 2}),
                             ('dropped site', lambda b: {guard: b[guard]})):
            def tampered(self, *args, _change=change, **kwargs):
                real(self, *args, **kwargs)
                self.branches = _change(dict(self.branches))
            with self.subTest(name=name), patch.object(owner_switch.OwnerSwitch, '__init__', tampered), \
                    self.assertRaisesRegex(ValueError, 'owner switch far default differs from its authenticated owner '
                                                       'graph|owner switch walk took a local BL other than its far '
                                                       'default arm|call is not a validated external direct Thumb BL'):
                self.walk(f, calls, words)

    def test_the_fingerprint_binds_the_sites(self):
        proof = self.walk(self.fixture(**SHARED))
        before = proof.fingerprint()
        record = proof.owner_switch.record
        arm = record['shared_far_default']
        for change in (dict(arm, sites=arm['sites'][:1]), dict(arm, target=0)):
            with self.subTest(change=change):
                proof.owner_switch.record = dict(record, shared_far_default=change)
                self.assertNotEqual(proof.fingerprint(), before)
        proof.owner_switch.record = record


# The far-default owner with an early `return 0` in case 0, before its 2 KB of calls: agbcc
# reaches the shared return-0 block from there by a second far BL.
SHARED_SWITCH = far.FAR_SWITCH.replace(
    "    case 0:\n        C64(1)", "    case 0:\n        if (data_02000000[2] == 9)\n            return 0;\n        C64(1)")


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativeSharedFarDefaultTests(unittest.TestCase):
    """match.py's default path on a compiled owner with two far BLs to its shared tail."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_shared_', dir=scratch)
        cls.root = far.build_far(Path(cls.temporary.name) / 'shared', SHARED_SWITCH % dict(parameters='', before=''))
        cls.code, cls.output, cls.report = data_calls.run(cls.root)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return evidence.report_matches(report, self.root, data_calls.A)

    def test_agbcc_emits_two_far_bls_to_the_shared_tail(self):
        import json
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        rom = (self.root / 'baserom.bin').read_bytes()
        mapping = (self.root / 'config/functions.json').read_bytes()
        end = int(json.loads(mapping)[0]['end'], 16)
        data = rom[data_calls.A - match.ROM_BASE:end - match.ROM_BASE]
        refinement = owner.refine(data, data_calls.A, mapping)
        switch, = refinement['word_switches']
        _, _, branches, _, _ = graph.graph(data, data_calls.A, refinement)
        target = data_calls.A + switch['default']
        self.assertEqual(len(branches), 2)
        self.assertEqual(set(dict(branches).values()), {target})
        self.assertIn(data_calls.A + switch['guard'] + 2, dict(branches))

    def test_the_owner_matches_reports_and_replays(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn('verdict MATCH - byte identical', self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        line, = [line for line in self.report.splitlines() if line.startswith(owner_switch.LINE)]
        self.assertIn('shared far default (' + owner_switch.SHARED_FAR_DEFAULT_NAME + ')', line)
        self.assertTrue(self.replays(self.report))
        with patch.object(owner_switch.SHARED_FAR_DEFAULT, 'enabled', False):
            self.assertFalse(self.replays(self.report))

    def test_disabled_refuses_at_the_second_bl(self):
        with patch.object(owner_switch.SHARED_FAR_DEFAULT, 'enabled', False), \
                patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(self.root), '--no-write', '0x08000200']), \
                contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stop:
            match.main()
        self.assertIn('owner-switch data-buffer proof: owner switch excludes local BL control', str(stop.exception.code))

    def test_a_tampered_line_fails(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.LINE))
        for change, edited in (('site', re.sub(r'BLs at 0x([0-9A-F]{8}), ', 'BLs at ', lines[at])),
                               ('target', re.sub(r'to 0x([0-9A-F]{8}), the guard', 'to 0x08000200, the guard', lines[at])),
                               ('removed', lines[at][:lines[at].index('; shared far default')])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('\n'.join(lines[:at] + [edited] + lines[at + 1:]) + '\n'))


if __name__ == '__main__':
    unittest.main()
