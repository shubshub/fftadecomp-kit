"""R2/R3 own-frame addresses at the plain owner switch's normal returns (owner_switch_buffer_profile).

agbcc can leave the address of a local in R2 or R3 on a path that returns early.  The owner
switch's walk (the default typed-data buffer proof) refused that as an escape.  Under the
`thumb-discarded-exit-scratch-v1` premise (R2/R3 carry no results under the agbcc Thumb ABI)
the owner's own normal returns drop and record such addresses; R0/R1 and every callee return
keep the refusal.
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
import named_data_buffer_profile as named_buffer
import owner_switch_buffer_profile as owner_switch
from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA, DISCARDED_SCRATCH_CONTRACT
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_interposed_pool_switch as pool_tests
import test_owner_switch_buffers as owner_tests
import test_owner_switch_far_default as far

A = pool_tests.A
ESCAPE = 'local stack pointer escapes through a return register'


class ExitScratchTests(pool_tests.PoolFixture):
    """Unit walks: caller pushes {r4, lr} and reserves 8 bytes, so SP+4 is entry-SP -12."""

    linked = far.FarDefaultTests.linked
    walk = far.FarDefaultTests.walk

    def returned(self, f):
        return f['symbols']['caller_end'] - 2   # the owner's only return, `bx r1`

    def test_r2_and_r3_are_dropped_and_recorded(self):
        for register in (2, 3):
            with self.subTest(register=register):
                f = self.fixture(case1=f'add r{register}, sp, #4\nmovs r0, #1')
                proof = self.walk(f)
                record = proof.owner_switch.evidence()
                self.assertEqual(record['exit_scratch'], dict(
                    schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3], contract=DISCARDED_SCRATCH_CONTRACT,
                    sites=[[self.returned(f), register, -12]]))
                switch_line, scratch_line = proof.loop_replay_lines()
                self.assertTrue(scratch_line.startswith(owner_switch.EXIT_SCRATCH_LINE + ': `' +
                                                        DISCARDED_SCRATCH_SCHEMA + '` premise, not checked: '))
                self.assertIn(f'`0x{self.returned(f):08X} r{register} -12`', scratch_line)

    def test_both_registers_on_one_return(self):
        f = self.fixture(case1='add r2, sp, #4\nadd r3, sp, #0\nmovs r0, #1')
        record = self.walk(f).owner_switch.evidence()
        self.assertEqual(record['exit_scratch']['sites'], [[self.returned(f), 2, -12], [self.returned(f), 3, -16]])

    def test_the_result_register_keeps_the_refusal(self):
        # (The fixture's epilogue pops the saved LR into R1, so R0 is the result register it can leave.)
        for case in ('add r0, sp, #4', 'add r0, sp, #4\nadd r2, sp, #0'):
            with self.subTest(case=case), self.assertRaisesRegex(ValueError, ESCAPE):
                self.walk(self.fixture(case1=case))

    def test_disabled_keeps_the_refusal(self):
        with patch.object(owner_switch.OWNER_EXIT_SCRATCH, 'enabled', False), self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(self.fixture(case1='add r2, sp, #4\nmovs r0, #1'))

    def test_an_owner_without_scratch_is_unchanged(self):
        for change in ({}, dict(guard=far.FAR)):
            with self.subTest(change=change):
                record = self.walk(self.fixture(**change)).owner_switch.evidence()
                self.assertNotIn('exit_scratch', record)
                self.assertEqual(len(self.walk(self.fixture(**change)).loop_replay_lines()), 1)

    def test_with_the_shared_far_default(self):
        f = self.fixture(guard=far.FAR, case1='add r2, sp, #4\nmovs r0, #1\nbl default')
        record = self.walk(f).owner_switch.evidence()
        self.assertIn('shared_far_default', record)
        self.assertEqual(record['exit_scratch']['sites'], [[self.returned(f), 2, -12]])

    def test_the_fingerprint_binds_the_sites(self):
        proof = self.walk(self.fixture(case1='add r2, sp, #4\nmovs r0, #1'))
        before = proof.fingerprint()
        record = proof.owner_switch.record
        scratch = record['exit_scratch']
        for change in (dict(scratch, sites=[]), dict(scratch, sites=[[scratch['sites'][0][0], 3, -12]])):
            with self.subTest(change=change):
                proof.owner_switch.record = dict(record, exit_scratch=change)
                self.assertNotEqual(proof.fingerprint(), before)
        proof.owner_switch.record = record

    def test_only_the_bound_owner_return_projects(self):
        proof = self.walk(self.fixture(case1='add r2, sp, #4\nmovs r0, #1'))
        f = self.fixture(case1='add r2, sp, #4\nmovs r0, #1')
        aliases = {match.ARM_REG_R0 + 2: -12}
        data = f['data']
        # Another body, another address, another site, or a callee walk in progress: unchanged.
        for name, call in (
                ('other site', lambda: owner_switch.exit_scratch_aliases(proof, data, A, A, aliases)),
                ('other address', lambda: owner_switch.exit_scratch_aliases(proof, data, A + 2,
                                                                                  self.returned(f), aliases)),
                ('other body', lambda: owner_switch.exit_scratch_aliases(proof, data[:-2] + b'\0\0', A,
                                                                               self.returned(f), aliases))):
            with self.subTest(name=name):
                self.assertEqual(call(), aliases)
        proof.active.add(0x08010100)
        self.assertEqual(owner_switch.exit_scratch_aliases(proof, data, A, self.returned(f), aliases), aliases)
        proof.active.clear()
        self.assertEqual(owner_switch.exit_scratch_aliases(proof, data, A, self.returned(f), aliases), {})
        # A positive (incoming-argument) offset is no own-frame address and is not projected.
        self.assertEqual(owner_switch.exit_scratch_aliases(
            proof, data, A, self.returned(f), {match.ARM_REG_R0 + 2: 4}), {match.ARM_REG_R0 + 2: 4})

    def test_the_hook_is_closed_to_other_proofs(self):
        # The default-path hook every stack-argument return calls: only the bound plain owner projects.
        f = self.fixture(case1='add r2, sp, #4\nmovs r0, #1')
        aliases = {match.ARM_REG_R0 + 2: -12}
        unbound = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                        bios_wrappers=True, copy_helper_index=f['index'],
                                        switch_callee_index=f['index'])
        self.assertEqual(owner_switch.exit_scratch_aliases(unbound, f['data'], A, self.returned(f), aliases), aliases)
        self.assertEqual(named_buffer.root_return_scratch_aliases(self.walk(f), f['data'], A, self.returned(f),
                                                                  aliases), aliases)

    def test_a_walk_split_on_r2_refuses(self):
        # Two cases leave r2 at different own-frame offsets for the one return: the plain walk keeps
        # the join apart (stack-split-join-v1), and the owner is refused rather than recorded with one.
        f = self.fixture(case1='add r2, sp, #4\nmovs r0, #1', case2='add r2, sp, #0\nmovs r0, #2')
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(f)
        # Each alone is admitted and recorded.
        for case, offset in (('case1', -12), ('case2', -16)):
            with self.subTest(case=case):
                change = {case: f'add r2, sp, #{4 if case == "case1" else 0}\nmovs r0, #1'}
                g = self.fixture(**change)
                self.assertEqual(self.walk(g).owner_switch.evidence()['exit_scratch']['sites'],
                                 [[self.returned(g), 2, offset]])

    def test_a_walk_split_on_r3_refuses(self):
        # (Reviewer case H3G.)
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(self.fixture(case1='add r3, sp, #4\nmovs r0, #1', case2='add r3, sp, #0\nmovs r0, #2'))

    def test_r2_copied_from_a_split_r12_refuses(self):
        # The join splits on R12 only (exempt at returns); after it R2 is copied from R12, so the two
        # split states reach the return with R2 at -12 and -16.  (Reviewer case H3H.)
        f = self.fixture(case1='add r0, sp, #4\nmov ip, r0\nmovs r0, #1\nb j',
                         case2='add r0, sp, #0\nmov ip, r0\nmovs r0, #2\nb j', extra='j: mov r2, ip\nb done\n')
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(f)
        # With one case only nothing splits, and the projection records its R2.
        g = self.fixture(case1='add r0, sp, #4\nmov ip, r0\nmovs r0, #1\nb j', extra='j: mov r2, ip\nb done\n')
        # (The extra block sits after the epilogue, so the return is not the fixture's last halfword.)
        sites = self.walk(g).owner_switch.evidence()['exit_scratch']['sites']
        self.assertEqual([(register, offset) for _, register, offset in sites], [(2, -12)])

    def test_a_split_on_an_unrelated_register_refuses(self):
        # R2 holds one own-frame offset on every path; only R1 is split (two locals, read after the
        # join, then overwritten).  Any split refuses the projection, so the owner is refused.
        f = self.fixture(case1='add r1, sp, #4\nadd r2, sp, #0\nmovs r0, #1\nb j',
                         case2='add r1, sp, #0\nadd r2, sp, #0\nmovs r0, #2\nb j',
                         extra='j: ldrh r3, [r1]\nmovs r1, #0\nmovs r3, #0\nb done\n')
        with self.assertRaisesRegex(ValueError, ESCAPE):
            self.walk(f)
        # The split is the only reason: with one locals pair, nothing splits and R2 is recorded.
        g = self.fixture(case1='add r1, sp, #4\nadd r2, sp, #0\nmovs r0, #1\nb j',
                         case2='add r1, sp, #4\nadd r2, sp, #0\nmovs r0, #2\nb j',
                         extra='j: ldrh r3, [r1]\nmovs r1, #0\nmovs r3, #0\nb done\n')
        proof = self.walk(g)
        self.assertFalse(any(key[0] == A for key in proof.split_joins))
        sites = proof.owner_switch.evidence()['exit_scratch']['sites']
        self.assertEqual([(register, offset) for _, register, offset in sites], [(2, -16)])

    def test_the_record_refuses_a_split_walk_too(self):
        # Defence in depth: a record made after any split refuses even if a projection slipped through.
        for register in (2, 12, 4):
            with self.subTest(register=register):
                proof = self.walk(self.fixture(case1='add r2, sp, #4\nmovs r0, #1'))
                proof.split_joins[(A, A + 0x40, match.ARM_REG_R0 + register, -12, -16)] = None
                with self.assertRaisesRegex(ValueError, 'owner exit scratch refuses a walk that kept a join apart'):
                    proof.owner_switch.record_exit_scratch(proof)
        # A split in another walk (a callee's) is not this owner's.
        proof = self.walk(self.fixture(case1='add r2, sp, #4\nmovs r0, #1'))
        proof.split_joins[(A + 0x100, A + 0x140, match.ARM_REG_R0 + 2, -12, -16)] = None
        proof.owner_switch.record_exit_scratch(proof)

    def test_binding_requires_the_plain_owner(self):
        f = self.fixture(case1='add r2, sp, #4\nmovs r0, #1')
        proof = self.walk(f)
        with self.assertRaisesRegex(ValueError, 'owner exit scratch requires the plain owner'):
            proof.owner_switch.bind_exit_scratch(proof, A, f['data'])   # already bound
        other = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                      bios_wrappers=True, copy_helper_index=f['index'], switch_callee_index=f['index'])
        with self.assertRaisesRegex(ValueError, 'owner exit scratch requires the plain owner'):
            proof.owner_switch.bind_exit_scratch(other, A, f['data'])   # not this owner's proof


# A typed-data owner whose case 1 builds two boxes on the stack and returns early: agbcc keeps
# the second box's address in a scratch register for its stores, and it is still there at the
# early `return 0`.
SCRATCH_SWITCH = data_calls.HEADER + """typedef int s32;
typedef struct { s32 a, b, c, d; } Box;
extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase, u16 *in)
{
    u16 buffer[4];
    Box near, far;
    switch (phase) {
    case 0:
        func_08000400(1, buffer);
        return buffer[0];
    case 1:
        near.a = in[0] - 16; near.b = in[1] + 16;
        far.c = in[2] - 16; far.a = in[3] - 16; far.d = in[4] + 16; far.b = in[5] + 16;
        if (near.a >= far.c) return 0;
        if (near.b <= far.a) return 0;
        data_02000000[0] = 5;
        return 1;
    case 2:
        data_02000000[1] = 3;
        return 2;
    case 3:
        return 7;
    case 4:
        func_08000400(2, buffer);
        return buffer[3];
    }
    return 0;
}
"""


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativeExitScratchTests(unittest.TestCase):
    """match.py's default path on a compiled owner that returns with a local's address in a scratch register."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_scratch_', dir=scratch)
        cls.root = owner_tests.build_switch(Path(cls.temporary.name) / 'scratch', SCRATCH_SWITCH)
        cls.code, cls.output, cls.report = data_calls.run(cls.root)
        # An owner switch whose returns hold no own-frame address.
        cls.plain = owner_tests.build_switch(Path(cls.temporary.name) / 'plain', owner_tests.DATA_SWITCH)
        cls.plain_code, cls.plain_output, cls.plain_report = data_calls.run(cls.plain)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return evidence.report_matches(report, self.root, data_calls.A)

    def test_the_owner_matches_reports_and_replays(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn('verdict MATCH - byte identical', self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        line, = [line for line in self.report.splitlines() if line.startswith(owner_switch.EXIT_SCRATCH_LINE)]
        self.assertIn('`' + DISCARDED_SCRATCH_SCHEMA + '` premise, not checked: ' + DISCARDED_SCRATCH_CONTRACT, line)
        self.assertRegex(line, r'`0x[0-9A-F]{8} r[23] -\d+`')
        self.assertTrue(self.replays(self.report))
        with patch.object(owner_switch.OWNER_EXIT_SCRATCH, 'enabled', False):
            self.assertFalse(self.replays(self.report))

    def test_the_field_is_a_data_buffer_field(self):
        self.assertIn(owner_switch.EXIT_SCRATCH_LINE, data_buffer.FIELDS)
        self.assertTrue(owner_switch.EXIT_SCRATCH_LINE.startswith(evidence.BUFFER_LINES))

    def test_disabled_refuses_at_the_return(self):
        with patch.object(owner_switch.OWNER_EXIT_SCRATCH, 'enabled', False), \
                patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(self.root), '--no-write', '0x08000200']), \
                contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stop:
            match.main()
        self.assertIn('owner-switch data-buffer proof: ' + ESCAPE, str(stop.exception.code))

    def test_an_owner_without_scratch_states_no_line(self):
        self.assertEqual(self.plain_code, 0, self.plain_output)
        self.assertNotIn(owner_switch.EXIT_SCRATCH_LINE, self.plain_report)
        lines = self.plain_report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.LINE)) + 1
        line, = [line for line in self.report.splitlines() if line.startswith(owner_switch.EXIT_SCRATCH_LINE)]
        with patch.dict(os.environ, FFTA_ROM=str(self.plain / 'baserom.bin')):
            self.assertTrue(evidence.report_matches(self.plain_report, self.plain, data_calls.A))
            self.assertFalse(evidence.report_matches('\n'.join(lines[:at] + [line] + lines[at:]) + '\n',
                                                     self.plain, data_calls.A))

    def test_a_tampered_or_missing_line_fails(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.EXIT_SCRATCH_LINE))
        for change, edited in (('offset', [re.sub(r' -(\d+)`', lambda m: f' -{int(m[1]) + 4}`', lines[at])]),
                               ('register', [re.sub(r' r([23]) ', lambda m: f' r{5 - int(m[1])} ', lines[at])]),
                               ('removed', [])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('\n'.join(lines[:at] + edited + lines[at + 1:]) + '\n'))


if __name__ == '__main__':
    unittest.main()
