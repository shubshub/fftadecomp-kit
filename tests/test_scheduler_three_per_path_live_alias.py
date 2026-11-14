"""Raw Thumb fixtures for conditional-scheduler-three-per-path-live-alias-v1."""
from pathlib import Path
import hashlib
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import conditional_local_buffer_profile as local
import scheduler_live_alias_profile as live
import scheduler_loop_composition_profile as composition
from test_scheduler_predicates import half, bl, fixture, A, B
from test_scheduler_counted_loop import decoded
from test_scheduler_loop_composition import Program, descriptor_call, caller, C

S = composition.SCHEDULER
SELECTOR = local.SCHEDULER_WIDE_LIVE_ALIAS
OLD = local.SCHEDULER_LOOP_LIVE_ALIAS
R0, R1 = match.ARM_REG_R0, match.ARM_REG_R0 + 1
# push {r4-r7,lr}; sub sp,#28: SP is entry-48, the descriptor frame.
FRAME = -48


def phase_owner(arms, *, prefix=0):
    """A phase switch on R0: arm i makes arms[i] scheduler calls, then one ordinary call."""
    p = Program()
    p.emit(0xB5F0, 0xB087)
    p.emit(*(0x46C0,) * prefix)
    for index in range(len(arms)):
        p.emit(0x2800 | index)                  # cmp r0,#index
        p.branch(0xD000, f'arm{index}')         # beq arm
    p.branch(0xE000, 'exit')
    for index, count in enumerate(arms):
        p.label(f'arm{index}')
        for call in range(count):
            descriptor_call(p, f'scheduler{index}_{call}')
        p.call(B, f'ordinary{index}')
        p.branch(0xE000, 'exit')
    p.label('exit')
    p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
    return p.build()


def alias_owner(*, after=(), second=False):
    """R1 = SP (a live local alias) into an ordinary call, then one scheduler call."""
    p = Program()
    p.emit(0xB5F0, 0xB087, 0xA900)              # add r1, sp, #0
    p.call(B, 'ordinary')
    p.emit(*after)
    if second:
        p.call(C, 'second')
    descriptor_call(p)
    p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
    return p.build()


def phases(data, calls, limits=composition.WIDE_LIMITS):
    ins, edges = decoded(data, calls)
    return composition.phases(ins, edges, calls, A, limits=limits)


def bound(data, calls, policy=SELECTOR, callee=half(0x4770), second=half(0x4770)):
    bodies = {A: data, B: callee, C: second, S: bytes(60), 0x08005954: bytes(206)}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in bodies.items()
            if a in (S, 0x08005954)}
    with mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p


def verify(data, calls, policy=SELECTOR, callee=half(0x4770), second=half(0x4770)):
    p = bound(data, calls, policy, callee, second)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
    return p


class PhaseBudgetTests(unittest.TestCase):
    def test_eight_sites_with_three_per_path_are_admitted(self):
        data, calls, labels = phase_owner([3, 3, 2])
        result = phases(data, calls)
        self.assertEqual(len(result['scheduler_sites']), 8)
        self.assertEqual(result['maximum_scheduler_calls_per_path_outside_loops'], 3)
        self.assertEqual((result['scheduler_site_budget'], result['ordinary_target_budget'],
                          result['call_site_budget'], result['instruction_budget']), (8, 32, 40, 512))
        self.assertEqual(result['scheduler_calls_per_path_budget'], 3)
        with self.assertRaisesRegex(ValueError, 'call-site or target bounds'):
            phases(data, calls, limits=None)

    def test_ninth_site_and_fourth_per_path_call_are_refused(self):
        with self.assertRaisesRegex(ValueError, 'call-site or target bounds'):
            phases(*phase_owner([3, 3, 3])[:2])
        with self.assertRaisesRegex(ValueError, 'per-path bound'):
            phases(*phase_owner([4, 1])[:2])

    def test_instruction_budget_is_512(self):
        size = len(decoded(*phase_owner([3, 3, 2])[:2])[0])
        data, calls, _ = phase_owner([3, 3, 2], prefix=512 - size)
        self.assertEqual(len(decoded(data, calls)[0]), 512)
        phases(data, calls)
        with self.assertRaisesRegex(ValueError, 'bounded instruction graph'):
            phases(data, calls, limits=None)
        data, calls, _ = phase_owner([3, 3, 2], prefix=513 - size)
        with self.assertRaisesRegex(ValueError, 'bounded instruction graph'):
            phases(data, calls)

    def test_limits_are_closed(self):
        data, calls, _ = phase_owner([1])
        for limits in (dict(composition.WIDE_LIMITS, instructions=0),
                       dict(composition.WIDE_LIMITS, extra=1),
                       {k: v for k, v in composition.WIDE_LIMITS.items() if k != 'call_sites'},
                       dict(composition.WIDE_LIMITS, scheduler_sites=True)):
            with self.subTest(limits=limits), self.assertRaisesRegex(ValueError, 'positive integers'):
                phases(data, calls, limits=limits)

    def test_counted_loops_keep_their_rules(self):
        data, calls, _ = caller(schedulers_after=3)
        [loop] = phases(data, calls)['counted_loops']
        self.assertEqual(loop['maximum_scheduler_calls'], 256)
        with self.assertRaisesRegex(ValueError, 'per-path bound'):
            phases(*caller(schedulers_after=4, scheduler_in_loop=False)[:2])

    def test_complete_replay_and_manifest(self):
        data, calls, _ = phase_owner([3, 3, 2])
        p = verify(data, calls)
        self.assertEqual(p.dependency_budget, 44)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], 'elf-symbol-thumb-' + SELECTOR)
        self.assertEqual(report['branch_calls']['instruction_budget'], 512)
        self.assertIn(live.ENTRY_LIVENESS_PREMISE, report['branch_calls']['ordinary_call_contract'])
        self.assertIn('Every sequential scheduler invocation', ' '.join(report['assumptions']))
        with self.assertRaisesRegex(ValueError, 'call-site or target bounds'):
            bound(data, calls, OLD)

    def test_old_selector_manifest_is_unchanged_in_shape(self):
        data, calls, _ = caller()
        p = bound(data, calls, OLD)
        self.assertNotIn('instruction_budget', p.branch_calls)
        self.assertNotIn(live.ENTRY_LIVENESS_PREMISE, p.branch_calls['ordinary_call_contract'])
        self.assertEqual(p.dependency_budget, 36)


class EntryLivenessTests(unittest.TestCase):
    def dead(self, callee):
        data, calls, _ = alias_owner()
        return live.dead_at_entry(bound(data, calls, SELECTOR, callee), B, {R1})

    def test_overwritten_before_observation_is_dead(self):
        for callee in (half(0x2100, 0x4770),                     # movs r1,#0; bx lr
                       half(0x4669, 0x7808, 0x4770),             # mov r1,sp; ldrb r0,[r1]
                       half(0x2800, 0xD001, 0x2100, 0x4770, 0x2101, 0x4770)):  # both arms kill
            with self.subTest(callee=callee.hex()):
                self.assertEqual(self.dead(callee), {R1})

    def test_every_observation_before_the_kill_keeps_it_live(self):
        for callee in (half(0x7808, 0x2100, 0x4770),             # ldrb r0,[r1] first
                       half(0x1C08, 0x2100, 0x4770),             # adds r0,r1,#0 first
                       half(0x4770),                             # returned unkilled
                       half(0xDF0B, 0x2100, 0x4770),             # swi CpuSet reads R1 implicitly
                       half(0x2800, 0xD000, 0x2100, 0x4770),     # killed on one arm only
                       half(0x2800, 0xD1FD, 0x2100, 0x4770),     # a cycle that never kills
                       half(0x3801, 0xD1FD, 0x2100, 0x4770)):    # least fixpoint: a cycle before the kill
            with self.subTest(callee=callee.hex()):
                self.assertEqual(self.dead(callee), set())

    def test_call_before_the_kill_keeps_it_live(self):
        data, calls, _ = alias_owner()
        body = bytearray(half(0xB500, 0, 0, 0x2100, 0xBC01, 0x4700))
        body[2:6] = bl(B + 2, C)
        p = bound(data, calls, SELECTOR, bytes(body))
        self.assertEqual(live.dead_at_entry(p, B, {R1}), set())

    def test_dead_alias_is_not_an_argument(self):
        data, calls, labels = alias_owner()
        p = verify(data, calls, callee=half(0x2100, 0x2000, 0x4770))
        observation = p.observations[labels['ordinary']]
        self.assertEqual(observation['dead_at_entry_aliases'], [(R1, FRAME)])
        self.assertEqual(observation['passed_aliases'], [])
        self.assertNotIn('access_lowest', observation)
        self.assertEqual(observation['entry_liveness_premise'], live.ENTRY_LIVENESS_PREMISE)

    def test_live_alias_is_still_replayed(self):
        data, calls, labels = alias_owner()
        p = verify(data, calls, callee=half(0x7808, 0x2100, 0x4770))
        observation = p.observations[labels['ordinary']]
        self.assertEqual(observation['dead_at_entry_aliases'], [])
        self.assertEqual(observation['passed_aliases'], [(R1, FRAME)])
        self.assertEqual((observation['access_lowest'], observation['access_end']), (FRAME, FRAME + 1))
        for callee, message in ((half(0x69C8, 0x2100, 0x4770), 'outside allocated local words'),
                                (half(0x6009, 0x2100, 0x4770), 'cannot be stored')):
            with self.subTest(callee=callee.hex()), self.assertRaisesRegex(ValueError, message):
                verify(data, calls, callee=callee)


class ReturnedAliasTests(unittest.TestCase):
    STORE = half(0x2200, 0x700A, 0x4770)            # movs r2,#0; strb r2,[r1]; bx lr: R1 survives

    def test_returned_alias_is_tracked_by_the_caller(self):
        data, calls, labels = alias_owner()
        p = verify(data, calls, callee=self.STORE)
        observation = p.observations[labels['ordinary']]
        self.assertEqual(observation['returned_aliases'], [(R1, FRAME)])
        self.assertEqual(observation['passed_aliases'], [(R1, FRAME)])
        with self.assertRaisesRegex(ValueError, 'return a local alias'):
            verify(data, calls, OLD, callee=self.STORE)

    def test_returned_alias_cannot_escape_afterwards(self):
        data, calls, _ = alias_owner(after=(0x6029,))  # str r1,[r5]
        with self.assertRaisesRegex(ValueError, 'escape'):
            verify(data, calls, callee=self.STORE)

    def test_stale_returned_alias_into_a_second_call(self):
        data, calls, labels = alias_owner(second=True)
        p = verify(data, calls, callee=self.STORE, second=half(0x2100, 0x2000, 0x4770))
        self.assertEqual(p.observations[labels['second']]['dead_at_entry_aliases'], [(R1, FRAME)])
        # A second callee that reads it gets the ordinary replay, with its bounds.
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            verify(data, calls, callee=self.STORE, second=half(0x3904, 0x7808, 0x4770))

    def test_stale_returned_alias_cannot_reach_the_scheduler(self):
        p = Program()
        p.emit(0xB5F0, 0xB087, 0xA900)
        p.call(B, 'ordinary')
        p.emit(0x2000, 0xAA00, 0x2300)                 # R1 still the returned alias
        p.call(composition.SCHEDULER, 'scheduler')
        p.emit(0xB007, 0xBCF0, 0xBC01, 0x4700)
        data, calls, _ = p.build()
        with self.assertRaisesRegex(ValueError, 'additional register or pointer-word aliases'):
            verify(data, calls, callee=self.STORE)


class RegistrationTests(unittest.TestCase):
    def test_selector_and_native_replay_registered(self):
        self.assertIn(SELECTOR, owner.named_buffer.SELECTORS)
        schema = local.SCHEMAS[SELECTOR]
        self.assertEqual(owner.selector_for_report('* verification: `' + schema + '`'), SELECTOR)
        data, calls, _ = phase_owner([1])
        self.assertTrue(match._ordinary_call_replay(bound(data, calls, SELECTOR), B))
        result = subprocess.run([sys.executable, '-B', str(Path(match.__file__)),
            '--owner-runtime-profile', SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_entry_liveness_is_boolean_and_off_for_other_selectors(self):
        data, calls, labels = alias_owner()
        p = bound(data, calls, OLD, self.callee())
        with self.assertRaisesRegex(ValueError, 'Boolean'):
            live.check_call(p, B, {R1: FRAME}, [(False, False, True)] * 7 + [(False, True, False)] * 5,
                            {}, site=labels['ordinary'], entry_liveness=1)

    @staticmethod
    def callee():
        return half(0x2100, 0x4770)


if __name__ == '__main__':
    unittest.main()
