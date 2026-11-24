"""Variable private-stack-array indices on the default Thumb path, retried after the plain walk refuses."""
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import default_stack_index_profile as default_index
import stack_index_precondition_profile as stack_index
# Modules only: importing their TestCase classes would run them here again.
import test_copy_helper_summary as copy_tests
import test_data_buffer_calls as data_calls

OWNER, HELPER, READ, LEAK = copy_tests.OWNER, copy_tests.HELPER, copy_tests.READ, copy_tests.LEAK
TRIGGER = 'unsupported stack-alias use or escape'
REVIEW = 'every caller passes an argument whose low four bits are below eight'

PROLOGUE = (0xb510, 0xb082)                              # push {r4, lr}; sub sp, #8
EPILOGUE = (0xb002, 0xbc10, 0xbc02, 0x4708)              # add sp, #8; pop {r4}; pop {r1}; bx r1
ZERO_FRAME = (0x2100, 0x9100, 0x9101)                    # movs r1, #0; str r1, [sp]; str r1, [sp, #4]
SAVE_ARGUMENT = (0x1c04,)                                # adds r4, r0, #0
MASK7, MASK15 = (0x2207, 0x4022), (0x220f, 0x4022)       # movs r2, #7 or #15; ands r2, r4
INDEX = (0x4669, 0x1888)                                 # mov r1, sp; adds r0, r1, r2
# ldrb r0, [r0]; or movs r3, #1; strb r3, [r0]; movs r0, #0 (the ranged address does not reach the return)
LOAD, STORE = (0x7800,), (0x2301, 0x7003, 0x2000)


def owner(*middle, frame=ZERO_FRAME, call=(READ,), index=MASK7, access=LOAD):
    """push {r4,lr}; sub sp,#8; <frame>; adds r4,r0,#0; <call>; <middle>; <index>; mov r1,sp;
    adds r0,r1,r2; <access>; epilogue.  The default reads table[entry_R0 & 7] of a zeroed 8-byte local."""
    return [*PROLOGUE, *frame, *SAVE_ARGUMENT, *call, *middle, *index, *INDEX, *access, *EPILOGUE]


def walk(code, *, premises=None, index=True):
    env = copy_tests.environment(code)

    def make_proof():
        return match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True,
                                     copy_helper_index=env['index'] if index else None, dead_registers=True)

    def run(proof):
        return match.verify_leaf_instructions(env['data'], OWNER, True, buffer_proof=proof,
                                              call_resolver=proof.target, incoming_narrow_reads=True)
    instructions, proof = default_index.walk(make_proof, run, env['data'], OWNER, premises)
    return instructions, proof, env


LOADS_THROUGH_R4 = 0x08014000                           # ldr r0, [r4]; bx lr (patched in per test)


class NoWatchPolicy(default_index.IndexPolicy):
    """The default policy with the #350 callee watch left unset."""

    @property
    def callee_watch(self):
        return None

    @callee_watch.setter
    def callee_watch(self, value):
        pass


def walk_without_watch(code):
    with patch.object(default_index, 'IndexPolicy', NoWatchPolicy):
        return walk(code)


def entry(rows, review=REVIEW):
    return json.dumps({f'0x{OWNER:08X}': {'review': review, 'rows': rows}}).encode()


def premise_rows(code):
    """The rows the retry asks a reviewer to check (from its refusal)."""
    with self_raises(ValueError) as caught:
        walk(code)
    refusal = caught.exception.__cause__
    if not isinstance(refusal, stack_index.PremiseRefusal):
        raise AssertionError(f'expected a premise refusal, got {caught.exception}')
    return refusal.entry['rows']


class self_raises:
    """assertRaises outside a TestCase."""
    def __init__(self, kind):
        self.kind, self.exception = kind, None

    def __enter__(self):
        return self

    def __exit__(self, kind, value, traceback):
        if kind is None or not issubclass(kind, self.kind):
            raise AssertionError(f'{self.kind.__name__} not raised')
        self.exception = value
        return True


class RetryTests(unittest.TestCase):
    def test_a_proved_index_is_admitted_after_the_plain_refusal(self):
        code = owner()
        env = copy_tests.environment(code)
        plain = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True)
        with self.assertRaisesRegex(ValueError, f'^{TRIGGER}$'):
            match.verify_leaf_instructions(env['data'], OWNER, True, buffer_proof=plain,
                                           call_resolver=plain.target, incoming_narrow_reads=True)
        _, proof, _ = walk(code)
        record = proof.stack_index_retry
        self.assertEqual(record['policy'], default_index.NAME)
        self.assertEqual(record['trigger'], TRIGGER)
        self.assertEqual(record['evidence']['preconditions'], [])
        # push {r4, lr}; sub sp, #8: the local array is entry_SP-16..-8, the index 0-7.
        self.assertEqual([access[1:5] for access in record['evidence']['accesses']], [['load', 1, -16, -9]])
        self.assertTrue(proof.buffer_evidence())
        self.assertFalse(proof.dependencies)
        self.assertEqual(record['evidence']['accepted'], None)

    def test_the_policy_object_disables_the_retry(self):
        with patch.object(default_index.POLICY, 'enabled', False):
            with self.assertRaisesRegex(ValueError, f'^{TRIGGER}$'):
                walk(owner())

    def test_a_walk_the_plain_proof_admits_is_unchanged(self):
        # mov r0, sp; bl READ: a bounded buffer callee, no variable index.
        code = [*PROLOGUE, *ZERO_FRAME, 0x4668, READ, *EPILOGUE]
        _, proof, env = walk(code)
        self.assertIsNone(proof.stack_index_retry)
        self.assertIsNone(proof.index_policy)
        plain = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True,
                                      copy_helper_index=env['index'], dead_registers=True)
        match.verify_leaf_instructions(env['data'], OWNER, True, buffer_proof=plain,
                                       call_resolver=plain.target, incoming_narrow_reads=True)
        self.assertEqual(proof.fingerprint(), plain.fingerprint())
        self.assertEqual(proof.loop_replay_lines(), plain.loop_replay_lines())

    def test_other_refusals_keep_their_text(self):
        # mov r0, sp; bl LEAK: the callee stores the pointer; no retry, the same message.
        code = [*PROLOGUE, *ZERO_FRAME, 0x4668, LEAK, *EPILOGUE]
        env = copy_tests.environment(code)
        plain = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True,
                                      copy_helper_index=env['index'], dead_registers=True)
        with self.assertRaises(ValueError) as expected:
            match.verify_leaf_instructions(env['data'], OWNER, True, buffer_proof=plain,
                                           call_resolver=plain.target, incoming_narrow_reads=True)
        with self.assertRaises(ValueError) as retried:
            walk(code)
        self.assertEqual(str(retried.exception), str(expected.exception))
        self.assertNotIn('retry', str(retried.exception))

    def test_a_load_premise_is_admitted_only_with_a_matching_reviewed_entry(self):
        code = owner(index=MASK15)
        rows = premise_rows(code)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]['bound'], 8)
        with self.assertRaises(ValueError) as missing:
            walk(code)
        self.assertRegex(str(missing.exception), f'^{TRIGGER}; default stack-index retry: stack index: '
                                                 'the premise rows of 0x08010000 need a reviewed entry')
        self.assertIn('none found', str(missing.exception))
        _, proof, _ = walk(code, premises=entry(rows))
        record = proof.stack_index_retry
        self.assertEqual(record['evidence']['accepted'], {'review': REVIEW, 'rows': rows})
        (row,) = record['evidence']['preconditions']
        self.assertEqual((row['kind'], row['bound'], row['premise_proved']), ('load', 8, False))
        premise, = [line for line in proof.loop_replay_lines() if line.startswith('* buffer stack index premise:')]
        self.assertIn(f"index {rows[0]['expression']} < 8", premise)
        self.assertIn('unproved runtime premise', premise)

    def test_a_differing_or_unreviewed_entry_is_refused(self):
        code = owner(index=MASK15)
        rows = premise_rows(code)
        for name, premises in (
                ('bound', entry([dict(rows[0], bound=9)])),
                ('expression', entry([dict(rows[0], expression='(u32)(entry_R1 & 15)')])),
                ('site', entry([dict(rows[0], site='0x08010002')])),
                ('extra row', entry(rows + [dict(rows[0], bound=4)])),
                ('other function', json.dumps({'0x08010004': {'review': REVIEW, 'rows': rows}}).encode())):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'need a reviewed entry'):
                walk(code, premises=premises)
        for review in ('', '<why>', 'TODO check the callers'):
            with self.subTest(review=review), self.assertRaisesRegex(ValueError, 'needs a written review'):
                walk(code, premises=entry(rows, review))

    def test_an_entry_for_a_proved_function_is_refused(self):
        with self.assertRaisesRegex(ValueError, 'lists premises 0x08010000 does not need'):
            walk(owner(), premises=entry([{'site': '0x08010000', 'expression': 'x', 'bound': 1}]))

    def test_a_store_that_needs_a_premise_is_refused(self):
        with self.assertRaisesRegex(ValueError, f'^{TRIGGER}; default stack-index retry: stack index: '
                                                r'the store at 0x[0-9A-F]{8} needs a runtime premise '
                                                r'\(\(u32\)\(15 & entry_R0\) < 8\); on the default path '
                                                'premise rows admit loads only$'):
            walk(owner(index=MASK15, access=STORE))
        # A reviewed entry that repeats the store's row does not admit it either.
        store = owner(index=MASK15, access=STORE)
        with self.assertRaises(ValueError) as caught:
            walk(store)
        found = re.search(r'the store at (0x[0-9A-F]{8}) needs a runtime premise \((.*) < (\d+)\)',
                          str(caught.exception))
        rows = [{'site': found.group(1), 'expression': found.group(2), 'bound': int(found.group(3))}]
        with self.assertRaisesRegex(ValueError, 'on the default path premise rows admit loads only$'):
            walk(store, premises=entry(rows))
        # The same store with a proved index is admitted.
        _, proof, _ = walk(owner(access=STORE))
        self.assertEqual([access[1] for access in proof.stack_index_retry['evidence']['accesses']], ['store'])

    def test_an_index_that_leaves_the_frame_without_a_source_is_refused(self):
        # str r4, [sp, #4]; ldr r2, [sp, #4]: the index comes through the stack, so no premise can be stated.
        code = owner(index=(0x9401, 0x9a01))
        with self.assertRaisesRegex(ValueError, 'index range leaves the allocated local frame.*'
                                                'index has no defined source'):
            walk(code)

    def test_a_ranged_address_in_a_callee_saved_register_needs_the_callee_watch(self):
        # movs r2,#7; ands r2,r0; mov r1,sp; adds r4,r1,r2; bl CALLEE; ldrb r0,[r4]: r4 is ranged across the call.
        def code(callee):
            return [*PROLOGUE, *ZERO_FRAME, 0x2207, 0x4002, 0x4669, 0x188c, callee, 0x7820, *EPILOGUE]
        # The #350 watch walks the callee: one that never reads R4 is admitted ...
        _, proof, _ = walk(code(READ))
        self.assertEqual([access[1] for access in proof.stack_index_retry['evidence']['accesses']], ['load'])
        self.assertIs(proof.index_policy.callee_watch, proof)
        # ... one that loads through it is refused at the call.
        with patch.dict(copy_tests.CALLEES, {LOADS_THROUGH_R4: [0x6820, 0x4770]}), \
                self.assertRaisesRegex(ValueError, f'^{TRIGGER}; default stack-index retry: stack index: ranged '
                                                   'stack address in a callee-saved register at a call: '):
            walk(code(LOADS_THROUGH_R4))
        # Without the watch the default policy refuses the call itself; the opt-in route carries R4-R11.
        with self.assertRaisesRegex(ValueError, 'ranged stack address escapes through a callee-saved '
                                                'register at a call'):
            walk_without_watch(code(READ))
        self.assertFalse(default_index.IndexPolicy.carry_callee_saved)
        self.assertTrue(stack_index.Policy.carry_callee_saved)

    def test_a_possible_ranged_address_in_r4_at_a_call_is_treated_as_a_ranged_one(self):
        # A proved load, then R4 = sp + (r0 & 7) on one path and 0 on the other, joined at a bl: R4 may hold a
        # ranged address there, which is refused without the watch and walked with it, like a certain one.
        def code(callee):
            return [*PROLOGUE, *ZERO_FRAME,
                    0x2207, 0x4002,          # movs r2, #7; ands r2, r0
                    0x4669, 0x188b, 0x781b,  # mov r1, sp; adds r3, r1, r2; ldrb r3, [r3]
                    0x2800, 0xd001,          # cmp r0, #0; beq +1
                    0x188c, 0xe000,          # adds r4, r1, r2; b +0
                    0x2400,                  # movs r4, #0
                    callee, 0x2000, *EPILOGUE]
        with self.assertRaisesRegex(ValueError, 'ranged stack address escapes through a callee-saved register '
                                                'at a call'):
            walk_without_watch(code(READ))
        with patch.dict(copy_tests.CALLEES, {LOADS_THROUGH_R4: [0x6820, 0x4770]}), \
                self.assertRaisesRegex(ValueError, 'ranged stack address in a callee-saved register at a call: '):
            walk(code(LOADS_THROUGH_R4))

    def test_an_index_one_byte_past_the_array_is_not_proved(self):
        # movs r2, #8; ands r2, r4: the index is 0 or 8, and byte 8 is the low byte of the saved R4 word.
        with self.assertRaises(ValueError) as caught:
            walk(owner(index=(0x2208, 0x4022)))
        self.assertRegex(str(caught.exception), f'^{TRIGGER}; default stack-index retry: stack index: ')
        self.assertRegex(str(caught.exception), 'need a reviewed entry|overlaps a saved register')

    def test_ranged_addresses_passed_or_stored_are_refused(self):
        for name, tail in (('R0 at a call', (0x4669, 0x1888, READ)),          # adds r0,r1,r2; bl READ
                           ('stored', (0x4669, 0x1888, 0x9001)),               # str r0, [sp, #4]
                           ('compared', (0x4669, 0x1888, 0x4288))):            # cmp r0, r1
            code = [*PROLOGUE, *ZERO_FRAME, *SAVE_ARGUMENT, READ, *MASK7, *tail, *EPILOGUE]
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, f'^{TRIGGER}; default stack-index retry: '):
                walk(code)

    def test_copy_helper_copies_initialise_the_array(self):
        # mov r0, sp; movs r1, #0; movs r2, #8; bl HELPER: an external source copied over the 8-byte local.
        code = [*PROLOGUE, *SAVE_ARGUMENT, 0x4668, 0x2100, 0x2208, HELPER, *MASK7, *INDEX, *LOAD, *EPILOGUE]
        _, proof, _ = walk(code)
        record = proof.stack_index_retry
        (site, destination, count), = record['copies']
        self.assertEqual((destination, count), (-16, 8))
        self.assertTrue(OWNER < site < OWNER + len(copy_tests.assemble(OWNER, code)))
        self.assertIn(f'* buffer stack index initialisation: copy helper 0x{HELPER:08X} at 0x{site:08X} writes '
                      'entry_SP-0x10..-0x8 from a non-local source', proof.loop_replay_lines())
        # Without the summary (no function index) the walk refuses at the helper, as before.
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC'):
            walk(code, index=False)

    def test_a_partial_copy_initialises_only_the_bytes_it_writes(self):
        # mov r0, sp; movs r1, #0; movs r2, #4; bl HELPER: 4 of the 8 local bytes. Index 0-7 is not proved; the
        # premise it asks for bounds the index by the 4 initialised bytes.
        code = [*PROLOGUE, *SAVE_ARGUMENT, 0x4668, 0x2100, 0x2204, HELPER, *MASK7, *INDEX, *LOAD, *EPILOGUE]
        (row,) = premise_rows(code)
        self.assertEqual(row['bound'], 4)

    def test_a_load_before_the_copy_or_from_a_local_source_reads_uninitialised_bytes(self):
        # The read precedes the copy: nothing is initialised at the access (movs r0, #0 drops the
        # helper's returned destination).
        early = [*PROLOGUE, *SAVE_ARGUMENT, *MASK7, *INDEX, *LOAD, 0x4668, 0x2100, 0x2208, HELPER, 0x2000,
                 *EPILOGUE]
        with self.assertRaisesRegex(ValueError, 'reads uninitialised local bytes'):
            walk(early)
        # sub sp, #16; copy sp+8 -> sp: a local source initialises nothing (movs r3, #0 drops the
        # helper's returned source end).
        local = [0xb510, 0xb084, *SAVE_ARGUMENT, 0x4668, 0xa902, 0x2208, HELPER, 0x2300, *MASK7, *INDEX, *LOAD,
                 0xb004, 0xbc10, 0xbc02, 0x4708]
        with self.assertRaisesRegex(ValueError, 'reads uninitialised local bytes'):
            walk(local)

    def test_copies_require_the_default_policy(self):
        env = copy_tests.environment(owner())
        proof = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True)
        with self.assertRaisesRegex(ValueError, 'require the default stack-index retry policy'):
            proof.index_copies()

    def test_the_retry_needs_a_fresh_stack_argument_proof(self):
        env = copy_tests.environment(owner())
        error = ValueError(TRIGGER)
        for make in (lambda: match.BufferCallProof(env['rom'], env['mapping']),):
            with self.assertRaisesRegex(ValueError, 'requires a fresh stack-argument buffer proof'):
                default_index.retry(error, lambda proof: None, make, env['data'], OWNER, None)
        with self.assertRaises(ValueError) as other:
            default_index.retry(ValueError('another refusal'), lambda proof: None, None, env['data'], OWNER, None)
        self.assertEqual(str(other.exception), 'another refusal')


class ReportTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='default_stack_index_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        variables = patch.dict(os.environ, {'FFTA_ROM': str(self.root / 'baserom.bin')})
        variables.start()
        self.addCleanup(variables.stop)

    def report(self, code, premises=None, *, call=True):
        _, proof, env = walk(code, premises=premises)
        (self.root / 'baserom.bin').write_bytes(env['rom'])
        (self.root / 'symbols').mkdir(exist_ok=True)
        (self.root / 'symbols/functions.txt').write_bytes(env['index'])
        (self.root / 'config').mkdir(exist_ok=True)
        if premises is not None:
            (self.root / stack_index.PREMISES_PATH).write_bytes(premises)
        flow = evidence.CALL_SUMMARY if call else 'closed leaf CFG'
        lines = [f"* compiled : `{env['data'].hex()}`",
                 f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`',
                 *proof.loop_replay_lines(),
                 f'* control flow: {flow}',
                 f"**MATCH - byte identical** - {len(env['data'])}/{len(env['data'])} bytes"]
        return lines, env

    def accepted(self, lines, env):
        return evidence.buffer_report_matches(lines, self.root, OWNER, env['mapping'], stack_arguments=True)

    def test_a_proved_report_replays_and_its_edits_fail(self):
        lines, env = self.report(owner())
        self.assertTrue(self.accepted(lines, env))
        head = next(i for i, line in enumerate(lines) if line.startswith('* buffer stack index: '))
        access = next(i for i, line in enumerate(lines) if line.startswith('* buffer stack index access: '))
        for name, edited in (
                ('summary', lines[:head] + [lines[head].replace('1 accesses', '2 accesses')] + lines[head + 1:]),
                ('range', lines[:access] + [lines[access].replace('-0x10', '-0x14')] + lines[access + 1:]),
                ('removed', lines[:access] + lines[access + 1:]),
                ('flow', [line.replace(evidence.CALL_SUMMARY, 'closed leaf CFG') for line in lines]),
                ('fingerprint', [line if not line.startswith('* buffer proof SHA-256') else
                                 '* buffer proof SHA-256: `' + '0' * 64 + '`' for line in lines])):
            with self.subTest(name=name):
                self.assertFalse(self.accepted(edited, env))
        with self.subTest(name='retry disabled'), patch.object(default_index.POLICY, 'enabled', False):
            self.assertFalse(self.accepted(lines, env))

    def test_a_premise_report_replays_only_with_its_reviewed_entry(self):
        code = owner(index=MASK15)
        rows = premise_rows(code)
        lines, env = self.report(code, entry(rows))
        self.assertTrue(self.accepted(lines, env))
        premise = next(i for i, line in enumerate(lines) if line.startswith('* buffer stack index premise: '))
        self.assertFalse(self.accepted(lines[:premise] + [lines[premise].replace('< 8', '< 9')] +
                                       lines[premise + 1:], env))
        # A changed review is a different accepted entry, so a different proof.
        (self.root / stack_index.PREMISES_PATH).write_bytes(entry(rows, 'the callers mask the argument'))
        self.assertFalse(self.accepted(lines, env))
        (self.root / stack_index.PREMISES_PATH).unlink()
        self.assertFalse(self.accepted(lines, env))

    def test_a_call_free_report_must_say_closed_leaf(self):
        code = [*PROLOGUE, *ZERO_FRAME, *SAVE_ARGUMENT, *MASK7, *INDEX, *LOAD, *EPILOGUE]
        lines, env = self.report(code, call=False)
        self.assertTrue(self.accepted(lines, env))
        self.assertFalse(self.accepted([line.replace('closed leaf CFG', evidence.CALL_SUMMARY)
                                        for line in lines], env))
        # A body with calls may not claim a closed leaf.
        lines, env = self.report(owner(), call=False)
        self.assertFalse(self.accepted(lines, env))


TABLE_SOURCE = """typedef unsigned char u8;
typedef unsigned int u32;
extern void func_08000400(u32 value);
u32 func_08000200(u32 value)
{
    u8 table[8];

    table[0] = 3;
    table[1] = 1;
    table[2] = 4;
    table[3] = 1;
    table[4] = 5;
    table[5] = 9;
    table[6] = 2;
    table[7] = 6;
%(call)s    return table[value & %(mask)d];
}
"""
# Word stores at [sp, #imm] need no copy of SP, so no stack address is left in R1-R3 at the return.
LEAF_SOURCE = """typedef unsigned int u32;
u32 func_08000200(u32 value)
{
    u32 table[4];

    table[0] = 3;
    table[1] = 1;
    table[2] = 4;
    table[3] = 9;
    return table[value & 3];
}
"""
STORE_SOURCE = """typedef unsigned char u8;
typedef unsigned int u32;
extern void func_08000500(u8 *buffer);
u32 func_08000200(u32 value)
{
    u8 table[8];

    func_08000500(table);
    table[value & 15] = value;
    return table[0] + value;
}
"""
WORDS = """    table[0] = 3;
    table[1] = 1;
    table[2] = 4;
    table[3] = 9;
"""
DATA_SOURCE = """typedef unsigned char u8;
typedef unsigned int u32;
extern u8 data_02000000[];
extern void func_08000400(u32 value);
void func_08000200(u32 value)
{
    u32 table[4];

%(call)s%(words)s    data_02000000[0] = table[value & 3];
%(tail)s}
"""
FUNCTION_SOURCE = """typedef unsigned int u32;
extern void func_08000400(u32 value);
extern void func_08000500(void);
u32 func_08000200(u32 value)
{
    u32 table[4];

%(words)s    func_08000400((u32)func_08000500);
    return table[value & 3];
}
"""
CALLEES = [('func_08000400', 'bx lr'), ('func_08000500', 'movs r1, #0\nstr r1, [r0]\nstr r1, [r0, #4]\nbx lr')]


def unlinked(runner, workspace, args, original, address, *rest, **options):
    """The caller's bytes as match.py reads a body without relocations (function_bytes)."""
    symbol, offset = match.function_record(original, f'func_{address:08X}', address, True)
    if original['relocations']:
        raise AssertionError('the leaf fixture has relocations')
    return original['text'][offset:offset + symbol['size']], {}, {}


@unittest.skipUnless(data_calls.tools_present(), 'fixed compiler and ARM tools required')
class NativeTests(unittest.TestCase):
    """match.py end to end on compiled C: the default path, its report, and the report's replay."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='default_stack_index_native_', dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def build(self, name, source):
        return data_calls.build(self.base / name, source, CALLEES)

    def build_leaf(self, name, source):
        """data_calls.build for a body without calls: match.py takes its bytes unlinked."""
        with patch.object(match, 'link_calls', unlinked):
            return data_calls.build(self.base / name, source, CALLEES)

    def replays(self, root, report):
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def test_a_proved_index_matches_and_replays(self):
        root = self.build('proved', TABLE_SOURCE % dict(call='    func_08000400(value);\n', mask=7))
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        self.assertEqual(data_calls.verification(report), evidence.STACK_BUFFER_SCHEMA)
        self.assertIn(f'* control flow: {evidence.CALL_SUMMARY}', report.splitlines())
        self.assertTrue(any(line.startswith('* buffer stack index: `default-stack-index-retry-v1`')
                            for line in report.splitlines()))
        self.assertTrue(self.replays(root, report))
        edited = report.replace('accesses proved', 'accesses  proved')
        self.assertFalse(self.replays(root, edited))
        with patch.object(default_index.POLICY, 'enabled', False):
            self.assertFalse(self.replays(root, report))

    def test_a_call_free_index_matches_and_replays(self):
        root = self.build_leaf('leaf', LEAF_SOURCE)
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), evidence.STACK_BUFFER_SCHEMA)
        self.assertIn('* control flow: closed leaf CFG', report.splitlines())
        self.assertTrue(self.replays(root, report))

    def test_a_load_premise_needs_its_reviewed_entry(self):
        root = self.build('premise', TABLE_SOURCE % dict(call='    func_08000400(value);\n', mask=15))
        code, output, report = data_calls.run(root)
        self.assertNotEqual(code, 0)
        self.assertIn('default stack-index retry: stack index: the premise rows of 0x08000200 need a '
                      'reviewed entry', output)
        self.assertIsNone(report)
        suggested = json.loads(output[output.index('add:\n') + 5:output.rindex('}') + 1])
        rows = suggested['0x08000200']['rows']
        (root / stack_index.PREMISES_PATH).write_text(json.dumps(
            {'0x08000200': {'review': 'every caller masks the argument to 0-7', 'rows': rows}}))
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        self.assertTrue(any(line.startswith('* buffer stack index premise: ') for line in report.splitlines()))
        self.assertTrue(self.replays(root, report))
        (root / stack_index.PREMISES_PATH).write_text(json.dumps(
            {'0x08000200': {'review': 'every caller masks the argument to 0-7',
                            'rows': [dict(rows[0], bound=rows[0]['bound'] + 1)]}}))
        self.assertFalse(self.replays(root, report))
        code, output, _ = data_calls.run(root)
        self.assertNotEqual(code, 0)
        self.assertIn('the entry differs', output)

    def test_the_data_buffer_proofs_retry(self):
        import data_buffer_profile as data_buffer
        # The second store keeps agbcc from leaving a copy of SP in R2 at the return.
        for name, call, tail, flow in (('data', '    func_08000400(value);\n', '    data_02000000[1] = value;\n',
                                        evidence.CALL_SUMMARY),
                                       ('data-leaf', '', '', 'closed leaf CFG')):
            with self.subTest(name=name):
                root = self.build(name, DATA_SOURCE % dict(words=WORDS, call=call, tail=tail))
                code, output, report = data_calls.run(root)
                self.assertEqual(code, 0, output)
                self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
                self.assertIn(f'* control flow: {flow}', report.splitlines())
                self.assertTrue(any(line.startswith('* buffer stack index access: ')
                                    for line in report.splitlines()))
                self.assertTrue(self.replays(root, report))
                other = evidence.CALL_SUMMARY if flow != evidence.CALL_SUMMARY else 'closed leaf CFG'
                self.assertFalse(self.replays(root, report.replace(f'* control flow: {flow}',
                                                                   f'* control flow: {other}')))
                with patch.object(default_index.POLICY, 'enabled', False):
                    self.assertFalse(self.replays(root, report))

    def test_the_function_buffer_proof_retries(self):
        root = self.build('function', FUNCTION_SOURCE % dict(words=WORDS))
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), evidence.FUNCTION_BUFFER_SCHEMA)
        self.assertTrue(any(line.startswith('* buffer stack index access: ') for line in report.splitlines()))
        self.assertTrue(self.replays(root, report))
        with patch.object(default_index.POLICY, 'enabled', False):
            self.assertFalse(self.replays(root, report))

    def test_a_store_premise_is_refused(self):
        root = self.build('store', STORE_SOURCE)
        code, output, report = data_calls.run(root)
        self.assertNotEqual(code, 0)
        self.assertIn('premise rows admit loads only', output)
        self.assertIsNone(report)


if __name__ == '__main__':
    unittest.main()
