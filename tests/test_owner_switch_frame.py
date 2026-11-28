"""An owner switch whose walk passes no local buffer (data_buffer_profile.OWNER_SWITCH_FRAME_SCHEMA).

The default path's typed-data buffer walk of an owner with its own guarded jump
table (owner_switch_buffer_profile) used to refuse at its closing check when no
call received a local buffer: "data-buffer evidence requires an inspected buffer
call".  The walk itself had proved the frame.  The owner switch frame schema
admits exactly that owner, says in its buffer-calls line that no call took a
local buffer, and refuses an owner with a `_call_via_rN` thunk call or a
function literal.
"""
import contextlib
import io
import json
import os
from pathlib import Path
import re
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
import data_buffer_profile as data_buffer
import owner_switch_buffer_profile as owner_switch
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_owner_switch_buffers as switch_tests
import test_signed_remainder_leaf as remainder_tests

FIXTURES = ROOT / 'tests/fixtures/owner_switch_frame'
NO_CALLS = f'* buffer calls: {data_buffer.NO_BUFFER_CALLS}'
PLAIN_CALLS = f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY}'
FRAME_LINE = data_buffer.FRAME_FIELD + data_buffer.SUMMARIES[data_buffer.OWNER_SWITCH_FRAME_SCHEMA]
DATA_LINE = data_buffer.CALLS_FIELD + data_buffer.SUMMARIES[data_buffer.SCHEMA]
INSPECTED = 'data-buffer evidence requires an inspected buffer call'
THUNKS = 'owner switch frame proof excludes call-via thunks and function literals'
DEAD = 'owner switch frame proof excludes stack addresses passed in dead registers'


class Assembled(unittest.TestCase):
    """The rule on assembled owners: switch_tests.OwnerSwitchTests' fixture, walked in process."""

    fixture = switch_tests.OwnerSwitchTests.fixture
    plain = switch_tests.OwnerSwitchTests.plain
    refinement = switch_tests.OwnerSwitchTests.refinement
    linked = switch_tests.OwnerSwitchTests.linked
    walk = switch_tests.OwnerSwitchTests.walk

    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_frame_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def walked(self, f, **options):
        """(proof, verified instructions, calls) of the plain proof's owner switch walk, as prove runs it."""
        calls, linked = self.linked(f)
        proof = self.plain(f, **options)
        instructions = owner_switch.walk(proof, f['data'], switch_tests.A, calls, linked)
        return proof, instructions, calls

    def scalar(self):
        """Both calling cases pass a number, so the walk inspects no buffer call."""
        f = self.fixture(case0='movs r0, #1\nbl callee', case2='movs r0, #2\nbl callee')
        return (f, *self.walked(f, dead_registers=True))

    def test_a_complete_owner_walk_without_a_buffer_call_is_the_frame_schema(self):
        _, proof, instructions, calls = self.scalar()
        self.assertFalse(proof.buffer_evidence())
        self.assertIs(proof.owner_switch.complete, True)
        self.assertIs(data_buffer.owner_switch_frame(proof, calls, {}, instructions), True)

    def test_kit_main_refuses_it(self):
        _, proof, instructions, calls = self.scalar()
        with patch.object(data_buffer.OWNER_SWITCH_FRAME, 'enabled', False), \
                self.assertRaisesRegex(ValueError, INSPECTED):
            data_buffer.owner_switch_frame(proof, calls, {}, instructions)

    def test_a_buffer_call_keeps_the_plain_schema(self):
        proof, instructions, calls = self.walked(self.fixture(), dead_registers=True)
        self.assertTrue(proof.buffer_evidence())
        with self.assertRaisesRegex(ValueError, INSPECTED):
            data_buffer.owner_switch_frame(proof, calls, {}, instructions)

    def test_only_the_retried_shape_takes_it(self):
        # match.py retries only an owner with a call and a fixed frame; replay must not admit others.
        _, proof, instructions, calls = self.scalar()
        frameless = [item for item in instructions if not match.uses_stack_frame([item])]
        self.assertTrue(match.uses_stack_frame(instructions))
        self.assertFalse(match.uses_stack_frame(frameless))
        for name, (sites, walked) in (('no call', ({}, instructions)), ('no fixed frame', (calls, frameless))):
            with self.subTest(case=name), self.assertRaisesRegex(ValueError, INSPECTED):
                data_buffer.owner_switch_frame(proof, sites, {}, walked)

    def test_a_stack_address_in_a_dead_register_refuses(self):
        # Inspecting the callee refuses (a SWI), and it overwrites r0 before reading it, so the call is
        # admitted uninspected (dead_register); it still received a stack address, so the no-buffer line
        # would be false.
        f = self.fixture(case0='add r0, sp, #0\nbl callee', case2='movs r0, #2\nbl callee',
                         callee='movs r0, #0\nswi 0x30\nbx lr')
        proof, instructions, calls = self.walked(f, dead_registers=True)
        self.assertFalse(proof.buffer_evidence())
        self.assertTrue(proof.dead_registers.observed())
        self.assertTrue(any(line.startswith('* buffer dead register') for line in proof.loop_replay_lines()))
        with self.assertRaisesRegex(ValueError, DEAD):
            data_buffer.owner_switch_frame(proof, calls, {}, instructions)

    def test_a_call_via_thunk_refuses(self):
        _, proof, instructions, calls = self.scalar()
        site = min(calls)
        for name, target in (('_call_via_r0', match.RUNTIME_HELPERS['_call_via_r0']),
                             ('_call_via_r3', match.RUNTIME_HELPERS['_call_via_r3']),
                             ('_call_via_r14', match.RUNTIME_HELPERS['_call_via_r14']),
                             ('_call_via_r3 in a wait-state mirror', match.RUNTIME_HELPERS['_call_via_r3'] + 0x02000000)):
            with self.subTest(thunk=name), self.assertRaisesRegex(ValueError, THUNKS):
                data_buffer.owner_switch_frame(proof, {**calls, site: target}, {}, instructions)

    def test_a_function_literal_refuses(self):
        _, proof, instructions, calls = self.scalar()
        with self.assertRaisesRegex(ValueError, THUNKS):
            data_buffer.owner_switch_frame(proof, calls, {0x20: ('func_08010100', switch_tests.B)}, instructions)

    def test_an_unauthenticated_switch_refuses(self):
        f, proof, instructions, calls = self.scalar()
        unwalked = self.plain(f, dead_registers=True)
        incomplete = self.plain(f, dead_registers=True)
        incomplete.owner_switch = owner_switch.OwnerSwitch(incomplete, f['data'], switch_tests.A, *self.linked(f))

        class StandIn:
            complete = True
            record = proof.owner_switch.record

        stand_in = self.plain(f, dead_registers=True)
        stand_in.owner_switch = StandIn()
        for name, candidate in (('no owner switch', unwalked), ('walk incomplete', incomplete),
                                ('not an OwnerSwitch', stand_in)):
            with self.subTest(case=name), self.assertRaisesRegex(ValueError, INSPECTED):
                data_buffer.owner_switch_frame(candidate, calls, {}, instructions)

    def test_only_the_plain_stack_argument_proof_takes_it(self):
        class Other(match.BufferCallProof):
            pass

        _, proof, instructions, calls = self.scalar()
        proof.__class__ = Other
        with self.assertRaisesRegex(ValueError, INSPECTED):
            data_buffer.owner_switch_frame(proof, calls, {}, instructions)
        _, proof, instructions, calls = self.scalar()
        proof.stack_arguments = False
        with self.assertRaisesRegex(ValueError, INSPECTED):
            data_buffer.owner_switch_frame(proof, calls, {}, instructions)


# Five outgoing words: the fifth goes on the stack, so the owner has a fixed frame and the buffer-free
# switch walk refuses it; no call receives a local address.
FRAME_SWITCH = data_calls.HEADER + """extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u32 e);
u32 func_08000200(u32 phase)
{
    switch (phase) {
    case 0:
        func_08000400(1, 2, 3, 4, 5);
        return 1;
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08000400(phase, 2, 3, 4, data_02000000[2]);
        return 3;
    case 3:
        return 7;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""
# The same owner calling through a typed table of function pointers (`bl _call_via_rN`).
THUNK_SWITCH = FRAME_SWITCH.replace(
    'extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u32 e);',
    'extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u32 e);\n'
    'extern void (*const data_02000010[])(u32 value);').replace(
    'case 3:\n        return 7;', 'case 3:\n        data_02000010[0](7);\n        return 7;')
# The same owner storing a function's address (a function literal).
LITERAL_SWITCH = FRAME_SWITCH.replace(
    'extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u32 e);',
    'extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u32 e);\n'
    'extern void func_08000500(void);\nextern void (*data_02000010)(void);').replace(
    'case 3:\n        return 7;', 'case 3:\n        data_02000010 = func_08000500;\n        return 7;')
# Shapes match.py never retries, which replay must not admit either (an independent review's probes):
# four register arguments, so no fixed frame, and the plain switch walk issues it;
FRAMELESS_SWITCH = FRAME_SWITCH.replace('u32 d, u32 e);', 'u32 d);').replace(
    'func_08000400(1, 2, 3, 4, 5);', 'func_08000400(1, 2, 3, 4);').replace(
    'func_08000400(phase, 2, 3, 4, data_02000000[2]);', 'func_08000400(phase, 2, 3, data_02000000[2]);')
# a fixed frame from an incoming stack argument, and no call at all.
NO_CALL_SWITCH = data_calls.HEADER + """u32 func_08000200(u32 phase, u32 a, u32 b, u32 c, u32 e)
{
    switch (phase) {
    case 0:
        data_02000000[0] = e;
        return 1;
    case 1:
        data_02000000[1] = a;
        return 1;
    case 2:
        data_02000000[2] = b + e;
        return 3;
    case 3:
        return 7;
    case 4:
        data_02000000[1] = c;
        return 2;
    }
    return 0;
}
"""
OBJECTS = dict(data_calls.OBJECTS, data_02000010='0x02000010')


def build_owner(root, source, callees, large=False):
    """data_calls.build, linking the caller's own switch table as match.py's default path does."""
    real = match.link_calls

    def with_switch(*args, **kwargs):
        if len(args) < 11 and 'switch_relocations' not in kwargs:
            kwargs.update(switch_relocations={}, allow_switch_data=True)
        return real(*args, **kwargs)

    with patch.object(match, 'link_calls', with_switch):
        return data_calls.build(root, source, callees, objects=OBJECTS, large=large)


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class Native(unittest.TestCase):
    """match.py's default path on compiled owners: issuance, --check-report, replay and tampers."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_frame_native_', dir=scratch)
        cls.runs = {}
        for name, source, callees, large in (
                ('frame', FRAME_SWITCH, [('func_08000400', 'bx lr')], False),
                ('buffer', switch_tests.DATA_SWITCH, [('func_08000400', data_calls.STORES)], False),
                ('thunk', THUNK_SWITCH, [('func_08000400', 'bx lr')], True),
                ('literal', LITERAL_SWITCH, [('func_08000400', 'bx lr'), ('func_08000500', 'bx lr')], False),
                ('frameless', FRAMELESS_SWITCH, [('func_08000400', 'bx lr')], False),
                ('no call', NO_CALL_SWITCH, [('func_08000400', 'bx lr')], False)):
            try:
                root = build_owner(Path(cls.temporary.name) / name, source, callees, large)
            except ValueError as error:
                # The link match.py runs first refuses the owner: no ROM image, no report.
                cls.runs[name] = (None, None, f'link refused: {error}', None)
                continue
            cls.runs[name] = (root, *data_calls.run(root))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, report):
        root = self.runs[name][0]
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def forced(self, name, patches):
        """match.main() in process with `patches` applied: (exit code or message, report or None)."""
        root = self.runs[name][0]
        path = root / 'docs/match/08000200.md'
        saved = path.read_text() if path.exists() else None
        with contextlib.ExitStack() as stack:
            for target, attribute, value in patches:
                stack.enter_context(patch.object(target, attribute, value))
            stack.enter_context(patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')))
            stack.enter_context(patch.object(sys, 'argv', ['match.py', '--root', str(root), '0x08000200']))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            if path.exists():
                path.unlink()
            try:
                match.main()
                code = 0
            except SystemExit as stop:
                code = stop.code
        report = path.read_text() if path.exists() else None
        if saved is None:
            path.unlink(missing_ok=True)
        else:
            path.write_text(saved)
        return code, report

    def check_never_retried(self, name, route):
        """Forced through the owner-switch retry the shape refuses; a report forged by admitting it anyway
        (the rule's check stubbed out) does not replay, with either control-flow line."""
        code, report = self.forced(name, [route])
        self.assertIsNone(report)
        self.assertIn('owner-switch data-buffer proof: ' + INSPECTED, str(code))
        code, forged = self.forced(name, [route, (data_buffer, 'owner_switch_frame', lambda *args: True)])
        self.assertEqual(code, 0)
        self.assertEqual(data_calls.verification(forged), data_buffer.OWNER_SWITCH_FRAME_SCHEMA)
        flow = '* control flow: ' + evidence.CALL_SUMMARY
        for text in (forged, forged.replace('* control flow: closed leaf CFG', flow)):
            with self.subTest(name=name, control_flow=flow in text):
                self.assertFalse(self.replays(name, text))

    def test_a_frameless_owner_keeps_its_switch_schema_and_never_takes_this_one(self):
        _, code, output, report = self.runs['frameless']
        self.assertEqual(code, 0, output)
        self.assertNotEqual(data_calls.verification(report), data_buffer.OWNER_SWITCH_FRAME_SCHEMA)
        self.assertTrue(self.replays('frameless', report))

        def refuse(*args, **kwargs):
            raise ValueError('switch walk refused for the test')
        self.check_never_retried('frameless', (match, 'verify_switches', refuse))

    def test_a_framed_owner_without_a_call_never_takes_this_schema(self):
        _, code, output, report = self.runs['no call']
        self.assertNotEqual(code, 0)
        self.assertIsNone(report)
        self.assertIn('switch evidence excludes fixed frames and runtime call thunks', output)
        self.assertNotIn('owner-switch data-buffer proof', output)
        self.check_never_retried('no call', (owner_switch, 'retries', lambda *args, **kwargs: True))

    def test_the_frame_owner_matches_states_no_buffer_call_and_replays(self):
        _, code, output, report = self.runs['frame']
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        self.assertEqual(data_calls.verification(report), data_buffer.OWNER_SWITCH_FRAME_SCHEMA)
        lines = report.splitlines()
        self.assertIn(NO_CALLS, lines)
        self.assertIn(FRAME_LINE, lines)
        self.assertNotIn(PLAIN_CALLS, lines)
        self.assertFalse(any(line.startswith(data_buffer.CALLS_FIELD) for line in lines))
        self.assertTrue(any(line.startswith('* stack frame: ') for line in lines))
        self.assertEqual(len([line for line in lines if line.startswith(owner_switch.LINE)]), 1)
        self.assertTrue(self.replays('frame', report))

    def test_check_report_reproduces_the_saved_report(self):
        root = self.runs['frame'][0]
        environment = dict(os.environ, FFTA_ROM=str(root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run([sys.executable, str(ROOT / 'tools/match.py'), '--root', str(root),
                                 '--check-report', '--no-write', '0x08000200'],
                                capture_output=True, text=True, env=environment, timeout=600)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('identical to the saved', result.stdout + result.stderr)

    def test_kit_main_refuses_the_frame_owner_and_its_report(self):
        root, _, _, report = self.runs['frame']
        with patch.object(data_buffer.OWNER_SWITCH_FRAME, 'enabled', False):
            self.assertFalse(self.replays('frame', report))
            with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')), \
                    patch.object(sys, 'argv', ['match.py', '--root', str(root), '--no-write', '0x08000200']), \
                    contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stop:
                match.main()
        self.assertIn('owner-switch data-buffer proof: ' + INSPECTED, str(stop.exception.code))

    def test_a_buffer_call_owner_keeps_the_data_buffer_schema(self):
        _, code, output, report = self.runs['buffer']
        self.assertEqual(code, 0, output)
        self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
        lines = report.splitlines()
        self.assertIn(PLAIN_CALLS, lines)
        self.assertIn(DATA_LINE, lines)
        self.assertNotIn(NO_CALLS, lines)
        self.assertTrue(self.replays('buffer', report))

    def test_a_call_via_owner_refuses(self):
        # The link refuses a `_call_via_rN` call beside the owner's table before any walk; the rule's own
        # check (Assembled.test_a_call_via_thunk_refuses) stands behind it.
        _, code, output, report = self.runs['thunk']
        self.assertIsNone(report)
        self.assertEqual(output, 'link refused: switch evidence excludes object, callback and runtime-thunk bindings')
        self.assertNotIn(data_buffer.OWNER_SWITCH_FRAME_SCHEMA, output)

    def test_a_function_literal_owner_refuses(self):
        # As for a thunk call, the link refuses first; Assembled.test_a_function_literal_refuses checks the rule.
        _, code, output, report = self.runs['literal']
        self.assertIsNone(report)
        self.assertEqual(output, 'link refused: switch evidence excludes object, callback and runtime-thunk bindings')

    def test_forged_or_tampered_lines_fail(self):
        lines = self.runs['frame'][3].splitlines()

        def swap(old, new):
            return [new if line == old else line for line in lines]

        at = lines.index(FRAME_LINE)
        for change, edited in (
                ('buffer calls claimed', swap(NO_CALLS, PLAIN_CALLS)),
                ('no-buffer line removed', [line for line in lines if line != NO_CALLS]),
                ('no-buffer line duplicated', lines[:lines.index(NO_CALLS) + 1] + [NO_CALLS] +
                 lines[lines.index(NO_CALLS) + 1:]),
                ('frame field relabelled', swap(FRAME_LINE, data_buffer.CALLS_FIELD +
                                                data_buffer.SUMMARIES[data_buffer.OWNER_SWITCH_FRAME_SCHEMA])),
                ('data buffer calls added', lines[:at + 1] + [DATA_LINE] + lines[at + 1:]),
                ('schema relabelled', [line.replace(data_buffer.OWNER_SWITCH_FRAME_SCHEMA, data_buffer.SCHEMA)
                                       for line in lines]),
                ('owner switch line removed', [line for line in lines if not line.startswith(owner_switch.LINE)])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('frame', '\n'.join(edited) + '\n'))

    def test_a_forged_no_buffer_report_for_a_buffer_call_owner_fails(self):
        # Every no-buffer line, with the data-buffer proof digest recomputed for the forged schema.
        root, _, _, report = self.runs['buffer']
        lines = report.splitlines()
        frame = data_buffer.OWNER_SWITCH_FRAME_SCHEMA

        def field(prefix):
            line, = [line for line in lines if line.startswith(prefix)]
            return line[len(prefix):].strip('`')

        manifest = json.loads(field(data_buffer.MANIFEST_FIELD))
        digest = data_buffer.fingerprint(
            frame, data_calls.A, bytes.fromhex(field('* compiled : ')), manifest, field('* source SHA-256: '),
            (root / 'config/functions.json').read_bytes(), (root / 'config/data_symbols.json').read_bytes(),
            field('* buffer proof SHA-256: '))
        forged = [NO_CALLS if line == PLAIN_CALLS else FRAME_LINE if line == DATA_LINE else
                  f'{data_buffer.PROOF_FIELD}`{digest}`' if line.startswith(data_buffer.PROOF_FIELD) else
                  line.replace(data_buffer.SCHEMA, frame) for line in lines]
        self.assertNotEqual(forged, lines)
        self.assertFalse(self.replays('buffer', '\n'.join(forged) + '\n'))


def real_root(root, rom):
    """080C2314's source with the approved ROM, its callees' map rows and its one data symbol."""
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build'):
        (root / name).mkdir(parents=True, exist_ok=True)
    (root / 'src/080C2314.c').write_bytes((FIXTURES / '080C2314.c').read_bytes())
    (root / 'include/ffta.h').write_bytes((FIXTURES / 'ffta.h').read_bytes())
    rows = [dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb') for start, end in REAL_ROWS]
    (root / 'config/functions.json').write_text(json.dumps(rows))
    (root / 'config/data_symbols.json').write_text(json.dumps({'data_0200F3F0': '0x0200F3F0'}))
    (root / 'symbols/functions.txt').write_text(''.join(
        f'{start:08X} {end:08X} {end - start} 0 return\n' for start, end in REAL_ROWS))
    (root / 'baserom.bin').symlink_to(Path(rom).resolve())
    return root


# 080C2314 and its fourteen callees, as the decomp's function map gives them.
REAL_ROWS = ((0x080C2314, 0x080C2616), (0x080C7EA4, 0x080C817C), (0x080C8280, 0x080C8296),
             (0x080CCD50, 0x080CCE60), (0x0812E0BC, 0x0812E0FA), (0x0812F2A4, 0x0812F2CC),
             (0x0812F328, 0x0812F34C), (0x0812F34C, 0x0812F358), (0x0812F358, 0x0812F39A),
             (0x0812F39C, 0x0812F3B0), (0x08130200, 0x081302F8), (0x08130FBC, 0x08131024),
             (0x08131378, 0x08131474), (0x08131B20, 0x08131BB6), (0x08133988, 0x081339A8))


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class Real080C2314(unittest.TestCase):
    """The byte-identical game function this schema was built for, on the approved ROM."""

    @classmethod
    def setUpClass(cls):
        if remainder_tests.approved_rom() is None:
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_frame_real_', dir=scratch)
        cls.root = real_root(Path(cls.temporary.name) / 'root', os.environ['FFTA_ROM'])
        cls.environment = dict(os.environ, FFTA_ROM=str(cls.root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run([sys.executable, str(ROOT / 'tools/match.py'), '--root', str(cls.root),
                                 '0x080C2314'], capture_output=True, text=True, env=cls.environment, timeout=900)
        cls.code, cls.output = result.returncode, result.stdout + result.stderr
        path = cls.root / 'docs/match/080C2314.md'
        cls.report = path.read_text() if path.exists() else None

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return evidence.report_matches(report, self.root, 0x080C2314)

    def test_it_matches_on_the_owner_switch_frame_schema_and_replays(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn('verdict MATCH - byte identical', self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.OWNER_SWITCH_FRAME_SCHEMA)
        lines = self.report.splitlines()
        self.assertIn(NO_CALLS, lines)
        self.assertIn(FRAME_LINE, lines)
        line, = [line for line in lines if line.startswith(owner_switch.LINE)]
        self.assertRegex(line, r'^\* buffer owner switch: `guarded-switch-owner-v1` 0x080C2314: dispatch at '
                               r'0x080C24EC, bound 5, ')
        self.assertTrue(self.replays(self.report))

    def test_check_report_reproduces_it(self):
        result = subprocess.run([sys.executable, str(ROOT / 'tools/match.py'), '--root', str(self.root),
                                 '--check-report', '--no-write', '0x080C2314'],
                                capture_output=True, text=True, env=self.environment, timeout=900)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('identical to the saved', result.stdout + result.stderr)

    def test_kit_main_refuses_it_at_the_closing_check(self):
        with patch.object(data_buffer.OWNER_SWITCH_FRAME, 'enabled', False):
            self.assertFalse(self.replays(self.report))
            with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')), \
                    patch.object(sys, 'argv', ['match.py', '--root', str(self.root), '--no-write', '0x080C2314']), \
                    contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stop:
                match.main()
        self.assertEqual(str(stop.exception.code).splitlines()[-1],
                         'switch evidence excludes fixed frames and runtime call thunks; '
                         'owner-switch data-buffer proof: ' + INSPECTED)

    def test_a_forged_buffer_calls_line_fails(self):
        lines = self.report.splitlines()
        self.assertFalse(self.replays('\n'.join(PLAIN_CALLS if line == NO_CALLS else line for line in lines) + '\n'))


if __name__ == '__main__':
    unittest.main()
