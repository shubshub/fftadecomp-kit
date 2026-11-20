"""Jump-table callees inspected by the default stack buffer walk (kit #241)."""
import ast
import json
import os
from pathlib import Path
import struct
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
import switch_callee_profile as switch_callees
# Modules, not classes: importing a TestCase class would make it run here again.
import test_buffer_discarded_return_scratch as scratch_fixture
import test_buffer_guarded_switch as switch_tests
import test_data_buffer_calls as data_calls

A, B, C = scratch_fixture.A, scratch_fixture.B, scratch_fixture.C


class SwitchCalleeTests(unittest.TestCase):
    setUp = scratch_fixture.DiscardedReturnScratchTests.setUp
    fixture = scratch_fixture.DiscardedReturnScratchTests.fixture
    switch_fixture = switch_tests.GuardedSwitchBufferTests.switch_fixture

    def prove(self, f, *, index=True):
        proof = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                      switch_callee_index=f['index'] if index else None)
        match.verify_leaf_instructions(f['data'], A, True, buffer_proof=proof,
                                       call_resolver=proof.target, incoming_narrow_reads=True)
        return proof

    def test_guarded_switch_callee_is_walked_through_every_case(self):
        for constants in (False, True):
            with self.subTest(constants=constants):
                proof = self.prove(self.switch_fixture(constants=constants))
                record, = proof.switch_callees.evidence()['callees']
                self.assertEqual(record['address'], B)
                structure = record['structure']
                self.assertEqual(structure['kind'], 'complete-guarded-buffer-switch-v1')
                self.assertEqual(structure['switch']['bound'], 1)
                self.assertEqual(len(structure['successors']), 2)
                self.assertEqual(structure['switch'].get('interposed_words', 0), 2 if constants else 0)
                line, = proof.loop_replay_lines()
                self.assertRegex(line, r'^\* buffer switch callee: `guarded-switch-callee-v1` 0x08010100: '
                                       r'dispatch at 0x080101[0-9A-F]{2}, 2 successors, [02] scalar words, '
                                       r'table [0-9a-f]{16}$')
                self.assertIn(B, proof.dependencies)

    def test_without_the_keyword_the_walk_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08010100: unresolved program-counter write'):
            self.prove(self.switch_fixture(), index=False)

    def test_every_case_keeps_the_buffer_rules(self):
        # case1 storing past the 8-byte local, or storing the pointer itself.
        for store, message in (('str r0, [r4, #8]', 'outside allocated local words'),
                               ('str r4, [r1]', 'unsupported buffer pointer use or escape|cannot be stored')):
            with self.subTest(store=store), self.assertRaisesRegex(ValueError, message):
                self.prove(self.switch_fixture(store=store))
        # case1 is reached only through the table, so these refusals show the cases are walked.
        # A case the table never names is unowned code, which the existing rule refuses.
        with self.assertRaisesRegex(ValueError, 'unowned complete-owner bytes'):
            self.prove(self.switch_fixture(case='case0'))

    def test_layout_refusals_are_the_existing_rule(self):
        for change in (dict(guard='bhs default'), dict(case='case1+1'), dict(case='child'),
                       dict(prefix='b skip\nnop\nskip:')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.prove(self.switch_fixture(**change))

    def test_tampered_table_word_refuses(self):
        f = self.switch_fixture()
        proof = self.prove(f)
        structure = proof.switch_callees.evidence()['callees'][0]['structure']
        image = bytearray(f['rom'])
        struct.pack_into('<I', image, structure['switch']['table'] + B - match.ROM_BASE, C)
        with self.assertRaises(ValueError):
            self.prove(dict(f, rom=bytes(image)))

    def test_ordinary_callees_are_unchanged(self):
        f = self.fixture(callee='str r0, [r3]\nmovs r3, #0\nbx lr')
        plain = self.prove(f, index=False)
        keyed = self.prove(f)
        self.assertEqual(keyed.switch_callees.records, {})
        self.assertEqual(plain.fingerprint(), keyed.fingerprint())
        self.assertEqual(plain.loop_replay_lines(), keyed.loop_replay_lines())

    def test_fingerprint_binds_the_record(self):
        proof = self.prove(self.switch_fixture())
        before = proof.fingerprint()
        record = proof.switch_callees.records[B]
        proof.switch_callees.records[B] = dict(record, structure=dict(record['structure'], successors=[]))
        self.assertNotEqual(proof.fingerprint(), before)
        proof.switch_callees.records[B] = record
        self.assertEqual(proof.fingerprint(), before)

    def test_only_the_plain_stack_argument_proof_takes_switch_callees(self):
        f = self.switch_fixture()
        for build in (lambda: match.BufferCallProof(f['rom'], f['mapping'], switch_callee_index=f['index']),
                      lambda: match.FunctionBufferCallProof(f['rom'], f['mapping'], stack_arguments=True,
                                                            switch_callee_index=f['index'])):
            with self.assertRaisesRegex(ValueError, 'switch callees require the plain stack-argument buffer proof'):
                build()
        proof = self.prove(f)
        other = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, switch_callee_index=f['index'])
        callee = f['rom'][B - match.ROM_BASE:B - match.ROM_BASE + 64]
        with self.assertRaisesRegex(ValueError, 'require their plain stack-argument buffer proof'):
            proof.switch_callees.inspect(other, B, callee)
        with patch.object(proof, 'stack_arguments', False), \
                self.assertRaisesRegex(ValueError, 'require their plain stack-argument buffer proof'):
            proof.switch_callees.inspect(proof, B, callee)

    def test_snapshots_must_be_bytes(self):
        f = self.switch_fixture()
        for field in ('mapping', 'index'):
            with self.subTest(field=field), self.assertRaisesRegex(
                    ValueError, 'require immutable ROM, mapping and index snapshots'):
                switch_callees.SwitchCallees(f['rom'], *(
                    (f['mapping'].decode(), f['index']) if field == 'mapping' else (f['mapping'], f['index'].decode())))

    def test_version_one_reports_replay_unchanged(self):
        f = self.fixture(callee='str r0, [r3]\nmovs r3, #0\nbx lr')
        proof = match.BufferCallProof(f['rom'], f['mapping'], loop_replay=True)
        match.verify_leaf_instructions(f['data'], A, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=True)
        root = self.root / 'replay-v1'
        (root / 'symbols').mkdir(parents=True)
        (root / 'baserom.bin').write_bytes(f['rom'])
        (root / 'symbols/functions.txt').write_bytes(f['index'])
        lines = [f"* compiled : `{f['data'].hex()}`", f'* buffer calls: {evidence.BUFFER_SUMMARY}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`',
                 f"**MATCH - byte identical** - {len(f['data'])}/{len(f['data'])} bytes"]
        with patch.dict(os.environ, {'FFTA_ROM': str(root / 'baserom.bin')}):
            self.assertTrue(evidence.buffer_report_matches(lines, root, A, f['mapping'], stack_arguments=False))

    def test_an_aborted_joined_pass_leaves_no_record(self):
        # A joined pass that ends in a loop replay may reach callees the replay does not;
        # like the base ledgers, its switch records never enter the evidence.
        f = self.switch_fixture()
        real = match.BufferCallProof._check_arguments
        stale = 0x08010200

        def joined_then_replay(proof, address, *args, replay, **kwargs):
            if not replay:
                proof.switch_callees.records[stale] = {'aborted': True}
                raise match._LoopReplayRequired()
            return real(proof, address, *args, replay=replay, **kwargs)

        with patch.object(match.BufferCallProof, '_check_arguments', joined_then_replay):
            proof = self.prove(f)
        self.assertEqual(sorted(proof.switch_callees.records), [B])
        self.assertEqual(len([line for line in proof.loop_replay_lines()
                              if line.startswith('* buffer switch callee')]), 1)

        # A record made before the aborted pass survives it.
        def aborted_then_empty(proof, address, *args, replay, **kwargs):
            if not replay:
                proof.switch_callees.records.clear()
                raise match._LoopReplayRequired()
            return proof.word_result({}, {})

        with patch.object(match.BufferCallProof, '_check_arguments', aborted_then_empty):
            proof.check_arguments(C, {}, [], {}, frozenset())
        self.assertEqual(sorted(proof.switch_callees.records), [B])

    def test_a_record_must_agree_on_every_visit(self):
        f = self.switch_fixture()
        proof = self.prove(f)
        record = proof.switch_callees.records[B]
        proof.switch_callees.records[B] = dict(record, body_sha256='0' * 64)
        span = proof.span(B)
        with self.assertRaisesRegex(ValueError, 'inspected differently on different paths'):
            proof.switch_callees.inspect(proof, B, span)

    def test_a_report_without_a_switch_callee_replays_without_an_index(self):
        # Without a function index no callee is delegated, so a report that needed none still replays.
        # (The register-indexed store needs the version-2 proof, which this report is.)
        f = self.fixture(callee='movs r2, #0\nstr r0, [r3, r2]\nmovs r3, #0\nbx lr')
        proof = self.prove(f)
        root = self.root / 'unindexed'
        (root / 'symbols').mkdir(parents=True)
        (root / 'baserom.bin').write_bytes(f['rom'])
        lines = [f"* compiled : `{f['data'].hex()}`",
                 f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`',
                 *proof.loop_replay_lines(),
                 f"**MATCH - byte identical** - {len(f['data'])}/{len(f['data'])} bytes"]
        with patch.dict(os.environ, {'FFTA_ROM': str(root / 'baserom.bin')}):
            self.assertTrue(evidence.buffer_report_matches(lines, root, A, f['mapping'], stack_arguments=True))

    def test_report_replays_and_tampers_fail(self):
        f = self.switch_fixture()
        proof = self.prove(f)
        root = self.root / 'replay'
        (root / 'symbols').mkdir(parents=True)
        (root / 'baserom.bin').write_bytes(f['rom'])
        (root / 'symbols/functions.txt').write_bytes(f['index'])
        lines = [f"* compiled : `{f['data'].hex()}`",
                 f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`',
                 *proof.loop_replay_lines(),
                 f"**MATCH - byte identical** - {len(f['data'])}/{len(f['data'])} bytes"]
        with patch.dict(os.environ, {'FFTA_ROM': str(root / 'baserom.bin')}):
            accepted = lambda candidate: evidence.buffer_report_matches(
                candidate, root, A, f['mapping'], stack_arguments=True)
            self.assertTrue(accepted(lines))
            at = next(i for i, line in enumerate(lines) if line.startswith('* buffer switch callee:'))
            tampers = {
                'successors': lines[at].replace('2 successors', '3 successors'),
                'table': lines[at][:-16] + '0' * 16,
                'indented': '  ' + lines[at],
            }
            for name, line in tampers.items():
                with self.subTest(name=name):
                    self.assertFalse(accepted(lines[:at] + [line] + lines[at + 1:]))
            with self.subTest(name='removed'):
                self.assertFalse(accepted(lines[:at] + lines[at + 1:]))
            with self.subTest(name='duplicated'):
                self.assertFalse(accepted(lines[:at + 1] + lines[at:]))
            with self.subTest(name='fingerprint'):
                self.assertFalse(accepted([line if not line.startswith('* buffer proof SHA-256')
                                           else '* buffer proof SHA-256: `' + '0' * 64 + '`' for line in lines]))
            (root / 'symbols/functions.txt').unlink()
            with self.subTest(name='no index'):
                self.assertFalse(accepted(lines))


# The #236 data-buffer caller with a jump-table callee: func_08000400(value, out) stores
# through `out` in both cases of a guarded two-entry table.
SWITCH_STORES = """push {r4, lr}
adds r4, r1, #0
cmp r0, #1
bhi default
lsls r0, r0, #2
ldr r1, pointer
adds r0, r0, r1
ldr r0, [r0]
mov pc, r0
.balign 4, 0
pointer: .word table
table: .word case0, case1
case0: movs r0, #7
strh r0, [r4]
b done
case1: movs r0, #8
strh r0, [r4, #6]
b done
default: movs r0, #0
done: pop {r4}
pop {r1}
bx r1"""


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class DataBufferCompositionTests(unittest.TestCase):
    """A typed-data caller reaches the switch callee through data_buffer_profile's proof."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='switch_callee_data_', dir=scratch)
        cls.root = data_calls.build(Path(cls.temporary.name) / 'switch',
                                    data_calls.PLAIN % dict(size=4, last=3, extra=''),
                                    [('func_08000400', SWITCH_STORES)])
        cls.code, cls.output, cls.report = data_calls.run(cls.root)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return evidence.report_matches(report, self.root, data_calls.A)

    def test_the_data_buffer_report_carries_and_replays_the_switch_callee(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn('verdict MATCH - byte identical', self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        line, = [line for line in self.report.splitlines() if line.startswith('* buffer switch callee:')]
        self.assertRegex(line, r'^\* buffer switch callee: `guarded-switch-callee-v1` 0x08000400: '
                               r'dispatch at 0x080004[0-9A-F]{2}, 2 successors, 0 scalar words, table [0-9a-f]{16}$')
        self.assertTrue(self.replays(self.report))

    def test_tampered_removed_or_duplicated_lines_fail(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith('* buffer switch callee:'))
        for name, edited in (('successors', lines[:at] + [lines[at].replace('2 successors', '3 successors')] + lines[at + 1:]),
                             ('table', lines[:at] + [lines[at][:-16] + '0' * 16] + lines[at + 1:]),
                             ('removed', lines[:at] + lines[at + 1:]),
                             ('duplicated', lines[:at + 1] + lines[at:])):
            with self.subTest(name=name):
                self.assertFalse(self.replays('\n'.join(edited) + '\n'))

    def test_a_replay_without_an_index_proves_without_summaries(self):
        # No function index: the replay still proves, with no delegation, and so refuses this report.
        index = self.root / 'symbols/functions.txt'
        saved, seen, real = index.read_bytes(), [], data_buffer.prove

        def recording(*arguments, **options):
            seen.append(options.get('index'))
            return real(*arguments, **options)

        index.unlink()
        try:
            with patch.object(data_buffer, 'prove', recording):
                self.assertFalse(self.replays(self.report))
        finally:
            index.write_bytes(saved)
        self.assertEqual(seen, [None])

    def test_without_the_index_the_data_proof_refuses_at_the_dispatch(self):
        rom = (self.root / 'baserom.bin').read_bytes()
        mapping = (self.root / 'config/functions.json').read_bytes()
        objects = (self.root / 'config/data_symbols.json').read_bytes()
        code = bytes.fromhex(next(line for line in self.report.splitlines()
                                  if line.startswith('* compiled : '))[len('* compiled : `'):-1])
        calls = {data_calls.A + offset: int(name[5:], 16) for offset, name in json.loads(next(
            line for line in self.report.splitlines()
            if line.startswith(data_buffer.MANIFEST_FIELD))[len(data_buffer.MANIFEST_FIELD) + 1:-1])['calls']}
        symbols = match.parse_data_symbols(objects)
        literals = {offset: (name, symbols[name] + delta) for offset, name, delta in json.loads(next(
            line for line in self.report.splitlines()
            if line.startswith(data_buffer.MANIFEST_FIELD))[len(data_buffer.MANIFEST_FIELD) + 1:-1])['data']}
        index = (self.root / 'symbols/functions.txt').read_bytes()
        _, proof, schema, _ = data_buffer.prove(code, data_calls.A, rom, mapping, objects, calls, literals,
                                                index=index)
        self.assertEqual((schema, sorted(proof.switch_callees.records)), (data_buffer.SCHEMA, [data_calls.CALLEES]))
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08000400: unresolved program-counter write'):
            data_buffer.prove(code, data_calls.A, rom, mapping, objects, calls, literals)


class WiringTests(unittest.TestCase):
    def test_only_reviewed_construction_sites_pass_the_index(self):
        found = set()
        for path in sorted((ROOT / 'tools').glob('*.py')):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call):
                            for keyword in node.keywords:
                                if keyword.arg == 'switch_callee_index':
                                    self.assertFalse(isinstance(keyword.value, ast.Constant), ast.dump(keyword))
                                    found.add((path.name, function.name))
        self.assertEqual(found, {('match.py', 'main'), ('match_evidence.py', 'buffer_report_matches'),
                                 ('function_thunk_profile.py', 'verify_source'),
                                 ('data_buffer_profile.py', 'prove')})

    def test_the_data_proof_receives_the_index_from_both_producers(self):
        # match.main and the data-buffer replay pass an index expression to data_buffer.prove.
        found = set()
        for name in ('match.py', 'data_buffer_profile.py'):
            for function in ast.walk(ast.parse((ROOT / 'tools' / name).read_text())):
                if isinstance(function, ast.FunctionDef):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call) and any(
                                keyword.arg == 'index' and not isinstance(keyword.value, ast.Constant)
                                for keyword in node.keywords):
                            callee = node.func.attr if isinstance(node.func, ast.Attribute) else node.func.id
                            found.add((name, function.name, callee))
        self.assertEqual(found, {('match.py', 'main', 'prove'),
                                 ('data_buffer_profile.py', 'verify_source', 'prove')})

    def test_data_buffer_reports_accept_and_compare_the_switch_callee_line(self):
        self.assertIn('* buffer switch callee', data_buffer.FIELDS)

    def test_other_reports_refuse_the_switch_callee_line(self):
        tree = ast.parse((ROOT / 'tools' / 'match_evidence.py').read_text())
        lists = [node for node in ast.walk(tree) if isinstance(node, ast.Tuple) and any(
            isinstance(item, ast.Constant) and isinstance(item.value, str) and
            item.value.startswith('* buffer loop replay') for item in node.elts)]
        self.assertGreaterEqual(len(lists), 6)
        for node in lists:
            with self.subTest(line=node.lineno):
                self.assertTrue(any(isinstance(item, ast.Constant) and isinstance(item.value, str) and
                                    item.value.startswith('* buffer switch callee') for item in node.elts))
        # The function-buffer report compares the switch callee lines with the recomputed proof.
        self.assertTrue(any(isinstance(node, ast.Call) and getattr(node.func, 'attr', None) == 'startswith' and
                            node.args and isinstance(node.args[0], ast.Constant) and
                            node.args[0].value == '* buffer switch callee' for node in ast.walk(tree)))

    def test_switch_callees_are_never_assigned_outside_the_constructor(self):
        for path in sorted((ROOT / 'tools').glob('*.py')):
            for node in ast.walk(ast.parse(path.read_text())):
                if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                    for target in targets:
                        if isinstance(target, ast.Attribute) and target.attr == 'switch_callees':
                            self.assertEqual(path.name, 'match.py', ast.dump(target))



# Case bodies for the edge probes: within the 8-byte local, past it, and storing the pointer.
GOOD, PAST, ESCAPE = 'movs r0, #7\nstr r0, [r4]', 'movs r0, #7\nstr r0, [r4, #8]', 'str r4, [r1]'
CALLER = 'push {r4, lr}\nsub sp, #8\nmov r3, sp\nbl callee\n%s\nadd sp, #8\npop {r4}\npop {r0}\nbx r0'


def table_callee(cases, *, default='movs r0, #0', guard='bhi default', selector='r0', prefix='', tag=''):
    """An agbcc guarded word switch on `selector`; the caller's pointer arrives in r3 and lives in r4."""
    labels = ', '.join(f'{tag}case{i}' for i in range(len(cases)))
    bodies = ''.join(f'{tag}case{i}: {case}\nb {tag}done\n' for i, case in enumerate(cases))
    return ('push {r4, lr}\nadds r4, r3, #0\nmovs r3, #0\n' + prefix +
            f'\ncmp {selector}, #{len(cases) - 1}\n{guard.replace("default", tag + "default")}\n'
            f'lsls r0, {selector}, #2\nldr r1, {tag}pointer\n'
            f'adds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n.balign 4, 0\n{tag}pointer: .word {tag}table\n'
            f'{tag}table: .word {labels}\n{bodies}{tag}default: {default}\n{tag}done: pop {{r4}}\npop {{r1}}\nbx r1')


def looped_callee(step, trips, store='str r0, [r4]'):
    """The guarded switch inside a counted loop; the pointer advances `step` bytes per trip."""
    return ('push {r4, r5, lr}\nadds r4, r3, #0\nmovs r3, #0\nmovs r5, #0\n'
            'loop: adds r0, r5, #0\ncmp r0, #1\nbhi default\nlsls r0, r0, #2\nldr r1, pointer\n'
            'adds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n.balign 4, 0\npointer: .word table\n'
            'table: .word case0, case1\n'
            f'case0: movs r0, #7\n{store}\nb next\ncase1: movs r0, #8\n{store}\nb next\n'
            f'default: movs r0, #0\n{store}\nnext: adds r4, #{step}\nadds r5, #1\ncmp r5, #{trips}\nbne loop\n'
            'pop {r4, r5}\npop {r1}\nbx r1')


class SwitchCalleeEdgeTests(unittest.TestCase):
    """Every successor of a delegated dispatch is walked; other layouts keep today's refusal."""
    setUp = scratch_fixture.DiscardedReturnScratchTests.setUp

    def build(self, callee, *, child='bx lr', grand='bx lr', after='', caller=None):
        names = ('caller', 'callee', 'child', 'grand')
        bodies = (caller or CALLER % after, callee, child, grand)
        text = ('.syntax unified\n.arch armv4t\n.thumb\n.text\n.global ' +
                ', '.join(f'{name}, {name}_end' for name in names) + '\n')
        for position, (name, body) in enumerate(zip(names, bodies)):
            text += (f'.org {position * 0x100:#x}\n' if position else '') + f'{name}:\n{body}\n{name}_end:\n'
        (self.root / 'edge.s').write_text(text)
        for command in (
                ['arm-none-eabi-as', '-mthumb-interwork', str(self.root / 'edge.s'), '-o', str(self.root / 'e.o')],
                ['arm-none-eabi-ld', '-Ttext=0x08010000', '-e', 'caller', str(self.root / 'e.o'),
                 '-o', str(self.root / 'e.elf')],
                ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text', str(self.root / 'e.elf'),
                 str(self.root / 'e.bin')]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / 'e.elf').read_bytes())
        symbols = {symbol['name']: symbol['value'] for symbol in image['symbols']}
        rows = [dict(rom=f'0x{symbols[name]:08X}', end=f'0x{symbols[name + "_end"]:08X}', mode='thumb', instrs=0)
                for name in names]
        binary = (self.root / 'e.bin').read_bytes()
        index = ''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
                        f'{int(row["end"], 16) - int(row["rom"], 16)} 0 return\n' for row in rows).encode()
        return dict(data=binary[:symbols['caller_end'] - A], rom=b'\0' * (A - match.ROM_BASE) + binary,
                    mapping=json.dumps(rows).encode(), index=index)

    prove = SwitchCalleeTests.prove

    def report(self, f, proof, *, stack_arguments=True):
        root = self.root / 'replay'
        (root / 'symbols').mkdir(parents=True, exist_ok=True)
        (root / 'baserom.bin').write_bytes(f['rom'])
        (root / 'symbols/functions.txt').write_bytes(f['index'])
        summary = evidence.STACK_BUFFER_SUMMARY if stack_arguments else evidence.BUFFER_SUMMARY
        lines = [f"* compiled : `{f['data'].hex()}`", f'* buffer calls: {summary}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`', *proof.loop_replay_lines(),
                 f"**MATCH - byte identical** - {len(f['data'])}/{len(f['data'])} bytes"]

        def accepted(candidate):
            with patch.dict(os.environ, {'FFTA_ROM': str(root / 'baserom.bin')}):
                return evidence.buffer_report_matches(candidate, root, A, f['mapping'],
                                                      stack_arguments=stack_arguments)
        return lines, accepted

    def test_the_default_edge_is_walked(self):
        proof = self.prove(self.build(table_callee([GOOD, GOOD], default='movs r0, #0\nstr r0, [r4, #4]')))
        self.assertEqual(len(proof.switch_callees.records[B]['structure']['successors']), 2)
        for default in (PAST, ESCAPE):
            with self.subTest(default=default), self.assertRaisesRegex(
                    ValueError, 'buffer callee 0x08010100: .*(outside allocated local words|use or escape)'):
                self.prove(self.build(table_callee([GOOD, GOOD], default=default)))

    def test_every_table_entry_is_walked(self):
        proof = self.prove(self.build(table_callee([GOOD] * 4)))
        self.assertEqual(len(proof.switch_callees.records[B]['structure']['successors']), 4)
        self.assertIn('4 successors', proof.loop_replay_lines()[0])
        for case in range(4):
            cases = [GOOD] * 4
            cases[case] = PAST
            with self.subTest(case=case), self.assertRaisesRegex(ValueError, 'outside allocated local words'):
                self.prove(self.build(table_callee(cases)))

    def test_calls_and_returns_inside_a_case_keep_the_buffer_rules(self):
        call = 'adds r3, r4, #0\nbl child'
        self.prove(self.build(table_callee([GOOD, call]), child='str r0, [r3, #4]\nmovs r3, #0\nbx lr'))
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08010100: buffer callee 0x08010200: '
                                                '.*outside allocated local words'):
            self.prove(self.build(table_callee([GOOD, call]), child='str r0, [r3, #8]\nmovs r3, #0\nbx lr'))
        # A case returning the pointer: the caller still tracks it, and storing it escapes.
        returning = table_callee([GOOD, 'adds r0, r4, #0'])
        self.prove(self.build(returning, after='str r1, [r0]'))
        with self.assertRaisesRegex(ValueError, '^unsupported stack-alias use or escape$'):
            self.prove(self.build(returning, after='str r0, [r1]'))

    def test_a_switch_inside_a_loop(self):
        # Constant pointer: the cases join at the loop head without a replay.
        proof = self.prove(self.build(looped_callee(0, 2)))
        self.assertEqual(sorted(proof.switch_callees.records), [B])
        self.assertEqual(proof.loop_replays, {})
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            self.prove(self.build(looped_callee(0, 2, store='str r0, [r4, #8]')))
        # An advancing pointer joins inconsistently: the aborted joined pass is restored and the
        # bounded replay re-inspects the callee, so its record survives exactly once.
        f = self.build(looped_callee(4, 2))
        proof = self.prove(f)
        self.assertEqual(sorted(proof.loop_replays), [B])
        self.assertEqual(sorted(proof.switch_callees.records), [B])
        kinds = [line.split(':', 1)[0] for line in proof.loop_replay_lines()]
        self.assertEqual(kinds, ['* buffer loop replay', '* buffer switch callee'])
        lines, accepted = self.report(f, proof)
        self.assertTrue(accepted(lines))
        loop_at = next(i for i, line in enumerate(lines) if line.startswith('* buffer loop replay'))
        swapped = list(lines)
        swapped[loop_at], swapped[loop_at + 1] = swapped[loop_at + 1], swapped[loop_at]
        self.assertFalse(accepted(swapped))
        self.assertFalse(accepted(lines[:loop_at + 1] + lines[loop_at + 2:]))
        self.assertIn('writes sp+0:4 sp+4:4;', lines[loop_at])
        # A third trip (its selector 2 takes the default edge) reaches past the local.
        with self.assertRaisesRegex(ValueError, 'bounded loop replay.*outside allocated local words'):
            self.prove(self.build(looped_callee(4, 3)))

    def test_a_nested_switch_callee(self):
        forward = 'push {lr}\nbl child\npop {r0}\nbx r0'
        child = table_callee([GOOD, 'movs r0, #8\nstr r0, [r4, #4]'])
        proof = self.prove(self.build(forward, child=child))
        self.assertEqual(sorted(proof.switch_callees.records), [C])
        self.assertRegex(proof.loop_replay_lines()[0], r'^\* buffer switch callee: `guarded-switch-callee-v1` 0x08010200:')
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08010100: buffer callee 0x08010200: '
                                                '.*outside allocated local words'):
            self.prove(self.build(forward, child=table_callee([GOOD, PAST])))

    def test_two_switch_callees_are_two_sorted_lines(self):
        caller = ('push {r4, lr}\nsub sp, #8\nmov r3, sp\nbl child\nmov r3, sp\nbl callee\n'
                  'add sp, #8\npop {r4}\npop {r0}\nbx r0')
        f = self.build(table_callee([GOOD, GOOD]), child=table_callee([GOOD, GOOD, GOOD], tag='c_'), caller=caller)
        proof = self.prove(f)
        self.assertEqual(sorted(proof.switch_callees.records), [B, C])
        lines, accepted = self.report(f, proof)
        self.assertTrue(accepted(lines))
        at = next(i for i, line in enumerate(lines) if line.startswith('* buffer switch callee'))
        self.assertIn('0x08010100', lines[at])
        self.assertIn('0x08010200', lines[at + 1])
        swapped = lines[:at] + [lines[at + 1], lines[at]] + lines[at + 2:]
        self.assertFalse(accepted(swapped))
        self.assertFalse(accepted(lines[:at] + lines[at + 1:]))
        self.assertFalse(accepted(lines[:at] + [lines[at + 1].replace('0x08010200', '0x08010100')] + lines[at + 1:]))

    def test_two_tables_in_one_callee_refuse(self):
        callee = ('push {r4, lr}\nadds r4, r3, #0\nmovs r3, #0\n'
                  'cmp r0, #1\nbhi mid\nlsls r0, r0, #2\nldr r1, p1\nadds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n'
                  '.balign 4, 0\np1: .word t1\nt1: .word a0, a1\na0: movs r0, #0\nb second\na1: movs r0, #1\n'
                  'b second\nmid: movs r0, #0\nsecond: cmp r0, #1\nbhi done\nlsls r0, r0, #2\nldr r1, p2\n'
                  'adds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n.balign 4, 0\np2: .word t2\nt2: .word b0, b1\n'
                  'b0: str r0, [r4]\nb done\nb1: str r0, [r4, #4]\ndone: pop {r4}\npop {r1}\nbx r1')
        with self.assertRaisesRegex(ValueError, 'buffer switch requires one guarded table'):
            self.prove(self.build(callee))

    def test_unguarded_and_preloaded_tables_keep_todays_refusal(self):
        unguarded = table_callee([GOOD, GOOD]).replace('cmp r0, #1\nbhi default\n', '')
        preloaded = ('push {r4, lr}\nadds r4, r3, #0\nmovs r3, #0\nldr r1, object\nldr r2, pointer\n'
                     'guard: cmp r0, #1\nbhi guard\nlsls r3, r0, #2\nadds r3, r3, r2\nldr r3, [r3]\nmov pc, r3\n'
                     '.balign 4, 0\nobject: .word 0x02000000\npointer: .word table\ntable: .word case0, case1\n'
                     'case0: movs r0, #7\nstr r0, [r4]\nb done\ncase1: movs r0, #8\nstr r0, [r4, #4]\n'
                     'done: pop {r4}\npop {r1}\nbx r1')
        for name, callee in (('unguarded', unguarded), ('preloaded', preloaded)):
            f = self.build(callee)
            if name == 'preloaded':
                self.assertIsNotNone(match.preloaded_switch_encoding(
                    f['rom'][B - match.ROM_BASE:B - match.ROM_BASE + 0x100], B, 28))
            for index in (True, False):
                with self.subTest(name=name, index=index), self.assertRaisesRegex(
                        ValueError, r'^buffer callee 0x08010100: unresolved program-counter write$'):
                    self.prove(f, index=index)

    def test_a_branch_around_the_guard_refuses(self):
        bypass = table_callee([GOOD, GOOD], prefix='cmp r2, #0\nbeq dispatch').replace(
            'bhi default\nlsls', 'bhi default\ndispatch: lsls')
        self.assertIn('dispatch: lsls', bypass)
        with self.assertRaisesRegex(ValueError, r'^buffer callee 0x08010100: (structural inventory is not closed|'
                                                r'.*bypassed by an unverified predecessor edge)'):
            self.prove(self.build(bypass))

    def test_the_pointer_as_the_selector_refuses(self):
        for cases in ([GOOD, GOOD], [GOOD]):
            with self.subTest(cases=len(cases)), self.assertRaisesRegex(ValueError, 'use or escape'):
                self.prove(self.build(table_callee(cases, selector='r4')))

    def test_a_version_one_report_cannot_carry_a_switch_callee_line(self):
        f = self.build('str r0, [r3]\nmovs r3, #0\nbx lr')
        proof = match.BufferCallProof(f['rom'], f['mapping'], loop_replay=True)
        match.verify_leaf_instructions(f['data'], A, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=True)
        lines, accepted = self.report(f, proof, stack_arguments=False)
        self.assertTrue(accepted(lines))
        forged = ('* buffer switch callee: `guarded-switch-callee-v1` 0x08010100: dispatch at 0x08010110, '
                  '2 successors, 0 scalar words, table 0000000000000000')
        self.assertFalse(accepted(lines[:3] + [forged] + lines[3:]))


class MappingParseTests(unittest.TestCase):
    """The delegation decodes its mapping snapshot once per proof, however many callees it inspects."""
    setUp = scratch_fixture.DiscardedReturnScratchTests.setUp
    build = SwitchCalleeEdgeTests.build

    def walk(self, f):
        """Prove `f` with the module's `json.loads` and `inspect` counted."""
        decoded, inspected, real = [], [], switch_callees.SwitchCallees.inspect

        def loads(text):
            decoded.append(text)
            return json.loads(text)

        def inspect(profile, proof, address, data):
            inspected.append(address)
            return real(profile, proof, address, data)

        proof = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                      switch_callee_index=f['index'])
        with patch.object(switch_callees, 'json', unittest.mock.Mock(loads=loads)), \
                patch.object(switch_callees.SwitchCallees, 'inspect', inspect):
            match.verify_leaf_instructions(f['data'], A, True, buffer_proof=proof,
                                           call_resolver=proof.target, incoming_narrow_reads=True)
        return proof, decoded, inspected

    def fixtures(self):
        # Two callers, each reaching a jump-table callee and an ordinary one; the second
        # mapping has one ARM row more, so the two snapshots differ in a row a Thumb-only list would drop.
        caller = ('push {r4, lr}\nsub sp, #8\nmov r3, sp\nbl child\nmov r3, sp\nbl callee\n'
                  'add sp, #8\npop {r4}\npop {r0}\nbx r0')
        f = self.build(table_callee([GOOD, GOOD]), child='str r0, [r3]\nmovs r3, #0\nbx lr', caller=caller)
        rows = json.loads(f['mapping'])
        extra = dict(rom='0x08010400', end='0x08010404', mode='arm', instrs=0)
        return f, dict(f, mapping=json.dumps(rows + [extra]).encode())

    def test_several_callees_decode_the_mapping_once(self):
        f, _ = self.fixtures()
        proof, decoded, inspected = self.walk(f)
        self.assertGreaterEqual(len(set(inspected)), 2)
        self.assertGreaterEqual(len(inspected), 2)
        self.assertEqual(decoded, [f['mapping']])
        self.assertEqual(sorted(proof.switch_callees.records), [B])

    def test_each_proof_decodes_its_own_mapping(self):
        first, second = self.fixtures()
        self.assertNotEqual(first['mapping'], second['mapping'])
        one, decoded_one, _ = self.walk(first)
        two, decoded_two, _ = self.walk(second)
        self.assertEqual((decoded_one, decoded_two), ([first['mapping']], [second['mapping']]))
        self.assertEqual(one.switch_callees.entries(), json.loads(first['mapping']))
        self.assertEqual(two.switch_callees.entries(), json.loads(second['mapping']))

    def test_one_decode_gives_the_evidence_of_a_decode_per_callee(self):
        f, _ = self.fixtures()
        cached, _, _ = self.walk(f)
        with patch.object(switch_callees.SwitchCallees, 'entries',
                          lambda profile: json.loads(profile.mapping)):
            fresh, _, _ = self.walk(f)
        self.assertEqual(cached.switch_callees.records, fresh.switch_callees.records)
        self.assertEqual(cached.fingerprint(), fresh.fingerprint())
        self.assertEqual(cached.loop_replay_lines(), fresh.loop_replay_lines())


if __name__ == '__main__':
    unittest.main()
