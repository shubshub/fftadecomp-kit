"""A guarded jump table in the owner of the default stack buffer walk (owner_switch_buffer_profile)."""
import argparse
import hashlib
import json
import os
import re
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
import owner_switch_buffer_profile as owner_switch
# A module, not its classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls

A, B, C = 0x08010000, 0x08010100, 0x08010200
CALLEE = 'movs r1, #5\nstrh r1, [r0, #2]\nmovs r0, #0\nbx lr'


class OwnerSwitchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def fixture(self, *, case0='mov r0, sp\nbl callee', case1='movs r0, #1', case2='add r0, sp, #4\nbl callee',
                loads='', words='', guard='bhi default', bound=2, table='case0, case1, case2', extra='',
                callee=CALLEE, body=None):
        """caller(index, out): a three-entry guarded table; cases 0 and 2 pass an 8-byte local."""
        caller = ('push {r4, lr}\nsub sp, #8\nadds r4, r1, #0\n' + loads + f'cmp r0, #{bound}\n' + guard + '\n'
                  'dispatch: lsls r0, r0, #2\nldr r1, pointer\nadds r0, r0, r1\nldr r0, [r0]\nmov pc, r0\n'
                  '.balign 4, 0\n' + words + 'pointer: .word table\ntable: .word ' + table + '\n'
                  f'case0: {case0}\nb done\ncase1: {case1}\nb done\ncase2: {case2}\nb done\n'
                  'default: movs r0, #0\ndone: add sp, #8\npop {r4}\npop {r1}\nbx r1\n' + extra)
        if body is not None:
            caller = body
        assembly = self.root / 'fixture.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
                            '.global caller, caller_end, callee, callee_end, child, child_end\n'
                            f'caller:\n{caller}\ncaller_end:\n.org 0x100\n'
                            f'callee:\n{callee}\ncallee_end:\n.org 0x200\n'
                            'child:\nbx lr\nchild_end:\n.org 0x300\nstray:\nbx lr\n')
        for command in (
                ['arm-none-eabi-as', '-mthumb-interwork', str(assembly), '-o', str(self.root / 'f.o')],
                ['arm-none-eabi-ld', '-Ttext=0x08010000', '-e', 'caller', str(self.root / 'f.o'),
                 '-o', str(self.root / 'f.elf')],
                ['arm-none-eabi-objcopy', '-O', 'binary', '--only-section=.text', str(self.root / 'f.elf'),
                 str(self.root / 'rom.bin')]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / 'f.elf').read_bytes())
        symbols = {symbol['name']: symbol['value'] for symbol in image['symbols']}
        rows = [dict(rom=f'0x{symbols[name]:08X}', end=f'0x{symbols[name + "_end"]:08X}', mode='thumb', instrs=0)
                for name in ('caller', 'callee', 'child')]
        binary = (self.root / 'rom.bin').read_bytes()
        index = ''.join(f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
                        f'{int(row["end"], 16) - int(row["rom"], 16)} 0 return\n' for row in rows).encode()
        return dict(data=binary[:symbols['caller_end'] - A], rom=b'\0' * (A - match.ROM_BASE) + binary,
                    mapping=json.dumps(rows).encode(), index=index)

    def plain(self, f, **options):
        options = dict(dict(stack_arguments=True, loop_replay=True, bios_wrappers=True,
                            copy_helper_index=f['index'], switch_callee_index=f['index']), **options)
        return match.BufferCallProof(f['rom'], f['mapping'], **options)

    def refinement(self, f):
        import analyze
        return analyze.refine_function(f['data'], A, json.loads(f['mapping']), max_bytes=len(f['data']),
                                       max_instructions=len(f['data']) // 2, rom_end=0x09000000,
                                       same_owner_long_branches=True)

    def linked(self, f):
        """The calls and table words a link gives: those of the owner's closed ROM graph."""
        import owner_graph_profile as graph
        _, _, _, calls, words = graph.graph(f['data'], A, self.refinement(f))
        return calls, words

    def walk(self, f, proof=None, calls=None, linked=None):
        if calls is None and linked is None:
            calls, linked = self.linked(f)
        proof = proof or self.plain(f)
        owner_switch.walk(proof, f['data'], A, calls, linked)
        return proof

    # Positives.

    def test_every_case_is_walked_with_the_buffer_rules(self):
        f = self.fixture()
        proof = self.walk(f)
        self.assertEqual(sorted(proof.dependencies), [B])
        record = proof.owner_switch.evidence()
        self.assertEqual((record['policy'], record['address'], record['switch']['bound']),
                         (owner_switch.POLICY, A, 2))
        self.assertEqual(len(record['successors']), 3)
        # The table hash covers the pointer and every table word, read independently here.
        switch = record['switch']
        self.assertEqual(record['table_words_sha256'], hashlib.sha256(
            f['data'][switch['literal']:switch['table'] + 4 * (switch['bound'] + 1)]).hexdigest())
        line, = proof.loop_replay_lines()
        self.assertRegex(line, r'^\* buffer owner switch: `guarded-switch-owner-v1` 0x08010000: '
                               r'dispatch at 0x080100[0-9A-F]{2}, bound 2, 3 successors, table [0-9a-f]{16}; ' +
                               re.escape(owner_switch.POINTER_RULE) + '$')

    def test_the_walk_is_repeatable(self):
        f = self.fixture()
        first, second = self.walk(f), self.walk(f)
        self.assertEqual(first.fingerprint(), second.fingerprint())
        self.assertEqual(first.loop_replay_lines(), second.loop_replay_lines())

    def test_each_case_is_checked(self):
        # A case reached only through the table: past the local, an escape, a returned local pointer.
        for name, case, message in (
                ('past the local', 'add r0, sp, #8\nbl callee', 'outside allocated local words'),
                ('stored pointer', 'mov r2, sp\nstr r2, [r4]', 'escape|cannot be stored'),
                ('returned pointer', 'mov r0, sp', 'escapes through a return register')):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                self.walk(self.fixture(case1=case))

    def test_the_fingerprint_binds_the_record(self):
        proof = self.walk(self.fixture())
        before = proof.fingerprint()
        record = proof.owner_switch.record
        for field, value in (('successors', []), ('table_words_sha256', '0' * 64), ('transfer', 0)):
            with self.subTest(field=field):
                proof.owner_switch.record = dict(record, **{field: value})
                self.assertNotEqual(proof.fingerprint(), before)
        proof.owner_switch.record = record
        self.assertEqual(proof.fingerprint(), before)

    def test_an_incomplete_walk_has_no_evidence(self):
        f = self.fixture()
        proof = self.plain(f)
        proof.owner_switch = owner_switch.OwnerSwitch(proof, f['data'], A, *self.linked(f))
        for read in (proof.fingerprint, proof.loop_replay_lines):
            with self.subTest(read=read.__name__), self.assertRaisesRegex(ValueError, 'walk is incomplete'):
                read()

    def test_a_proof_without_an_owner_switch_is_unchanged(self):
        f = self.fixture()
        proof = self.plain(f)
        self.assertIsNone(proof.owner_switch)
        self.assertFalse(owner_switch.context(proof, f['data'], A, {}, {}, None))
        self.assertFalse(owner_switch.context(None, f['data'], A, {}, {}, None))
        self.assertEqual(proof.loop_replay_lines(), [])

    # Obligation 1: the default path's plain stack-argument proof, one owner.

    def test_only_the_default_plain_proof_takes_an_owner_switch(self):
        f = self.fixture()
        builds = {
            'version 1': lambda: match.BufferCallProof(f['rom'], f['mapping'], loop_replay=True),
            'no switch callees': lambda: self.plain(f, switch_callee_index=None),
            'function literals': lambda: match.FunctionBufferCallProof(f['rom'], f['mapping'],
                                                                      stack_arguments=True, loop_replay=True),
        }
        for name, build in builds.items():
            with self.subTest(name=name), self.assertRaisesRegex(
                    ValueError, 'owner switch requires the default plain stack-argument buffer proof'):
                self.walk(f, build())
        # A subclass, or a plain proof without stack arguments, carrying the jump-table callee summaries.
        callees = self.plain(f).switch_callees
        subclass = match.FunctionBufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True)
        subclass.switch_callees = callees
        unstacked = self.plain(f)
        unstacked.stack_arguments = False
        for name, proof in (('subclass', subclass), ('no stack arguments', unstacked)):
            with self.subTest(name=name), self.assertRaisesRegex(
                    ValueError, 'owner switch requires the default plain stack-argument buffer proof'):
                self.walk(f, proof)
        proof = self.walk(f)
        with self.assertRaisesRegex(ValueError, 'owner switch requires the default plain stack-argument buffer proof'):
            self.walk(f, proof)

    # Obligation 2: exactly one guarded table, no scalar words.

    def test_one_table_without_scalar_words(self):
        # agbcc's five-word interposed pool layout is refined, then refused here.
        pool = self.fixture(guard='bls dispatch\nb default',
                            words=''.join(f'word{n}: .word {n + 1}\n' for n in range(5)))
        switch, = self.refinement(pool)['word_switches']
        self.assertEqual(switch.get('interposed_words'), 5)
        with self.assertRaisesRegex(ValueError, 'owner switch requires one guarded table without scalar words'):
            self.walk(pool, calls={}, linked=dict(switch['relocations']))
        # No table at all.
        straight = self.fixture(body='push {lr}\nsub sp, #8\nmov r0, sp\nbl callee\nadd sp, #8\npop {r1}\nbx r1')
        with self.assertRaisesRegex(ValueError, 'owner switch requires one guarded table without scalar words'):
            self.walk(straight)

    # Obligation 3: a closed owner graph without local BL; runtime thunks stay the walk's refusal.

    def test_local_bl_is_refused(self):
        f = self.fixture(case1='bl local', extra='local: bx lr\n')
        with self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
            self.walk(f)

    def test_an_unindexed_call_never_closes_the_graph(self):
        with self.assertRaisesRegex(ValueError, 'structural inventory is not closed'):
            self.walk(self.fixture(case1='bl stray'))

    def test_runtime_thunks_stay_refused_beside_the_switch(self):
        f = self.fixture()
        with patch.dict(match.RUNTIME_HELPERS, _call_via_test=B), \
                self.assertRaisesRegex(ValueError, 'switch evidence excludes fixed frames and runtime call thunks'):
            self.walk(f)

    # Obligation 4: the link agrees with the ROM.

    def test_linked_relocations_and_calls_must_agree(self):
        f = self.fixture()
        calls, words = self.linked(f)
        moved = dict(words)
        moved[max(moved)] += 2
        site = next(iter(calls))
        for name, linked in (('table word', dict(calls=calls, linked=moved)),
                             ('missing word', dict(calls=calls, linked={k: v for k, v in words.items()
                                                                        if k != max(words)})),
                             ('call target', dict(calls={**calls, site: C}, linked=words)),
                             ('extra call', dict(calls={**calls, A: B}, linked=words))):
            with self.subTest(name=name), self.assertRaisesRegex(
                    ValueError, 'owner switch differs from its linked relocations'):
                self.walk(f, **linked)

    # Obligation 5: the canonical guarded layout.

    def test_the_layout_is_the_canonical_guarded_one(self):
        # A wrong guard condition, a bound past the table, a case before the table.
        for change in (dict(guard='bhs default'), dict(bound=3), dict(table='case0, case1, caller')):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.walk(self.fixture(**change))

    def test_a_path_around_the_guard_is_refused(self):
        # The refinement already refuses it; the walk's predecessor check would too.
        with self.assertRaisesRegex(ValueError, 'structural inventory is not closed|switch selector bound is bypassed'):
            self.walk(self.fixture(case1='movs r0, #0\nb dispatch'))

    # Obligation 6: the walk covers the complete owner graph.

    def test_the_walk_must_cover_the_owner_graph(self):
        import owner_graph_profile as graph
        f = self.fixture()
        real = graph.graph

        def widened(*args, **kwargs):
            instructions, edges, branches, calls, words = real(*args, **kwargs)
            return {**instructions, A + len(f['data']): None}, edges, branches, calls, words

        with patch.object(graph, 'graph', widened), \
                self.assertRaisesRegex(ValueError, 'owner switch walk differs from the complete owner graph'):
            self.walk(f)

    # The walk's own guard: only the bound owner, with its own table.

    def test_the_bound_switch_admits_only_its_own_walk(self):
        f = self.fixture()
        proof = self.walk(f)
        _, _, calls, words = proof.owner_switch.key
        for name, arguments in (('table', (calls, {**words, max(words): words[max(words)] + 2}, None)),
                                ('calls', ({**calls, A: B}, words, None)),
                                ('data words', (calls, words, {0: ('data_02000000', 0x02000000)}))):
            with self.subTest(name=name), self.assertRaisesRegex(
                    ValueError, 'owner switch differs from its authenticated owner'):
                owner_switch.context(proof, f['data'], A, *arguments)
        with self.assertRaisesRegex(ValueError, 'owner switch differs from its authenticated owner'):
            owner_switch.context(proof, f['data'][:-2] + b'\0\0', A, calls, words, None)
        self.assertTrue(owner_switch.context(proof, f['data'], A, calls, words, None))

    def test_without_the_owner_switch_the_walk_refuses_as_before(self):
        f = self.fixture()
        _, words = self.linked(f)
        with self.assertRaisesRegex(ValueError, 'switch evidence cannot combine frame or buffer proof profiles'):
            match.verify_leaf_instructions(f['data'], A, True, self.linked(f)[0], buffer_proof=self.plain(f),
                                           switch_relocations=words)
        with self.assertRaisesRegex(ValueError, 'stack aliases cannot cross calls in caller-clobbered registers'):
            match.verify_leaf_instructions(f['data'], A, True, self.linked(f)[0], switch_relocations=words)

    # match.py's retry and the no-data proof.

    def test_the_retry_takes_only_a_plain_switch_data_owner(self):
        # Structural only: any refusal of the buffer-free switch walk is retried.
        manifest = dict(calls=[], data=[], switch=dict(literal=0))
        args = argparse.Namespace(switch_data_profile=None)
        retries = lambda **change: owner_switch.retries(**dict(
            dict(manifest=manifest, args=args, calls={A: B},
                 data_relocations={0: ('data_02000000', 0x02000000)}, function_relocations={}, thumb=True,
                 matches_rom=True),
            **change))
        self.assertTrue(retries())
        self.assertTrue(retries(manifest=dict(manifest, data_policy='x')))
        for name, change in (
                ('bytes differ from the ROM', dict(matches_rom=False)),
                ('arm', dict(thumb=False)), ('no calls', dict(calls={})),
                ('no typed data', dict(data_relocations={})),
                ('function literals', dict(function_relocations={0: ('func_08010100', B | 1)})),
                ('switch-data selector', dict(args=argparse.Namespace(switch_data_profile='x'))),
                ('scalar policy', dict(manifest=dict(manifest, scalar_policy='x'))),
                ('preloaded', dict(manifest=dict(manifest, switch=dict(preload=1)))),
                ('not a manifest', dict(manifest=None))):
            with self.subTest(name=name):
                self.assertFalse(retries(**change))

    def typed(self, **change):
        """The fixture with case1 storing through a typed object word, and its data-buffer proof inputs."""
        f = self.fixture(**dict(dict(case1='movs r0, #1\nldr r2, object\nstrh r0, [r2]',
                                     extra='.balign 4, 0\nobject: .word 0x02000000\n'), **change))
        offset = next(o for o in range(0, len(f['data']), 4) if f['data'][o:o + 4] == bytes.fromhex('00000002'))
        return f, b'{"data_02000000": "0x02000000"}', {offset: ('data_02000000', 0x02000000)}

    def test_the_typed_data_proof_takes_the_table_pointer(self):
        f, objects, literals = self.typed()
        calls, words = self.linked(f)
        _, proof, schema, manifest = data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls,
                                                       literals, index=f['index'], switch_relocations=words)
        self.assertEqual((schema, manifest['data']), (data_buffer.SCHEMA, [[min(literals), 'data_02000000', 0]]))
        self.assertEqual(proof.loop_replay_lines(), self.walk(f).loop_replay_lines())
        # Without the table the typed-data walk refuses at the dispatch, as before.
        with self.assertRaisesRegex(ValueError, 'non-leaf indirect control flow|program-counter'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls, literals, index=f['index'])
        # No index: no default-path proof, so no owner switch.
        with self.assertRaisesRegex(ValueError, 'owner switch requires the default plain stack-argument buffer proof'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls, literals,
                              switch_relocations=words)

    def test_a_table_pointer_read_elsewhere_stays_untyped(self):
        f, objects, literals = self.typed(loads='ldr r3, pointer\n')
        calls, words = self.linked(f)
        with self.assertRaisesRegex(ValueError, 'untyped word'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls, literals,
                              index=f['index'], switch_relocations=words)

    def test_every_foreign_line_list_names_the_owner_line(self):
        # Wherever a report check lists the switch-callee line, it lists the owner-switch line too.
        import ast
        tree = ast.parse((ROOT / 'tools/match_evidence.py').read_text())
        lists = [node for node in ast.walk(tree) if isinstance(node, (ast.Tuple, ast.List, ast.BoolOp))]
        strings = lambda node: [item.value for item in ast.walk(node)
                                if isinstance(item, ast.Constant) and isinstance(item.value, str)]
        named = [node for node in lists if any(value.startswith('* buffer switch callee') for value in strings(node))
                 and not any(isinstance(child, (ast.Tuple, ast.List, ast.BoolOp)) for child in ast.iter_child_nodes(node))]
        self.assertGreaterEqual(len(named), 7)
        for node in named:
            with self.subTest(line=node.lineno):
                self.assertTrue(any(value.startswith(owner_switch.LINE) for value in strings(node)))
        self.assertIn(owner_switch.LINE, data_buffer.FIELDS)


# A typed-data owner and a data-free owner, each with a guarded five-entry table, whose
# cases 0 and 2 hand a four-halfword local to func_08000400(value, out).
DATA_SWITCH = data_calls.HEADER + """extern void func_08000400(u16 value, u16 *out);
u32 func_08000200(u32 phase)
{
    u16 buffer[4];

    switch (phase) {
    case 0:
        func_08000400(1, buffer);
        return buffer[0];
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08000400(2, buffer);
        return buffer[3];
    case 3:
        return 7;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""
PLAIN_SWITCH = DATA_SWITCH.replace('data_02000000[0] = 5;', 'phase = 5;').replace(
    'data_02000000[1] = 3;', 'phase = 3;').replace('extern u16 data_02000000[];\n', '')
# The local as the fifth (outgoing stack) argument: the buffer-free switch walk refuses first at its
# store to the outgoing slot (`unsupported stack-alias use or escape`), not at the call.
STACK_SWITCH = DATA_SWITCH.replace('extern void func_08000400(u16 value, u16 *out);',
                                   'extern void func_08000400(u32 a, u32 b, u32 c, u32 d, u16 *out);').replace(
    'func_08000400(1, buffer);', 'func_08000400(0, 0, 0, 0, buffer);').replace(
    'func_08000400(2, buffer);', 'func_08000400(1, 2, 3, 4, buffer);')
STACK_CALLEE = 'ldr r1, [sp]\nstrh r0, [r1]\nstrh r0, [r1, #6]\nbx lr'
# A two-halfword local the callee writes past (its second store is at +6): both proofs refuse.
SHORT_SWITCH = DATA_SWITCH.replace('u16 buffer[4];', 'u16 buffer[2];').replace('buffer[3]', 'buffer[1]')


def build_switch(root, source, callee=data_calls.STORES):
    """data_calls.build, linking the caller's own switch table as match.py's default path does."""
    real = match.link_calls

    def with_switch(*args, **kwargs):
        if len(args) < 11 and 'switch_relocations' not in kwargs:
            kwargs.update(switch_relocations={}, allow_switch_data=True)
        return real(*args, **kwargs)

    with patch.object(match, 'link_calls', with_switch):
        return data_calls.build(root, source, [('func_08000400', callee)])


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativeOwnerSwitchTests(unittest.TestCase):
    """match.py's default path on compiled owners: the report, its replay and its tampers."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_native_', dir=scratch)
        cls.runs = {}
        for name, source, callee in (('data', DATA_SWITCH, data_calls.STORES),
                                     ('plain', PLAIN_SWITCH, data_calls.STORES),
                                     ('stack', STACK_SWITCH, STACK_CALLEE),
                                     ('short', SHORT_SWITCH, data_calls.STORES),
                                     ('drift', DATA_SWITCH, data_calls.STORES)):
            root = build_switch(Path(cls.temporary.name) / name, source, callee)
            if name == 'drift':
                # The source no longer gives the ROM's bytes, as while a matcher iterates.
                source_path = root / 'src/08000200.c'
                source_path.write_text(source_path.read_text().replace('return 7;', 'return 9;'))
            cls.runs[name] = (root, *data_calls.run(root))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, report):
        root = self.runs[name][0]
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def test_the_typed_data_owner_matches_and_replays(self):
        self.check_admitted('data')

    def test_a_local_passed_on_the_stack_is_retried_and_matches(self):
        # Whatever the buffer-free walk refuses first, the retry is structural.
        self.check_admitted('stack')

    def test_a_failed_retry_reports_both_refusals(self):
        _, code, output, report = self.runs['short']
        self.assertNotEqual(code, 0)
        self.assertIsNone(report)
        self.assertRegex(output, r'stack aliases cannot cross calls in caller-clobbered registers; '
                                 r'owner-switch data-buffer proof: buffer callee 0x08000400: .*'
                                 r'outside allocated local words')

    def test_bytes_that_differ_from_the_rom_keep_their_own_refusal(self):
        _, code, output, report = self.runs['drift']
        self.assertNotEqual(code, 0)
        self.assertIsNone(report)
        self.assertIn('differs from the ROM', output)
        self.assertNotIn('owner-switch data-buffer proof', output)

    def check_admitted(self, name):
        _, code, output, report = self.runs[name]
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
        line, = [line for line in report.splitlines() if line.startswith(owner_switch.LINE)]
        self.assertRegex(line, r'^\* buffer owner switch: `guarded-switch-owner-v1` 0x08000200: '
                               r'dispatch at 0x080002[0-9A-F]{2}, bound 4, 5 successors, table [0-9a-f]{16}; ' +
                               re.escape(owner_switch.POINTER_RULE) + '$')
        self.assertFalse(any(line.startswith(('* switches', '* switch manifest', '* switch proof'))
                             for line in report.splitlines()))
        self.assertTrue(self.replays(name, report))

    def test_an_owner_without_typed_data_keeps_its_refusal(self):
        _, code, output, report = self.runs['plain']
        self.assertNotEqual(code, 0)
        self.assertIn('stack aliases cannot cross calls in caller-clobbered registers', output)
        self.assertNotIn('owner-switch data-buffer proof', output)
        self.assertIsNone(report)

    def test_tampered_removed_or_duplicated_lines_fail(self):
        lines = self.runs['data'][3].splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.LINE))
        for change, edited in (('successors', lines[:at] + [lines[at].replace('5 successors', '6 successors')]
                                + lines[at + 1:]),
                               ('bound', lines[:at] + [lines[at].replace('bound 4', 'bound 5')] + lines[at + 1:]),
                               ('table', lines[:at] + [lines[at][:-16] + '0' * 16] + lines[at + 1:]),
                               ('indented', lines[:at] + ['  ' + lines[at]] + lines[at + 1:]),
                               ('removed', lines[:at] + lines[at + 1:]),
                               ('duplicated', lines[:at + 1] + lines[at:])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('data', '\n'.join(edited) + '\n'))

    def test_a_replay_without_an_index_refuses(self):
        root = self.runs['data'][0]
        index = root / 'symbols/functions.txt'
        saved = index.read_bytes()
        index.unlink()
        try:
            self.assertFalse(self.replays('data', self.runs['data'][3]))
        finally:
            index.write_bytes(saved)

    def test_without_the_table_the_data_proof_refuses_at_the_dispatch(self):
        root, _, _, report = self.runs['data']
        rom = (root / 'baserom.bin').read_bytes()
        mapping = (root / 'config/functions.json').read_bytes()
        objects = (root / 'config/data_symbols.json').read_bytes()
        code = bytes.fromhex(next(line for line in report.splitlines()
                                  if line.startswith('* compiled : '))[len('* compiled : `'):-1])
        manifest = json.loads(next(line for line in report.splitlines()
                                   if line.startswith(data_buffer.MANIFEST_FIELD))[len(data_buffer.MANIFEST_FIELD) + 1:-1])
        calls = {data_calls.A + offset: int(name[5:], 16) for offset, name in manifest['calls']}
        symbols = match.parse_data_symbols(objects)
        literals = {offset: (name, symbols[name] + delta) for offset, name, delta in manifest['data']}
        index = (root / 'symbols/functions.txt').read_bytes()
        with self.assertRaises(ValueError):
            data_buffer.prove(code, data_calls.A, rom, mapping, objects, calls, literals, index=index)


if __name__ == '__main__':
    unittest.main()
