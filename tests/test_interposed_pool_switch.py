"""Guarded jump tables behind their dispatch's own literal pool (interposed_pool_switch)."""
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
import analyze
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import interposed_pool_switch as pool
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_switch_buffer_profile as owner_switch
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_owner_switch_buffers as owner_tests

A, B = 0x08010000, 0x08010100
CALLEE = 'movs r1, #5\nstrh r1, [r0, #2]\nmovs r0, #0\nbx lr'
# Two numbers loaded before the switch: agbcc flushes them between `mov pc` and the table pointer.
LOADS = 'ldr r2, word0\nldr r3, word1\n'
WORDS = 'word0: .word 0x1234\nword1: .word 0x5678\n'


def tools_present():
    import shutil
    return all(shutil.which(tool) for tool in ('arm-none-eabi-as', 'arm-none-eabi-ld', 'arm-none-eabi-objcopy'))


@unittest.skipUnless(tools_present(), 'ARM binutils required')
class PoolFixture(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix='interposed_pool_', dir=scratch)
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def fixture(self, *, prelude='', loads=LOADS, words=WORDS, pad='.balign 4, 0\n', bound=2,
                guard='bls dispatch\nb default', table='case0, case1, case2',
                case0='mov r0, sp\nbl callee', case1='movs r0, #1', case2='add r0, sp, #4\nbl callee',
                extra=''):
        """caller(index, out): a three-entry table behind `words`; cases 0 and 2 pass an 8-byte local."""
        caller = ('push {r4, lr}\nsub sp, #8\nadds r4, r1, #0\n' + prelude + loads + f'cmp r0, #{bound}\n' +
                  guard + '\n'
                  'dispatch: lsls r0, r0, #2\nldr r1, pointer\nadds r0, r0, r1\nldr r0, [r0]\ntransfer: mov pc, r0\n'
                  + pad + words + 'pointer: .word table\ntable: .word ' + table + '\n'
                  f'case0: {case0}\nb done\ncase1: {case1}\nb done\ncase2: {case2}\nb done\n'
                  'default: movs r0, #0\ndone: add sp, #8\npop {r4}\npop {r1}\nbx r1\n' + extra)
        assembly = self.root / 'fixture.s'
        assembly.write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n'
                            '.global caller, caller_end, callee, callee_end, child, child_end, transfer\n'
                            f'caller:\n{caller}\ncaller_end:\n.org 0x100\n'
                            f'callee:\n{CALLEE}\ncallee_end:\n.org 0x200\n'
                            'child:\nbx lr\nchild_end:\n')
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
                    mapping=json.dumps(rows).encode(), index=index, symbols=symbols)

    def refine(self, f, **options):
        return analyze.refine_function(f['data'], A, json.loads(f['mapping']), max_bytes=len(f['data']),
                                       max_instructions=len(f['data']) // 2, rom_end=0x09000000,
                                       same_owner_long_branches=True, **options)

    def rule(self, f):
        """The owner route's refinement, which takes the rule (owner_admission_profile.refine)."""
        return owner.refine(f['data'], A, f['mapping'])

    def placed(self, f):
        result = self.rule(f)
        self.assertTrue(result['cfg_closed'], result['partial_reasons'])
        self.assertEqual(result['partial_reasons'], [])
        switch, = result['word_switches']
        return result, switch

    def refused(self, f, reason=None):
        result = self.rule(f)
        self.assertFalse(result['cfg_closed'])
        if reason is not None:
            self.assertTrue(any(reason in item for item in result['partial_reasons']), result['partial_reasons'])
        return result

    def unresolved(self, f):
        return self.refused(f, f'unresolved jump at 0x{f["symbols"]["transfer"]:08X}')


class RefinementTests(PoolFixture):
    """analyze.refine_function: where the table is, what it covers, and what the pool may be."""

    def test_kit_main_leaves_the_dispatch_unresolved(self):
        # The refusal this rule lifts: no layout places the pointer behind two words.
        f = self.fixture()
        result = self.refine(f)
        self.assertFalse(result['cfg_closed'])
        self.assertIn(f'unresolved jump at 0x{f["symbols"]["transfer"]:08X}', result['partial_reasons'])
        self.assertEqual(result['word_switches'], [])

    def test_the_table_is_placed_behind_its_pool(self):
        f = self.fixture()
        result, switch = self.placed(f)
        symbols = f['symbols']
        self.assertEqual((switch['interposed_words'], switch['pool_policy'], switch['bound']), (2, pool.NAME, 2))
        self.assertEqual((A + switch['dispatch'], A + switch['literal'], A + switch['table']),
                         (symbols['dispatch'], symbols['pointer'], symbols['table']))
        self.assertEqual(switch['relocations'], [[symbols['pointer'] - A, symbols['table'] - A]] +
                         [[symbols['table'] - A + 4 * n, symbols[f'case{n}'] - A] for n in range(3)])
        # The pool and the table are literal bytes; nothing else is.
        self.assertEqual(result['literal_ranges'],
                         [[f'0x{symbols["word0"]:08X}', f'0x{symbols["table"] + 12:08X}']])
        reads = {int(read['address'], 16) for read in result['literal_reads']}
        self.assertEqual(reads, {symbols['word0'], symbols['word1'], symbols['pointer']})

    def test_every_guard_pool_size_and_alignment(self):
        sizes = {'bhi default': 4, 'bls dispatch\nb default': 6, 'bls dispatch\nbl default': 8}
        for words in (1, 2, 3, 7):
            for guard, size in sizes.items():
                for prelude in ('', 'movs r5, #0\n'):
                    with self.subTest(words=words, guard=guard, prelude=prelude):
                        f = self.fixture(prelude=prelude, guard=guard,
                                         loads=''.join(f'ldr r2, word{n}\n' for n in range(words)),
                                         words=''.join(f'word{n}: .word {0x100 + n}\n' for n in range(words)))
                        _, switch = self.placed(f)
                        self.assertEqual(switch['interposed_words'], words)
                        self.assertEqual(A + switch['comparison'], f['symbols']['dispatch'] - size)

    def test_a_table_found_today_is_unchanged(self):
        # The adjacent table keeps its descriptor byte for byte. agbcc's five-word pool keeps
        # it without the opt-in; under it, test_five_word_pool_switch covers FIVE_WORDS.
        five = dict(loads='', words=''.join(f'w{n}: .word {n}\n' for n in range(5)))
        for name, change, five_words in (('adjacent', dict(loads='', words=''), True),
                                         ('five words', five, False)):
            with self.subTest(name=name), patch.object(pool.FIVE_WORDS, 'enabled', five_words):
                f = self.fixture(**change)
                self.assertEqual(self.refine(f), self.refine(f, interposed_pool_switch=True))
                self.assertNotIn('pool_policy', self.refine(f)['word_switches'][0])

    def test_the_opt_in_is_isolated(self):
        f = self.fixture()
        for options, reason in (
                (dict(interposed_pool_switch=1), 'must be Boolean'),
                (dict(interposed_pool_switch=True, one_object_word_switch=True), 'cannot combine'),
                (dict(interposed_pool_switch=True, two_constant_word_switch=True), 'cannot combine'),
                (dict(interposed_pool_switch=True, one_numeric_word_switch=True), 'cannot combine')):
            with self.subTest(options=options):
                result = self.refine(f, **options)
                self.assertFalse(result['cfg_closed'])
                self.assertTrue(any(reason in item for item in result['partial_reasons']), result)

    # Mutants: the pool stays data, every pool word is read, the table is still proved from the bytes.

    def test_an_unread_pool_word_refuses(self):
        self.refused(self.fixture(loads='ldr r2, word0\n'), 'interposed switch pool requires every reached word load')

    def test_pool_bytes_never_become_code(self):
        # A reached branch into the pool, and a case word aimed at a pool word.
        self.refused(self.fixture(case1='movs r0, #1\nb word1'), 'code/literal overlap')
        self.unresolved(self.fixture(table='case0, word1, case2'))

    def test_a_case_into_the_guard_dispatch_pointer_or_table_refuses(self):
        for target in ('dispatch', 'transfer', 'pointer', 'table'):
            with self.subTest(target=target):
                self.unresolved(self.fixture(table=f'case0, {target}, case2'))

    def test_backward_cases_refuse(self):
        self.unresolved(self.fixture(prelude='back: movs r5, #0\n', table='case0, back, case2'))

    def test_the_bound_comes_from_the_guard(self):
        # One past the table reads a code word as a case: no table.
        self.unresolved(self.fixture(bound=3))
        # One short: the table is the two words the guard admits, and the third is owned by nothing.
        f = self.fixture(bound=1)
        result, switch = self.placed(f)
        self.assertEqual((switch['bound'], len(switch['relocations'])), (1, 3))
        instructions, _, _, _, words = graph.graph(f['data'], A, result)
        with self.assertRaisesRegex(ValueError, 'unowned complete-owner bytes'):
            graph.partition(f['data'], A, result, instructions, words)

    def test_a_dispatch_is_never_given_another_dispatch_s_table(self):
        # An earlier guarded dispatch loads the same pointer: the layout behind the pool belongs to the
        # dispatch right before it, so the earlier one stays unresolved even though its guard matches.
        f = self.fixture(prelude='cmp r0, #2\nbls early\nb main\nearly: lsls r0, r0, #2\nldr r1, pointer\n'
                                 'adds r0, r0, r1\nldr r0, [r0]\nearlytransfer: mov pc, r0\nmain: ')
        result = self.refused(f, f'unresolved jump at 0x{f["symbols"]["earlytransfer"]:08X}')
        self.assertEqual([A + switch['dispatch'] for switch in result['word_switches']], [f['symbols']['dispatch']])

    def test_a_noncanonical_guard_refuses(self):
        for guard in ('bhs default', 'bgt default', 'bls dispatch\nbhi default'):
            with self.subTest(guard=guard):
                self.unresolved(self.fixture(guard=guard))

    def test_the_guard_cannot_be_bypassed(self):
        self.refused(self.fixture(case1='movs r0, #1\nb dispatch'), 'word-switch guard can be bypassed')

    def test_only_zero_alignment_before_the_pool(self):
        # The dispatch ends on a halfword boundary here, so one halfword pads it to the pool.
        f = self.fixture(pad='.hword 0\n.balign 4, 0\n')
        _, switch = self.placed(f)
        self.assertEqual(f['symbols']['dispatch'] + 10 + 2, f['symbols']['word0'])
        self.unresolved(self.fixture(pad='.hword 0x4770\n.balign 4, 0\n'))

    def test_a_pool_word_read_from_the_table_span_is_not_a_pool_word(self):
        # Reading a table word is no pool word: the placed pool is exactly the words before the pointer.
        f = self.fixture(loads=LOADS + 'ldr r5, table\n')
        _, switch = self.placed(f)
        self.assertEqual(switch['interposed_words'], 2)


class OwnerGraphTests(PoolFixture):
    """owner_graph_profile: the byte replay of a placed table and the complete owner partition."""

    def test_the_partition_owns_each_pool_word_as_a_read_literal(self):
        f = self.fixture()
        result, switch = self.placed(f)
        instructions, edges, branches, calls, words = graph.graph(f['data'], A, result)
        partition = graph.partition(f['data'], A, result, instructions, words)
        rows = {row['address']: row for row in partition['words']}
        symbols = f['symbols']
        for name in ('word0', 'word1'):
            self.assertFalse(rows[symbols[name]]['switch_word'])
            self.assertEqual(len(rows[symbols[name]]['load_sites']), 1)
        self.assertTrue(rows[symbols['pointer']]['switch_word'])
        self.assertEqual(sorted(words), sorted(offset for offset, _ in switch['relocations']))
        self.assertEqual(sorted(edges[symbols['transfer']]), [symbols[f'case{n}'] for n in range(3)])

    def test_a_tampered_descriptor_refuses(self):
        f = self.fixture()
        result, switch = self.placed(f)
        for name, change, message in (
                ('word count', dict(interposed_words=3), 'word count differs'),
                ('policy name', dict(pool_policy='x'), 'requires its enabled policy'),
                ('bound', dict(bound=1), 'differs from native byte-exact replay|switch')):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                graph.graph(f['data'], A, dict(result, word_switches=[dict(switch, **change)]))
        with patch.object(pool.POLICY, 'enabled', False), \
                self.assertRaisesRegex(ValueError, 'requires its enabled policy'):
            graph.graph(f['data'], A, result)

    def test_the_owner_refinement_follows_the_policy(self):
        f = self.fixture()
        self.assertEqual(self.rule(f), self.refine(f, interposed_pool_switch=True))
        self.assertTrue(self.rule(f)['cfg_closed'])
        with patch.object(pool.POLICY, 'enabled', False):
            self.assertEqual(self.rule(f), self.refine(f))
            self.assertFalse(self.rule(f)['cfg_closed'])


class OwnerRuntimeTests(PoolFixture):
    """owner_runtime_profile.verify re-runs the refinement itself: its fresh replay takes the rule too."""

    def indexed(self, f):
        """The fixture's mapping with the owner row's count set to the placed refinement's."""
        rows = json.loads(f['mapping'])
        rows[0]['instrs'] = self.placed(f)[0]['instrs']
        return json.dumps(rows).encode()

    def test_the_fresh_replay_places_the_same_table(self):
        import owner_runtime_profile as runtime
        f = self.fixture()
        mapping = self.indexed(f)
        refinement = owner.refine(f['data'], A, mapping)
        self.assertTrue(pool.marked(refinement['word_switches'][0]))
        self.assertIsInstance(runtime.verify(f['data'], A, f['rom'], mapping, refinement), dict)
        # A fresh replay that does not place the table differs from the owner's refinement.
        real = runtime.analyze.refine_function

        def unplaced(*args, **kwargs):
            return real(*args, **dict(kwargs, interposed_pool_switch=False))

        with patch.object(runtime.analyze, 'refine_function', unplaced), self.assertRaisesRegex(
                ValueError, 'owner refinement differs from fresh native CFG/guard replay'):
            runtime.verify(f['data'], A, f['rom'], mapping, refinement)
        # Without the rule there is no closed refinement to verify.
        with patch.object(pool.POLICY, 'enabled', False), self.assertRaises(ValueError):
            runtime.verify(f['data'], A, f['rom'], mapping, owner.refine(f['data'], A, mapping))


class OwnerSwitchTests(PoolFixture):
    """The default path's owner-switch walk (owner_switch_buffer_profile) over a placed table."""

    def plain(self, f):
        return match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                     bios_wrappers=True, copy_helper_index=f['index'], switch_callee_index=f['index'])

    def linked(self, f):
        _, _, _, calls, words = graph.graph(f['data'], A, self.placed(f)[0])
        return calls, words

    def walk(self, f, calls=None, linked=None):
        if calls is None:
            calls, linked = self.linked(f)
        proof = self.plain(f)
        owner_switch.walk(proof, f['data'], A, calls, linked)
        return proof

    def test_the_walk_takes_the_placed_table(self):
        f = self.fixture()
        proof = self.walk(f)
        self.assertEqual(sorted(proof.dependencies), [B])
        record = proof.owner_switch.evidence()
        self.assertEqual((record['switch']['interposed_words'], record['switch']['pool_policy']), (2, pool.NAME))
        self.assertEqual(len(record['successors']), 3)
        line, = proof.loop_replay_lines()
        self.assertTrue(line.endswith('; ' + pool.RULE.format(words=2)), line)

    def test_kit_main_refuses_the_owner(self):
        f = self.fixture()
        calls, words = self.linked(f)
        self.assertTrue(calls and words)
        with patch.object(pool.POLICY, 'enabled', False), self.assertRaisesRegex(
                ValueError, 'owner switch requires one guarded table without scalar words'):
            self.walk(f, calls, words)

    def test_the_link_must_equal_the_rom_table(self):
        # A pool word linked as a local .text word, or a moved table word.
        f = self.fixture()
        calls, words = self.linked(f)
        word0 = f['symbols']['word0'] - A
        for name, linked in (('pool word as a local word', {**words, word0: 0}),
                             ('moved case', {**words, max(words): words[max(words)] + 2})):
            with self.subTest(name=name), self.assertRaisesRegex(
                    ValueError, 'owner switch differs from its linked relocations'):
                self.walk(f, calls, linked)

    def test_the_walk_rederives_the_authenticated_pool_layout(self):
        f = self.fixture()
        calls, words = self.linked(f)
        real = owner_switch.OwnerSwitch.__init__

        def tampered(self, *args, **kwargs):
            real(self, *args, **kwargs)
            self.record['switch'] = dict(self.record['switch'], literal=self.record['switch']['literal'] - 4)

        with patch.object(owner_switch.OwnerSwitch, '__init__', tampered), self.assertRaisesRegex(
                ValueError, 'owner switch pool layout differs from its authenticated owner'):
            self.walk(f, calls, words)

    def test_the_fingerprint_binds_the_pool(self):
        proof = self.walk(self.fixture())
        before = proof.fingerprint()
        record = proof.owner_switch.record
        proof.owner_switch.record = dict(record, switch=dict(record['switch'], interposed_words=3))
        self.assertNotEqual(proof.fingerprint(), before)

    # The typed-data proof binds each read pool word like any other literal.

    def typed(self, pool_value):
        f = self.fixture(words=f'word0: .word {pool_value}\nword1: .word 0x5678\n',
                         case1='movs r0, #1\nldr r2, object\nstrh r0, [r2]',
                         extra='.balign 4, 0\nobject: .word 0x02000000\n')
        offset = f['symbols']['object'] - A
        return f, b'{"data_02000000": "0x02000000"}', {offset: ('data_02000000', 0x02000000)}

    def test_a_number_in_the_pool_is_a_number(self):
        f, objects, literals = self.typed('0x1234')
        calls, words = self.linked(f)
        _, proof, schema, manifest = data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls,
                                                       literals, index=f['index'], switch_relocations=words)
        self.assertEqual(schema, data_buffer.SCHEMA)
        self.assertEqual(proof.owner_switch.record['switch']['interposed_words'], 2)

    def test_an_address_in_the_pool_must_be_typed(self):
        f, objects, literals = self.typed('0x02000004')
        calls, words = self.linked(f)
        with self.assertRaisesRegex(ValueError, 'untyped word 0x[0-9A-F]{8} = 0x02000004'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls, literals,
                              index=f['index'], switch_relocations=words)
        # Typed, it is an object literal like any other.
        word0 = f['symbols']['word0'] - A
        objects = b'{"data_02000000": "0x02000000", "data_02000004": "0x02000004"}'
        data_buffer.prove(f['data'], A, f['rom'], f['mapping'], objects, calls,
                          {**literals, word0: ('data_02000004', 0x02000004)},
                          index=f['index'], switch_relocations=words)

    def test_a_table_word_read_as_a_literal_stays_untyped(self):
        f = self.fixture(loads=LOADS + 'ldr r5, table\n', case1='movs r0, #1\nldr r2, object\nstrh r0, [r2]',
                         extra='.balign 4, 0\nobject: .word 0x02000000\n')
        calls, words = self.linked(f)
        literals = {f['symbols']['object'] - A: ('data_02000000', 0x02000000)}
        with self.assertRaisesRegex(ValueError, 'untyped word'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], b'{"data_02000000": "0x02000000"}', calls,
                              literals, index=f['index'], switch_relocations=words)


class SelectedLayoutTests(PoolFixture):
    """match.selected_switch_layout: the link places the table only where the fixed layouts refuse."""

    def words(self, f):
        s = f['symbols']
        return {s['pointer'] - A: s['table'] - A, **{s['table'] - A + 4 * n: s[f'case{n}'] - A for n in range(3)}}

    def test_a_numeric_pool_is_placed_at_link_time(self):
        f = self.fixture()
        layout = match.selected_switch_layout(f['data'], A, self.words(f))
        self.assertEqual(A + layout['dispatch'], f['symbols']['dispatch'])
        with patch.object(pool.POLICY, 'enabled', False), self.assertRaisesRegex(
                ValueError, 'switch requires one exact adjacent unsigned guard and five-op dispatch'):
            match.selected_switch_layout(f['data'], A, self.words(f))

    def test_an_adjacent_table_is_unchanged_and_other_failures_keep_their_message(self):
        f = self.fixture(loads='', words='')
        self.assertEqual(match.selected_switch_layout(f['data'], A, self.words(f)),
                         match.switch_layout(f['data'], A, self.words(f), allow_backward_cases=True))
        f = self.fixture()
        words = self.words(f)
        wrong = {**words, min(words): words[min(words)] + 4}
        with self.assertRaisesRegex(ValueError, 'invalid local switch word or section-relative target'):
            match.selected_switch_layout(f['data'], A, wrong)

    def test_the_buffer_free_switch_walk_still_refuses_the_pool(self):
        f = self.fixture()
        manifest = dict(calls=[], switch=match.selected_switch_layout(f['data'], A, self.words(f)))
        with self.assertRaisesRegex(ValueError, 'switch requires one exact adjacent unsigned guard'):
            match.verify_switches(f['data'], A, f['rom'], f['mapping'], manifest)


# A typed-data owner whose two pool words agbcc flushes after its dispatch: a number it stores
# before the switch, and the typed object it loads there.
NUMERIC_POOL = owner_tests.DATA_SWITCH.replace(
    'u32 func_08000200(u32 phase)\n{\n    u16 buffer[4];\n',
    'u32 func_08000200(u32 phase, u16 *out)\n{\n    u16 buffer[4];\n\n    out[0] = 0x1234;\n')
OBJECT_POOL = NUMERIC_POOL.replace('out[0] = 0x1234;', 'out[0] = data_02000000[2];')


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativePoolTests(unittest.TestCase):
    """match.py's default path on compiled owners: admitted, reported, replayed, and refused without the rule."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='interposed_pool_native_', dir=scratch)
        cls.runs = {}
        for name, source in (('numeric', NUMERIC_POOL), ('object', OBJECT_POOL)):
            root = owner_tests.build_switch(Path(cls.temporary.name) / name, source)
            cls.runs[name] = (root, *data_calls.run(root))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, report):
        root = self.runs[name][0]
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def in_process(self, name):
        """match.main with the rule disabled: (exit message, stdout)."""
        root = self.runs[name][0]
        output = io.StringIO()
        with patch.object(pool.POLICY, 'enabled', False), patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(root), '--no-write', '0x08000200']), \
                contextlib.redirect_stdout(output), self.assertRaises(SystemExit) as stop:
            match.main()
        return str(stop.exception.code), output.getvalue()

    def test_the_pool_is_where_agbcc_puts_it(self):
        for name in self.runs:
            with self.subTest(name=name):
                root = self.runs[name][0]
                rom = (root / 'baserom.bin').read_bytes()
                mapping = (root / 'config/functions.json').read_bytes()
                end = int(json.loads(mapping)[0]['end'], 16)
                data = rom[data_calls.A - match.ROM_BASE:end - match.ROM_BASE]
                switch, = owner.refine(data, data_calls.A, mapping)['word_switches']
                self.assertEqual((switch['pool_policy'], switch['interposed_words'] >= 1), (pool.NAME, True))

    def test_each_owner_matches_reports_and_replays(self):
        for name in self.runs:
            with self.subTest(name=name):
                _, code, output, report = self.runs[name]
                self.assertEqual(code, 0, output)
                self.assertIn('verdict MATCH - byte identical', output)
                self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
                line, = [line for line in report.splitlines() if line.startswith(owner_switch.LINE)]
                self.assertRegex(line, r'; table behind its \d+-word literal pool \(' + re.escape(pool.NAME) + r'\)')
                self.assertTrue(self.replays(name, report))
                with patch.object(pool.POLICY, 'enabled', False):
                    self.assertFalse(self.replays(name, report))

    def test_kit_main_refuses_each_owner_at_the_pool(self):
        # The numeric pool fails at the link layout; the typed one at the owner switch's refinement.
        message, _ = self.in_process('numeric')
        self.assertIn('switch requires one exact adjacent unsigned guard and five-op dispatch', message)
        message, _ = self.in_process('object')
        self.assertIn('owner switch requires one guarded table without scalar words', message)

    def test_a_tampered_pool_line_fails(self):
        lines = self.runs['numeric'][3].splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.LINE))
        for change, edited in (('words', re.sub(r'its \d+-word', 'its 9-word', lines[at])),
                               ('removed', lines[at][:lines[at].index('; table behind')])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('numeric', '\n'.join(lines[:at] + [edited] + lines[at + 1:]) + '\n'))


if __name__ == '__main__':
    unittest.main()
