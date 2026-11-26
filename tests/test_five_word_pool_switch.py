"""agbcc's five-word switch pool under the interposed-pool rule's proof (interposed_pool_switch.FIVE_WORDS)."""
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import data_buffer_profile as data_buffer
import interposed_pool_switch as pool
import owner_graph_profile as graph
import owner_switch_buffer_profile as owner_switch
# The module, not its classes: importing a TestCase class would make it run here again.
import test_interposed_pool_switch as base

A, B = base.A, base.B
FIVE_LOADS = ''.join(f'ldr r2, word{n}\n' for n in range(5))
FIVE_WORDS = ''.join(f'word{n}: .word {0x100 + n}\n' for n in range(5))
GUARDS = {'bhi default': 4, 'bls dispatch\nb default': 6, 'bls dispatch\nbl default': 8}


class FiveWordFixture(base.PoolFixture):
    def five(self, **options):
        return self.fixture(**dict(dict(loads=FIVE_LOADS, words=FIVE_WORDS), **options))

    def fixed(self, f):
        """The fixed five-word descriptor every refinement took before this rule."""
        with patch.object(pool.FIVE_WORDS, 'enabled', False):
            switch, = self.refine(f, interposed_pool_switch=True)['word_switches']
        return switch


class FiveWordRefinementTests(FiveWordFixture):
    """analyze.refine_function under the opt-in: the fixed five-word table takes the rule's descriptor."""

    def test_kit_main_takes_the_fixed_five_word_layout(self):
        f = self.five()
        switch = self.fixed(f)
        self.assertEqual(switch['interposed_words'], 5)
        self.assertNotIn('pool_policy', switch)

    def test_the_owner_refinement_marks_the_five_word_pool(self):
        f = self.five()
        result, switch = self.placed(f)
        self.assertEqual((switch['interposed_words'], switch['pool_policy']), (5, pool.NAME))
        fixed = self.fixed(f)
        self.assertEqual({key: switch[key] for key in fixed}, fixed)
        self.assertEqual(set(switch) - set(fixed), {'pool_policy'})
        reads = {int(read['address'], 16) for read in result['literal_reads']}
        self.assertTrue({f['symbols'][f'word{n}'] for n in range(5)} <= reads)

    def test_without_the_opt_in_the_fixed_descriptor_stands(self):
        f = self.five()
        switch, = self.refine(f)['word_switches']
        self.assertEqual(switch, self.fixed(f))

    def test_every_guard_takes_five_words(self):
        # bhi and bls; bl never had a fixed five-word layout; the rule already placed them.
        for guard, size in GUARDS.items():
            with self.subTest(guard=guard):
                f = self.five(guard=guard)
                _, switch = self.placed(f)
                self.assertEqual((switch['interposed_words'], switch['pool_policy']), (5, pool.NAME))
                self.assertEqual(A + switch['comparison'], f['symbols']['dispatch'] - size)

    def test_an_unread_five_word_pool_refuses(self):
        # The per-word proof is the rule's: a word no reached PC load reads is no pool word.
        f = self.five(loads=''.join(f'ldr r2, word{n}\n' for n in range(4)))
        self.refused(f, 'interposed switch pool requires every reached word load')

    def test_a_non_adjacent_table_refuses(self):
        # The pointer aimed one word past the word that follows it: neither layout places a table.
        f = self.five()
        offset = f['symbols']['pointer'] - A
        word = struct.pack('<I', f['symbols']['table'] + 4)
        at = A - match.ROM_BASE + offset
        moved = dict(f, data=f['data'][:offset] + word + f['data'][offset + 4:],
                     rom=f['rom'][:at] + word + f['rom'][at + 4:])
        self.unresolved(moved)
        self.assertEqual(self.refine(moved)['word_switches'], [])

    def test_the_descriptors_must_agree(self):
        f = self.five()
        fixed = self.fixed(f)
        _, placed = self.placed(f)
        self.assertIs(pool.five_word_pool(fixed, placed), placed)
        for name, left, right in (
                ('another table', fixed, dict(placed, table=placed['table'] + 4)),
                ('another bound', fixed, dict(placed, bound=placed['bound'] + 1)),
                ('another default', fixed, dict(placed, default=placed['default'] + 2)),
                ('another entry', fixed, dict(placed, relocations=placed['relocations'][:-1])),
                ('four words', dict(fixed, interposed_words=4), dict(placed, interposed_words=4)),
                ('an unmarked placement', fixed, {k: v for k, v in placed.items() if k != 'pool_policy'}),
                ('a marked fixed layout', dict(fixed, pool_policy=pool.NAME), placed)):
            with self.subTest(name=name):
                self.assertIsNone(pool.five_word_pool(left, right))
        for switch in (pool.POLICY, pool.FIVE_WORDS):
            with self.subTest(policy=type(switch).__name__), patch.object(switch, 'enabled', False):
                self.assertIsNone(pool.five_word_pool(fixed, placed))


class FiveWordOwnerTests(FiveWordFixture):
    """The owner graph and the default path's owner-switch walk over the five-word pool."""

    def plain(self, f):
        return match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                     bios_wrappers=True, copy_helper_index=f['index'], switch_callee_index=f['index'])

    def linked(self, f):
        _, _, _, calls, words = graph.graph(f['data'], A, self.placed(f)[0])
        return calls, words

    def walk(self, f, calls=None, words=None):
        if calls is None:
            calls, words = self.linked(f)
        proof = self.plain(f)
        owner_switch.walk(proof, f['data'], A, calls, words)
        return proof

    def test_the_partition_owns_each_pool_word_as_a_read_literal(self):
        f = self.five()
        result, _ = self.placed(f)
        instructions, _, _, _, words = graph.graph(f['data'], A, result)
        partition = graph.partition(f['data'], A, result, instructions, words)
        owned = {word['address']: word for word in partition['words']}
        for n in range(5):
            word = owned[f['symbols'][f'word{n}']]
            self.assertFalse(word['switch_word'])
            self.assertEqual(len(word['load_sites']), 1)

    def test_kit_main_s_owner_graph_cannot_replay_the_fixed_layout(self):
        f = self.five()
        with patch.object(pool.FIVE_WORDS, 'enabled', False):
            result = self.rule(f)
            with self.assertRaises(ValueError):
                graph.graph(f['data'], A, result)

    def test_the_walk_takes_the_five_word_table(self):
        f = self.five()
        proof = self.walk(f)
        self.assertEqual(sorted(proof.dependencies), [B])
        record = proof.owner_switch.evidence()
        self.assertEqual((record['switch']['interposed_words'], record['switch']['pool_policy']), (5, pool.NAME))
        line, = proof.loop_replay_lines()
        self.assertTrue(line.endswith('; ' + pool.RULE.format(words=5)), line)

    def test_kit_main_refuses_the_owner(self):
        f = self.five()
        calls, words = self.linked(f)
        with patch.object(pool.FIVE_WORDS, 'enabled', False), self.assertRaisesRegex(
                ValueError, 'owner switch requires one guarded table without scalar words'):
            self.walk(f, calls, words)

    def test_the_walk_rederives_the_five_word_layout(self):
        f = self.five()
        calls, words = self.linked(f)
        real = owner_switch.OwnerSwitch.__init__

        def tampered(self, *args, **kwargs):
            real(self, *args, **kwargs)
            self.record['switch'] = dict(self.record['switch'], literal=self.record['switch']['literal'] - 4)

        with patch.object(owner_switch.OwnerSwitch, '__init__', tampered), self.assertRaisesRegex(
                ValueError, 'owner switch pool layout differs from its authenticated owner'):
            self.walk(f, calls, words)

    def test_an_address_in_the_five_word_pool_must_be_typed(self):
        # word0 is the last load, so its value is still in R2 at the cases' calls (as in the rule's own test).
        words = FIVE_WORDS.replace('word0: .word 256', 'word0: .word 0x02000004')
        loads = 'ldr r1, word1\nldr r3, word2\nldr r1, word3\nldr r3, word4\nldr r2, word0\n'
        f = self.five(words=words, loads=loads, case1='movs r0, #1\nldr r2, object\nstrh r0, [r2]',
                      extra='.balign 4, 0\nobject: .word 0x02000000\n')
        calls, linked = self.linked(f)
        literals = {f['symbols']['object'] - A: ('data_02000000', 0x02000000)}
        with self.assertRaisesRegex(ValueError, 'untyped word 0x[0-9A-F]{8} = 0x02000004'):
            data_buffer.prove(f['data'], A, f['rom'], f['mapping'], b'{"data_02000000": "0x02000000"}', calls,
                              literals, index=f['index'], switch_relocations=linked)
        word0 = f['symbols']['word0'] - A
        _, proof, _, _ = data_buffer.prove(
            f['data'], A, f['rom'], f['mapping'], b'{"data_02000000": "0x02000000", "data_02000004": "0x02000004"}',
            calls, {**literals, word0: ('data_02000004', 0x02000004)}, index=f['index'], switch_relocations=linked)
        self.assertEqual(proof.owner_switch.record['switch']['interposed_words'], 5)


if __name__ == '__main__':
    unittest.main()
