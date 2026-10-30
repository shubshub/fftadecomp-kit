"""Composition checks for named output, incoming word0 and local zero indices."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path[:0] = [str(Path(__file__).resolve().parents[1] / 'tools'), str(Path(__file__).resolve().parent)]
import ordinary_named_output_entry_word_inventory as profile
import ordinary_named_output_leaf_only_inventory as previous
import test_ordinary_named_output_leaf_only_inventory as fixtures

ENTRY = {'schema': 'thumb-readonly-entry-stack-word-v1', 'words': [0]}
# The incoming value remains unknown. It supplies no caller-local pointer fact.
SEQUENCE = list(fixtures.LINEAR)
SEQUENCE[SEQUENCE.index(0x8800):SEQUENCE.index(0x8800)+1] = [0x2100, 0x5E40]
SEQUENCE.insert(SEQUENCE.index(0xB004), 0x9808)


def inputs(sequence=SEQUENCE):
    values = fixtures.fixture(sequence)
    values.update(selector=profile.SELECTOR, readonly_entry_word_policy=copy.deepcopy(ENTRY))
    return values


class NamedOutputEntryWordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        values = inputs()
        body = values['rom'][fixtures.S-profile.parent.match.ROM_BASE:fixtures.S-profile.parent.match.ROM_BASE+72]
        helper = patch.object(profile, 'LEAF', (fixtures.S, fixtures.S+72, 34, profile.sha(body)))
        helper.start()
        cls.addClassCleanup(helper.stop)

    def test_API_CLI_actual_entry_read_and_fresh_output_effects(self):
        values = inputs()
        result, instructions = profile.verify(**values)
        self.assertEqual(result['instructions'], len(SEQUENCE))
        self.assertEqual(len(instructions), len(SEQUENCE))
        frame = result['frame']
        self.assertEqual(frame['maximum_frame_bytes'], 32)
        self.assertEqual(frame['entry_stack']['words'], [0])
        self.assertEqual([row[1:] for row in frame['entry_stack']['reads']], [[0, 4, '0898']])
        self.assertEqual(len(frame['zero_index_signed_loads']), 1)
        self.assertEqual(frame['formal_stack_callee']['calls'][0]['writes_entry_SP_offsets'],
                         [[-24, 2], [-22, 2], [-20, 2]])
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertFalse(result['source_or_ELF_admission'])
        self.assertFalse(result['memory_safety_claim'])
        self.assertEqual(profile.verify(**values, manifest=result)[0], result)
        root = Path(os.environ['FFTA_ENTRY_OUTPUT_RETAIN'])
        root.mkdir(parents=True, exist_ok=True)
        names = {'rom': 'synthetic-rom.bin', 'mapping': 'functions.json',
                 'index': 'functions.txt', 'data_mapping': 'data_symbols.json'}
        for key, name in names.items():
            (root/name).write_bytes(values[key])
        (root/'synthetic-api.json').write_text(json.dumps(result, indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));'
                'import ordinary_named_output_entry_word_inventory as p;'
                f'p.LEAF={profile.LEAF!r};p.main()')
        command = [sys.executable, '-c', code, str(Path(profile.__file__).parent),
                   '--profile', profile.SELECTOR]
        for key, name in names.items():
            command += ['--'+key.replace('_', '-'), str(root/name)]
        command += ['--readonly-named-buffer-policy', profile.text(values['readonly_named_buffer_policy']),
                    '--readonly-entry-word-policy', profile.text(ENTRY), f'{fixtures.A:08X}']
        run = subprocess.run(command, capture_output=True, text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        (root/'synthetic-cli.json').write_text(run.stdout)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), result)

    def test_explicit_exact_entry_and_named_premises(self):
        for policy in (None, {}, True, dict(ENTRY, words=[False]), dict(ENTRY, words=[0,1]),
                       dict(ENTRY, words=[1]), dict(ENTRY, readable=True)):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                profile.verify(**dict(inputs(), readonly_entry_word_policy=policy))
        for policy in (None, {}, dict(profile.named.named_policy(), readable=1)):
            with self.subTest(named=policy), self.assertRaises(ValueError):
                profile.verify(**dict(inputs(), readonly_named_buffer_policy=policy))

    def test_read_beyond_word0_and_write_to_incoming_are_rejected(self):
        for word in (0x9809, 0x9008):
            sequence = list(SEQUENCE)
            sequence[sequence.index(0x9808)] = word
            with self.subTest(word=word), self.assertRaises(ValueError):
                profile.verify(**inputs(sequence))

    def test_declared_but_unused_incoming_word_is_rejected(self):
        sequence = list(SEQUENCE)
        sequence.remove(0x9808)
        with self.assertRaisesRegex(ValueError, 'actual reached incoming'):
            profile.verify(**inputs(sequence))

    def test_unknown_incoming_value_cannot_become_local_output(self):
        sequence = list(SEQUENCE)
        sequence[sequence.index(0xAB02)] = 0x9B08
        with self.assertRaises(ValueError):
            profile.verify(**inputs(sequence))

    def test_nonzero_local_index_and_outgoing_overlap_are_rejected(self):
        sequence = list(SEQUENCE)
        sequence[sequence.index(0x2100)] = 0x2101
        with self.assertRaises(ValueError):
            profile.verify(**inputs(sequence))
        sequence = list(SEQUENCE)
        sequence[sequence.index(0xAB02)] = 0xAB01
        with self.assertRaises(ValueError):
            profile.verify(**inputs(sequence))

    def test_default_formal_and_local_slot_composition_stays_closed(self):
        values = inputs()
        instructions, edges, calls, _ = profile.parent.complete(values['data'], values['address'],
            values['rom'], values['mapping'], values['index'])
        body = values['rom'][fixtures.S-profile.parent.match.ROM_BASE:fixtures.S-profile.parent.match.ROM_BASE+72]
        def fresh():
            return profile.named.NamedReadonlyFormalLeafProof(body, fixtures.S, values['rom'],
                values['mapping'], values['index'], values['data_mapping'],
                {site: target for site, target in calls.items() if target == fixtures.S},
                values['readonly_named_buffer_policy'])
        kwargs = dict(stack_aliases=True, local_alias_slot_policy=profile.parent.slots.SELECTOR,
                      entry_stack_policy=ENTRY, zero_index_profile=profile.parent.zero_index.SELECTOR)
        for token in (None, True, previous.SELECTOR):
            with self.subTest(token=token), self.assertRaises(ValueError):
                profile.parent.frame.prove_frame(instructions, edges, values['address'], {}, calls,
                    formal_stack_callee_proof=fresh(), formal_stack_entry_word_policy=token, **kwargs)
        with self.assertRaises(ValueError):
            profile.parent.frame.prove_frame(instructions, edges, values['address'], {}, calls,
                formal_stack_entry_word_policy=profile.SELECTOR, **kwargs)
        with patch.object(previous, 'LEAF', profile.LEAF), self.assertRaises(ValueError):
            old = dict(values, selector=previous.SELECTOR)
            old.pop('readonly_entry_word_policy')
            previous.verify(**old)

    def test_actual_calls_indices_body_identity_and_manifest(self):
        values = inputs()
        for field in ('calls', 'bindings'):
            with self.subTest(field=field), self.assertRaises(ValueError):
                profile.verify(**dict(values, **{field: {}}))
        with self.assertRaises(ValueError):
            profile.verify(**dict(values, selector=previous.SELECTOR))
        rom = bytearray(values['rom'])
        rom[fixtures.S-profile.parent.match.ROM_BASE] ^= 4
        with self.assertRaises(ValueError):
            profile.verify(**dict(values, rom=bytes(rom)))
        with self.assertRaises(ValueError):
            profile.verify(**values, manifest={})
        rows = json.loads(values['mapping'])
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(values, mapping=json.dumps(rows).encode()))


if __name__ == '__main__':
    unittest.main()
