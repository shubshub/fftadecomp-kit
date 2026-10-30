"""Synthetic complete-owner cases for the explicit named output pair."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm_const import ARM_REG_R0, ARM_REG_R1, ARM_REG_R3
import ordinary_named_pair_entry_words_inventory as profile
from test_ordinary_named_output_leaf_only_inventory import SECOND_WORDS

parent, named = profile.parent, profile.named
A, S, T, O = 0x08010000, 0x08021000, 0x08021800, 0x08022000
OUTPUT_WORDS = [0x4B02, 0x8C9A, 0x8002, 0x8CD8, 0x8008, 0x4770, 0x7F40, 0x0200]
CALLER = [0xB5F0, 0xB085, 0x9C0A, 0x9D0B, 0x466E, 0x360A, 0x9600,
    0xAB03, 0x9301, 0xAB02, 'named', 0xA802, 0x2100, 0x5E40, 0x2200,
    0x5EB0, 0xAC04, 0x466D, 0x3512, 0x1C20, 0x1C29, 'output', 0x980C,
    0x980D, 'ordinary', 0xB005, 0xBCF0, 0xBC01, 0x4700]


def machine(sequence, address=A):
    data = bytearray()
    for word in sequence:
        if type(word) is int:
            data += struct.pack('<H', word)
        else:
            target = {'named': S, 'output': T, 'ordinary': O}[word]
            delta = target-(address+len(data))-4
            data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF),
                                0xF800|((delta >> 1)&0x7FF))
    return bytes(data)


FIRST_BODY = machine(SECOND_WORDS, S)+struct.pack('<I', named.GLOBAL)
OUTPUT_BODY = machine(OUTPUT_WORDS, T)


def fixture(sequence=CALLER):
    body = machine(sequence)
    bodies = ((A, body, len(sequence)), (S, FIRST_BODY, 34),
              (T, OUTPUT_BODY, 6), (O, b'\x70\x47', 1))
    rows = [dict(rom=f'0x{address:08X}', end=f'0x{address+len(data):08X}',
                 mode='thumb', instrs=count) for address, data, count in bodies]
    mapping = (json.dumps(rows, indent=2)+'\n').encode()
    index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
        f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
        for row in rows).encode()
    rom = bytearray(O-parent.match.ROM_BASE+2)
    for address, data, _ in bodies:
        offset = address-parent.match.ROM_BASE
        rom[offset:offset+len(data)] = data
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    calls = {item.address: item.operands[0].imm for item in decoder.disasm(body, A)
             if item.mnemonic == 'bl'}
    return dict(data=body, address=A, rom=bytes(rom), mapping=mapping, index=index,
        data_mapping=(json.dumps({named.NAME: f'0x{named.GLOBAL:08X}'})+'\n').encode(),
        calls=calls, bindings={site: f'func_{target:08X}' for site, target in calls.items()},
        selector=profile.SELECTOR, readonly_named_buffer_policy=named.named_policy(),
        readonly_second_named_buffer_policy=profile.output.second.second_named_policy(),
        readonly_entry_words_policy=profile.entry_policy())


class NamedPairEntryWordsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for module, field, value in (
                (profile, 'FIRST', (S, S+72, 34, profile.sha(FIRST_BODY))),
                (profile.leaf, 'LEAF', (S, S+72, 34, profile.sha(FIRST_BODY))),
                (profile.output, 'IDENTITY', (T, T+16, 6, profile.sha(OUTPUT_BODY)))):
            patched = patch.object(module, field, value)
            patched.start()
            cls.addClassCleanup(patched.stop)

    def native(self, sequence=CALLER, **changes):
        values = fixture(sequence)
        values.update(changes)
        return profile.verify(**values)

    def proof(self, values=None):
        values = fixture() if values is None else values
        return profile.NamedPairEntryWordsProof(values['rom'], values['mapping'], values['index'],
            values['data_mapping'], values['calls'], values['readonly_named_buffer_policy'],
            values['readonly_second_named_buffer_policy'])

    def frame(self, proof, **changes):
        values = fixture()
        instructions, edges, calls, _ = parent.complete(values['data'], A, values['rom'],
                                                       values['mapping'], values['index'])
        options = dict(stack_aliases=True, local_alias_slot_policy=parent.slots.SELECTOR,
            formal_stack_callee_proof=proof, entry_stack_policy=profile.entry_policy(),
            formal_stack_entry_words_policy=profile.SELECTOR,
            zero_index_profile=parent.zero_index.SELECTOR)
        options.update(changes)
        return parent.frame.prove_frame(instructions, edges, A, {}, calls, **options)

    def test_complete_API_CLI_fresh_frames_and_observed_effects(self):
        values = fixture()
        with patch.object(parent.frame, 'prove_frame', wraps=parent.frame.prove_frame) as frames:
            result, instructions = profile.verify(**values)
        self.assertEqual([call.args[2] for call in frames.call_args_list], [S, T, A])
        self.assertEqual(len(instructions), 29)
        self.assertEqual(result['instructions'], 29)
        self.assertEqual(result['partition']['code_bytes'], 64)
        frame = result['frame']
        self.assertEqual(frame['maximum_frame_bytes'], 40)
        self.assertEqual([row[1:3] for row in frame['entry_stack']['reads']],
                         [[0, 4], [4, 4], [8, 4], [12, 4]])
        self.assertEqual(len(frame['zero_index_signed_loads']), 2)
        pair = frame['formal_stack_callee']
        first, second = pair['callees']
        self.assertEqual(first['calls'][0]['writes_entry_SP_offsets'], [[-32,2],[-30,2],[-28,2]])
        self.assertEqual(second['calls'][0]['writes_entry_SP_offsets'], [[-24,2],[-22,2]])
        self.assertEqual(first['native_leaf']['frame']['maximum_frame_bytes'], 24)
        self.assertEqual(second['native_leaf']['frame']['maximum_frame_bytes'], 0)
        self.assertEqual([child['native_leaf']['effects']['store_event_count']
                          for child in pair['callees']], [5, 2])
        self.assertEqual([row[2:4] for row in first['native_leaf']['effects']['named_reads']],
                         [[32,2],[34,2]])
        self.assertEqual([row[2:4] for row in second['native_leaf']['effects']['named_reads']],
                         [[36,2],[38,2]])
        self.assertEqual(pair['store_events'], 7)
        self.assertEqual(result['component_accounting']['fresh_helper_frames'], 2)
        self.assertEqual(result['numeric_return_facts'], [])
        for field in ('source_or_ELF_admission', 'arithmetic_C_equivalence', 'physical_memory_claim',
                      'memory_safety_claim', 'nonescape_claim', 'universal_termination_claim'):
            self.assertIs(result[field], False)
        root = Path(os.environ['FFTA_PAIR_ENTRY_RETAIN'])
        root.mkdir(parents=True, exist_ok=True)
        names = {'rom':'synthetic-rom.bin', 'mapping':'functions.json',
                 'index':'functions.txt', 'data_mapping':'data_symbols.json'}
        for field, filename in names.items():
            (root/filename).write_bytes(values[field])
        (root/'caller.bin').write_bytes(values['data'])
        (root/'api.json').write_text(json.dumps(result, indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));'
            'import ordinary_named_pair_entry_words_inventory as p;'
            f'p.FIRST={profile.FIRST!r};p.leaf.LEAF={profile.leaf.LEAF!r};'
            f'p.output.IDENTITY={profile.output.IDENTITY!r};p.main()')
        command = [sys.executable, '-c', code, str(Path(profile.__file__).parent),
                   '--profile', profile.SELECTOR]
        for field, filename in names.items():
            command += ['--'+field.replace('_','-'), str(root/filename)]
        for field in ('readonly_named_buffer_policy', 'readonly_second_named_buffer_policy',
                      'readonly_entry_words_policy'):
            command += ['--'+field.replace('_','-'), profile.text(values[field])]
        command += [f'{A:08X}']
        run = subprocess.run(command, capture_output=True, text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        (root/'cli.json').write_text(run.stdout)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), result)

    def test_explicit_exact_entry_and_both_named_read_premises(self):
        policy = profile.entry_policy()
        invalid = (None, {}, True, dict(policy, words=[0,True,2,3]),
            dict(policy, words=[0,1,2]), dict(policy, words=[0,1,2,3,4]),
            dict(policy, words=(0,1,2,3)), dict(policy, writable=True))
        for value in invalid:
            with self.subTest(entry=value), self.assertRaises(ValueError):
                self.native(readonly_entry_words_policy=value)
        for field, expected in (('readonly_named_buffer_policy', named.named_policy()),
                ('readonly_second_named_buffer_policy', profile.output.second.second_named_policy())):
            for value in (None, {}, True, dict(expected, readable=1),
                          dict(expected, reads=expected['reads']+[[40,2]]),
                          dict(expected, reads=[[expected['reads'][0][0],4], expected['reads'][1]])):
                with self.subTest(field=field, policy=value), self.assertRaises(ValueError):
                    self.native(**{field:value})
        output = profile.output
        for policy in (None, {}, dict(output.output_policy(), writes=[[False,0,2],[1,0,2]]),
                       dict(output.output_policy(), writes=[[0,0,4],[1,0,2]])):
            with self.subTest(formal=policy), self.assertRaises(ValueError):
                output.verify(OUTPUT_BODY, T, fixture()['rom'], fixture()['mapping'], fixture()['index'],
                    fixture()['data_mapping'], selector=output.SELECTOR,
                    readonly_named_buffer_policy=output.second.second_named_policy(),
                    formal_output_policy=policy)

    def test_every_declared_incoming_word_is_actually_read_and_never_written(self):
        for position, replacement in ((3,0x9D0A), (23,0x980C), (23,0x980E),
                                      (2,0x900A), (23,0x900D)):
            sequence = list(CALLER)
            sequence[position] = replacement
            with self.subTest(position=position, replacement=replacement), self.assertRaises(ValueError):
                self.native(sequence)

    def test_incoming_unknown_words_cannot_become_output_pointer_origins(self):
        for position, replacement in ((6,0x9400), (19,0x980A), (20,0x990B)):
            sequence = list(CALLER)
            sequence[position] = replacement
            with self.subTest(position=position, replacement=replacement), self.assertRaises(ValueError):
                self.native(sequence)
        proof = self.proof()
        site = next(iter(proof._second.sites))
        with self.assertRaises(ValueError):
            proof.check_call(site, T, {ARM_REG_R0:frozenset(((-24,True),))},
                             [('local',None)]*5+[('saved',None)]*5, {})

    def test_local_halfwords_require_alignment_disjoint_domains_and_live_allocation(self):
        for position, replacement in ((5,0x360B), (7,0xAB02), (9,0xAB00),
                (16,0xAC00), (16,0xAC05), (18,0x3511), (18,0x3510)):
            sequence = list(CALLER)
            sequence[position] = replacement
            with self.subTest(position=position, replacement=replacement), self.assertRaises(ValueError):
                self.native(sequence)
        proof = self.proof()
        site = next(iter(proof._second.sites))
        stack = [('local',None)]*5+[('saved',None)]*5
        for origin in ((-22,False), (-21,True), (-40,True), (-20,True), (-24,True)):
            aliases = {ARM_REG_R0:frozenset(((-24,True),)), ARM_REG_R1:frozenset((origin,))}
            with self.subTest(origin=origin), self.assertRaises(ValueError):
                proof.check_call(site, T, aliases, stack, {})

    def test_helper_writes_invalidate_overlapping_scalar_and_alias_slot_facts(self):
        # A pointer spilled at SP+16 is partially overwritten by the second leaf.
        # Reloading it after the call must retain taint, never yield a scalar.
        sequence = CALLER[:19]+[0x9604]+CALLER[19:22]+[0x9804,0x7800]+CALLER[22:]
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired|partial load'):
            self.native(sequence)
        # A copied entry-LR token in SP+16 must not survive the two halfword writes.
        sequence = CALLER[:2]+[0x4677,0x9704]+CALLER[2:25]+[0x9A04]+CALLER[25:-2]+[0xBC02,0x4710]
        with self.assertRaises(ValueError):
            self.native(sequence)
        # Releasing and re-allocating locals cannot revive the old r5/r6 aliases.
        sequence = CALLER[:19]+[0xB005,0xB085]+CALLER[19:]
        with self.assertRaisesRegex(ValueError, 'expired'):
            self.native(sequence)

    def test_pair_gate_stays_closed_without_exact_token_and_native_children(self):
        proof = self.proof()
        for token in (None, True, named.SELECTOR):
            with self.subTest(token=token), self.assertRaises(ValueError):
                self.frame(proof, formal_stack_entry_words_policy=token)
        for fake in ({'complete':True}, proof._first, proof._second):
            with self.subTest(fake=type(fake).__name__), self.assertRaises(ValueError):
                self.frame(fake)
        for change in (dict(formal_stack_entry_word_policy='wrong'),
                       dict(formal_stack_alias_constant_policy=parent.slots.FORMAL_MOVS10_POLICY),
                       dict(stack_aliases=False), dict(local_alias_slot_policy=None)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.frame(proof, **change)

    def test_mutated_child_seals_exact_types_and_marked_sites_are_rejected(self):
        for child in ('_first','_second'):
            proof = self.proof()
            getattr(proof, child)._record['effects']['writes'] = []
            with self.subTest(seal=child), self.assertRaises(ValueError):
                proof.validate_calls(fixture()['calls'])
            proof = self.proof()
            setattr(proof, child, object())
            with self.subTest(type=child), self.assertRaises(ValueError):
                proof.validate_calls(fixture()['calls'])
        proof = self.proof()
        site = min(proof.sites)
        proof.sites[site+2] = proof.sites.pop(site)
        with self.assertRaises(ValueError):
            proof.validate_calls(fixture()['calls'])
        proof = self.proof()
        site = next(iter(proof._second.sites))
        proof._second.sites[site+2] = proof._second.sites.pop(site)
        with self.assertRaises(ValueError):
            proof.validate_calls(fixture()['calls'])
        with self.assertRaises(ValueError):
            self.proof().fingerprint()

    def test_actual_bodies_dual_indexes_and_named_binding_are_authenticated(self):
        values = fixture()
        for address, offset in ((S,0), (S,68), (T,4), (T,12)):
            rom = bytearray(values['rom'])
            rom[address-parent.match.ROM_BASE+offset] ^= 4
            with self.subTest(address=address, offset=offset), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        for row_number in (0,1,2):
            rows = json.loads(values['mapping'])
            rows[row_number]['instrs'] += 1
            with self.subTest(json_row=row_number), self.assertRaises(ValueError):
                self.native(mapping=json.dumps(rows).encode())
        for old, new in ((b'72 34 return',b'72 35 return'), (b'16 6 return',b'16 7 return')):
            with self.subTest(text_row=old), self.assertRaises(ValueError):
                self.native(index=values['index'].replace(old,new))
        for data_mapping in (b'{}', json.dumps({named.NAME:'0x02007F42'}).encode(),
                             bytearray(values['data_mapping'])):
            with self.subTest(data=data_mapping), self.assertRaises(ValueError):
                self.native(data_mapping=data_mapping)
        rows = json.loads(values['mapping'])
        rows.append(copy.deepcopy(rows[2]))
        with self.assertRaises(ValueError):
            self.native(mapping=json.dumps(rows).encode())

    def test_selector_actual_calls_bindings_shape_and_manifest_are_exact(self):
        for selector in (None, True, profile.leaf.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        values = fixture()
        for field in ('calls','bindings'):
            changed = dict(values[field])
            changed.pop(min(changed))
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.native(**{field:changed})
        for position, replacement in ((10,'ordinary'), (21,'ordinary'), (24,'named'), (24,'output')):
            sequence = list(CALLER)
            sequence[position] = replacement
            with self.subTest(position=position, replacement=replacement), self.assertRaises(ValueError):
                self.native(sequence)
        for manifest in ({}, dict(source_or_ELF_admission=True), dict(numeric_return_facts=[0])):
            with self.subTest(manifest=manifest), self.assertRaises(ValueError):
                self.native(manifest=manifest)
        for target in (0x081426B8, parent.thunks.ALIASES['_call_via_r4']):
            calls = dict(values['calls'])
            calls[max(calls)] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, values['mapping'], A, len(values['data']), len(values['rom']))


if __name__ == '__main__':
    unittest.main()
