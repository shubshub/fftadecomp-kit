"""Decoded cases for a single authenticated named-read output leaf."""
import copy
import importlib.util
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
from capstone.arm_const import ARM_REG_R3
import ordinary_named_output_leaf_only_inventory as profile

parent, named = profile.parent, profile.named
A, S, O = 0x08010000, 0x08021000, 0x08022000
SECOND_WORDS = [0xB5F0,0x4647,0xB480,0x9C06,0x46A0,0x9F07,0x0400,0x1400,
    0x0412,0x1412,0x1A84,0x1064,0x801C,0x4E0A,0x8C35,0x1964,0x801C,
    0x1880,0x1082,0x0409,0x1449,0x1A52,0x4641,0x800A,0x8C71,0x1852,
    0x4644,0x8022,0x8038,0xBC08,0x4698,0xBCF0,0xBC01,0x4700]
LINEAR = [0xB570,0xB084,0x466D,0x350A,0xAB03,0x2108,0x5E44,0x220A,
    0x5E81,0x260C,0x5F82,0x9500,0x9301,0x1C20,0xAB02,'named',
    0xA802,0x8800,0x3878,0x0400,0x1400,0x8829,0x3960,0x0409,0x1409,
    'ordinary',0x0600,0x0E00,0xB004,0xBC70,0xBC02,0x4708]
BRANCHED = [0xB530,0xB084,0x1C02,0x0609,0x0E09,0x1C0B,0x2000,0x2901,
    0xD00B,0x2901,0xDC02,0x2900,0xD003,0xE025,0x2B02,0xD01E,0xE022,
    0x1C10,'ordinary',0xE01C,0x466C,0x340A,0xAB03,0x2108,0x5E50,
    0x250A,0x5F51,0x250C,0x5F52,0x9400,0x9301,0xAB02,'named',0xA802,
    0x8800,0x3878,0x0400,0x1400,0x8821,0x3960,0x0409,0x1409,'ordinary',
    0xE002,0x1C10,'ordinary',0x0600,0x0E00,0xB004,0xBC30,0xBC02,0x4708]


def machine(sequence, address=A):
    data = bytearray()
    for word in sequence:
        if type(word) is int:
            data += struct.pack('<H', word)
        else:
            target = {'named': S, 'ordinary': O}[word]
            delta = target-(address+len(data))-4
            data += struct.pack('<HH', 0xF000|((delta >> 12)&0x7FF), 0xF800|((delta >> 1)&0x7FF))
    return bytes(data)


def fixture(sequence=LINEAR):
    body = machine(sequence)
    helper = machine(SECOND_WORDS, S)+struct.pack('<I', named.GLOBAL)
    rows = [{'rom': f'0x{address:08X}', 'end': f'0x{address+len(data):08X}',
        'mode': 'thumb', 'instrs': count} for address, data, count in
        ((A, body, len(sequence)), (S, helper, 34), (O, b'\x70\x47', 1))]
    mapping = (json.dumps(rows, indent=2)+'\n').encode()
    index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
    rom = bytearray(O-parent.match.ROM_BASE+2)
    for address, data in ((A, body), (S, helper), (O, b'\x70\x47')):
        rom[address-parent.match.ROM_BASE:address-parent.match.ROM_BASE+len(data)] = data
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    calls = {i.address: i.operands[0].imm for i in decoder.disasm(body, A) if i.mnemonic == 'bl'}
    return dict(data=body, address=A, rom=bytes(rom), mapping=mapping, index=index,
        data_mapping=(json.dumps({named.NAME: f'0x{named.GLOBAL:08X}'})+'\n').encode(),
        calls=calls, bindings={s: f'func_{t:08X}' for s, t in calls.items()}, selector=profile.SELECTOR,
        readonly_named_buffer_policy=named.named_policy())


class NamedOutputLeafOnlyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.helper = machine(SECOND_WORDS, S)+struct.pack('<I', named.GLOBAL)
        patched = patch.object(profile, 'LEAF', (S, S+len(cls.helper), 34, profile.sha(cls.helper)))
        patched.start()
        cls.addClassCleanup(patched.stop)

    def native(self, sequence=LINEAR, **changes):
        values = fixture(sequence)
        values.update(changes)
        return profile.verify(**values)

    def proof(self, values=None):
        values = fixture() if values is None else values
        sites = {s: t for s, t in values['calls'].items() if t == S}
        return named.NamedReadonlyFormalLeafProof(self.helper, S, values['rom'], values['mapping'],
            values['index'], values['data_mapping'], sites, values['readonly_named_buffer_policy'])

    def test_complete_linear_branch_API_CLI_and_actual_effects(self):
        values = fixture()
        result, instructions = profile.verify(**values)
        self.assertEqual(result['instructions'], 32)
        self.assertEqual(len(instructions), 32)
        self.assertEqual(result['partition']['code_bytes'], 68)
        self.assertEqual(result['frame']['maximum_frame_bytes'], 32)
        effect = result['frame']['formal_stack_callee']
        self.assertEqual(effect['calls'][0]['writes_entry_SP_offsets'], [[-24,2],[-22,2],[-20,2]])
        leaf = effect['native_leaf']
        self.assertEqual(leaf['effects']['store_event_count'], 5)
        self.assertEqual(leaf['effects']['writes'], [[3,0,2],[4,0,2],[5,0,2]])
        self.assertEqual([[r[2],r[3]] for r in leaf['effects']['named_reads']], [[32,2],[34,2]])
        self.assertEqual(leaf['partition']['literal_and_table_bytes'], 4)
        self.assertEqual(result['numeric_return_facts'], [])
        self.assertNotIn('exact_MOVS10_SP_constructors', result)
        self.assertNotIn('constant_policy', result['frame']['local_alias_slots'])
        self.assertNotIn('exact_noop', result)
        branch, _ = self.native(BRANCHED)
        self.assertEqual(branch['instructions'], 52)
        self.assertEqual(branch['frame']['maximum_frame_bytes'], 28)
        self.assertEqual(branch['frame']['formal_stack_callee']['calls'][0]['writes_entry_SP_offsets'],
            [[-20,2],[-18,2],[-16,2]])
        root = Path(os.environ['FFTA_NAMED_OUTPUT_RETAIN'])
        root.mkdir(parents=True, exist_ok=True)
        for name, data in (('caller.bin', values['data']), ('helper.bin', self.helper),
                ('synthetic-rom.bin', values['rom']), ('functions.json', values['mapping']),
                ('functions.txt', values['index']), ('data_symbols.json', values['data_mapping'])):
            (root/name).write_bytes(data)
        (root/'synthetic-api.json').write_text(json.dumps(result, indent=2)+'\n')
        (root/'synthetic-branch-api.json').write_text(json.dumps(branch, indent=2)+'\n')
        code = ('import sys;sys.path.insert(0,sys.argv.pop(1));'
            'import ordinary_named_output_leaf_only_inventory as p;'
            f'p.LEAF={profile.LEAF!r};p.main()')
        run = subprocess.run([sys.executable, '-c', code, str(Path(profile.__file__).parent),
            '--profile', profile.SELECTOR, '--rom', str(root/'synthetic-rom.bin'),
            '--mapping', str(root/'functions.json'), '--index', str(root/'functions.txt'),
            '--data-mapping', str(root/'data_symbols.json'), '--readonly-named-buffer-policy',
            profile.text(named.named_policy()), f'{A:08X}'], capture_output=True, text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), result)
        (root/'synthetic-cli.json').write_text(run.stdout)

    def test_missing_wrong_and_wider_named_data_premises(self):
        for data in (b'{}', b'{"g_state_02007F40":"0x02007F42"}', bytearray(b'{}'),
                b'{"g_state_02007F40":"0x02007F40","g_state_02007F40":"0x02007F40"}'):
            with self.subTest(data=str(data)), self.assertRaises(ValueError):
                self.native(data_mapping=data)
        for policy in (None, {}, True, dict(named.named_policy(), readable=1),
                dict(named.named_policy(), reads=[[32,4],[34,2]]),
                dict(named.named_policy(), reads=[[32,2],[34,2],[36,2]])):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                self.native(readonly_named_buffer_policy=policy)

    def test_body_dual_indices_and_literal_identity(self):
        values = fixture()
        for offset in (0, 68):
            rom = bytearray(values['rom'])
            rom[S-parent.match.ROM_BASE+offset] ^= 4
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'body identity'):
                self.native(rom=bytes(rom))
        rows = json.loads(values['mapping'])
        rows[1]['instrs'] = 36
        with self.assertRaises(ValueError):
            self.native(mapping=json.dumps(rows).encode())
        with self.assertRaises(ValueError):
            self.native(index=values['index'].replace(b'72 34 return', b'72 36 return'))
        rows = json.loads(values['mapping'])
        rows.append(copy.deepcopy(rows[1]))
        with self.assertRaises(ValueError):
            self.native(mapping=json.dumps(rows).encode())

    def test_selector_actual_calls_bindings_and_one_leaf_shape(self):
        for selector in (None, True, named.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.native(selector=selector)
        values = fixture()
        for field in ('calls', 'bindings'):
            changed = dict(values[field])
            changed.pop(min(changed))
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.native(**{field: changed})
        with self.assertRaises(ValueError):
            self.native(manifest={})
        for replacement in ('ordinary', 'named'):
            seq = list(LINEAR)
            seq[15 if replacement == 'ordinary' else 25] = replacement
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                self.native(seq)
        for target in (0x081426B8, 0x08142950, parent.thunks.ALIASES['_call_via_r4']):
            calls = dict(values['calls'])
            calls[min(calls)] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, values['mapping'], A, len(values['data']), len(values['rom']))

    def test_outgoing_pointer_and_live_local_safety(self):
        for position, replacement in ((3,0x250A),(3,0x350B),(3,0x3510),
                (11,0x2000),(11,0x9000),(12,0x9302),(14,0xAB00),(14,0xAB03)):
            sequence = list(LINEAR)
            sequence[position] = replacement
            with self.subTest(position=position,replacement=replacement), self.assertRaises(ValueError):
                self.native(sequence)

    def test_unmarked_alias_call_and_partial_output_pointer_taint(self):
        with self.assertRaisesRegex(ValueError, 'crossing calls'):
            self.native(LINEAR[:25]+[0xA802]+LINEAR[25:])
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired'):
            self.native(LINEAR[:15]+[0x9503]+LINEAR[15:16]+[0x9803,0x7800]+LINEAR[16:])

    def test_exact_fresh_proof_seal_sites_and_forged_outgoing_facts(self):
        values = fixture()
        instructions, edges, calls, _ = parent.complete(values['data'], A, values['rom'],
            values['mapping'], values['index'])
        with self.assertRaisesRegex(ValueError, 'exclusive fresh native'):
            parent.frame.prove_frame(instructions, edges, A, {}, calls, stack_aliases=True,
                local_alias_slot_policy=parent.slots.SELECTOR,
                formal_stack_callee_proof={'complete': True, 'writes': [[3,0,2],[4,0,2],[5,0,2]]})
        proof = self.proof()
        proof._record['effects']['named_reads'] = []
        with self.assertRaises(ValueError):
            proof.validate_calls(values['calls'])
        proof = self.proof()
        site = next(iter(proof.sites))
        proof.sites[site+2] = proof.sites.pop(site)
        with self.assertRaises(ValueError):
            proof.validate_calls(values['calls'])
        proof = self.proof()
        stack = [('local',None)]*4+[('saved',None)]*4
        aliases = {ARM_REG_R3: frozenset(((-24,True),))}
        slots = {-32:frozenset(((-22,True),)), -28:frozenset(((-20,True),))}
        for value in (frozenset(((-22,False),)), frozenset(((-22,True),(-20,True))),
                frozenset(((-21,True),)), frozenset(((-16,True),)), frozenset(((-32,True),))):
            changed = dict(slots)
            changed[-32] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                proof.check_call(site, S, aliases, stack, changed)

    def test_default_frame_output_and_unproved_alias_refusal_unchanged(self):
        code = machine([0xB510,0x1C04,0x1C20,0xBC10,0xBC02,0x4708])
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        instructions = {i.address:i for i in decoder.disasm(code,A)}
        edges = {s: (() if s == A+len(code)-2 else (s+2,)) for s in instructions}
        original = Path(os.environ['FFTA_NAMED_OUTPUT_BASELINE'])/'tools/local_long_branch_profile.py'
        spec = importlib.util.spec_from_file_location('unchanged_parent_frame', original)
        baseline = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(baseline)
        self.assertEqual(parent.frame.prove_frame(instructions,edges,A,{},{}),
            baseline.prove_frame(instructions,edges,A,{},{}))
        values = fixture()
        ins, edges, calls, _ = parent.complete(values['data'],A,values['rom'],values['mapping'],values['index'])
        with self.assertRaisesRegex(ValueError,'crossing calls'):
            parent.frame.prove_frame(ins,edges,A,{},calls,stack_aliases=True,
                local_alias_slot_policy=parent.slots.SELECTOR)


if __name__ == '__main__':
    unittest.main()
