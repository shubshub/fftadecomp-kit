"""Decoded synthetic proofs for the explicit formal-stack output composition."""
import copy
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
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import ARM_REG_R0, ARM_REG_R3
import ordinary_formal_stack_callee_inventory as profile

A, L, N, O = 0x08010000, 0x08020000, 0x08021000, 0x08022000
LEAF_WORDS = [0xB530, 0x9C03, 0x9D04, 0x0400, 0x12C0, 0x3010, 0x8018,
    0x0109, 0x8021, 0x0412, 0x12D2, 0x3210, 0x802A, 0xBC30, 0xBC01, 0x4700]
HEAD = [0xB570, 0xB085]
ARGUMENTS = [0x466E, 0x360E, 0x9600, 0xAD04, 0x9501, 0xAB03]
TAIL = [0xA803, 0x2200, 0x5E81, 0x2000, 0x5E32, 0x2000, 0x5E2B,
    0x2015, 0x9000, 'ordinary', 0x2000, 0xB005, 0xBC70, 0xBC02, 0x4708]
SEQUENCE = HEAD+['ordinary', 0xAC02, 'noop', 0x8021]+ARGUMENTS+['leaf']+TAIL


def machine(sequence, address=A):
    data = bytearray()
    for value in sequence:
        if type(value) is int:
            data += struct.pack('<H', value)
        else:
            target = {'ordinary': O, 'noop': N, 'leaf': L}[value]
            delta = target-(address+len(data))-4
            data += struct.pack('<HH', 0xF000|((delta>>12)&0x7FF), 0xF800|((delta>>1)&0x7FF))
    return bytes(data)


def indexes(rows):
    return ((json.dumps(rows, indent=2)+'\n').encode(),
        ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
            f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n' for row in rows).encode())


def fixture(sequence=SEQUENCE, leaf=None):
    leaf = machine(LEAF_WORDS, L) if leaf is None else leaf
    body = machine(sequence)
    rows = [{'rom':f'0x{address:08X}', 'end':f'0x{address+len(data):08X}',
             'mode':'thumb', 'instrs':len(data)//2}
            for address, data in ((A, body), (L, leaf), (N, b'\x70\x47'), (O, b'\x70\x47'))]
    mapping, _ = indexes(rows)
    rows[0]['instrs'] = profile.owner.refine(body, A, mapping)['instrs']
    mapping, index = indexes(rows)
    rom = bytearray(O-profile.match.ROM_BASE+2)
    for address, data in ((A, body), (L, leaf), (N, b'\x70\x47'), (O, b'\x70\x47')):
        rom[address-profile.match.ROM_BASE:address-profile.match.ROM_BASE+len(data)] = data
    calls = {int(row['site'],16):int(row['target'],16)
             for row in profile.owner.refine(body, A, mapping)['calls']}
    return dict(data=body, address=A, rom=bytes(rom), mapping=mapping, index=index,
                calls=calls, bindings={site:f'func_{target:08X}' for site,target in calls.items()},
                selector=profile.SELECTOR)


class FormalStackCalleeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.leaf_body = machine(LEAF_WORDS, L)
        cls.leaf_patch = patch.object(profile, 'LEAF', (L, L+32, 16, profile.sha(cls.leaf_body)))
        cls.noop_patch = patch.object(profile, 'NOOP', (N, N+2, 1, profile.sha(b'\x70\x47')))
        cls.leaf_patch.start(); cls.addClassCleanup(cls.leaf_patch.stop)
        cls.noop_patch.start(); cls.addClassCleanup(cls.noop_patch.stop)

    def native(self, sequence=SEQUENCE, **changes):
        values = fixture(sequence)
        values.update(changes)
        return profile.verify(**values)

    def components(self, values=None):
        values = fixture() if values is None else values
        body = values['rom'][L-profile.match.ROM_BASE:L-profile.match.ROM_BASE+32]
        sites = {site:target for site,target in values['calls'].items() if target == L}
        return profile.FormalStackCalleeProof(body, L, values['rom'], values['mapping'], values['index'], sites)

    def frame(self, sequence, proof=True):
        values = fixture(sequence)
        instructions, edges, calls, _ = profile.complete(values['data'], A,
            values['rom'], values['mapping'], values['index'])
        return profile.frame.prove_frame(instructions, edges, A, {}, calls,
            stack_aliases=True, local_alias_slot_policy=profile.slots.SELECTOR,
            zero_index_profile=profile.zero_index.SELECTOR,
            formal_stack_callee_proof=self.components(values) if proof else None)

    def test_complete_synthetic_API_CLI_and_observed_effects(self):
        values = fixture()
        result, decoded = profile.verify(**values)
        effect = result['frame']['formal_stack_callee']
        self.assertEqual(effect['native_leaf']['effects']['writes'], [[3,0,2],[4,0,2],[5,0,2]])
        self.assertEqual(effect['native_leaf']['effects']['reads'], [])
        self.assertEqual(effect['native_leaf']['frame']['maximum_frame_bytes'], 12)
        self.assertEqual(effect['calls'][0]['writes_entry_SP_offsets'], [[-24,2],[-22,2],[-20,2]])
        self.assertEqual(len(decoded), len(values['data'])//2-4)
        self.assertTrue(result['complete_native_structural_proof'])
        self.assertFalse(result['physical_memory_claim'] or result['source_or_ELF_admission'])
        root = Path(os.environ.get('FFTA_FORMAL_STACK_RETAIN', os.environ['TMPDIR']))
        root.mkdir(parents=True, exist_ok=True)
        for name, data in (('caller.bin', values['data']), ('leaf.bin', self.leaf_body),
                ('synthetic-rom.bin', values['rom']), ('functions.json', values['mapping']), ('functions.txt', values['index'])):
            (root/name).write_bytes(data)
        (root/'synthetic-api.json').write_text(json.dumps(result, indent=2)+'\n')
        # Only the two relocated test identities change; this never qualifies an
        # original ROM component. CLI calls the same public explicit selector.
        code = ('import sys,json;sys.path.insert(0,sys.argv.pop(1));'
            'import ordinary_formal_stack_callee_inventory as p;'
            f'p.LEAF={profile.LEAF!r};p.NOOP={profile.NOOP!r};p.main()')
        command = [sys.executable, '-c', code, str(Path(profile.__file__).parent), '--profile',profile.SELECTOR,
            '--rom',str(root/'synthetic-rom.bin'),'--mapping',str(root/'functions.json'),
            '--index',str(root/'functions.txt'),f'{A:08X}']
        run = subprocess.run(command, capture_output=True, text=True)
        (root/'cli-stderr.txt').write_text(run.stderr)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout), result)
        (root/'synthetic-cli.json').write_text(run.stdout)

    def test_default_refusal_and_unmarked_call_alias(self):
        with self.assertRaisesRegex(ValueError, 'crossing calls require native buffer proof'):
            self.frame(SEQUENCE, False)
        sequence = HEAD+ARGUMENTS+['ordinary','leaf']+TAIL
        with self.assertRaisesRegex(ValueError, 'crossing calls require native buffer proof'):
            self.frame(sequence)

    def test_selector_types_and_incomplete_call_bindings(self):
        for selector in (None, True, 'other'):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'explicit default-off'):
                self.native(selector=selector)
        values = fixture()
        for field in ('calls', 'bindings'):
            changed = dict(values[field]); changed.pop(next(iter(changed)))
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.native(**{field:changed})

    def test_leaf_and_noop_forged_body_rejected(self):
        values = fixture()
        for address in (L, N):
            rom = bytearray(values['rom']); rom[address-profile.match.ROM_BASE] ^= 1
            with self.subTest(address=address), self.assertRaisesRegex(ValueError, 'body identity'):
                self.native(rom=bytes(rom))

    def test_dual_index_and_ambiguous_target_ownership(self):
        values = fixture()
        rows = json.loads(values['mapping'])
        rows[0]['instrs'] += 1
        with self.assertRaises(ValueError): self.native(mapping=indexes(rows)[0])
        with self.assertRaises(ValueError): self.native(index=values['index'].replace(b'16 return',b'15 return'))
        rows = json.loads(values['mapping']); rows.append(dict(rows[1]))
        with self.assertRaises(ValueError): self.native(mapping=indexes(rows)[0])

    def test_reserved_runtime_targets_never_become_ordinary(self):
        values = fixture()
        for target in (0x081426B8, 0x08142950, 0x08142AB0, 0x08142B28, profile.thunks.ALIASES['_call_via_r4']):
            calls = dict(values['calls']); calls[min(calls)] = target
            with self.subTest(target=target), self.assertRaises(ValueError):
                profile.bind_calls(calls, values['mapping'], A, len(values['data']), len(values['rom']))

    def test_formal_load_offset_missing_origin_and_wrong_write_width(self):
        for position, replacement in ((2,0x9D05), (2,0x2500), (6,0x8000), (8,0x7021), (8,0x8023)):
            sequence = list(LEAF_WORDS); sequence[position] = replacement
            values = fixture(leaf=machine(sequence, L))
            with self.subTest(position=position,replacement=replacement), self.assertRaises(ValueError):
                self.components(values)

    def test_leaf_CFG_nested_call_and_return_restoration(self):
        values = fixture()
        instructions, edges, _, _ = profile.complete(self.leaf_body,L,values['rom'],values['mapping'],values['index'])
        bad = dict(edges); bad[L+2] = (L+6,)
        with self.assertRaisesRegex(ValueError, 'CFG'):
            profile.prove_formal_origins(instructions,bad,L)
        for position,replacement in ((13,0xBC10),(14,0xBC02),(15,0x4708),(0,0xB538)):
            sequence = list(LEAF_WORDS); sequence[position] = replacement
            with self.subTest(position=position), self.assertRaises(ValueError):
                self.components(fixture(leaf=machine(sequence,L)))

    def test_missing_scalar_misaligned_and_saved_slot_outgoing_pointer(self):
        for args in (ARGUMENTS[:2]+[0x2000,0x9000]+ARGUMENTS[3:],
                ARGUMENTS[:2]+ARGUMENTS[3:], ARGUMENTS[:1]+[0x360F]+ARGUMENTS[2:],
                ARGUMENTS[:-1]+[0xAB05], ARGUMENTS[:3]+[0xAD05]+ARGUMENTS[4:]):
            with self.subTest(args=args), self.assertRaises(ValueError):
                self.frame(HEAD+args+['leaf']+TAIL)

    def test_output_cannot_overlap_outgoing_words_or_other_output(self):
        for args in (ARGUMENTS[:-1]+[0xAB00], ARGUMENTS[:-1]+[0xAB04]):
            with self.subTest(args=args), self.assertRaisesRegex(ValueError, 'overlaps'):
                self.frame(HEAD+args+['leaf']+TAIL)

    def test_unknown_or_expired_pointer_slot_stays_rejected(self):
        for middle in ([0xB005,0xB085], [0x4668,0x2100,0x7001]):
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                self.frame(HEAD+ARGUMENTS+middle+['leaf']+TAIL)

    def test_effect_write_invalidates_overlapping_saved_origin_word(self):
        # A local word holds the entry LR, then receives the leaf's two-byte
        # output. Reusing that word as an exit must lose the entry-LR token.
        sequence = HEAD+[0x4670,0x9003]+ARGUMENTS+['leaf',0x9803,
            0xB005,0xBC70,0xBC02,0x4700]
        values = fixture(sequence)
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB); decoder.detail = True
        instructions = {item.address:item for item in decoder.disasm(values['data'],A)}
        edges = {site: (() if item.mnemonic == 'bx' else (site+item.size,))
                 for site,item in instructions.items()}
        calls = {site:item.operands[0].imm for site,item in instructions.items() if item.mnemonic == 'bl'}
        with self.assertRaisesRegex(ValueError, 'restore SP'):
            profile.frame.prove_frame(instructions,edges,A,{},calls,stack_aliases=True,
                local_alias_slot_policy=profile.slots.SELECTOR,
                formal_stack_callee_proof=self.components(values))

    def test_effect_partial_write_taints_overlapping_pointer_word(self):
        sequence = HEAD+[0xAC02,0x9403]+ARGUMENTS+['leaf',0x9803,0x7800]+TAIL
        with self.assertRaisesRegex(ValueError, 'ambiguous or expired'):
            self.frame(sequence)

    def test_forged_descriptor_effect_and_marked_site_rejected(self):
        values = fixture(); proof = self.components(values)
        calls = dict(values['calls']); marked = next(iter(proof.sites))
        changed = dict(calls); changed[marked] = N
        with self.assertRaisesRegex(ValueError, 'descriptor'): proof.validate_calls(changed)
        proof._record['effects']['writes'] = []
        with self.assertRaisesRegex(ValueError, 'descriptor'): proof.validate_calls(calls)
        proof = self.components(values); proof.sites[marked+2] = proof.sites.pop(marked)
        with self.assertRaisesRegex(ValueError, 'descriptor'): proof.validate_calls(calls)
        with self.assertRaisesRegex(ValueError, 'exclusive fresh native'):
            profile.frame.prove_frame({}, {}, A, {}, {}, stack_aliases=True,
                local_alias_slot_policy=profile.slots.SELECTOR,formal_stack_callee_proof={'complete':True})

    def test_forged_saved_slot_and_outgoing_overlap_descriptor_state(self):
        proof = self.components(); site = next(iter(proof.sites))
        stack = [('local',None)]*5+[('saved',None)]*4
        aliases = {ARM_REG_R3:frozenset(((-24,True),))}
        pointer_slots = {-36:frozenset(((-22,True),)), -32:frozenset(((-20,True),))}
        writes = proof.check_call(site,L,aliases,stack,pointer_slots)
        self.assertEqual(writes,[(-24,2),(-22,2),(-20,2)])
        for bad in ({-36:frozenset(((-14,True),)),-32:pointer_slots[-32]},
                {-36:frozenset(((-35,True),)),-32:pointer_slots[-32]}):
            with self.assertRaises(ValueError): proof.check_call(site,L,aliases,stack,bad)


if __name__ == '__main__':
    unittest.main()
