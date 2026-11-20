"""Regression tests for the USA party-effect scheduler and map-query return lifetime."""
import copy
import json
import os
from pathlib import Path
import struct
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import party_effect_scheduler as party


def straight(words, base=0x08010000):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoder.detail = True
    body = struct.pack('<'+'H'*len(words), *words)
    ins = {i.address:i for i in decoder.disasm(body, base)}
    edges = {pc:(pc+i.size,) if pc+i.size in ins else () for pc,i in ins.items()}
    return ins, edges, base


class ScratchTests(unittest.TestCase):
    def test_actual_entry_overwrite_must_precede_observation(self):
        ins, edges, base = straight([0x0600,0x7a1a,0x4770])
        self.assertEqual(party.entry_kill(ins, edges, {}, base), [base,base+2])
        for words in ([0x1c10,0x7a1a,0x4770], [0x0600,0x1c02,0x4770]):
            ins, edges, base = straight(words)
            with self.assertRaises(ValueError):
                party.entry_kill(ins, edges, {}, base)

    def test_every_outgoing_path_checks_reads_calls_and_returns(self):
        ins, edges, base = straight([0x2800,0xd000,0x2200,0x2200,0x4770])
        edges[base+2] = (base+4,base+6)
        self.assertEqual(party.consumer(ins, edges, {}, base, {})['overwrites'],
                         [(base+4,base+4),(base+6,base+6)])
        for words in ([0x2800,0xd000,0x2200,0x1c10,0x4770],
                      [0x2800,0xd000,0x2200,0x4770,0x4770]):
            ins, edges, base = straight(words)
            edges[base+2] = (base+4,base+6)
            with self.assertRaises(ValueError):
                party.consumer(ins,edges,{},base,{})
        ins, edges, base = straight([0xf000,0xf800,0x4770])
        with self.assertRaises(ValueError):
            party.consumer(ins,edges,{base:0x08003300},base,{})

    def test_native_frame_refuses_unknown_sp_materialization_or_unbalanced_leave(self):
        for words in ([0x4668,0x4770],[0xb081,0x4770]):
            ins, edges, base = straight(words)
            with self.assertRaises(ValueError):
                party.member_frame(base,ins,edges,{})

    def test_unrelated_owner_is_rejected(self):
        with self.assertRaises(ValueError):
            party.bind(None, bytes(1366), party.OWNER, {}, {}, {})


@unittest.skipUnless(os.getenv('FFTA_PARTY_EFFECT_ROOT'), 'requires indexed FFTA USA fixture')
class NativePartyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import inert_spin_profile
        import match_evidence as evidence
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        cls.root = Path(os.environ['FFTA_PARTY_EFFECT_ROOT']).resolve()
        cls.rom = Path(evidence.report_rom_path(cls.root)).read_bytes()
        cls.mapping = evidence.mapping_snapshot(cls.root)
        index = inert_spin_profile.index_snapshot(cls.root)
        cls.proof = party.named.NamedDataBufferProof(cls.rom, cls.mapping, index, evidence.data_snapshot(cls.root))
        cls.body = cls.proof.span(party.OWNER)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.body, party.OWNER,
                                                         owner.refine(cls.body, party.OWNER, cls.mapping))
        line = next(line for line in (cls.root/'docs/match/08104AEC.md').read_text().splitlines()
                    if line.startswith('* owner runtime evidence:'))
        cls.evidence = json.loads(line.split('`')[1])
        cls.bindings = cls.evidence['manifest']['bindings']
        cls.contract = cls.evidence['manifest']['proof']['buffers']['conditional_local_calls']

    def test_outcome_includes_four_query_consumers_and_five_live_descriptors(self):
        self.assertEqual((self.evidence['bytes'],self.evidence['instructions']), (1366,629))
        data = self.contract['party_effect']
        self.assertEqual(data['child_tasks']['timers'], [1,31,61,91,121])
        self.assertEqual(data['child_tasks']['descriptor_halfword_reads'], [0,20,22])
        self.assertEqual(data['child_tasks']['payload_writes'], [[7,1],[6,1],[4,2]])
        self.assertFalse(data['child_tasks']['callback_retains_descriptor'])
        self.assertEqual(data['map_query']['callee']['observations'], [[136,2,-35]])
        self.assertEqual({int(s) for s in data['map_query']['continuations']}, party.QUERIES)
        member = data['member_footprint']
        self.assertEqual(len(member['checked_owners']), 75)
        self.assertEqual(len(member['native_derived_SP']), 18)
        self.assertEqual(len(member['indirect_sites']), 7)
        self.assertTrue(all(row[3] is None or row[3] <= 0 for row in member['checked_owners']))

    def test_wrong_callback_member_or_bound_is_refused(self):
        cb = self.proof.span(party.CALLBACK)
        real_span = self.proof.span
        altered = bytearray(cb)
        altered[0x08104976-party.CALLBACK] ^= 0x40
        with patch.object(self.proof, 'span', side_effect=lambda a:bytes(altered) if a == party.CALLBACK else real_span(a)):
            with self.assertRaises(ValueError):
                party.children(self.proof, self.body, self.edges)
        root = bytearray(self.body)
        root[0x08104F1A-party.OWNER] = 5
        with self.assertRaises(ValueError):
            party.children(self.proof, root, self.edges)
        bypass = dict(self.edges)
        bypass[party.OWNER] = (party.REGISTER,)
        with self.assertRaises(ValueError):
            party.children(self.proof,self.body,bypass)

    def test_an_alias_in_the_real_descriptor_is_rejected(self):
        r = match.ARM_REG_R0
        aliases = {r+2:-100,r+5:-100,r+6:-62,r+7:-72,r+9:-64,r+10:-68}
        slots = {-124:-64,-120:-62,-44:-100,-36:-70}
        stack = [(False,False,True)]*23+[(False,True,False)]*8
        context = SimpleNamespace(access=self.proof.access, observations={},
            scheduler_call_sites=self.contract['call_sites'])
        party.register(context,aliases,stack,slots,party.REGISTER)
        with self.assertRaises(ValueError):
            party.register(context,aliases,stack,{**slots,-80:-62},party.REGISTER)
        with self.assertRaises(ValueError):
            party.register(context,{**aliases,r+1:-62},stack,slots,party.REGISTER)

    def test_callback_function_and_four_script_bindings_are_typed(self):
        party.check_bindings(self.bindings)
        for role in ('functions','data'):
            changed = copy.deepcopy(self.bindings)
            changed[role][0][1] = 'data_0839F75C'
            with self.assertRaises(ValueError):
                party.check_bindings(changed)

    def test_nested_position_selection_rejects_a_different_scene_script(self):
        altered = bytearray(self.body)
        altered[0x08104D28-party.OWNER] ^= 4
        with self.assertRaises(ValueError):
            party.scene_position(self.proof,altered)
