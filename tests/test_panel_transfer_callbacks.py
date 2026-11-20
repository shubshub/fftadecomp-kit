"""Retain exact scheduler and callback evidence for the phased panel transfer owner."""
import copy
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import panel_transfer_callbacks as panel


class PanelCallbackTests(unittest.TestCase):
    def test_indirect_target_rejects_local_or_return_provenance(self):
        site = min(panel.SITES)
        target = panel.thunk.ALIASES['_call_via_r2']
        proof = SimpleNamespace(calls={site: target}, panel_checked=set())
        panel.check_indirect(proof, site, target, {}, {})
        panel.check_call(proof, site, target, {}, {})
        self.assertEqual(proof.panel_checked, {site})
        alias = {match.ARM_REG_R0: -4}
        with self.assertRaises(ValueError):
            panel.check_indirect(proof, site, target, {}, alias)
        with self.assertRaises(ValueError):
            panel.check_indirect(proof, site, target, alias, {})
        with self.assertRaises(ValueError):
            panel.check_call(proof, site, target, {}, {-4: -8})

    def test_image_rejects_alternate_code(self):
        with self.assertRaises(ValueError):
            panel.image_effects(bytes(176))


@unittest.skipUnless(os.getenv('FFTA_PANEL_TRANSFER_ROOT'), 'requires the indexed USA fixture')
class NativePanelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import inert_spin_profile
        import match_evidence
        import owner_admission_profile as owner
        import owner_graph_profile as graph

        root = Path(os.environ['FFTA_PANEL_TRANSFER_ROOT']).resolve()
        cls.rom = Path(match_evidence.report_rom_path(root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(root)
        cls.index = inert_spin_profile.index_snapshot(root)
        cls.body = cls.rom[panel.OWNER-match.ROM_BASE:panel.OWNER-match.ROM_BASE+1992]
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(
            cls.body, panel.OWNER, owner.refine(cls.body, panel.OWNER, cls.mapping))
        cls.inputs = panel.bits.prove_bits(cls.ins, cls.edges, panel.OWNER, cls.body)
        report = (root / 'docs/match/081295C8.md').read_text()
        line = next(line for line in report.splitlines() if line.startswith('* owner runtime evidence:'))
        cls.evidence = json.loads(line.split('`')[1])
        cls.manifest = cls.evidence['manifest']['proof']['buffers']['conditional_local_calls']
        cls.bindings = cls.evidence['manifest']['bindings']

    def test_conditional_effects_and_scheduler_registration(self):
        self.assertEqual((self.evidence['bytes'], self.evidence['instructions']), (1992, 823))
        contract = self.manifest['panel_callbacks']
        self.assertEqual([row['count'] for row in contract['sites']], [608, 64, 32, 608])
        self.assertEqual(contract['image_effects']['zero']['alignments'], [0, 1, 2, 3])
        self.assertEqual([row['alignment_cases'] for row in contract['image_effects']['copy']], [16, 16])
        self.assertEqual(self.bindings['functions'], [[624, 'func_08129D90']])
        self.assertIn([panel.REGISTER-panel.OWNER, 'func_08121B8C'], self.bindings['calls'])

    def test_native_counter_table_and_entry_are_each_checked(self):
        site = min(panel.SITES)
        spec, count = panel.SITES[site]
        def record(data, rom, count):
            return panel.callback_record(rom, data, panel.OWNER, self.ins, self.edges, self.calls,
                                         site, spec, count, self.inputs)
        row = record(self.body, self.rom, count)
        with self.assertRaises(ValueError):
            record(self.body, self.rom, count-1)
        data = bytearray(self.body)
        data[row['literal_offsets'][0]] ^= 4
        with self.assertRaises(ValueError):
            record(data, self.rom, count)
        rom = bytearray(self.rom)
        rom[spec[2]-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            record(self.body, rom, count)

    def test_typed_bindings_and_complete_callback_coverage(self):
        panel.check_bindings(self.manifest, self.bindings)
        for role, row in (('functions', [624, 'func_08129D90']),
                          ('data', [564, 'g_callbacks_0836D4B8', 0]), ('calls', [486, '_call_via_r2'])):
            with self.subTest(role=role):
                bindings = copy.deepcopy(self.bindings)
                bindings[role].remove(row)
                with self.assertRaises(ValueError):
                    panel.check_bindings(self.manifest, bindings)
        with self.assertRaises(ValueError):
            panel.finish(SimpleNamespace(panel_checked=set(panel.SITES)-{min(panel.SITES)}), {})

    def test_original_graph_thunk_and_scheduler_calls_cannot_be_substituted(self):
        for site in (min(panel.SITES), panel.REGISTER):
            with self.subTest(site=hex(site)):
                calls = dict(self.calls)
                calls[site] = 0x08000000
                with self.assertRaises(ValueError):
                    panel.bind(None, self.body, panel.OWNER, self.ins, self.edges, calls)
