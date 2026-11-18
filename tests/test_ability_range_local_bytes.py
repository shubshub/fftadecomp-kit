"""Native positive and adversarial evidence for the two private ability range outputs."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import ability_range_local_bytes as ability
import match
import match_evidence
import owner_admission_profile as owner


@unittest.skipUnless(os.getenv('FFTA_ABILITY_RANGE_ROOT'), 'requires the indexed USA ROM and native source fixture')
class AbilityRangeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_ABILITY_RANGE_ROOT']).resolve()
        cls.rom = (cls.root/'baserom.bin').read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.body = cls.rom[ability.ROOT-match.ROM_BASE:ability.ROOT-match.ROM_BASE+158]
        cls.report = (cls.root/'docs/match/080CD2C4.md').read_text()
        cls.manifest = json.loads(next(line.split('`')[1] for line in cls.report.splitlines()
                                      if line.startswith('* owner runtime evidence:')))['manifest']
        cls.refine = owner.refine(cls.body, ability.ROOT, cls.mapping)
        cls.ins, cls.edges, _, cls.calls, _ = ability.graph.graph(cls.body, ability.ROOT, cls.refine)

    def test_native_exact_and_replay(self):
        self.assertIn('158/158 bytes', self.report)
        self.assertEqual(len(self.ins), 74)
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), ability.ROOT))
        for field in ('"returning_ids":252', '"maximum_iterations":92', '"last_store":[', '"kills_before_read_or_return":{'):
            forged = self.report.replace(field, field.replace(':', '_tampered:'))
            self.assertNotEqual(forged, self.report)
            self.assertFalse(match_evidence.report_matches(forged, str(self.root), ability.ROOT))

    def test_real_ranges_and_no_wrap(self):
        evidence = ability.resolve_ranges(self.rom)
        self.assertEqual(evidence['returning_ids'], 252)
        self.assertEqual(evidence['repeating_redirect_ids'], [80, 81, 82, 85])
        self.assertEqual((evidence['maximum_last'], evidence['maximum_iterations']), (222, 92))
        mutated = bytearray(self.rom)
        base = ability.RECORDS-match.ROM_BASE
        mutated[base+5] = 0
        mutated[base+47] = 255
        with self.assertRaisesRegex(ValueError, 'wraparound'):
            ability.resolve_ranges(mutated)
        mutated[base+47] = 254
        mutated[base+46] = 0
        self.assertEqual(ability.resolve_ranges(mutated)['maximum_iterations'], 255)
        mutated[base+5] = 255
        self.assertIn(0, ability.resolve_ranges(mutated)['repeating_redirect_ids'])

    def test_original_stores_forwarded_last_and_multiple_exits(self):
        frame = ability.scan_frame(self.ins, self.edges)
        self.assertEqual(frame['first_store'], [0x080CD2FE, -32])
        self.assertEqual(frame['last_store'], [0x080CD302, -31])
        self.assertEqual(frame['kills_before_read_or_return'], dict(
            r1=[0x080CD32A, 0x080CD35E], r8=[0x080CD314, 0x080CD358], r9=[0x080CD35A]))
        for site in (0x080CD2DA, 0x080CD2E2, 0x080CD2F2, 0x080CD2FC, 0x080CD2FE,
                     0x080CD300, 0x080CD302, 0x080CD30E, 0x080CD310, 0x080CD316,
                     0x080CD34E, 0x080CD350, 0x080CD356, 0x080CD358, 0x080CD35E):
            ins = dict(self.ins)
            ins[site] = self.ins[0x080CD33E]  # movs r0, #0
            with self.subTest(site=site), self.assertRaises(ValueError):
                ability.scan_frame(ins, self.edges)

    def test_alias_may_cross_neutral_backedge_but_never_a_read_or_exit(self):
        start, r1 = 0x080CD310, match.ARM_REG_R1
        self.assertEqual(ability.observed_lifetime(self.ins, self.edges, start, r1), [0x080CD32A, 0x080CD35E])
        for target in (0x080CD336, 0x080CD360, 0x080CD2F4):  # AND, BX r1, ordinary BL
            edges = dict(self.edges)
            edges[0x080CD350] = (0x080CD318, target)
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, 'observed'):
                ability.observed_lifetime(self.ins, edges, start, r1)
        edges = dict(self.edges)
        edges[0x080CD348] = ()
        with self.assertRaisesRegex(ValueError, 'lives at an exit'):
            ability.observed_lifetime(self.ins, edges, start, r1)

    def test_callee_ambient_alias_dispatch_redirect_and_field(self):
        class ChangedQuery(ability.named.NamedDataBufferProof):
            def inspect(self, address, data):
                instructions, transfers = super().inspect(address, data)
                # Decode operands and read/write sets, as the real inspected CFG does.
                decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
                decoder.detail = True
                replacement = next(decoder.disasm(self.change, self.site))
                return [replacement if i.address == self.site else i for i in instructions], transfers

        for pc, change in ((0x080C857E, b'\xc0\x46'), (0x080C8978, b'\x2e\x30'),
                           (0x080C895E, b'\x00\x28'), (0x080C8A06, b'\x80\x18'),
                           (0x080C8A1E, b'\x60\xbc'), (0x080C8588, b'\x40\x46')):
            query = ChangedQuery(self.rom, self.mapping, self.index, self.objects)
            query.site, query.change = pc, change
            with self.subTest(site=pc), self.assertRaises(ValueError):
                ability.query(query)

    def test_typed_bindings_and_instruction_metadata(self):
        bindings = self.manifest['bindings']
        cases = []
        for key, changed in [('calls', [[32, 'func_080C8570']]), ('data', [[128, 'g_table_0851BA84', 1]])]:
            cases.append((dict(bindings, **{key: changed}), self.mapping, self.index))
        mapping = json.loads(self.mapping)
        next(row for row in mapping if int(row['rom'], 16) == ability.ROOT)['instrs'] = 79
        changed_index = self.index.replace(b'080CD362   158  74', b'080CD362   158  79')
        self.assertNotEqual(changed_index, self.index)
        cases.append((bindings, json.dumps(mapping).encode(), changed_index))
        for binding, mapping, index in cases:
            with self.subTest(binding=binding, bad_index=index != self.index), self.assertRaises(ValueError):
                ability.prove(self.body, ability.ROOT, self.rom, mapping, index, self.objects, binding,
                              self.ins, self.edges, self.calls, self.refine)

    def test_default_policy_isolated(self):
        for profile in (None, 'named-data-buffer-v1'):
            cmd = [sys.executable, str(Path(match.__file__)), '--root', str(self.root), '--no-write']
            if profile:
                cmd.extend(['--owner-runtime-profile', profile])
            check = subprocess.run(cmd + ['080CD2C4'], capture_output=True, text=True)
            self.assertNotEqual(check.returncode, 0)
            self.assertIn('inspected buffer call', check.stdout+check.stderr)


if __name__ == '__main__':
    unittest.main()
