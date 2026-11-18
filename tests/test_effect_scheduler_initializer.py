"""ROM and frame mutations for the effect scheduler's two local descriptors."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import effect_scheduler_initializer as effect
import match
import match_evidence
import named_data_buffer_profile as named
import owner_admission_profile as owner
import owner_graph_profile as graph
from software_double_profile import indices


@unittest.skipUnless(os.getenv('FFTA_EFFECT_INITIALIZER_ROOT'), 'needs the indexed USA ROM and recovered source')
class EffectSchedulerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_EFFECT_INITIALIZER_ROOT']).resolve()
        cls.rom = (cls.root/'baserom.bin').read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root/'symbols/functions.txt').read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)
        cls.data = cls.rom[effect.OWNER-match.ROM_BASE:effect.OWNER-match.ROM_BASE+408]
        refinement = owner.refine(cls.data, effect.OWNER, cls.mapping)
        cls.ins, cls.edges, _, cls.calls, _ = graph.graph(cls.data, effect.OWNER, refinement)
        cls.report = (cls.root/'docs/match/0810CC44.md').read_text()
        cls.manifest = json.loads(next(l.split('`')[1] for l in cls.report.splitlines()
                                      if l.startswith('* owner runtime evidence:')))['manifest']
        cls.record = cls.manifest['proof']['buffers']['conditional_local_calls']

    def proof(self, *, rom=None):
        return named.NamedDataBufferProof(self.rom if rom is None else rom, self.mapping, self.index, self.objects)

    def test_native_and_saved_replay(self):
        self.assertIn('408/408 bytes', self.report)
        self.assertEqual(len(self.ins), 176)
        self.assertTrue(match_evidence.report_matches(self.report, str(self.root), effect.OWNER))
        for field in ('"one_past_r2_overwrite"', '"initialized_descriptor"', '"getter_while_r5_live"'):
            bad = self.report.replace(field, field.replace('"', '"tampered_', 1))
            self.assertNotEqual(bad, self.report)
            self.assertFalse(match_evidence.report_matches(bad, str(self.root), effect.OWNER))

    def test_real_descriptors_initializer_and_getter(self):
        self.assertEqual(self.record['initialized_descriptor'], [-84, -56])
        self.assertEqual(self.record['second_descriptor'], [-56, -28])
        self.assertEqual(self.record['one_past_r2_overwrite'], 0x0810CCDE)
        self.assertEqual(self.record['post_zero_field_writes'], [[22, 2], [24, 2], [4, 4]])
        self.assertEqual(self.record['second_field_writes'], [[20, 2], [4, 4]])
        zeros = self.record['initializer']['aligned_case']
        self.assertEqual(zeros['writes'], [['stack', -4, 4]] + [['destination', i, 4] for i in range(0, 28, 4)])
        self.assertFalse(self.record['initializer']['installed_identity_proved'])
        self.assertFalse(self.record['actual_callback_effects_proved'])
        for row in self.record['getter_while_r5_live']:
            self.assertIn(row['address'], (0x080DD4A4, 0x080A8810))
            self.assertEqual(row['saved_lr_below_sp'], 4)

    def test_local_bounds_and_receiver(self):
        class Frame:
            def __init__(self):
                self.accesses = []
            def access(self, offset, width, stack):
                self.accesses.append((offset, width))
        r0, r1 = match.ARM_REG_R0, match.ARM_REG_R1
        valid = (effect.INITIALIZE, {r0: -84}, [None]*23, {}, {r1: 28}, {})
        frame = Frame()
        effect.check_call(frame, *valid)
        self.assertEqual(frame.accesses, [(i, 1) for i in range(-84, -56)])
        for index, bad in ((0, effect.FIRST), (1, {r0: -56}), (1, {r0: -84, r1: -84}),
                           (2, [None]*22), (3, {-84: -40}), (4, {r1: 27}), (5, {-84: -40})):
            args = list(valid)
            args[index] = bad
            with self.subTest(index=index, value=bad), self.assertRaises(ValueError):
                effect.check_call(Frame(), *args)

    def test_native_initializer_inputs_effect_calls_and_post_call_kills(self):
        for pc in (0x0810CCBE, 0x0810CCC0, 0x0810CCC2, 0x0810CCC4, 0x0810CCCE,
                   0x0810CCD0, 0x0810CCD4, 0x0810CCDE, 0x0810CD76, 0x0810CD7A,
                   0x0810CD82, 0x0810CD86, 0x0810CD8C):
            ins = dict(self.ins)
            ins[pc] = self.ins[0x0810CDCC]  # movs r0, #0
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                effect.bind(self.proof(), self.data, effect.OWNER, ins, self.edges, self.calls)
        for pc, target in ((effect.INITIALIZE, effect.SCHEDULER), (effect.FIRST, effect.THUNK),
                           (effect.SECOND, 0x08005954)):
            calls = {**self.calls, pc: target}
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                effect.bind(self.proof(), self.data, effect.OWNER, self.ins, self.edges, calls)
        for destination in (effect.FIRST, 0x0810CCDE, effect.SECOND, 0x0810CD86):
            edges = dict(self.edges)
            edges[effect.OWNER] = (destination,)
            with self.subTest(destination=destination), self.assertRaisesRegex(ValueError, 'bypasses'):
                effect.bind(self.proof(), self.data, effect.OWNER, self.ins, edges, self.calls)

    def test_watched_getter_rejects_r5_use_and_store(self):
        entries, rows = indices(self.mapping, self.index)
        for site, instruction in ((0x080DD4A6, b'\x28\x46'), (0x080A8812, b'\x28\x46'),
                                  (0x080A881A, b'\x08\x60')):
            rom = bytearray(self.rom)
            offset = site-match.ROM_BASE
            rom[offset:offset+2] = instruction
            with self.subTest(site=site), self.assertRaises(ValueError):
                effect.getter_footprint(self.proof(rom=bytes(rom)), entries, rows)

    def test_typed_installer_and_child_literals(self):
        bindings = self.manifest['bindings']
        effect.check_bindings(bindings)
        for key, n in (('data', 0), ('data', 1), ('functions', 0), ('functions', 1), ('calls', 1)):
            bad = copy.deepcopy(bindings)
            bad[key].pop(n)
            with self.subTest(key=key, n=n), self.assertRaises(ValueError):
                effect.check_bindings(bad)
        for pc in (0x0810CCF0, 0x0810CCF4, 0x0810CCF8, 0x0810CDB4):
            data = bytearray(self.data)
            data[pc-effect.OWNER] ^= 1
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                effect.bind(self.proof(), bytes(data), effect.OWNER, self.ins, self.edges, self.calls)

    def test_original_profiles_still_refuse_this_shape(self):
        for profile in ('conditional-scheduler-zero-descriptor-v1', 'conditional-scheduler-call-site-summaries-v1'):
            cmd = [sys.executable, str(Path(match.__file__)), '--root', str(self.root), '--no-write',
                   '--owner-runtime-profile', profile, '0810CC44']
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn('verdict MATCH', result.stdout+result.stderr)


if __name__ == '__main__':
    unittest.main()
