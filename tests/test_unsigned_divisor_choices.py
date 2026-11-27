"""Finite nonzero divisor choices composed with exact canonical thunks.

Synthetic tests replace only the separately tested native runtime closure.
The full caller CFG, must-definition joins, thunk identity, saved frame,
manifest binding, and report parser execute unchanged.
"""
import copy
import report_fixtures
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import function_thunk_profile as thunks
import match
import match_evidence as evidence
import owner_admission_profile as owner
import owner_graph_profile as graph
import udiv_constant_choices_inventory as choices
import unsigned_divmod_thunk_inventory as inventory
import unsigned_thunk_profile as profile
import test_unsigned_thunk_frame_source as reports

A, TABLE = 0x08010000, 0x02001100
UDIV, UMOD = inventory.OPERATIONS['__udivsi3'], inventory.OPERATIONS['__umodsi3']
R2 = thunks.ALIASES['_call_via_r2']
TARGETS = {'udiv': UDIV, 'umod': UMOD, 'thunk': R2}
JOIN = (0x2A00, 0xD001, 0x2128, 0xE000, 0x2130)
RETURN = (0xBC10, 0xBC01, 0x4700)


def bl(site, target):
    delta = target-site-4
    return struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7ff), 0xF800 | ((delta >> 1) & 0x7ff))


class UnsignedDivisorChoicesTests(unittest.TestCase):
    report_root = reports.UnsignedThunkFrameSourceTests.report_root

    def setUp(self):
        runtime = patch.object(inventory.divmod, 'runtime_closure', return_value=(
            [['synthetic authenticated native runtime closure']], [['synthetic native runtime frames']]))
        runtime.start()
        self.addCleanup(runtime.stop)
        self.fixture()

    def fixture(self, choice=JOIN, *, before=(), after=(), suffix=RETURN):
        body, calls, loads = bytearray(), {}, []
        sequence = (0xB510, 0x1C04, *before, *choice, *after, 'umod', 0x210A, 'udiv',
                    ('literal', 2, TABLE), 0x6812, 0x1C20, 'thunk', *suffix)
        for value in sequence:
            site = A+len(body)
            if type(value) is tuple:
                loads.append((len(body), value[1], value[2]))
                body += b'\0\0'
            elif value in TARGETS:
                calls[site] = TARGETS[value]
                body += bl(site, TARGETS[value])
            else:
                body += struct.pack('<H', value)
        while len(body) % 4:
            body += b'\0\0'
        literals = {}
        for offset, register, word in loads:
            literals[len(body)] = ('synthetic_table', word)
            struct.pack_into('<H', body, offset, 0x4800 | (register << 8) |
                             ((len(body)-((offset+4) & ~3))//4))
            body += struct.pack('<I', word)
        self.body, self.calls, self.literals = bytes(body), calls, literals
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb', instrs=0),
                dict(rom=f'0x{R2:08X}', end=f'0x{R2+4:08X}', mode='thumb', instrs=2),
                dict(rom=f'0x{UDIV:08X}', end=f'0x{UMOD:08X}', mode='thumb', instrs=60),
                dict(rom=f'0x{UMOD:08X}', end='0x08142BE8', mode='thumb', instrs=95),
                dict(rom='0x0814274C', end='0x0814274E', mode='thumb', instrs=1)]
        rows[0]['instrs'] = owner.refine(self.body, A, json.dumps(rows).encode())['instrs']
        self.mapping = (json.dumps(rows, indent=2)+'\n').encode()
        self.index = ''.join(f'{int(row["rom"],16):08X} {int(row["end"],16):08X} '
                             f'{int(row["end"],16)-int(row["rom"],16)} {row["instrs"]} return\n'
                             for row in rows).encode()
        image = bytearray(0x142BE8)
        image[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        struct.pack_into('<HH', image, R2-match.ROM_BASE, 0x4710, 0x46C0)
        self.rom = bytes(image)
        self.objects = json.dumps({'synthetic_table': f'0x{TABLE:08X}'}).encode()

    def prove(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping,
                      index=self.index, calls=self.calls, selector=profile.CHOICES_SELECTOR)
        values.update(changes)
        return profile.prove(**values)

    def manifest(self):
        proof, instructions = self.prove()
        return thunks.make_manifest(self.calls, {}, self.literals, A, self.rom, self.objects,
                                   instructions, selector=profile.CHOICES_SELECTOR, frame_proof=proof)

    def verify(self, manifest=None):
        return thunks.verify(self.body, A, self.rom, self.mapping, self.index, self.objects,
                             self.manifest() if manifest is None else manifest)

    def test_two_choices_and_singletons_at_both_unsigned_operations(self):
        proof, _ = self.prove()
        self.assertEqual([values for _, values in proof['caller_divisors']], [[40, 48], [10]])
        self.assertEqual(proof['schema'], inventory.CHOICES_SCHEMA)
        self.assertEqual(self.manifest()['divisor_choices'], proof['caller_divisors'])
        self.assertTrue(self.verify())
        for value in (1, 40, 48, 255):
            with self.subTest(value=value):
                self.fixture((0x2100 | value,))
                self.assertEqual(self.manifest()['divisor_choices'][0][1], [value])
                self.verify()

    def test_all_paths_required_for_zero_unknown_and_undefined_joins(self):
        for first in (0x2100, 0x1C11, 0x46C0):
            with self.subTest(first=first):
                self.fixture((0x2A00, 0xD001, first, 0xE000, 0x2130))
                with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
                    self.prove()

    def test_unsupported_writes_and_call_results_kill_facts(self):
        # ADD #0, XOR and a load still write r1; a call also clears r1.
        for after in ((0x3100,), (0x4051,), (0x6801,), ('thunk',)):
            with self.subTest(after=after):
                self.fixture(after=after)
                with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
                    self.prove()
        self.fixture((), before=('umod',))
        with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
            self.prove()

    def test_every_runtime_call_is_checked(self):
        self.fixture(after=('umod',))
        with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
            self.prove()
        self.fixture(after=('umod', 0x2130))
        self.assertEqual([values for _, values in self.manifest()['divisor_choices']], [[40, 48], [48], [10]])

    def test_callee_saved_copies_survive_calls_but_caller_saved_copies_do_not(self):
        for move in (0x1C29, 0x0029):
            with self.subTest(move=move):
                self.fixture((0x2530, 'thunk', move), before=(0xB420,), suffix=(0xBC20, *RETURN))
                self.assertEqual(self.manifest()['divisor_choices'][0][1], [48])
                self.verify()
        # High-register MOVs use an actual high register on ARMv4T. Save and
        # restore r8 through r6, with the original r5/r6 saved on the stack.
        self.fixture((0x2530, 0x46A8, 'thunk', 0x4641), before=(0xB460, 0x4646),
                     suffix=(0x46B0, 0xBC60, *RETURN))
        self.assertEqual(self.manifest()['divisor_choices'][0][1], [48])
        self.verify()
        self.fixture((0x2530, 'thunk', 0x4629), before=(0xB420,), suffix=(0xBC20, *RETURN))
        with self.assertRaisesRegex(ValueError, 'ARMv4T'):
            self.prove()
        self.fixture((0x2330, 'thunk', 0x1C19))
        with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
            self.prove()

    def test_third_value_and_cfg_cycles_refuse(self):
        self.fixture((0x2800, 0xD005, 0x2A00, 0xD001, 0x2128,
                      0xE002, 0x2130, 0xE000, 0x2138))
        with self.assertRaisesRegex(ValueError, 'all-path defined r1 choices'):
            self.prove()
        self.fixture((0x2130, 0x2A00, 0xD1FD))
        with self.assertRaisesRegex(ValueError, 'cycles'):
            self.prove()

    def test_saved_only_frame_and_canonical_thunk_identity_stay_exact(self):
        for before in ((0xB081,), (0x4668,), (0x9900,), (0x9100,)):
            with self.subTest(before=before):
                self.fixture(before=before)
                with self.assertRaises(ValueError):
                    self.prove()
        self.fixture()
        rom = bytearray(self.rom)
        rom[R2-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            self.prove(rom=bytes(rom))
        with self.assertRaises(ValueError):
            self.prove(calls={})
        lines = self.index.decode().splitlines()
        first = lines[0].split()
        first[3] = str(int(first[3])+1)
        lines[0] = ' '.join(first)
        with self.assertRaises(ValueError):
            self.prove(index=('\n'.join(lines)+'\n').encode())

    def test_existing_single_constant_and_fixed_4_8_contracts_stay_unchanged(self):
        for selector in (profile.SELECTOR, profile.FRAME_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'constant in r1'):
                self.prove(selector=selector)
        refinement = owner.refine(self.body, A, self.mapping)
        instructions, edges, _, _, _ = graph.graph(self.body, A, refinement)
        with self.assertRaisesRegex(ValueError, 'within .4,8.'):
            choices.prove_divisor_choices(instructions, edges, A,
                {site: UDIV for site, target in self.calls.items() if target == UMOD})
        with self.assertRaises(ValueError):
            self.prove(selector=None)

    def test_actual_producer_source_is_bound_in_both_manifests(self):
        proof, _ = self.prove()
        for pins in (proof['producer_source_sha256'], self.manifest()['producer_source_sha256']):
            self.assertIn('udiv_constant_choices_inventory.py', pins)
            self.assertEqual(pins['udiv_constant_choices_inventory.py'],
                             inventory.sha(Path(choices.__file__).read_bytes()))
        self.assertNotIn('udiv_constant_choices_inventory.py', profile.producer_sources())

    def test_manifest_rejects_missing_extra_reordered_and_forged_choices(self):
        manifest = self.manifest()
        variants = [[], [[manifest['divisor_choices'][0][0], [48, 40]], *manifest['divisor_choices'][1:]],
                    [[manifest['divisor_choices'][0][0], [40]], *manifest['divisor_choices'][1:]],
                    [[manifest['divisor_choices'][0][0], [0, 48]], *manifest['divisor_choices'][1:]],
                    None, True, {}, '40,48']
        for value in variants:
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.verify({**manifest, 'divisor_choices': value})
        for value in ({key: item for key, item in manifest.items() if key != 'divisor_choices'},
                      {**manifest, 'extra': True}, {**manifest, 'selector': profile.SELECTOR},
                      {**manifest, 'producer_source_sha256': profile.producer_sources()}):
            with self.assertRaises(ValueError):
                self.verify(value)

    def report(self, root, manifest=None, **changes):
        return reports.UnsignedThunkFrameSourceTests.report(self, root, manifest,
            schema=changes.get('schema', profile.CHOICES_SCHEMA),
            selector=changes.get('selector', profile.CHOICES_SELECTOR))

    def test_report_fresh_verification_rejects_wrong_schema_and_malformed_sets(self):
        self.manifest = self.manifest()
        root, rom_path = self.report_root()
        report = self.report(root)
        with patch.object(evidence, 'report_rom_path', return_value=rom_path), \
                patch.object(thunks, 'verify_source', return_value=True):
            self.assertTrue(thunks.report_matches(report, root, A))
            self.assertTrue(evidence.report_matches(report_fixtures.carried(report, root, A), root, A))
            bad_sets = copy.deepcopy(self.manifest)
            bad_sets['divisor_choices'][0][1] = [40]
            for bad in (self.report(root, bad_sets), self.report(root, schema=profile.SCHEMA),
                        self.report(root, selector=profile.SELECTOR),
                        report + f'* function-address thunks: {profile.CHOICES_SELECTOR}\n',
                        report.replace('"divisor_choices":', '"extra":')):
                self.assertFalse(thunks.report_matches(bad, root, A))
            with patch.object(thunks, 'verify_source', side_effect=ValueError('fresh source differs')):
                self.assertFalse(thunks.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
