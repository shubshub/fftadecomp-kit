"""Engine-track switch proof. Set FFTA_M4A_TEST_ROOT to replay a local game and its report."""
import copy
import json
import os
from pathlib import Path
import sys
import unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import library_units as units
import m4a_track_switch as music
import match
import match_evidence as evidence
import rebuild
import switch_data_thunks as thunks


def fixed_args():
    return SimpleNamespace(cc=match.DEFAULT_CC, flags=match.DEFAULT_FLAGS, cpp=match.DEFAULT_CPP,
                           assembler=match.DEFAULT_AS, linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY,
                           mode='thumb', control_flow_profile='ordinary', unit_toolchain=music.TOOLCHAIN,
                           switch_data_profile=music.SELECTOR)


class SelectionTests(unittest.TestCase):
    def setUp(self):
        start, end, digest = music.UNIT
        self.unit = SimpleNamespace(start=start, end=end, toolchain=music.TOOLCHAIN, proof=0x08146264,
            row={'identity': [{'address': f'0x{start:08X}', 'size': end-start, 'sha256': digest}]})

    def test_only_exact_unit_owner_and_no_orphan(self):
        self.assertIn(music.SCHEMA, units.schemas(self.unit, music.ADDRESS))
        for unit, address, orphan in ((None, music.ADDRESS, None), (self.unit, music.ADDRESS + 2, None),
                                     (self.unit, music.ADDRESS, '{}')):
            self.assertNotIn(music.SCHEMA, units.schemas(unit, address, orphan))
        for key, change in (('proof', music.ADDRESS), ('toolchain', 'agbcc-O1-v1'), ('row', {'identity': []})):
            different = copy.copy(self.unit)
            setattr(different, key, change)
            self.assertNotIn(music.SCHEMA, units.schemas(different, music.ADDRESS))

    def test_all_foreign_selectors_and_overrides_rejected(self):
        args = fixed_args()
        with patch.object(units, 'load', return_value=[self.unit]), \
                patch.object(match, 'function_span', return_value=music.END - music.ADDRESS):
            for key in ('signed_quotient_profile', 'unsigned_quotient_profile', 'signed_runtime_profile',
                        'unsigned_runtime_profile', 'addressed_signed_runtime_profile', 'software_double_profile',
                        'software_double_remainder_profile', 'function_address_profile', 'switch_profile',
                        'owner_runtime_profile', 'palette_closure_bundle', 'flags', 'cc', 'assembler',
                        'objcopy', 'linker', 'cpp', 'mode', 'control_flow_profile', 'wsl', 'wsl_path',
                        'unit_toolchain'):
                bad = copy.copy(args)
                setattr(bad, key, 'other')
                with self.subTest(key=key), self.assertRaises(ValueError):
                    units.gate('.', music.ADDRESS, bad)
            for wrong in ('switch-thunks-v1', 'switch-thunks-frame-v1', 'u16-scalars-v1'):
                bad = copy.copy(args)
                bad.switch_data_profile = wrong
                with self.assertRaises(ValueError):
                    units.gate('.', music.ADDRESS, bad)
            args.unit_toolchain = None
            with self.assertRaises(ValueError):
                units.gate('.', music.ADDRESS, args)

    def test_track_marker_requires_an_isolated_unframed_thunk(self):
        plain = {'thunk_policy': thunks.POLICY}
        self.assertEqual(thunks.selector_for_manifest(plain), 'switch-thunks-v1')
        track = dict(plain, engine_tracks={})
        self.assertEqual(thunks.selector_for_manifest(track), music.SELECTOR)
        for key in ('stack_policy', 'pool_policy', 'scalar_policy'):
            with self.assertRaises(ValueError):
                thunks.selector_for_manifest(dict(track, **{key: 'other'}))


@unittest.skipUnless(os.environ.get('FFTA_M4A_TEST_ROOT'), 'local game ROM and issued report required')
class GameTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ['FFTA_M4A_TEST_ROOT']).resolve()
        cls.rom = (cls.root / 'baserom.bin').read_bytes()
        cls.body = cls.rom[music.ADDRESS - music.ROM_BASE:music.END - music.ROM_BASE]
        cls.mapping = evidence.mapping_snapshot(cls.root)
        cls.objects = evidence.data_snapshot(cls.root)
        cls.report = (cls.root / 'docs/match/0814636C.md').read_text()
        line = next(line for line in cls.report.splitlines() if line.startswith('* switch manifest:'))
        cls.manifest = json.loads(line.split('`')[1])

    def test_real_compiler_replay_and_rebuild_arguments(self):
        self.assertEqual(rebuild.saved_profile_arguments(self.report, str(self.root), music.ADDRESS),
                         ['--switch-data-profile', music.SELECTOR, '--unit-toolchain', music.TOOLCHAIN])

    def test_rom_registration_and_caller_dependency_mutations(self):
        for start in [row[0] for row in music.DEPENDENCIES] + [0x0814BB28, music.ADDRESS]:
            damaged = bytearray(self.rom)
            damaged[start - music.ROM_BASE] ^= 1
            with self.subTest(start=hex(start)), self.assertRaises(ValueError):
                music.entry_contract(bytes(damaged), music.ADDRESS, self.body)

    def test_literal_thunk_and_track_substitutions_fail_closed(self):
        for mutation in ('track', 'remove', 'thunk', 'slot', 'addend', 'float', 'summary'):
            bad = copy.deepcopy(self.manifest)
            if mutation == 'track':
                bad['engine_tracks']['registrations'][0][1] = music.CALLBACK - 64
            elif mutation == 'remove':
                del bad['engine_tracks']
            elif mutation == 'thunk':
                bad['thunks'][0][1] = '_call_via_r3'
            elif mutation == 'slot':
                bad['data'][0][1] = 'other'
            elif mutation == 'addend':
                bad['data'][0][2] = 0
            elif mutation == 'float':
                bad['engine_tracks']['registrations'][1][2] = 6.0
            else:
                bad['engine_tracks']['entry_r1'] = 'any external pointer'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                match.verify_switches(self.body, music.ADDRESS, self.rom, self.mapping, bad, data_mapping=self.objects)

    def test_saved_metadata_cannot_drop_premise_or_compiler(self):
        for old, new in ((music.SCHEMA, thunks.SCHEMAS['switch-thunks-v1']), (music.SUMMARY, 'arbitrary tracks'),
                         (units.COMPILER_LINE, '* changed digest: '), (units.UNIT_LINE, '* changed unit: ')):
            altered = self.report.replace(old, new)
            self.assertNotEqual(altered, self.report)
            self.assertFalse(evidence.report_matches(altered, str(self.root), music.ADDRESS))
        # A current source hash and a signed structural manifest alone cannot establish a source match.
        with patch.object(music, 'replay', return_value=False):
            self.assertFalse(evidence.report_matches(self.report, str(self.root), music.ADDRESS))


if __name__ == '__main__':
    unittest.main()
