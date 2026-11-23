"""Numeric hardware literals retain exact ELF bytes without fictitious symbols."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import test_bios_scalar_function_literals as fixtures

profile, match, A = fixtures.profile, fixtures.match, fixtures.A


class BiosNumericMmioLiteralTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.BiosScalarFunctionLiteralTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, value=0x04000134):
        f = self.base.fixture()
        body = bytearray(f['data'])
        offset = f['data_bindings'][-1][0]
        struct.pack_into('<I', body, offset, value)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        f.update(data=bytes(body), rom=bytes(rom),
                 data_bindings=f['data_bindings'][:-1],
                 selector=profile.BIOS_SCALAR_MMIO_DATA_SELECTOR)
        return f

    def test_numeric_words_keep_scalar_and_object_roles_separate(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        words = manifest['numeric_mmio_literals']['words']
        self.assertEqual(words, [[len(f['data'])-4, 0x04000134, [6]]])
        self.assertEqual(manifest['data_bindings'], f['data_bindings'])
        self.assertTrue(manifest['bios_scalar_control']['words'])
        self.assertIn('hardware access validity', manifest['numeric_mmio_literals']['contract'])
        self.assertEqual(manifest['runtime_numeric_return_facts'], [])
        self.assertFalse(manifest['arithmetic_C_equivalence'])

    def test_old_selectors_ram_odd_and_outside_window_are_not_mmio(self):
        f = self.fixture()
        # The 32-bit fill control needs a type where controls are not computed.
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR))
        # Outside the numeric-MMIO selectors the I/O word is a numeric hardware word.
        manifest, _ = profile.verify(**dict(f, selector=profile.BIOS_SCALAR_DATA_SELECTOR))
        self.assertNotIn('numeric_mmio_literals', manifest)
        self.assertEqual(manifest['numeric_hardware_words']['words'], [[len(f['data'])-4, 0x04000134, [6]]])
        for value in (0x03000134, 0x04000135, 0x03FFFFFE, 0x04000400, 0x05000010):
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.verify(**self.fixture(value))
        for value in (0x04000000, 0x0400012A, 0x040003FE):
            with self.subTest(value=value):
                self.assertEqual(profile.verify(**self.fixture(value))[0]
                    ['numeric_mmio_literals']['words'][0][1], value)

    def test_fabricated_object_and_missing_or_forged_roles_refuse(self):
        f = self.fixture()
        offset = len(f['data'])-4
        objects = json.loads(f['data_mapping'])
        objects['fake_mmio'] = '0x04000134'
        with self.assertRaisesRegex(ValueError, 'also be a typed object'):
            profile.verify(**dict(f, data_mapping=json.dumps(objects).encode(),
                data_bindings=f['data_bindings']+[[offset, 'fake_mmio', 0]]))
        with self.assertRaisesRegex(ValueError, 'actual reached MMIO'):
            profile.verify(**dict(self.base.base.fixture(data=True, control=0x05000010),
                selector=f['selector']))
        manifest, _ = profile.verify(**f)
        forged = copy.deepcopy(manifest)
        forged['numeric_mmio_literals']['words'][0][1] += 2
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=forged)

    def test_original_elf_has_no_mmio_symbol_or_relocation_and_link_cannot_change_word(self):
        f = self.fixture()
        helper = self.base.base.base
        original = helper.data_image(f)
        linked = helper.linked_data_image(f, original)
        records = {}
        calls, _, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            selector=f['selector'], data_mapping=f['data_mapping'], data_relocations=records)
        offset = len(f['data'])-4
        self.assertNotIn(offset, records)
        self.assertNotIn(0x04000134, targets.values())
        self.assertEqual(struct.unpack_from('<I', original['text'], offset)[0], 0x04000134)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records), f['data'])
        bad = copy.deepcopy(linked)
        text = bytearray(bad['text'])
        struct.pack_into('<I', text, offset, 0x04000136)
        bad['text'] = bytes(text)
        with self.assertRaisesRegex(ValueError, 'outside call relocations'):
            profile.linked_bytes(original, bad, A, calls, targets, data_relocations=records)

    def test_cli_and_report_authenticate_source_runtime_producer_and_literal_policy(self):
        f = self.fixture()
        helper = self.base.base.base
        with helper.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fixtures.functions.fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'Literal identity only', 'forged identity'), root, A))
            with patch.object(profile, 'runtime_fingerprint', return_value={'changed': True}):
                self.assertFalse(evidence.report_matches(report, root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'addressed_signed_runtime_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
