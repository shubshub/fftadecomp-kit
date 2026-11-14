"""Zero-extended BIOS fill controls: an opt-in bit proof for LDRB/LDRH/MULS."""
from contextlib import redirect_stdout
import copy
import io
import struct
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fixtures
import bios_cpuset_fill_profile as bios

profile, match, A = fixtures.profile, fixtures.match, fixtures.A

NEW = profile.BIOS_ZERO_EXTENDED_DATA_SELECTOR
LDRB_R1_R3 = 0x7819      # ldrb r1,[r3,#0]
LDRB_R0_R3 = 0x7818      # ldrb r0,[r3,#0]
LDRB_R1_R3_1 = 0x7859    # ldrb r1,[r3,#1]
LDRH_R0_R3 = 0x8818      # ldrh r0,[r3,#0]
LDRH_R1_R3 = 0x8819      # ldrh r1,[r3,#0]
LDR_R1_R3 = 0x6819       # ldr r1,[r3,#0]
MULS_R0_R1 = 0x4348      # muls r0,r1,r0
ORRS_R2_R1 = 0x430A      # orrs r2,r1
ORRS_R2_R0 = 0x4302      # orrs r2,r0
FILL_BIT = 0x01000000


class BiosZeroExtendedControlTests(unittest.TestCase):
    def setUp(self):
        self.fixture_case = fixtures.BiosCpuSetFillTests('runTest')
        self.fixture_case.setUp()
        self.addCleanup(self.fixture_case.doCleanups)

    def fixture(self, after, selector=NEW, control=FILL_BIT):
        f = self.fixture_case.fixture(data=True, control=control, after=after)
        f['selector'] = selector
        return f

    def site(self, f):
        return profile.verify(**f)[0]['native_buffers']['bios_fill']['sites'][0]

    def test_byte_control_clears_bit26_and_selects_halfword_source(self):
        f = self.fixture((LDRB_R1_R3, ORRS_R2_R1))
        manifest, _ = profile.verify(**f)
        site = manifest['native_buffers']['bios_fill']['sites'][0]
        self.assertEqual(site[2], 2)
        self.assertEqual(site[3], FILL_BIT)
        self.assertEqual(site[4] & (1 << 26), 1 << 26)
        self.assertEqual(site[4] & 0xFF, 0)       # the low byte is unknown
        self.assertIn('zero-extending', manifest['native_buffers']['bios_fill']['bit_rules'])
        # The older selector keeps the conservative whole-word source unit.
        old = self.site(dict(f, selector=profile.BIOS_DATA_SELECTOR))
        self.assertEqual(old[2], 4)

    def test_older_selectors_do_not_report_new_rules(self):
        f = self.fixture((LDRB_R1_R3, ORRS_R2_R1), selector=profile.BIOS_DATA_SELECTOR)
        manifest, _ = profile.verify(**f)
        self.assertNotIn('bit_rules', manifest['native_buffers']['bios_fill'])

    def test_halfword_control_clears_bit26(self):
        f = self.fixture((LDRH_R1_R3, ORRS_R2_R1))
        site = self.site(f)
        self.assertEqual((site[2], site[4] & 0xFFFF), (2, 0))

    def test_multiply_bounds_the_product_only_when_widths_fit(self):
        # u8*u8 < 2**16 and u16*u8 < 2**24 keep bit 26 clear.
        for loads in ((LDRB_R0_R3, LDRB_R1_R3_1), (LDRH_R0_R3, LDRB_R1_R3_1)):
            f = self.fixture((*loads, MULS_R0_R1, ORRS_R2_R0))
            with self.subTest(loads=loads):
                self.assertEqual(self.site(f)[2], 2)
        # u16*u16 can reach 2**32: no bit above bit 24 is known, so the width stays whole.
        for loads in ((LDRH_R0_R3, LDRH_R1_R3), (LDRB_R0_R3, LDR_R1_R3),
                      (0x6818, LDRB_R1_R3_1)):
            f = self.fixture((*loads, MULS_R0_R1, ORRS_R2_R0))
            with self.subTest(loads=loads):
                self.assertEqual(self.site(f)[2], 4)

    def test_other_loads_and_clobbers_gain_no_facts(self):
        # ldrsb sign-extends, a full word load is unknown, ldrb into the control
        # register itself leaves no fill bit, and a call drops caller-saved facts.
        for after in ((LDR_R1_R3, ORRS_R2_R1),
                      (0x5699, ORRS_R2_R1),            # ldrsb r1,[r3,r2]
                      (0x5E19, ORRS_R2_R1)):           # ldrsh r1,[r3,r0]
            with self.subTest(after=after):
                self.assertEqual(self.site(self.fixture(after))[2], 4)
        with self.assertRaisesRegex(ValueError, 'bit24'):
            profile.verify(**self.fixture((0x781A,)))     # ldrb r2,[r3,#0] replaces the control
        with self.assertRaisesRegex(ValueError, 'bit24'):
            profile.verify(**self.fixture((LDRB_R1_R3, 0x1C0A)))  # adds r2,r1,#0 loses bit24

    def test_zero_known_bits_are_never_widened_by_a_later_write(self):
        # The byte is loaded, then r1 is overwritten before the OR: no bound remains.
        f = self.fixture((LDRB_R1_R3, LDR_R1_R3, ORRS_R2_R1))
        self.assertEqual(self.site(f)[2], 4)

    def test_wide_encodings_and_condition_codes_are_not_decoded(self):
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        from capstone.arm import ARM_REG_R1
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        # ldrb.w r1,[r3]: a four-byte Thumb-2 form is no ARMv4T instruction.
        wide = next(decoder.disasm(bytes.fromhex('93f80010'), 0x1000))
        self.assertEqual(wide.size, 4)
        self.assertIsNone(bios.transfer(wide, {}, b'', 0x1000, True))
        narrow = next(decoder.disasm(struct.pack('<H', LDRB_R1_R3), 0x1000))
        self.assertEqual(bios.transfer(narrow, {}, b'', 0x1000, True),
                         (ARM_REG_R1, (0, 0xFFFFFF00)))
        # Without the opt-in the same encoding introduces nothing.
        self.assertIsNone(bios.transfer(narrow, {}, b'', 0x1000))
        for code in (0xDF00, 0xBE00, 0xDE00):     # svc, bkpt, udf
            item = next(decoder.disasm(struct.pack('<H', code), 0x1000))
            self.assertIsNone(bios.transfer(item, {}, b'', 0x1000, True))

    def test_product_width_arithmetic(self):
        self.assertEqual([bios.known_width(bits) for bits in
                          ((0, bios.MASK), (0, 0xFFFFFF00), (0, 0xFFFF0000), (0, 0), (1, 0))],
                         [0, 8, 16, 32, 32])

    def test_opt_in_is_boolean_and_selector_scoped(self):
        f = self.fixture((LDRB_R1_R3, ORRS_R2_R1))
        with self.assertRaisesRegex(ValueError, 'Boolean'):
            bios.BiosFillProof(f['data'], A, f['rom'], f['mapping'], f['index'], f['calls'],
                               zero_extension=1)
        # The new selector needs typed named data like BIOS_DATA_SELECTOR.
        plain = self.fixture_case.fixture(control=FILL_BIT, after=(LDRB_R1_R3, ORRS_R2_R1))
        with self.assertRaises(ValueError):
            profile.verify(**dict(plain, selector=NEW))

    def test_forged_manifest_and_relabelled_selector_are_refused(self):
        f = self.fixture((LDRB_R1_R3, ORRS_R2_R1))
        manifest, _ = profile.verify(**f)
        forged = copy.deepcopy(manifest)
        forged['native_buffers']['bios_fill']['sites'][0][2] = 4
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=forged)
        # A report made under the new rules cannot be replayed as an older selector.
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR), manifest=manifest)

    def test_native_cli_and_report_replay(self):
        f = self.fixture((LDRB_R1_R3, ORRS_R2_R1))
        with self.fixture_case.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', NEW, f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root / 'docs/match/08010000.md').read_text()
            evidence = fixtures.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertIn(NEW, report)
            # Relabelled to an older selector, or with the rules text forged: refused.
            self.assertFalse(evidence.report_matches(
                report.replace(NEW, profile.BIOS_DATA_SELECTOR), root, A))
            self.assertFalse(evidence.report_matches(
                report.replace('zero-extending-loads', 'forged-loads'), root, A))
            source = root / 'src/08010000.c'
            source.write_bytes(source.read_bytes() + b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
