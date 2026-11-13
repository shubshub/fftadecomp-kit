"""Narrow conditional BIOS fill admission keeps native frame and replay gates."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_addressed_unsigned_runtime_profile as fixtures
import bios_cpuset_fill_profile as bios

profile, match, A, B = fixtures.profile, fixtures.match, fixtures.A, fixtures.B


class BiosCpuSetFillTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, prefix=(0x2280, 0x0452), source=0x4668, destination=0x2100,
                data=False, control=None, after=()):
        tokens = [0xB500, 0xB081, *prefix]
        if control is not None:
            tokens.append('literal')
        tokens += after
        tokens += [source, destination, 'bios', 0xB001, 0xBC01, 0x4700]
        body, calls, bindings = bytearray(), {}, {}
        literal_load = None
        for token in tokens:
            if isinstance(token, int):
                body += struct.pack('<H', token)
            elif token == 'literal':
                literal_load = len(body)
                body += b'\0\0'
            else:
                target = bios.ADDRESS if token == 'bios' else B
                site = A + len(body)
                calls[site] = target
                if token == 'bios':
                    bindings[site] = bios.NAME
                body += fixtures.fixtures.bl(site, target)
        if data:
            # A reached external object load, independently typed by ABS32.
            body[4:4] = b'\0\x4b'
            calls = {site+2:target for site,target in calls.items()}
            bindings = {site+2:name for site,name in bindings.items()}
            for site, target in calls.items():
                body[site-A:site-A+4] = fixtures.fixtures.bl(site,target)
            if literal_load is not None:
                literal_load += 2
        if control is not None or data:
            if len(body) % 4:
                body += b'\0\0'
        if control is not None:
            pool = len(body)
            struct.pack_into('<H', body, literal_load,
                0x4A00 | ((pool-((literal_load+4)&~3))//4))
            body += struct.pack('<I', control)
        records = []
        if data:
            pool = len(body)
            struct.pack_into('<H', body, 4, 0x4B00 | ((pool-8)//4))
            body += struct.pack('<I', 0x03000020)
            records = [[pool, 'destination', 0]]
        rows = [
            dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}',
                 mode='thumb', instrs=len(tokens)+int(data)),
            dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1),
            dict(rom=f'0x{bios.ADDRESS:08X}', end=f'0x{bios.ADDRESS+4:08X}',
                 mode='thumb', instrs=2)]
        mapping, index = fixtures.fixtures.indexes(rows)
        rom = bytearray(0x143000)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = b'\x70\x47'
        rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4] = bios.WRAPPER
        result = dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping,
                      index=index, calls=calls, bindings=bindings,
                      selector=profile.BIOS_DATA_SELECTOR if data else profile.BIOS_SELECTOR)
        if data:
            result.update(data_mapping=b'{"destination":"0x03000020"}', data_bindings=records)
        return result

    def test_explicit_fill_accepts_native_modes_and_conservative_unknown_width(self):
        for control, prefix, width in ((0x01000010,(0x2280,0x0452),2),
                                       (None,(0x22A0,0x04D2),4),
                                       (None,(0x2280,0x0452),2)):
            f = self.fixture(control=control,prefix=prefix)
            manifest, _ = profile.verify(**f)
            proof = manifest['native_buffers']['bios_fill']
            self.assertEqual(proof['sites'][0][2], width)
            self.assertEqual(proof['dependency'][:2], [bios.ADDRESS,4])
            self.assertIn('conditional returning', proof['contract'])
            self.assertIn('bios_cpuset_fill_profile.py', manifest['producer_source_sha256'])
            self.assertFalse(manifest['arithmetic_C_equivalence'])
        # R2 is arbitrary; OR with native bit24 still proves fill. Width
        # remains unknown, so the proof requires a whole aligned local word.
        f = self.fixture(prefix=(0x2080, 0x0440, 0x4302))
        proof = profile.verify(**f)[0]['native_buffers']['bios_fill']
        self.assertEqual(proof['sites'][0][2], 4)
        for selector in (profile.BUFFER_SELECTOR, profile.UNSIGNED_BUFFER_SELECTOR, profile.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector))

    def test_mode_joins_calls_unknown_writes_and_literal_bits_fail_closed(self):
        for prefix in ((), (0x2200,), (0x2280,0x0452,'ordinary'),
                       (0x2280,0x0452,0x6812),
                       (0x2B00,0xD001,0x2280,0x0452)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                profile.verify(**self.fixture(prefix=prefix))
        for control in (0, 0x04000010, 0x00FFFFFF):
            with self.subTest(control=control), self.assertRaises(ValueError):
                profile.verify(**self.fixture(control=control))
        # Both arms retain the same fill fact after a real conditional split.
        profile.verify(**self.fixture(prefix=(0x2280,0x0452,0x2B00,0xD000,0x2301)))

    def test_immediate_add_and_subtract_derive_exact_control_words(self):
        # One pooled word, later control words derived by ADDS/SUBS immediate
        # (imm8 and imm3 forms), with exact 32-bit wraparound.
        for control, after, width in ((0x01000001, (0x3202,), 2),          # adds r2,#2
                                      (0x01000001, (0x1C92,), 2),          # adds r2,r2,#2
                                      (0x01000005, (0x3A04,), 2),          # subs r2,#4
                                      (0x01000005, (0x1E52,), 2),          # subs r2,r2,#1
                                      (0x00FFFFFF, (0x3201,), 2),          # carry sets bit24
                                      (0x00000001, (0x3A02,), 4),          # wraps to 0xFFFFFFFF
                                      (0x01000001, (0x1C13, 0x1C5A), 2)):  # r3=r2+0; r2=r3+1
            with self.subTest(control=control, after=after):
                proof = profile.verify(**self.fixture(control=control, after=after)
                                       )[0]['native_buffers']['bios_fill']
                site = proof['sites'][0]
                self.assertEqual(site[2], width)
                expected = bios.exact(control + {0x3202:2, 0x1C92:2, 0x3A04:-4, 0x1E52:-1,
                                                 0x3201:1, 0x3A02:-2, 0x1C5A:1}[after[-1]])
                self.assertEqual(tuple(site[3:]), expected)

    def test_immediate_add_and_subtract_fail_closed(self):
        # Unknown input: bit24 is known from ORRS but the rest is not, so a
        # carry could clear it; the sum must become unknown.
        with self.assertRaises(ValueError):
            profile.verify(**self.fixture(prefix=(0x2080, 0x0440, 0x4302, 0x3201)))
        # The undisturbed literal proves fill; wrap and borrow clear bit24.
        profile.verify(**self.fixture(control=0xFFFFFFFF))
        for control, after in ((0xFFFFFFFF, (0x3202,)),    # adds wraps to 1
                               (0xFFFFFFFF, (0x1C92,)),
                               (0x01000000, (0x3A01,)),    # subs below bit24
                               (0x01000000, (0x1E52,)),
                               (0x01000001, (0x1C5A,))):   # r3 unknown
            with self.subTest(control=control, after=after), self.assertRaises(ValueError):
                profile.verify(**self.fixture(control=control, after=after))
        # Partial facts never pass through a non-zero immediate.
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        from capstone.arm import ARM_REG_R2
        for code in (0x3201, 0x3A01, 0x1C52, 0x1E52):
            item = next(decoder.disasm(struct.pack('<H', code), 0x1000))
            self.assertEqual(bios.transfer(item, {ARM_REG_R2: (1 << 24, 0)}, b'', 0x1000),
                             (ARM_REG_R2, (0, 0)))
            self.assertEqual(bios.transfer(item, {}, b'', 0x1000), (ARM_REG_R2, (0, 0)))

    def test_local_destination_other_aliases_and_source_extent_are_rejected(self):
        for f in (self.fixture(destination=0x4669),
                  self.fixture(source=0x2000,destination=0x4669),
                  self.fixture(source=0xA801),
                  self.fixture(prefix=(0x466B,0x2280,0x0452)),
                  self.fixture(source=0x2000)):
            with self.subTest(data=f['data'].hex()), self.assertRaises(ValueError):
                profile.verify(**f)
        f = self.fixture()
        proof = bios.BiosFillProof(f['data'], A, f['rom'], f['mapping'], f['index'], f['calls'])
        site = next(iter(f['calls']))
        stack = [(False,False,True),(False,True,False)]
        self.assertEqual(proof.check_call(site, {bios.ARM_REG_R0:-6}, stack), {})
        f32 = self.fixture(prefix=(0x22A0,0x04D2))
        wide = bios.BiosFillProof(f32['data'], A, f32['rom'], f32['mapping'], f32['index'], f32['calls'])
        with self.assertRaises(ValueError):
            wide.check_call(next(iter(f32['calls'])), {bios.ARM_REG_R0:-6}, stack)
        with self.assertRaises(ValueError):
            proof.check_call(site, {bios.ARM_REG_R0:-4}, [(False,True,False)])
        with self.assertRaises(ValueError):
            match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, bios_fill_proof=proof)

    def test_wrapper_both_indexes_and_root_calls_are_authenticated(self):
        f = self.fixture()
        for code in (b'\x0c\xdf\x70\x47', b'\x0b\xdf\x00\x47'):
            bad = dict(f)
            rom = bytearray(f['rom'])
            rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4] = code
            bad['rom'] = bytes(rom)
            with self.subTest(wrapper=code.hex()), self.assertRaises(ValueError):
                profile.verify(**bad)
        for change in ('missing','end','text','duplicate'):
            bad = dict(f)
            rows = json.loads(f['mapping'])
            if change == 'missing':
                rows = rows[:-1]
            elif change == 'end':
                rows[-1]['end'] = f'0x{bios.ADDRESS+2:08X}'
            elif change == 'duplicate':
                rows.append(dict(rows[-1]))
            bad['mapping'], bad['index'] = fixtures.fixtures.indexes(rows)
            if change == 'text':
                bad['index'] = bad['index'].replace(b'08141870',b'08141872')
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify(**bad)
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, bindings={}))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(f['data'], A, True, f['calls'],
                addressed_signed_runtime_context=(f['rom'],f['mapping'],f['index'],
                                                  f['bindings'],{},profile.BIOS_SELECTOR),
                buffer_proof=object())

    def test_typed_data_requires_exact_identity_and_pins_new_producer(self):
        f = self.fixture(data=True)
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['data_bindings'], f['data_bindings'])
        self.assertIn('bios_cpuset_fill_profile.py', manifest['producer_source_sha256'])
        for records in ([], [[f['data_bindings'][0][0],'destination',4]]):
            with self.subTest(records=records), self.assertRaises(ValueError):
                profile.verify(**dict(f, data_bindings=records))
        bad = copy.deepcopy(manifest)
        bad['native_buffers']['bios_fill']['sites'][0][2] = 4
        with self.assertRaisesRegex(ValueError,'manifest differs'):
            profile.verify(**f, manifest=bad)

    def test_cli_replay_authenticates_source_runtime_wrapper_and_proof(self):
        f = self.fixture(data=True)
        with self.base.build_boundary(f) as (root, _, _), patch.object(
                profile,'toolchain_fingerprint',return_value=[['synthetic','1'*64]]):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report,root,A))
            self.assertFalse(evidence.report_matches(report.replace(
                '"source span only"','"forged"') if '"source span only"' in report else
                report.replace(bios.SCHEMA, bios.SCHEMA+'-forged'),root,A))
            for relative in ('src/08010000.c','config/functions.json','symbols/functions.txt'):
                path = root/relative
                before = path.read_bytes()
                path.write_bytes(before+b' ')
                try:
                    self.assertFalse(evidence.report_matches(report,root,A))
                finally:
                    path.write_bytes(before)
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            pins = profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile,'data_producer_fingerprint',return_value=dict(
                    pins,**{'bios_cpuset_fill_profile.py':'0'*64})):
                self.assertFalse(evidence.report_matches(report,root,A))
            rom = bytearray((root/'baserom.bin').read_bytes())
            rom[bios.ADDRESS-match.ROM_BASE] ^= 1
            (root/'baserom.bin').write_bytes(rom)
            self.assertFalse(evidence.report_matches(report,root,A))


if __name__ == '__main__':
    unittest.main()
