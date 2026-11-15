"""Ordinary CpuSet wrapper admission has no local-buffer or memory-effect grant."""
from contextlib import redirect_stdout
import copy
import io
import json
import sys
import unittest
from unittest.mock import patch

import test_bios_cpuset_fill_profile as fill

profile, match, bios, A = fill.profile, fill.match, fill.bios, fill.A


class OrdinaryBiosDataTests(unittest.TestCase):
    def setUp(self):
        self.base = fill.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, prefix=(), source=0x1C18, destination=0x2100):
        f = self.base.fixture(prefix=prefix, source=source, destination=destination, data=True)
        f['selector'] = profile.BIOS_ORDINARY_DATA_SELECTOR
        return f

    def test_external_arguments_use_separate_conditional_ordinary_boundary(self):
        for prefix in ((),(0x2200,),(0x2280,0x0452)):
            f = self.fixture(prefix=prefix)
            manifest, _ = profile.verify(**f)
            self.assertNotIn('native_buffers',manifest)
            self.assertEqual(manifest['bios_ordinary']['dependency'][:2],[bios.ADDRESS,4])
            self.assertIn('no BIOS memory effects',manifest['bios_ordinary']['contract'])
            self.assertEqual(manifest['runtime_numeric_return_facts'],[])
            self.assertIn('bios_cpuset_fill_profile.py',manifest['producer_source_sha256'])
        f = self.fixture()
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,selector=profile.BIOS_DATA_SELECTOR))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,selector=profile.DATA_SELECTOR))

    def test_all_local_argument_aliases_and_frame_corruption_remain_refused(self):
        for f in (self.fixture(source=0x4668),
                  self.fixture(destination=0x4669),
                  self.fixture(prefix=(0x466A,)),
                  self.fixture(prefix=(0x2400,))):
            with self.subTest(data=f['data'].hex()),self.assertRaises(ValueError):
                profile.verify(**f)

    def test_wrapper_indexes_calls_and_original_relocations_are_bound(self):
        f = self.fixture()
        for code in (b'\x0c\xdf\x70\x47',b'\x0b\xdf\x00\x47'):
            bad=dict(f);rom=bytearray(f['rom'])
            rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4]=code
            bad['rom']=bytes(rom)
            with self.subTest(wrapper=code.hex()),self.assertRaises(ValueError):
                profile.verify(**bad)
        for change in ('missing','text','end'):
            bad=dict(f);rows=json.loads(f['mapping'])
            if change=='missing':rows=rows[:-1]
            if change=='end':rows[-1]['end']=f'0x{bios.ADDRESS+2:08X}'
            bad['mapping'],bad['index']=fill.fixtures.fixtures.indexes(rows)
            if change=='text':bad['index']=bad['index'].replace(b'08141870',b'08141872')
            with self.subTest(change=change),self.assertRaises(ValueError):
                profile.verify(**bad)
        original=self.base.base.data_image(f);records={}
        calls,bindings,targets=profile.original_bindings(original,A,f['rom'],f['mapping'],
            data_mapping=f['data_mapping'],data_relocations=records,selector=f['selector'])
        self.assertEqual(calls,f['calls'])
        self.assertEqual(bindings,f['bindings'])
        for name in ('func_08141868','_call_via_r0','func_0814186E'):
            bad=copy.deepcopy(original);bad['symbols'][1]['name']=name
            with self.subTest(name=name),self.assertRaises(ValueError):
                profile.original_bindings(bad,A,f['rom'],f['mapping'],
                    data_mapping=f['data_mapping'],data_relocations={},selector=f['selector'])
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,bindings={}))
        with self.assertRaises(ValueError):
            profile.verify(**dict(f,data_bindings=[]))
        without=self.fixture(prefix=('ordinary',))
        site=next(k for k,v in without['calls'].items() if v==bios.ADDRESS)
        body=bytearray(without['data'])
        body[site-A:site-A+4]=fill.fixtures.fixtures.bl(site,fill.B)
        rom=bytearray(without['rom']);rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)]=body
        without.update(data=bytes(body),rom=bytes(rom),
            calls={k:fill.B for k in without['calls']},bindings={})
        with self.assertRaises(ValueError):
            profile.verify(**without)

    def test_cli_replay_retains_source_rom_producer_runtime_and_manifest_checks(self):
        f=self.fixture()
        boundary=self.base.base.build_boundary
        with boundary(f) as (root,_,_),patch.object(profile,'toolchain_fingerprint',
                return_value=[['synthetic','1'*64]]):
            with patch.object(sys,'argv',['match.py','--root',str(root),
                    '--addressed-runtime-profile',f['selector'],f'{A:08X}']),redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(),0)
            report=(root/'docs/match/08010000.md').read_text()
            evidence=fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report,root,A))
            self.assertFalse(evidence.report_matches(report.replace(
                bios.WRAPPER.hex(),'00000000'),root,A)) if bios.WRAPPER.hex() in report else None
            for relative in ('src/08010000.c','config/functions.json','symbols/functions.txt'):
                path=root/relative;before=path.read_bytes();path.write_bytes(before+b' ')
                try:self.assertFalse(evidence.report_matches(report,root,A))
                finally:path.write_bytes(before)
            with patch.object(profile,'runtime_fingerprint',return_value={'changed':True}):
                self.assertFalse(evidence.report_matches(report,root,A))
            pins=profile.data_producer_fingerprint(f['selector'])
            with patch.object(profile,'data_producer_fingerprint',return_value=dict(
                    pins,**{'bios_cpuset_fill_profile.py':'0'*64})):
                self.assertFalse(evidence.report_matches(report,root,A))
            # The manifest's explicit conditional boundary must replay exactly.
            self.assertFalse(evidence.report_matches(report.replace(
                'no BIOS memory effects','unproved memory effects accepted'),root,A))
            rom=bytearray((root/'baserom.bin').read_bytes());rom[bios.ADDRESS-match.ROM_BASE]^=1
            (root/'baserom.bin').write_bytes(rom)
            self.assertFalse(evidence.report_matches(report,root,A))


if __name__=='__main__':
    unittest.main()
