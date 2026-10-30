"""Saved optional MOD selection survives native status/rebuild without widening defaults."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
import test_software_double_target_remainder_profile as fixture

match, profile, BASE = fixture.match, fixture.profile, fixture.BASE
import status
import rebuild


class TargetRemainderLifecycleTests(fixture.SoftwareDoubleTargetRemainderTests):
    def test_native_status_write_verify_and_compiled_rebuild_roundtrip(self):
        self.fixture()
        self.native_report()
        rom = self.root / 'fixture.rom'
        rom.write_bytes(self.rom)
        (self.root / 'README.md').write_text(status.START + '\n' + status.END + '\n')
        environment = dict(os.environ, FFTA_ROM=str(rom), TMPDIR=str(self.root),
                           PYTHONDONTWRITEBYTECODE='1')
        tool = Path(status.__file__).parent
        commands = [
            [sys.executable, str(tool / 'status.py'), '--root', str(self.root),
             '--write', '--verify', '--static-badges'],
            [sys.executable, str(tool / 'rebuild.py'), str(self.root), '--compiled'],
        ]
        results = [subprocess.run(command, env=environment, capture_output=True, text=True,
                                  timeout=120) for command in commands]
        for result in results:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = (self.root / 'docs/match/08000000.md').read_text()
        with patch.dict(os.environ, {'FFTA_ROM':str(rom)}):
            self.assertTrue(profile.target_remainder_selected(report))
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            self.assertEqual(rebuild.saved_profile_arguments(report, self.root, BASE), [
                '--software-double-profile', profile.SELECTOR,
                '--software-double-remainder-profile', profile.REMAINDER_TARGET_SELECTOR])
        self.assertIn(f'compiled bytes     : {len(self.body)}', results[1].stdout)
        self.assertIn('rebuild is byte-exact', results[1].stdout)
        self.assertIn('Functions matched | 1 /', (self.root / 'docs/status.md').read_text())
        print(json.dumps({'native_status_write_verify_exit':results[0].returncode,
                          'native_compiled_rebuild_exit':results[1].returncode,
                          'caller_bytes':len(self.body), 'instructions':len(self.instructions),
                          'report_sha256':hashlib.sha256(report.encode()).hexdigest()}))

    def test_selector_requires_exact_unambiguous_versioned_record(self):
        self.fixture()
        report = self.native_report()
        self.assertTrue(profile.target_remainder_selected(report))
        encoded = profile.manifest_text(self.manifest)
        for kind in ('runtime','abi','semantics','record_runtime','body','count','boolean','site','alias','mixed'):
            manifest = copy.deepcopy(self.manifest)
            if kind in ('runtime','abi','semantics'): manifest[kind] = 'unproved'
            elif kind == 'record_runtime': manifest['target_remainder']['runtime'] = 'unproved'
            elif kind == 'body': manifest['target_remainder']['dependencies'][0][3] = '0'*64
            elif kind == 'count': manifest['target_remainder']['dependencies'][0][2] += 1
            elif kind == 'boolean': manifest['target_remainder']['dependencies'][-1][2] = True
            elif kind == 'site': manifest['target_remainder']['calls'][0] += 2
            elif kind == 'alias':
                next(row for row in manifest['calls'] if row[1] == '__modsi3')[1] = 'func_08142950'
            else: manifest['remainder'] = {}
            changed = report.replace(encoded, profile.manifest_text(manifest))
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.target_remainder_selected(changed)
        line = next(line for line in report.splitlines() if line.startswith('* software double manifest:'))
        malformed = (report + '\n' + line, report.replace(encoded, '{bad'),
                     report.replace(encoded, json.dumps(self.manifest, indent=2)),
                     report.replace(encoded, encoded[:-1] + ',"target_remainder":{}}'))
        for changed in malformed:
            with self.subTest(report=changed[-100:]), self.assertRaises(ValueError):
                profile.target_remainder_selected(changed)
        self.assertFalse(profile.target_remainder_selected('ordinary report'))

    def test_stale_saved_source_or_proof_cannot_forward_or_launch_matcher(self):
        self.fixture()
        report = self.native_report()
        path = self.root / 'docs/match/08000000.md'
        source = self.root / 'src/08000000.c'
        original = source.read_text()
        for kind in ('source','proof'):
            changed = report
            if kind == 'source': source.write_text(original.replace('% denominator','% 7'))
            else:
                line = next(line for line in report.splitlines()
                            if line.startswith('* software double proof SHA-256:'))
                changed = report.replace(line, '* software double proof SHA-256: `' + '0'*64 + '`')
            path.write_text(changed)
            self.assertTrue(profile.target_remainder_selected(changed))
            with self.subTest(kind=kind), patch.object(subprocess, 'run') as invocation:
                with self.assertRaisesRegex(ValueError, 'invalid saved profile report'):
                    rebuild.saved_profile_arguments(changed, self.root, BASE)
                result = status.collect(str(self.root), True, quiet=True, write_reports=True)
                self.assertEqual(result[1], 0)
                self.assertEqual(result[4], ['08000000: invalid saved target-state remainder report'])
                invocation.assert_not_called()
            source.write_text(original)

    def test_no_opt_in_keeps_bounded_default_and_native_dynamic_refusal(self):
        self.fixture()
        report = self.native_report()
        without = copy.deepcopy(self.manifest)
        del without['target_remainder']
        no_opt_in = report.replace(profile.manifest_text(self.manifest), profile.manifest_text(without))
        self.assertFalse(profile.target_remainder_selected(no_opt_in))
        with self.assertRaises(ValueError):
            rebuild.saved_profile_arguments(no_opt_in, self.root, BASE)
        rom = self.root / 'fixture.rom';rom.write_bytes(self.rom)
        environment = dict(os.environ, FFTA_ROM=str(rom), TMPDIR=str(self.root),
                           PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run([sys.executable, str(Path(match.__file__)), '--root', str(self.root),
            '--software-double-profile',profile.SELECTOR,'--no-write','0x08000000'],
            env=environment,capture_output=True,text=True,timeout=120)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('signed16 r0 and nonzero r1',result.stdout+result.stderr)
        bounded = fixture.SOURCE.replace('(int)(value','(short)(int)(value').replace('% denominator','% 7')
        self.fixture(bounded,target=False)
        old = self.native_report(target=False)
        self.assertFalse(profile.target_remainder_selected(old))
        opening,reading = self.patched_rom()
        with opening,reading:
            self.assertEqual(rebuild.saved_profile_arguments(old,self.root,BASE),
                             ['--software-double-profile',profile.SELECTOR])


def load_tests(loader,tests,pattern):
    return unittest.TestSuite(TargetRemainderLifecycleTests(name)
                             for name in sorted(vars(TargetRemainderLifecycleTests))
                             if name.startswith('test_'))


if __name__ == '__main__': unittest.main()
