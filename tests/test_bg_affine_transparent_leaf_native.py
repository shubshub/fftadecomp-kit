"""One native CLI match and one source-bound replay on fresh compiler bytes."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import bios_bg_affine_set_profile as affine
import match
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
from test_bios_bg_affine_set_native import SOURCE as BASE_SOURCE

A, B, C = 0x08010000, 0x08010200, 0x08010300
SOURCE = BASE_SOURCE.replace('short func_08010000(short a, short b)',
    'extern void func_08010200(Dest *destination);\nextern short func_08010300(short *values);\nshort func_08010000(short a, short b, short *values)').replace(
    'return destination.pa;', 'func_08010200(&destination);\n    return func_08010300(values);')
HELPER = bytes.fromhex('031c002018807047')
LEAF = bytes.fromhex('00b500210222805e002800d10121081c02bc0847')


class BgAffineTransparentLeafNativeTests(unittest.TestCase):
    def test_native_cli_and_single_source_bound_replay(self):
        scratch = Path(os.environ['FFTA_TEST_SCRATCH'])
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='bg_affine_transparent_', dir=scratch) as directory:
            root = Path(directory)
            for name in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
                (root/name).mkdir(parents=True, exist_ok=True)
            (root/'src/08010000.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            rom = bytearray(affine.ADDRESS-match.ROM_BASE+4)
            rom[affine.ADDRESS-match.ROM_BASE:] = affine.WRAPPER
            rom[B-match.ROM_BASE:B-match.ROM_BASE+len(HELPER)] = HELPER
            rom[C-match.ROM_BASE:C-match.ROM_BASE+len(LEAF)] = LEAF
            runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                                 root=root, timeout=120)
            with runner.workspace() as workspace:
                original, body, image = match.compile_object(runner, workspace, args,
                    root, A, 'src/08010000.c')
                size = match.function_record(image, f'func_{A:08X}', A, True)[0]['size']
                rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=0)
                    for a,n in ((A,size),(B,len(HELPER)),(C,len(LEAF)),(affine.ADDRESS,4))]
                mapping = json.dumps(rows).encode()
                data, bindings = owner.object_bytes(runner, workspace, args, image, A,
                    bytes(rom), mapping, b'{}', selector=buffers.BG_AFFINE_TRANSPARENT_SELECTOR)
                (root/'original.o').write_bytes(original)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            (root/'config/functions.json').write_bytes(mapping)
            (root/'config/data_symbols.json').write_bytes(b'{}')
            index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} 0 return\n' for r in rows).encode()
            (root/'symbols/functions.txt').write_bytes(index)
            (root/'baserom.bin').write_bytes(rom)
            command = [sys.executable, str(Path(match.__file__)), '--root', str(root),
                f'0x{A:08X}', '--owner-runtime-profile', buffers.BG_AFFINE_TRANSPARENT_SELECTOR]
            try:
                with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
                    result = subprocess.run(command, text=True, capture_output=True)
                    (root/'native-cli.log').write_text(result.stdout+result.stderr)
                    (root/'native-command.json').write_text(json.dumps(command, indent=2))
                    self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
                    self.assertIn('MATCH', result.stdout)
                    report = (root/'docs/match/08010000.md').read_text()
                    self.assertIn('"normal_return_scratch"', report)
                    self.assertIn('"transparent_leaf_calls"', report)
                    self.assertIn(f'* owner runtime: {buffers.BG_AFFINE_TRANSPARENT_SELECTOR}', report)
                    self.assertIn('"toolchain"', report)
                    self.assertIn('"runtime"', report)
                    self.assertIn('"bios_bg_affine_set"', report)
                    self.assertTrue(match_evidence.report_matches(report, root, A))
                    (root/'source-replay.json').write_text(json.dumps(dict(
                        calls=1, result=True, API='match_evidence.report_matches(report, root, A)')))
                    # Malformed report identities reject before any native replay.
                    with patch.object(owner, 'build', side_effect=AssertionError('unexpected replay')) as replay:
                        for bad in (report + f'\n* verification: `{buffers.BG_AFFINE_SCHEMA}`\n',
                                    report.replace('* owner runtime evidence: `', '* stale owner runtime evidence: `')):
                            self.assertFalse(match_evidence.report_matches(bad, root, A))
                        source=root/'src/08010000.c'
                        source.write_text(SOURCE+'\n')
                        self.assertFalse(match_evidence.report_matches(report, root, A))
                        source.write_text(SOURCE)
                        replay.assert_not_called()
                    # Refuse stale/tampered proof receipts through fresh native byte verification.
                    evidence = json.loads(next(line[len('* owner runtime evidence: `'):-1]
                        for line in report.splitlines() if line.startswith('* owner runtime evidence: `')))
                    manifest = evidence['manifest']
                    for field in ('consumer_sha256', 'site', 'callee'):
                        changed = json.loads(json.dumps(manifest))
                        changed['proof']['buffers']['normal_return_scratch']['transparent_leaf_calls']['observations'][0][field] = None
                        with self.assertRaisesRegex(ValueError, 'manifest differs'):
                            owner.verify(data,A,bytes(rom),mapping,index,b'{}',
                                bindings=bindings, manifest=changed, selector=buffers.BG_AFFINE_TRANSPARENT_SELECTOR)
            finally:
                if target := os.environ.get('FFTA_NATIVE_EVIDENCE'):
                    shutil.copytree(root, Path(target)/'native-fixture', dirs_exist_ok=True)


if __name__ == '__main__':
    unittest.main()
