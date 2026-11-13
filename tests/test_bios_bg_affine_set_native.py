"""Real agbcc, CLI and report replay for a synthetic BgAffineSet caller."""
import argparse
import json
import os
from pathlib import Path
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

A = 0x08010000
SOURCE = '''typedef struct { int x, y; short sx, sy, scx, scy; unsigned short angle; } Source;
typedef struct { short pa, pb, pc, pd; int x, y; } Dest;
extern void func_08141864(const Source *source, Dest *destination, int count);
short func_08010000(short a, short b)
{
    Source source;
    Dest destination;

    source.x = a << 8;
    source.y = b << 8;
    source.sx = a;
    source.sy = b;
    source.scx = 0x100;
    source.scy = 0x100;
    source.angle = 0;
    func_08141864(&source, &destination, 1);
    return destination.pa;
}
'''


class BgAffineSetNativeTests(unittest.TestCase):
    def test_real_compiler_cli_and_report_replay(self):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='bg_affine_', dir=scratch) as directory:
            root = Path(directory)
            for name in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
                (root / name).mkdir(parents=True, exist_ok=True)
            (root / 'src/08010000.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            objects = b'{}'
            rom = bytearray(affine.ADDRESS - match.ROM_BASE + 4)
            rom[affine.ADDRESS-match.ROM_BASE:] = affine.WRAPPER
            runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                                 root=root, timeout=120)
            with runner.workspace() as workspace:
                original, body, image = match.compile_object(runner, workspace, args,
                    root, A, 'src/08010000.c')
                rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=0)
                        for a, n in ((A, len(body)), (affine.ADDRESS, 4))]
                mapping = json.dumps(rows).encode()
                data, _ = owner.object_bytes(runner, workspace, args, image, A,
                    bytes(rom), mapping, objects, selector=buffers.BG_AFFINE_SELECTOR)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
            rows[1]['instrs'] = 2
            (root/'config/functions.json').write_text(json.dumps(rows))
            (root/'config/data_symbols.json').write_bytes(objects)
            (root/'symbols/functions.txt').write_text(''.join(
                f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                for r in rows))
            (root/'baserom.bin').write_bytes(rom)
            with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
                result = owner.build(root, A, selector=buffers.BG_AFFINE_SELECTOR)
                self.assertEqual(result[8], original)
                report = owner.render(A, result)
                self.assertTrue(match_evidence.report_matches(report, root, A))
                check = subprocess.run([sys.executable, str(Path(match.__file__)),
                    '--root', str(root), f'0x{A:08X}', '--owner-runtime-profile',
                    buffers.BG_AFFINE_SELECTOR], text=True, capture_output=True)
                self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
                self.assertIn('MATCH', check.stdout)
                self.assertIn('"bios_bg_affine_set"', report)
                for before, after in (('-44,-24,1]]', '-44,-24,2]]'),
                                      ('-44,-24,1]]', '-44,-20,1]]'),
                                      ('"wrapper_hex":"0edf7047"', '"wrapper_hex":"0bdf7047"')):
                    self.assertIn(before, report)
                    self.assertFalse(match_evidence.report_matches(
                        report.replace(before, after), root, A))
                (root/'src/08010000.c').write_text(SOURCE + '\n')
                self.assertFalse(match_evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
