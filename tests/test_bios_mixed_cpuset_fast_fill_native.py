"""Real agbcc, typed linking, CLI and report replay for CpuSet+CpuFastSet fill."""
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
import bios_cpuset_fill_profile as cpuset
import bios_fast_fill_source_profile as fast
import match
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

A, B = 0x08010000, 0x08011000
SELECTOR = buffers.MIXED_CPUSET_FAST_FILL_SELECTOR
SOURCE = '''extern unsigned short halves[];
extern unsigned int words[];
extern void func_08011000(unsigned int *value);
extern void func_0814186C(const void *source, void *dest, unsigned int control);
extern void func_08141868(const unsigned int *source, unsigned int *dest,
                          unsigned int control);
void func_08010000(void)
{
    unsigned int value = 0;
    func_08011000(&value);
    func_0814186C(&value, halves, 0x01000010);
    value = 0;
    func_08141868(&value, words, 0x01000008);
}
'''


class MixedCpuSetFastFillNativeTests(unittest.TestCase):
    def test_real_compiler_cli_and_report_replay(self):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='mixed_cpuset_fast_fill_',
                                         dir=scratch) as directory:
            root = Path(directory)
            for name in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
                (root / name).mkdir(parents=True, exist_ok=True)
            (root / 'src/08010000.c').write_text(SOURCE)
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            objects = b'{"halves":"0x02000000","words":"0x02000100"}'
            rom = bytearray(cpuset.ADDRESS - match.ROM_BASE + 4)
            rom[fast.ADDRESS-match.ROM_BASE:fast.ADDRESS-match.ROM_BASE+4] = fast.WRAPPER
            rom[cpuset.ADDRESS-match.ROM_BASE:] = cpuset.WRAPPER
            rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = bytes.fromhex('7047')
            runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                                 root=root, timeout=120)
            with runner.workspace() as workspace:
                original, body, image = match.compile_object(runner, workspace, args,
                    root, A, 'src/08010000.c')
                rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=0)
                        for a, n in ((A, len(body)), (B, 2), (fast.ADDRESS, 4),
                                     (cpuset.ADDRESS, 4))]
                mapping = json.dumps(rows).encode()
                data, _ = owner.object_bytes(runner, workspace, args, image, A,
                    bytes(rom), mapping, objects, selector=SELECTOR)
            rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
            rows[1]['instrs'], rows[2]['instrs'], rows[3]['instrs'] = 1, 2, 2
            (root/'config/functions.json').write_text(json.dumps(rows))
            (root/'config/data_symbols.json').write_bytes(objects)
            (root/'symbols/functions.txt').write_text(''.join(
                f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n'
                for r in rows))
            (root/'baserom.bin').write_bytes(rom)
            with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
                result = owner.build(root, A, selector=SELECTOR)
                self.assertEqual(result[8], original)
                report = owner.render(A, result)
                self.assertEqual(owner.selector_for_report(report), SELECTOR)
                self.assertIn(f'* verification: `{buffers.MIXED_CPUSET_FAST_FILL_SCHEMA}`',
                              report.splitlines())
                self.assertTrue(match_evidence.report_matches(report, root, A))
                check = subprocess.run([sys.executable, str(Path(match.__file__)),
                    '--root', str(root), f'0x{A:08X}', '--owner-runtime-profile',
                    SELECTOR], text=True, capture_output=True)
                self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
                self.assertIn('MATCH', check.stdout)
                # The older mixed CpuFastSet selector still refuses this owner.
                check = subprocess.run([sys.executable, str(Path(match.__file__)),
                    '--root', str(root), f'0x{A:08X}', '--no-write',
                    '--owner-runtime-profile', buffers.MIXED_FAST_FILL_SELECTOR],
                    text=True, capture_output=True)
                self.assertNotEqual(check.returncode, 0, check.stdout + check.stderr)
                self.assertIn('buffer callee 0x0814186C: non-leaf calls',
                              check.stdout + check.stderr)
                (root/'src/08010000.c').write_text(SOURCE + '\n')
                self.assertFalse(match_evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
