"""Real agbcc, linking, CLI and report replay for numeric hardware words."""
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
import report_fixtures
import match_evidence
import named_data_buffer_profile as buffers
import owner_admission_profile as owner

A, B = 0x08010000, 0x08011000
FAST_SOURCE = '''extern void func_08011000(unsigned int *value);
extern void func_08141868(const unsigned int *source, unsigned int *dest,
                          unsigned int control);
void func_08010000(void)
{
    unsigned int value = 0;
    func_08011000(&value);
    func_08141868(&value, (unsigned int *)0x%08X, 0x01000008);
}
'''
CPUSET_SOURCE = '''extern unsigned int destination[];
extern void func_0814186C(const unsigned int *source, unsigned int *dest,
                          unsigned int control);
void func_08010000(void)
{
    unsigned int value = 0x66666666;
    destination[0] = 0;
    func_0814186C(&value, (unsigned int *)0x%08X, 0x05000100);
}
'''


class NumericHardwareWordNativeTests(unittest.TestCase):
    def build(self, root, source, selector, wrapper):
        for name in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
            (root / name).mkdir(parents=True, exist_ok=True)
        (root / 'src/08010000.c').write_text(source)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        objects = b'{"destination":"0x02000000"}'
        rom = bytearray(wrapper.ADDRESS - match.ROM_BASE + 4)
        rom[wrapper.ADDRESS-match.ROM_BASE:] = wrapper.WRAPPER
        rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = bytes.fromhex('7047')
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
        with runner.workspace() as workspace:
            original, body, image = match.compile_object(runner, workspace, args, root, A, 'src/08010000.c')
            rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=0)
                    for a, n in ((A, len(body)), (B, 2), (wrapper.ADDRESS, 4))]
            data, _ = owner.object_bytes(runner, workspace, args, image, A, bytes(rom),
                                         json.dumps(rows).encode(), objects, selector=selector)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        rows[0]['instrs'] = owner.refine(data, A, json.dumps(rows).encode())['instrs']
        rows[1]['instrs'], rows[2]['instrs'] = 1, 2
        (root/'config/functions.json').write_text(json.dumps(rows))
        (root/'config/data_symbols.json').write_bytes(objects)
        (root/'symbols/functions.txt').write_text(''.join(
            f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows))
        (root/'baserom.bin').write_bytes(rom)
        return original

    def test_real_compiler_cli_and_report_replay(self):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        for selector, source, wrapper in ((buffers.MIXED_FAST_FILL_SELECTOR, FAST_SOURCE, fast),
                                          (buffers.BIOS_FILL_SELECTOR, CPUSET_SOURCE, cpuset)):
            with self.subTest(selector=selector), \
                    tempfile.TemporaryDirectory(prefix='numeric_hardware_', dir=scratch) as directory:
                root = Path(directory)
                original = self.build(root, source % 0x0600B1E0, selector, wrapper)
                with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
                    result = owner.build(root, A, selector=selector)
                    self.assertEqual(result[8], original)
                    proof = result[1]['proof']
                    [row] = proof['numeric_hardware_words']['words']
                    self.assertEqual(row[1], 0x0600B1E0)
                    if selector == buffers.BIOS_FILL_SELECTOR:
                        self.assertEqual([word[1] for word in proof['bios_scalar_control_words']], [0x05000100])
                    report = owner.render(A, result)
                    self.assertTrue(match_evidence.report_matches(report_fixtures.carried(report, root, A), root, A))
                    text = json.dumps(row, separators=(',', ':'))
                    self.assertIn(text, report)
                    for forged in (text.replace(str(0x0600B1E0), str(0x0600B1E4)),
                                   f'{text},[{row[0]+4},{0x0600B1E0},{json.dumps(row[2])}]'):
                        self.assertFalse(report_fixtures.replay(report.replace(text, forged), root, A))
                    record = json.dumps(dict(numeric_hardware_words=proof['numeric_hardware_words']),
                                        sort_keys=True, separators=(',', ':'))[1:-1] + ','
                    dropped = report.replace(record, '')
                    self.assertNotEqual(dropped, report)
                    self.assertFalse(report_fixtures.replay(dropped, root, A))
                    check = subprocess.run([sys.executable, str(Path(match.__file__)),
                        '--root', str(root), f'0x{A:08X}', '--owner-runtime-profile', selector],
                        text=True, capture_output=True)
                    self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
                    self.assertIn('MATCH', check.stdout)
            with self.subTest(selector=selector, value='RAM'), \
                    tempfile.TemporaryDirectory(prefix='numeric_hardware_', dir=scratch) as directory:
                root = Path(directory)
                self.build(root, source % 0x0200B1E0, selector, wrapper)
                with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')), \
                        self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
                    owner.build(root, A, selector=selector)


if __name__ == '__main__':
    unittest.main()
