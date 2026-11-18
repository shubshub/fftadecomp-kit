"""Compile the palette fill through the native ELF path and reject wider effects."""
import argparse
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import addressed_signed_runtime_profile as profile
import bios_cpuset_fill_profile as bios
import match
import match_evidence
import owner_admission_profile as owner
import plausible
import sdk_cpuset_halfword as sdk

HEADER = b'''#ifndef FFTA_H
#define FFTA_H
typedef unsigned char u8;
typedef signed char s8;
typedef unsigned short u16;
typedef signed short s16;
typedef unsigned int u32;
typedef signed int s32;
#endif
'''
SOURCE = '#include "ffta.h"\n' + sdk.BODY


class CpuFill16Tests(unittest.TestCase):
    def test_source_rejects_extra_access_escape_and_interposition(self):
        self.assertEqual(sdk.source_offset(SOURCE, HEADER), SOURCE.index('volatile'))
        for old, new in (
                ('fill = pattern;', 'fill = pattern; fill = 0;'),
                ('fill = pattern;', 'fill = pattern; (void)fill;'),
                ('&fill, destination', '&fill + 1, destination'),
                ('destination, 0x01000010', '&fill, 0x01000010'),
                ('volatile u16', 'volatile u32'),
                ('0x01000010', '0x01000000'),
                ('0x01000010', '0x05000010'),
                ('#include', '#define fill proxy\n#include'),
                ('#include', '#include "other.h"\n#include'),
                ('#include', '// splice\\\n#include'),
                ('extern void', 'extern int dummy; extern void'),
                ('0814186C', '08141868'),
                ('color << 12', 'color < < 12')):
            with self.subTest(change=new):
                self.assertIsNone(sdk.source_offset(SOURCE.replace(old, new), HEADER))
        for old, new in ((b'unsigned short', b'signed short'), (b'#endif', b'#define fill proxy\n#endif'),
                         (b'#endif', b'extern void func_0814186C(void);\n#endif'),
                         (b'#endif', b'#include "hidden.h"\n#endif')):
            with self.subTest(header=new):
                self.assertIsNone(sdk.source_offset(SOURCE, HEADER.replace(old, new)))

    def test_native_cli_replay_and_mutated_effects(self):
        base = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='sdk_halfword_', dir=base) as directory:
            root = Path(directory)
            for name in ('src', 'build', 'include', 'config', 'symbols', 'docs/match'):
                (root / name).mkdir(parents=True, exist_ok=True)
            (root / sdk.SOURCE).write_text(SOURCE)
            (root / sdk.HEADER).write_bytes(HEADER)
            (root / 'config/data_symbols.json').write_text('{}')
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
                assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
                linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
            rom = bytearray(bios.ADDRESS - match.ROM_BASE + len(bios.WRAPPER))
            rom[-len(bios.WRAPPER):] = bios.WRAPPER
            runner = match.Runner(args.cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
            rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=i)
                    for a, n, i in ((sdk.OWNER, sdk.SIZE, 0), (bios.ADDRESS, 4, 2))]
            mapping = json.dumps(rows).encode()
            with runner.workspace() as workspace:
                _, _, image = match.compile_object(runner, workspace, args, root, sdk.OWNER, sdk.SOURCE)
                body, _, _ = profile.object_bytes(runner, workspace, args, image, sdk.OWNER,
                    bytes(rom), mapping, selector=profile.BIOS_SELECTOR)
                _, ordinary, _ = match.compile_object(runner, workspace, args, root, sdk.OWNER,
                    sdk.SOURCE, rewrite=lambda preprocessed: preprocessed.replace('volatile u16 fill', 'u16 fill'))
                self.assertEqual(len(ordinary), 48)
            self.assertEqual(len(body), 52)
            start = sdk.OWNER - match.ROM_BASE
            rom[start:start + len(body)] = body
            rows[0]['instrs'] = owner.refine(body, sdk.OWNER, mapping)['instrs']
            (root / 'config/functions.json').write_text(json.dumps(rows))
            (root / 'symbols/functions.txt').write_text(''.join(
                f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows))
            (root / 'baserom.bin').write_bytes(rom)
            with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
                issued = subprocess.run([sys.executable, match.__file__, '--root', str(root),
                    '--addressed-runtime-profile', profile.BIOS_SELECTOR, f'{sdk.OWNER:08X}'],
                    text=True, capture_output=True, timeout=120)
                self.assertEqual(issued.returncode, 0, issued.stdout + issued.stderr)
                report = (root / 'docs/match/0813FB7C.md').read_text()
                self.assertTrue(match_evidence.report_matches(report, root, sdk.OWNER))
                self.assertFalse(match_evidence.report_matches(
                    report.replace('"local_stores":1', '"local_stores":2'), root, sdk.OWNER))
                other = root / 'src/0813FB78.c'
                other.write_text(SOURCE)
                self.assertTrue(any(row[1] == 'volatile' for row in plausible.check_file(other)))
                (root / sdk.SOURCE).write_text(SOURCE.replace('fill = pattern;', 'fill = pattern; (void)fill;'))
                self.assertTrue(any(row[1] == 'volatile' for row in plausible.check_file(root / sdk.SOURCE)))
                self.assertFalse(match_evidence.report_matches(report, root, sdk.OWNER))
            observed = sdk.native_evidence(body, bios.WRAPPER)
            self.assertEqual((observed['store'], observed['call'], observed['entry_sp_offset'],
                              observed['source_bytes'], observed['halfwords']),
                             (sdk.OWNER+0x1c, sdk.OWNER+0x24, -8, 2, 16))
            for offset, replacement, reason in (
                    (0x02, 0xB082, 'different lifetime'),
                    (0x0a, 0x00c8, 'wrong color bits'),
                    (0x0a, 0x8808, 'extra memory read'),
                    (0x0a, 0x8008, 'extra memory write'),
                    (0x1a, 0x4619, 'store to external destination'),
                    (0x1c, 0x7008, 'only a byte initialized'),
                    (0x1e, 0x4a03, 'different literal'),
                    (0x20, 0x4669, 'source not passed in R0'),
                    (0x22, 0x4669, 'destination aliases source'),
                    (0x26, 0xF800, 'different callee'),
                    (0x28, 0x8008, 'store after call'),
                    (0x30, 0, 'empty transfer'),
                    (0x32, 0x0500, 'word fill')):
                with self.subTest(reason=reason), self.assertRaises(ValueError):
                    mutated = bytearray(body)
                    struct.pack_into('<H', mutated, offset, replacement)
                    sdk.native_evidence(bytes(mutated), bios.WRAPPER)
            with self.assertRaises(ValueError):
                sdk.native_evidence(body, bytes.fromhex('0cdf7047'))


if __name__ == '__main__':
    unittest.main()
