"""Check the SDK word fill and its paired word copy under the native compiler."""
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
import match
import match_evidence
import plausible
import tile_cpufill32 as tile
from test_sdk_cpuset_halfword import HEADER

SOURCE = '''#include "ffta.h"
extern void func_0814186C(const void *source, void *destination, u32 control);
void func_0804BF78(u32 *tiles, u8 x, u8 y, u8 width, u8 height) {
    u8 row = y & 7;
    u8 dy;
    for (dy = 0; dy < 2 && y + dy < height; ++dy) {
        u32 col = x;
        u32 *line = tiles + (row & 7);
        u8 dx;
        for (dx = 0; dx < 2 && x + dx < width; ++dx) {
            u32 input;
            col &= 7;
            func_0814186C(line, &input, 0x04000001);
            {
                volatile u32 fill = input & ~(15u << (col * 4));
                func_0814186C((const void *)&fill, line, 0x05000001);
            }
            if (++col > 7) line = tiles + 8;
        }
        if (++row > 7) tiles += 256;
    }
}
'''


class TileFill32Tests(unittest.TestCase):
    def test_source_requires_exact_local_width_lifetime_and_transfer(self):
        self.assertEqual(tile.source_offset(SOURCE, HEADER), SOURCE.index('volatile'))
        self.assertIsNone(tile.source_offset(SOURCE, HEADER.replace(b'#endif', b'#define fill injected\n#endif')))
        for old, new in (
                ('u32 input;', 'volatile u32 input;'),
                ('volatile u32 fill', 'volatile u16 fill'),
                ('(const void *)&fill', '(const void *)&input'),
                ('(col * 4)', '(col * 2)'),
                ('0x04000001', '0x05000001'),
                ('0x05000001', '0x05000002'),
                ('0x05000001);', '0x05000001); (void)fill;'),
                ('u32 *tiles', 'volatile u32 *tiles'),
                ('#include', '#define fill other\n#include')):
            with self.subTest(change=new):
                self.assertIsNone(tile.source_offset(SOURCE.replace(old, new), HEADER))

    def test_native_compiler_issue_replay_and_boundary_mutations(self):
        base = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        base.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='tile-cpufill32-', dir=base) as directory:
            root = Path(directory)
            for name in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
                (root / name).mkdir(parents=True, exist_ok=True)
            (root / tile.SOURCE).write_text(SOURCE)
            (root / tile.HEADER).write_bytes(HEADER)
            rows = [(tile.OWNER, tile.SIZE, 95), (tile.CPUSET, 4, 2)]
            mapping = json.dumps([dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=i)
                                  for a, n, i in rows]).encode()
            (root / 'config/functions.json').write_bytes(mapping)
            (root / 'config/data_symbols.json').write_text('{}')
            (root / 'symbols/functions.txt').write_text(''.join(
                f'{a:08X} {a+n:08X} {n} {i} return\n' for a, n, i in rows))
            rom = bytearray(tile.CPUSET - tile.BASE + 4)
            rom[-4:] = tile.WRAPPER
            args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, flags=match.DEFAULT_FLAGS,
                                      assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD)
            runner = match.Runner(args.cc, root=str(root), timeout=120)
            with runner.workspace() as work:
                _, _, obj = match.compile_object(runner, work, args, str(root), tile.OWNER, tile.SOURCE)
                body, calls, _ = match.link_calls(runner, work, args, obj, tile.OWNER, mapping, len(rom), bytes(rom))
                _, _, erased = match.compile_object(runner, work, args, str(root), tile.OWNER, tile.SOURCE,
                    rewrite=lambda text: text.replace('volatile u32 fill', 'u32 fill'))
                ordinary, _, _ = match.link_calls(runner, work, args, erased, tile.OWNER, mapping, len(rom), bytes(rom))
            tile.compare_words(body, ordinary)
            for pc in (0x0804BFC8, 0x0804BFCA, 0x0804BFD8, 0x0804BFDA, 0x0804BFDC, 0x0804BFDE, 0x0804BFE0):
                changed = bytearray(ordinary)
                changed[pc - tile.OWNER] ^= 1
                with self.subTest(control=f'{pc:08X}'), self.assertRaises(ValueError):
                    tile.compare_words(body, changed)
            self.assertEqual(calls, tile.CALLS)
            start = tile.OWNER - tile.BASE
            rom[start:start+len(body)] = body
            path = root / 'baserom.bin'
            path.write_bytes(rom)
            with patch.dict(os.environ, FFTA_ROM=str(path)):
                issued = subprocess.run([sys.executable, match.__file__, '--root', str(root), '0804BF78'],
                                        capture_output=True, text=True, timeout=120)
                self.assertEqual(issued.returncode, 0, issued.stdout + issued.stderr)
                report = (root / 'docs/match/0804BF78.md').read_text()
                self.assertTrue(match_evidence.report_matches(report, root, tile.OWNER))
                for old, new in (('entry SP-52', 'entry SP-48'), ('"destination":[-48,4]', '"destination":[-48,8]'),
                                 ('"killed":[0]', '"killed":[]'), ('204/204 bytes', '203/204 bytes')):
                    with self.subTest(report=new):
                        self.assertIn(old, report)
                        self.assertFalse(match_evidence.report_matches(report.replace(old, new), root, tile.OWNER))
                other = root / 'src/0804BF74.c'
                other.write_text(SOURCE)
                self.assertTrue(any(f[1] == 'volatile' for f in plausible.check_file(other)))
                for pc, half in ((0x0804BFCA, 0x4669), (0x0804BFDC, 0x9001), (0x0804BFE4, 0x4770),
                                 (0x0804C03C, 2), (0x0804C042, 0x0100), (tile.CPUSET, 0xDF0C)):
                    with self.subTest(pc=f'{pc:08X}'), self.assertRaises(ValueError):
                        changed = bytearray(rom)
                        struct.pack_into('<H', changed, pc - tile.BASE, half)
                        tile.original(changed)
                (root / tile.SOURCE).write_text(SOURCE.replace('0x05000001);', '0x05000001); (void)fill;'))
                self.assertFalse(match_evidence.report_matches(report, root, tile.OWNER))


if __name__ == '__main__':
    unittest.main()
