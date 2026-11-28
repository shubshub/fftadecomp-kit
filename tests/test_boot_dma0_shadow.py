"""Frame/data unit replay and independent DMA setup, poll and shadow checks."""
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import boot_dma0_shadow as dma
import match
import report_fixtures
import match_evidence
import plausible
import test_library_units as library
from test_sdk_cpuset_halfword import HEADER

SOURCE = '#include "ffta.h"\n' + dma.BODY.replace(
    'volatile u32 *dma', '/* plausible: DMA0 hardware registers */\n        volatile u32 *dma')


class BootDma0Tests(unittest.TestCase):
    def test_source_qualification(self):
        offsets = dma.source_offsets(SOURCE, HEADER)
        self.assertEqual(len(offsets), 4)
        self.assertTrue(all(SOURCE[pos:].startswith('volatile') for pos in offsets))
        for old, new in (
                ('#include', '#define dma alias\n#include'),
                ('#include', '// splice\\\n#include'),
                ('u32 *dma', 'u16 *dma'), ('(volatile u32 *)', '(u32 *)'),
                ('0x040000B0', '0x030000B0'), ('dma[1]', 'dma[4]'),
                ('dma[0] =', 'dma++; dma[0] ='), ('dma[1] =', 'other(dma); dma[1] ='),
                ('(void)dma[2];', ''), ('(void)dma[2];', '(void)dma[2]; (void)dma[2];'),
                ('while (dma[2]', 'while (src[2]'), ('& 0x80000000', '& 0x40000000'),
                ('0x80000027', '0x84000027'), ('03000940', '03000942'),
                ('/* plausible:', '/* hardware:')):
            with self.subTest(change=new):
                self.assertNotEqual(len(dma.source_offsets(SOURCE.replace(old, new), HEADER)), 4)
        for header in (HEADER.replace(b'unsigned int', b'signed int'),
                       HEADER.replace(b'#endif', b'#define dma hidden\n#endif')):
            self.assertFalse(dma.source_offsets(SOURCE, header))

    @unittest.skipUnless(library.HAVE_COMPILER, 'needs agbcc and arm-none-eabi binutils')
    def test_native_unit_replay_and_rejections(self):
        # Compile our own complete fixture. Its two linked IWRAM names agree
        # with the game. No ROM-derived byte sequences are distributed.
        typedefs = HEADER.decode().split('#define FFTA_H\n', 1)[1].split('#endif')[0]
        inline = SOURCE.replace('#include "ffta.h"', typedefs)
        tool = library.units.TOOLCHAINS['agbcc-O0-v1']
        with patch.object(library, 'SYMBOLS', dma.SYMBOLS):
            fixture = library.Root([(dma.OWNER, inline, tool['cc'], tool['flags']),
                                    (library.G, library.IDENTITY_O0, tool['cc'], tool['flags'])], [])
        self.addCleanup(fixture.temporary.cleanup)
        root = fixture.path
        fixture.write_table([library.row('boot fixture', dma.OWNER, fixture.end(library.G),
                                         'agbcc-O0-v1', dma.OWNER)])
        (root / dma.HEADER).write_bytes(HEADER)
        source = root / dma.SOURCE
        source.write_text(SOURCE)
        rom = root / 'baserom.bin'
        raw = rom.read_bytes()
        offset = dma.OWNER - match.ROM_BASE
        body = raw[offset:offset + dma.SIZE]
        with patch.dict(os.environ, FFTA_ROM=str(rom)):
            self.assertEqual(dma.native_evidence(body),
                             (0x08000744, 0x08000750, 0x08000758, 0x0800074A, 0x0800076E))
            self.assertEqual(plausible.check_file(source), [])
            result = fixture.run(dma.OWNER, '--unit-toolchain', 'agbcc-O0-v1', write=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = fixture.report(dma.OWNER)
            self.assertIn('112/112 bytes', report)
            self.assertIn('elf-symbol-thumb-frame-data-v1', report)
            self.assertTrue(match_evidence.report_matches(report, root, dma.OWNER))
            line = next(line for line in report.splitlines() if line.startswith('* allowlisted volatile MMIO:'))
            for edit in ('', line + '\n' + line, line.replace('hardware-dependent', 'guaranteed')):
                self.assertFalse(match_evidence.report_matches(report.replace(line, edit), root, dma.OWNER))
            for length in (dma.SIZE - 2, dma.SIZE + 4):
                forged = raw[offset:offset + length].hex()
                altered = report.replace(body.hex(), forged).replace(
                    f'({dma.SIZE} bytes)', f'({length} bytes)').replace(
                    f'{dma.SIZE}/{dma.SIZE} bytes', f'{length}/{length} bytes')
                self.assertFalse(match_evidence.report_matches(altered, root, dma.OWNER))
            for prefix in ('* ROM bytes:', '* compiled :'):
                line = next(line for line in report.splitlines() if line.startswith(prefix))
                self.assertFalse(report_fixtures.replay(report.replace(line, line+'\n'+line), root, dma.OWNER))
            with patch.dict(os.environ, FFTA_ROM=str(root / 'nonexistent.gba')):
                with self.assertRaises(ValueError):
                    plausible.allowlisted_volatile_uses(root, dma.OWNER)
                self.assertFalse(report_fixtures.replay(report, root, dma.OWNER))
            neighbor = root / 'src/08000714.c'
            neighbor.write_text(SOURCE)
            self.assertTrue(any(row[1] == 'volatile' for row in plausible.check_file(neighbor)))
            symbol_file = root / 'config/data_symbols.json'
            original_symbols = json.loads(symbol_file.read_text())
            for name in dma.SYMBOLS:
                with self.subTest(identity=name):
                    changed = dict(original_symbols, **{name: '0x03000100'})
                    symbol_file.write_text(json.dumps(changed))
                    self.assertTrue(any(row[1] == 'volatile' for row in plausible.check_file(source)))
                    self.assertFalse(match_evidence.report_matches(report, root, dma.OWNER))
            symbol_file.write_text(json.dumps(original_symbols))
            for at, value, why in (
                    (0x02, 0xB081, 'one-word frame'), (0x12, 0x7001, 'byte source write'),
                    (0x1a, 0x6000, 'wrong destination value'), (0x24, 0x8001, 'halfword control write'),
                    (0x2c, 0x6008, 'readback changed to store'),
                    (0x32, 0x6839, 'polling shadow RAM'), (0x38, 0x8801, 'narrow poll'),
                    (0x3a, 0x0f8a, 'wrong shift'), (0x3e, 0x2801, 'wrong comparison'),
                    (0x40, 0xd008, 'exit on busy'), (0x42, 0xe007, 'exit returns to spin'),
                    (0x54, 0xe7f0, 'skip fresh MMIO load'),
                    (0x5a, 0x780a, 'byte shadow load'), (0x5c, 0x8001, 'store pointer instead of display'),
                    (0x44, 0x0940, 'DMA source'), (0x48, 0x00bc, 'different channel'),
                    (0x4c, 0x000a, 'alternate display register'), (0x50, 0x0028, '40 halfwords'),
                    (0x52, 0x8400, '32-bit transfer mode'), (0x68, 0x2bbe, 'copy destination'),
                    (0x6c, 0x0942, 'copy source')):
                with self.subTest(why=why), self.assertRaises(ValueError):
                    mutated = bytearray(body)
                    struct.pack_into('<H', mutated, at, value)
                    dma.native_evidence(bytes(mutated))
            corrupted = bytearray(raw)
            struct.pack_into('<H', corrupted, offset + 0x50, 0x28)
            rom.write_bytes(corrupted)
            self.assertTrue(any(row[1] == 'volatile' for row in plausible.check_file(source)))
            self.assertFalse(report_fixtures.replay(report, root, dma.OWNER))


if __name__ == '__main__':
    unittest.main()
