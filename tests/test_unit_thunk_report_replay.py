"""Saved-report replay of library-unit reports whose function calls _call_via_rN.

match.py --unit-toolchain verifies such a function; the saved-report check
(match_evidence.report_matches, run by status.py --write --verify) must
replay it with the report's unit toolchain and orphan exclusion, and keep
replaying every other thunk report with the default toolchain.
"""
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
import match
import match_evidence
import library_units as units
import status
from test_orphan_call_thunks_and_fill import (A, B, IDENTITY, OBJECTS, HAVE_COMPILER, base_rom,
                                              compile_original, rom_body, text_relocations)

D = 0x08002000  # outside the unit, default toolchain
DEFAULT_FLAGS = match.DEFAULT_FLAGS
# a call through a function pointer that -O1 and -O2 compile differently:
# -O1 reloads the counter before the decrement
THUNK = '''extern unsigned char (*data_03001000)(unsigned char *address);
extern unsigned short data_03001004;
extern void func_08001100(void);

unsigned short func_{address:08X}(unsigned char *address, unsigned char last)
{{
    func_08001100();
    while (data_03001000(address) != last)
        ;
    if (data_03001004 != 0 && --data_03001004 == 0)
        return 1;
    return 0;
}}
'''
# a call through a function pointer that old_agbcc and agbcc compile
# differently at -O2: the register choice for the loads
FIELDS_CALL = '''struct Fields {{ unsigned short low; unsigned char middle; unsigned char high; }};
extern unsigned int (*data_03001000)(unsigned int value);

unsigned int func_{address:08X}(struct Fields *fields, unsigned int extra)
{{
    return data_03001000((fields->low << 4) | (fields->middle << 12) | extra);
}}
'''
OLD_CC = units.TOOLCHAINS['old-agbcc-O2-v1']['cc']
HAVE_OLD = HAVE_COMPILER and Path(os.path.expandvars(OLD_CC)).is_file()


def compile_image(root, address, cc, flags):
    args = argparse.Namespace(cc=cc, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=flags)
    runner = match.Runner(cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root)
    with runner.workspace() as workspace:
        _, _, image = match.compile_object(runner, workspace, args, root, address, f'src/{address:08X}.c')
    return image


def write_root(root, rom, spans, row):
    """ROM, index, data symbols and a one-row unit table for a synthetic decomp root."""
    spans = sorted(spans)
    (root / 'baserom.bin').write_bytes(rom)
    (root / 'config/data_symbols.json').write_bytes(OBJECTS)
    (root / 'config/functions.json').write_text(json.dumps(
        [dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb', instrs=(end - start) // 2,
              kind='return') for start, end in spans]))
    (root / 'symbols/functions.txt').write_text('# test index\n' + ''.join(
        f'{start:08X} {end:08X} {end - start} {(end - start) // 2} return\n' for start, end in spans))
    (root / units.TABLE).write_text(json.dumps({'units': [row]}))


def unit_row(toolchain):
    return {'name': 'testlib', 'start': f'0x{A:08X}', 'end': f'0x{B + 2:08X}', 'toolchain': toolchain,
            'identity': [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_V100'}],
            'proof': f'0x{A:08X}', 'evidence': 'synthetic library object for the tests'}


def new_root():
    temporary = tempfile.TemporaryDirectory()
    root = Path(temporary.name)
    for folder in ('src', 'include', 'config', 'symbols', 'build', 'docs/match'):
        (root / folder).mkdir(parents=True, exist_ok=True)
    rom = base_rom()
    rom[IDENTITY - match.ROM_BASE:IDENTITY - match.ROM_BASE + 13] = b'TESTLIB_V100\0'
    return temporary, root, rom


def run_match(root, address, *options):
    command = [sys.executable, str(Path(match.__file__)), '--root', str(root), f'0x{address:08X}', *options]
    environment = dict(os.environ, FFTA_ROM=str(root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1')
    return subprocess.run(command, capture_output=True, text=True, env=environment, timeout=300)


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class UnitThunkReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary, cls.root, rom = new_root()
        root = cls.root
        spans = [(B, B + 2)]
        _, unit_image, _ = compile_original(root, A, THUNK)
        body = rom_body(unit_image, A)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        spans.append((A, A + len(body)))
        cls.unit_body = body
        # the same source outside the unit, compiled with the default toolchain
        (root / 'src' / f'{D:08X}.c').write_text(THUNK.format(address=D))
        image = compile_image(root, D, match.DEFAULT_CC, DEFAULT_FLAGS)
        assert any(name.startswith('_call_via_') for _, _, name in text_relocations(image))
        assert image['text'] != unit_image['text']
        body = rom_body(image, D)
        rom[D - match.ROM_BASE:D - match.ROM_BASE + len(body)] = body
        spans.append((D, D + len(body)))
        cls.rom = bytes(rom)
        cls.row = unit_row('agbcc-O1-v1')
        write_root(root, cls.rom, spans, cls.row)
        for address, options in ((A, ['--unit-toolchain', 'agbcc-O1-v1']), (D, [])):
            result = run_match(root, address, *options)
            assert result.returncode == 0, result.stdout + result.stderr
        cls.unit_report = (root / 'docs/match/08001000.md').read_text()
        cls.default_report = (root / 'docs/match/08002000.md').read_text()
        cls.saved_rom = os.environ.get('FFTA_ROM')
        os.environ['FFTA_ROM'] = str(root / 'baserom.bin')

    @classmethod
    def tearDownClass(cls):
        if cls.saved_rom is None:
            os.environ.pop('FFTA_ROM', None)
        else:
            os.environ['FFTA_ROM'] = cls.saved_rom
        cls.temporary.cleanup()

    def matches(self, report, address=A):
        return match_evidence.report_matches(report, str(self.root), address)

    def test_unit_thunk_report_replays_with_its_unit_toolchain(self):
        self.assertIn('* unit toolchain: `agbcc-O1-v1`', self.unit_report.splitlines())
        self.assertIn('* unit orphan constants: `', self.unit_report)
        self.assertTrue(self.matches(self.unit_report))

    def test_default_thunk_report_still_replays_with_the_default_toolchain(self):
        self.assertNotIn('* unit', self.default_report)
        self.assertIn(f'* compiler: `{match.DEFAULT_CC} {DEFAULT_FLAGS}`', self.default_report.splitlines())
        self.assertTrue(self.matches(self.default_report, D))

    def test_status_write_verify_counts_both_reports(self):
        try:
            result = status.collect(str(self.root), True, write_reports=True)
        finally:
            (self.root / 'docs/match/08001000.md').write_text(self.unit_report)
            (self.root / 'docs/match/08002000.md').write_text(self.default_report)
        self.assertEqual(result[4], [])
        self.assertEqual(result[1], 2)

    def test_swapped_or_removed_unit_toolchain_is_refused(self):
        old_cc = units.TOOLCHAINS['old-agbcc-O2-v1']['cc']
        swapped = self.unit_report.replace('* unit toolchain: `agbcc-O1-v1`', '* unit toolchain: `old-agbcc-O2-v1`')
        self.assertFalse(self.matches(swapped))
        swapped = swapped.replace(f'* compiler: `{match.DEFAULT_CC} -mthumb-interwork -O1`',
                                  f'* compiler: `{old_cc} -mthumb-interwork -O2`')
        self.assertFalse(self.matches(swapped))
        unit_lines = [line for line in self.unit_report.splitlines() if line.startswith(units.MARKERS)]
        self.assertEqual(len(unit_lines), 4)
        removed = '\n'.join(line for line in self.unit_report.split('\n') if line not in unit_lines)
        self.assertFalse(self.matches(removed))
        default = removed.replace(f'* compiler: `{match.DEFAULT_CC} -mthumb-interwork -O1`',
                                  f'* compiler: `{match.DEFAULT_CC} {DEFAULT_FLAGS}`')
        self.assertNotEqual(default, removed)
        self.assertFalse(self.matches(default))

    def test_unit_lines_outside_their_unit_are_refused(self):
        # the default thunk report outside the unit, given the unit's lines and compiler line
        unit_lines = [line for line in self.unit_report.splitlines() if line.startswith(units.MARKERS)]
        default_compiler = f'* compiler: `{match.DEFAULT_CC} {DEFAULT_FLAGS}`'
        forged = self.default_report.replace(default_compiler, '\n'.join(
            [f'* compiler: `{match.DEFAULT_CC} -mthumb-interwork -O1`', *unit_lines]))
        self.assertNotEqual(forged, self.default_report)
        self.assertFalse(self.matches(forged, D))
        # the genuine unit report, once its address lies in no unit
        table = (self.root / units.TABLE).read_bytes()
        (self.root / units.TABLE).unlink()
        try:
            self.assertFalse(self.matches(self.unit_report))
        finally:
            (self.root / units.TABLE).write_bytes(table)
        self.assertTrue(self.matches(self.unit_report))

    def test_changed_bytes_are_refused_by_the_unit_replay(self):
        # movs r0, #0 -> movs r0, #1 in the ROM and in the report alike, so
        # only the replayed compile can tell the bytes from the source's
        offsets = [offset for offset in range(0, len(self.unit_body), 2)
                   if self.unit_body[offset:offset + 2] == b'\x00\x20']
        self.assertTrue(offsets)
        changed = bytearray(self.unit_body)
        changed[offsets[0]] = 1
        report = self.unit_report.replace(self.unit_body.hex(), bytes(changed).hex())
        self.assertNotEqual(report, self.unit_report)
        rom = bytearray(self.rom)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(changed)] = changed
        (self.root / 'baserom.bin').write_bytes(bytes(rom))
        try:
            self.assertFalse(self.matches(report))
        finally:
            (self.root / 'baserom.bin').write_bytes(self.rom)
        self.assertTrue(self.matches(self.unit_report))


@unittest.skipUnless(HAVE_OLD, 'old_agbcc required')
class OldAgbccUnitThunkReplayTests(unittest.TestCase):
    """A thunk caller in an old-agbcc-O2-v1 unit replays with old_agbcc."""

    @classmethod
    def setUpClass(cls):
        cls.temporary, cls.root, rom = new_root()
        root = cls.root
        (root / 'src' / f'{A:08X}.c').write_text(FIELDS_CALL.format(address=A))
        image = compile_image(root, A, OLD_CC, '-mthumb-interwork -O2')
        assert any(name.startswith('_call_via_') for _, _, name in text_relocations(image))
        assert image['text'] != compile_image(root, A, match.DEFAULT_CC, DEFAULT_FLAGS)['text']
        body = rom_body(image, A)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        rom[B - match.ROM_BASE:B - match.ROM_BASE + 2] = b'\x70\x47'
        write_root(root, bytes(rom), [(A, A + len(body)), (B, B + 2)], unit_row('old-agbcc-O2-v1'))
        result = run_match(root, A, '--unit-toolchain', 'old-agbcc-O2-v1')
        assert result.returncode == 0, result.stdout + result.stderr
        cls.report = (root / 'docs/match/08001000.md').read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_old_agbcc_unit_thunk_report_replays_with_old_agbcc(self):
        self.assertIn('* unit toolchain: `old-agbcc-O2-v1`', self.report.splitlines())
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            self.assertTrue(match_evidence.report_matches(self.report, str(self.root), A))


if __name__ == '__main__':
    unittest.main()
