"""Library units: the table rules, unit toolchains inside units only, consistency, proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import library_units as units
import rebuild
import status

MATCH_PY = str(Path(match.__file__))
A, B, C, D, E, F, G = 0x08001000, 0x08001100, 0x08002000, 0x08001300, 0x08001400, 0x08001800, 0x08001900
IDENTITY = 0x08003000
SYMBOLS = {'data_03001000': 0x03001000, 'data_03001004': 0x03001004}

# differs between -O1 and -O2: -O1 reloads the counter before the decrement
COUNTDOWN = '''extern unsigned short data_03001000;
extern unsigned char data_03001004;

void func_08001000(void)
{
    if (data_03001000 != 0 && --data_03001000 == 0)
        data_03001004 = 1;
}
'''
# the same object at -O1 and -O2; agbcc saves lr here where old_agbcc does not
LOOP = '''int func_{address:08X}(int count, int step)
{{
    int sum = 0;

    while (count > 0) {{
        sum += step;
        count--;
    }}
    return sum;
}}
'''
OUTSIDE = '''int func_08002000(int a, int b)
{
    return a + b;
}
'''
# a frame at -O0, one instruction at -O2
SUM = '''int func_08001800(int a, int b)
{
    return a + b;
}
'''
IDENTITY_O0 = '''int func_08001900(int a)
{
    return a;
}
'''
# the same object under both compilers
DIFFERENCE = '''int func_08001400(int a, int b)
{
    return a - b;
}
'''
# differs between agbcc and old_agbcc: register choice for the loads
FIELDS = '''struct Fields { unsigned short low; unsigned char middle; unsigned char high; };

unsigned int func_08001300(struct Fields *fields, unsigned int extra)
{
    return (fields->low << 4) | (fields->middle << 12) | extra;
}
'''
HAVE_COMPILER = Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which('arm-none-eabi-ld')
OLD_CC = units.TOOLCHAINS['old-agbcc-O2-v1']['cc']
HAVE_OLD = HAVE_COMPILER and Path(os.path.expandvars(OLD_CC)).is_file()


def row(name, start, end, toolchain, proof, identity=None):
    return {'name': name, 'start': f'0x{start:08X}', 'end': f'0x{end:08X}', 'toolchain': toolchain,
            'identity': identity or [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_V100'}],
            'proof': f'0x{proof:08X}', 'evidence': 'synthetic library object for the tests'}


def index_rows(spans):
    return [{'rom': f'0x{start:08X}', 'end': f'0x{end:08X}', 'mode': mode, 'instrs': (end - start) // 2,
             'kind': 'return'} for start, end, mode in spans]


def compiled_body(root, address, text, cc, flags):
    """The linked bytes of one source: data literals take their absolute addresses."""
    (root / 'src' / f'{address:08X}.c').write_text(text)
    args = argparse.Namespace(cc=cc, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=flags)
    runner = match.Runner(cc, 'Ubuntu', match.DEFAULT_WSL_PATH, root=str(root))
    with runner.workspace() as workspace:
        _, _, image = match.compile_object(runner, workspace, args, root, address, f'src/{address:08X}.c')
    symbol, offset = match.function_record(image, f'func_{address:08X}', address, True)
    body = bytearray(image['text'][offset:offset + symbol['size']])
    for index in image['relocations']:
        section = image['sections'][index]
        if section[7] != image['text_index']:
            continue
        payload, symbols = image['section_data'][index], image['symbol_tables'][section[6]]
        for position in range(0, len(payload), 8):
            site, info = struct.unpack_from('<II', payload, position)
            assert info & 255 == 2
            name = symbols[info >> 8]['name']
            struct.pack_into('<I', body, site - offset, SYMBOLS[name] + struct.unpack_from('<I', body, site - offset)[0])
    return bytes(body)


class Root:
    """A synthetic decomp root: index, data symbols, ROM and one unit table."""

    def __init__(self, functions, table):
        self.temporary = tempfile.TemporaryDirectory()
        self.path = root = Path(self.temporary.name)
        for folder in ('src', 'include', 'config', 'symbols', 'build', 'docs/match'):
            (root / folder).mkdir(parents=True)
        (root / 'config/data_symbols.json').write_text(json.dumps({k: f'0x{v:08X}' for k, v in SYMBOLS.items()}))
        rom = bytearray(0x4000)
        rom[IDENTITY - match.ROM_BASE:IDENTITY - match.ROM_BASE + 13] = b'TESTLIB_V100\0'
        spans = []
        for address, text, cc, flags in functions:
            body = compiled_body(root, address, text, cc, flags)
            rom[address - match.ROM_BASE:address - match.ROM_BASE + len(body)] = body
            spans.append((address, address + len(body), 'thumb'))
        self.spans = spans
        (root / 'config/functions.json').write_text(json.dumps(index_rows(spans)))
        (root / 'symbols/functions.txt').write_text('# test index\n' + ''.join(
            f'{start:08X} {end:08X} {end - start} {(end - start) // 2} return\n' for start, end, _ in spans))
        (root / 'baserom.bin').write_bytes(bytes(rom))
        self.write_table(table)
        self.environment = dict(os.environ, FFTA_ROM=str(root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1')

    def end(self, address):
        return next(end for start, end, _ in self.spans if start == address)

    def write_table(self, table):
        (self.path / units.TABLE).write_text(json.dumps({'units': table}, indent=2))

    def run(self, address, *options, write=False):
        command = [sys.executable, MATCH_PY, '--root', str(self.path), f'0x{address:08X}', *options]
        if not write:
            command.append('--no-write')
        return subprocess.run(command, capture_output=True, text=True, env=self.environment, timeout=300)

    def report(self, address):
        return (self.path / 'docs/match' / f'{address:08X}.md').read_text()


class TableTests(unittest.TestCase):
    """Pure table validation against a synthetic ROM and index."""

    def setUp(self):
        self.rom = bytearray(0x4000)
        self.rom[IDENTITY - match.ROM_BASE:IDENTITY - match.ROM_BASE + 12] = b'TESTLIB_V100'
        self.rom = bytes(self.rom)
        self.spans = [(A, A + 0x28, 'thumb'), (A + 0x28, A + 0x40, 'thumb'), (B, B + 0x18, 'thumb'),
                      (C, C + 4, 'thumb'), (C + 4, C + 8, 'thumb'), (C + 8, C + 12, 'arm')]
        self.mapping = json.dumps(index_rows(self.spans)).encode()

    def parse(self, rows):
        return units.parse(json.dumps({'units': rows}).encode(), self.rom, self.mapping)

    def refused(self, rows, message):
        with self.assertRaisesRegex(units.Refusal, message):
            self.parse(rows)

    def test_valid_rows_are_sorted_and_contain_whole_functions(self):
        later = row('later', C, C + 8, 'old-agbcc-O2-v1', C,
                    [{'address': f'0x{C:08X}', 'size': 16, 'sha256': hashlib.sha256(bytes(16)).hexdigest()}])
        parsed = self.parse([later, row('flash', A, B + 0x18, 'agbcc-O1-v1', A)])
        self.assertEqual([unit.name for unit in parsed], ['flash', 'later'])
        self.assertIs(units.containing(parsed, A + 0x28, A + 0x40), parsed[0])
        self.assertIsNone(units.containing(parsed, C + 8, C + 12))
        with self.assertRaisesRegex(units.Refusal, 'straddles library unit'):
            units.containing(parsed, C + 4, C + 12)
        self.assertEqual(units.parse(None, self.rom, self.mapping), ())
        self.assertEqual(json.loads(parsed[0].text), row('flash', A, B + 0x18, 'agbcc-O1-v1', A))

    def test_overlapping_rows_are_refused(self):
        self.refused([row('one', A, A + 0x40, 'agbcc-O1-v1', A),
                      row('two', A + 0x28, B + 0x18, 'old-agbcc-O2-v1', B,
                          [{'address': f'0x{C:08X}', 'size': 16,
                            'sha256': hashlib.sha256(bytes(16)).hexdigest()}])], 'units one and two overlap')

    def test_rows_must_align_to_index_function_boundaries(self):
        self.refused([row('start', A + 2, A + 0x40, 'agbcc-O1-v1', A + 0x28)], 'straddles index function')
        self.refused([row('end', A, A + 0x30, 'agbcc-O1-v1', A)], 'straddles index function')
        self.refused([row('gap', A, A + 0x80, 'agbcc-O1-v1', A)], 'index function boundaries')
        self.refused([row('gap', A - 0x10, A + 0x40, 'agbcc-O1-v1', A)], 'index function boundaries')
        self.refused([row('arm', C, C + 12, 'agbcc-O1-v1', C)], 'non-Thumb')
        self.refused([row('one', A, A + 0x28, 'agbcc-O1-v1', A)], 'at least 2 index functions')
        self.refused([row('odd', A, A + 0x41, 'agbcc-O1-v1', A)], 'even')

    def test_identity_bytes_are_checked_against_the_rom(self):
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_V101'}])], 'identity string')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{A:08X}', 'size': 0x40, 'sha256': '0' * 64}])], 'identity digest')
        self.refused([dict(row('flash', A, A + 0x40, 'agbcc-O1-v1', A), identity=[])], 'identity evidence')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_V100', 'size': 1}])], 'identity items')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': '0x0800FFF8', 'ascii': 'TESTLIB_V100'}])], 'identity string')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB'}])], 'at least 8 characters')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_'}])], 'NUL-terminated')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{IDENTITY + 4:08X}', 'ascii': 'LIB_V100'}])], 'tail of a longer string')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A,
                          [{'address': f'0x{C:08X}', 'size': 8, 'sha256': hashlib.sha256(bytes(8)).hexdigest()}])],
                     'malformed identity digest')

    def test_rows_may_not_share_identity_bytes(self):
        digest = [{'address': f'0x{C:08X}', 'size': 16, 'sha256': hashlib.sha256(bytes(16)).hexdigest()}]
        self.refused([row('one', A, A + 0x40, 'agbcc-O1-v1', A), row('two', C, C + 8, 'agbcc-O1-v1', C)],
                     'share identity bytes')
        self.refused([row('one', A, A + 0x40, 'agbcc-O1-v1', A, digest),
                      row('two', C, C + 8, 'agbcc-O1-v1', C,
                          [{'address': f'0x{C + 8:08X}', 'size': 16,
                            'sha256': hashlib.sha256(bytes(16)).hexdigest()}])], 'share identity bytes')
        self.assertEqual(len(self.parse([row('one', A, A + 0x40, 'agbcc-O1-v1', A),
                                         row('two', C, C + 8, 'agbcc-O1-v1', C, digest)])), 2)

    def test_toolchain_proof_and_row_shape(self):
        self.refused([row('flash', A, A + 0x40, 'agbcc-O3-v1', A)], 'unknown toolchain')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', B)], 'proof')
        self.refused([row('flash', A, A + 0x40, 'agbcc-O1-v1', A + 2)], 'proof')
        extra = dict(row('flash', A, A + 0x40, 'agbcc-O1-v1', A), flags='-O1')
        self.refused([extra], 'exactly the keys')
        lower = dict(row('flash', A, A + 0x40, 'agbcc-O1-v1', A), start='0x0800100a')
        self.refused([lower], 'canonical')
        self.refused([row('same', A, A + 0x40, 'agbcc-O1-v1', A), row('same', B, B + 0x18, 'agbcc-O1-v1', B)],
                     'duplicate library unit name')
        self.refused([dict(row('flash', A, A + 0x40, 'agbcc-O1-v1', A), start=1)], 'canonical')
        with self.assertRaisesRegex(units.Refusal, 'duplicate key'):
            units.parse(b'{"units": [], "units": []}', self.rom, self.mapping)
        with self.assertRaisesRegex(units.Refusal, 'one `units` list'):
            units.parse(b'{"units": [], "other": 1}', self.rom, self.mapping)

    def test_report_binding_lines(self):
        lines = ['* library unit: `{}`', '* unit toolchain: `agbcc-O1-v1`', f'* unit compiler SHA-256: `{"0" * 64}`']
        self.assertEqual(units.binding('\n'.join(lines)), ('{}', 'agbcc-O1-v1', '0' * 64, None))
        self.assertIsNone(units.binding('* compiler: `x`'))
        for broken in (lines[:2], lines + lines[1:2], lines + ['* unit extra: `1`'],
                       [lines[0][:-1]] + lines[1:]):
            with self.subTest(broken=broken), self.assertRaises(units.Refusal):
                units.binding('\n'.join(broken))


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class UnitToolchainTests(unittest.TestCase):
    """agbcc -O1 inside one unit; the default toolchain elsewhere."""

    @classmethod
    def setUpClass(cls):
        cls.root = Root([(A, COUNTDOWN, match.DEFAULT_CC, '-mthumb-interwork -O1'),
                         (B, LOOP.format(address=B), match.DEFAULT_CC, match.DEFAULT_FLAGS),
                         (C, OUTSIDE, match.DEFAULT_CC, match.DEFAULT_FLAGS)], [])
        cls.row = row('testlib', A, cls.root.end(B), 'agbcc-O1-v1', A)
        cls.root.write_table([cls.row])
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root.path / 'baserom.bin'))
        cls.environment.start()
        result = cls.root.run(A, '--unit-toolchain', 'agbcc-O1-v1', write=True)
        assert result.returncode == 0, result.stdout + result.stderr
        cls.proof_report = cls.root.report(A)
        result = cls.root.run(B, write=True)
        assert result.returncode == 0, result.stdout + result.stderr
        cls.member_report = cls.root.report(B)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.root.temporary.cleanup()

    def setUp(self):
        self.root.write_table([self.row])

    def test_unit_toolchain_admits_the_proof_and_excludes_orphan_constants(self):
        report = self.proof_report
        self.assertIn('**MATCH - byte identical** - 40/40 bytes', report)
        self.assertIn(f'* library unit: `{units.canonical(self.row)}`', report)
        self.assertIn('* unit toolchain: `agbcc-O1-v1`', report)
        self.assertIn('* compiler: `$HOME/agbcc/gcc/agbcc -mthumb-interwork -O1`', report)
        self.assertIn(f'* verification: `{match_evidence.DATA_SCHEMA}`', report)
        orphan = json.loads(units.binding(report)[3])
        self.assertEqual(orphan['excluded_ROM_credit'], 0)
        self.assertEqual(orphan['excluded_sections'], ['.rodata', '.rel.rodata'])
        self.assertIs(orphan['section_exclusion_performed'], True)
        self.assertIs(orphan['prerequisite']['section_exclusion_performed'], True)
        self.assertEqual(orphan['prerequisite']['orphan_section']['bytes'], 8)
        self.assertTrue(match_evidence.report_matches(report, self.root.path, A))
        self.assertEqual(units.report_toolchain(report), 'agbcc-O1-v1')
        self.assertEqual(rebuild.saved_profile_arguments(report, self.root.path, A),
                         ['--unit-toolchain', 'agbcc-O1-v1'])
        self.assertEqual(rebuild.saved_profile_arguments(self.member_report, self.root.path, B), [])

    def test_default_toolchain_inside_a_unit_needs_the_same_object(self):
        result = self.root.run(A)
        self.assertEqual(result.returncode, 1)
        self.assertIn("default-toolchain object differs from agbcc-O1-v1's", result.stderr)
        self.assertIn('verdict MATCH - byte identical', self.root.run(B).stdout.splitlines())
        self.assertTrue(match_evidence.report_matches(self.member_report, self.root.path, B))
        self.assertIn('verdict MATCH - byte identical',
                      self.root.run(B, '--unit-toolchain', 'agbcc-O1-v1').stdout.splitlines())
        forged = self.proof_report
        for line in forged.splitlines():
            if line.startswith(units.MARKERS):
                forged = forged.replace(line + '\n', '')
        forged = forged.replace('-mthumb-interwork -O1`', '-mthumb-interwork -O2`')
        self.assertFalse(match_evidence.report_matches(forged, self.root.path, A))

    def test_consistency_compile_failure_is_a_refusal(self):
        source = self.root.path / 'src/08001100.c'
        original = source.read_text()
        try:
            source.write_text(original + '\nint broken(\n')
            result = self.root.run(B)
            self.assertEqual(result.returncode, 1)
            self.assertIn('refused:', result.stderr)
            self.assertIn('could not compile', result.stderr)
            self.assertNotIn('Traceback', result.stderr)
        finally:
            source.write_text(original)

    def test_wrong_toolchain_inside_a_unit_is_refused(self):
        for options, message in ((('--unit-toolchain', 'old-agbcc-O2-v1'), 'built with agbcc-O1-v1'),
                                 (('--flags', '-mthumb-interwork -O1'), 'verify it with --unit-toolchain'),
                                 (('--unit-toolchain', 'agbcc-O1-v1', '--flags', '-mthumb-interwork -O1'),
                                  'do not combine'),
                                 (('--owner-runtime-profile', 'compiler-orphan-address-constants-O0-v1',
                                   '--flags', '-mthumb-interwork -O0'), 'verify it with --unit-toolchain'),
                                 (('--unit-toolchain', 'agbcc-O1-v1', '--switch-profile', 'two-constants-v2'),
                                  'ordinary Thumb path only'),
                                 (('--unit-toolchain', 'agbcc-O1-v1', '--wsl-path', '/elsewhere'),
                                  'default WSL options')):
            with self.subTest(options=options):
                result = self.root.run(A, *options)
                self.assertEqual(result.returncode, 1)
                self.assertIn(message, result.stderr)

    def test_unit_toolchain_outside_its_unit_is_refused(self):
        result = self.root.run(C, '--unit-toolchain', 'agbcc-O1-v1')
        self.assertEqual(result.returncode, 1)
        self.assertIn('not inside a library unit', result.stderr)

    def test_another_toolchain_outside_units_is_never_a_match(self):
        result = self.root.run(C, '--flags', '-mthumb-interwork -O1', write=True)
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root.path / 'docs/match/08002000.md').exists())
        self.assertIn('no report written', result.stdout)
        self.assertIn('bytes   identical', result.stdout)
        self.assertNotIn('verdict MATCH - byte identical', result.stdout.splitlines())
        self.assertTrue(any(line.startswith('verdict NOT VERIFIED') for line in result.stdout.splitlines()))
        result = self.root.run(C, '--flags', '-mthumb-interwork -O1', '--switch-profile', 'two-constants-v2')
        self.assertIn('admitted only through --unit-toolchain', result.stderr)
        result = self.root.run(C, write=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = self.root.report(C)
        self.assertTrue(match_evidence.report_matches(report, self.root.path, C))
        for flags in ('-mthumb-interwork -O1', '-mthumb-interwork -O0', '-O2'):
            flagged = report.replace('-mthumb-interwork -O2`', flags + '`')
            self.assertFalse(match_evidence.report_matches(flagged, self.root.path, C))
        bound = report.replace('* compiler:', '\n'.join(units.report_lines(
            {'unit': units.load(self.root.path)[0], 'tool': units.resolve('agbcc-O1-v1')}, None)) +
            '\n* compiler:')
        self.assertFalse(match_evidence.report_matches(bound, self.root.path, C))

    def test_identity_mismatch_refuses_runs_and_reports(self):
        rom_file = self.root.path / 'baserom.bin'
        original = rom_file.read_bytes()
        changed = bytearray(original)
        changed[IDENTITY - match.ROM_BASE + 11] ^= 1
        try:
            rom_file.write_bytes(bytes(changed))
            result = self.root.run(A, '--unit-toolchain', 'agbcc-O1-v1')
            self.assertEqual(result.returncode, 1)
            self.assertIn('identity string', result.stderr)
            self.assertFalse(match_evidence.report_matches(self.proof_report, self.root.path, A))
            self.assertFalse(match_evidence.report_matches(self.member_report, self.root.path, B))
        finally:
            rom_file.write_bytes(original)
        self.assertTrue(match_evidence.report_matches(self.proof_report, self.root.path, A))

    def test_reports_bind_the_row_and_the_compiler(self):
        self.root.write_table([dict(self.row, evidence='edited after the report')])
        self.assertFalse(match_evidence.report_matches(self.proof_report, self.root.path, A))
        self.root.write_table([self.row])
        digest = units.resolve('agbcc-O1-v1')['sha256']
        self.assertFalse(match_evidence.report_matches(
            self.proof_report.replace(digest, '0' * 64), self.root.path, A))
        self.assertFalse(match_evidence.report_matches(
            self.proof_report.replace('* unit toolchain: `agbcc-O1-v1`', '* unit toolchain: `old-agbcc-O2-v1`'),
            self.root.path, A))
        self.root.write_table([])
        self.assertFalse(match_evidence.report_matches(self.proof_report, self.root.path, A))

    def test_stale_and_unproved_rows_are_reported(self):
        functions = json.loads((self.root.path / 'config/functions.json').read_text())
        matched = {A, B, C}
        problems, summary = units.status_summary(self.root.path, functions, matched, 0x08150000)
        self.assertEqual(problems, [])
        self.assertEqual(summary['units'][0]['matched'], 2)
        self.assertEqual((summary['outside_functions'], summary['outside_matched']), (1, 1))
        problems, _ = units.status_summary(self.root.path, functions, {B, C}, 0x08150000)
        self.assertEqual(problems, ['library unit testlib: proving function 0x08001000 is not verified'])
        self.root.write_table([dict(self.row, proof=f'0x{B:08X}')])
        problems, _ = units.status_summary(self.root.path, functions, matched, 0x08150000)
        self.assertEqual(problems, ['library unit testlib: proving function 0x08001100 is not verified '
                                    'with agbcc-O1-v1'])
        member = self.root.path / 'docs/match/08001100.md'
        try:
            self.assertEqual(self.root.run(B, '--unit-toolchain', 'agbcc-O1-v1', write=True).returncode, 0)
            problems, _ = units.status_summary(self.root.path, functions, matched, 0x08150000)
            self.assertEqual(problems, ['library unit testlib is stale: proving function 0x08001100 compiles '
                                        'to the same function under the default toolchain'])
        finally:
            member.write_text(self.member_report)

    def test_status_replays_unit_reports_with_their_toolchain(self):
        commands = []
        run = subprocess.run

        def recording(command, **options):
            commands.append(command)
            return run(command, **options)

        progress = {}
        with patch.object(status.subprocess, 'run', side_effect=recording):
            result = status.collect(str(self.root.path), True, progress=progress)
        self.assertEqual(result[4], [])
        self.assertEqual(result[1], 3)
        replays = [command for command in commands if type(command) is list and MATCH_PY in command]
        self.assertEqual(len(replays), 3)
        proof = [command for command in replays if f'{A:08X}' in command]
        self.assertEqual(len(proof), 1)
        self.assertIn('--unit-toolchain', proof[0])
        self.assertNotIn('--flags', proof[0])
        block = status.render(*result[:5], progress=progress)[0]
        self.assertIn(f'| testlib | `0x08001000`-`0x{self.root.end(B):08X}` | `agbcc-O1-v1` | 2 / 2 |', block)
        self.assertIn('| Everything outside library units | | default | 1 / 1 | |', block)


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class O0UnitTests(unittest.TestCase):
    """An agbcc-O0-v1 unit admits the ordinary path and the fixed-O0 selector."""

    @classmethod
    def setUpClass(cls):
        cls.root = Root([(F, SUM, match.DEFAULT_CC, '-mthumb-interwork -O0'),
                         (G, IDENTITY_O0, match.DEFAULT_CC, '-mthumb-interwork -O0'),
                         (A, COUNTDOWN, match.DEFAULT_CC, '-mthumb-interwork -O1'),
                         (B, LOOP.format(address=B), match.DEFAULT_CC, match.DEFAULT_FLAGS)], [])
        rom = (cls.root.path / 'baserom.bin').read_bytes()
        boot = [{'address': f'0x{F:08X}', 'size': cls.root.end(G) - F,
                 'sha256': hashlib.sha256(rom[F - match.ROM_BASE:cls.root.end(G) - match.ROM_BASE]).hexdigest()}]
        cls.root.write_table([row('boot', F, cls.root.end(G), 'agbcc-O0-v1', F, boot),
                              row('testlib', A, cls.root.end(B), 'agbcc-O1-v1', A)])
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root.path / 'baserom.bin'))
        cls.environment.start()

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.root.temporary.cleanup()

    def arguments(self, **changes):
        values = dict(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                      objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS,
                      mode='thumb', control_flow_profile='ordinary', unit_toolchain=None,
                      owner_runtime_profile=None)
        values.update(changes)
        return argparse.Namespace(**values)

    def test_ordinary_o0_unit_report(self):
        result = self.root.run(F, '--unit-toolchain', 'agbcc-O0-v1', write=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = self.root.report(F)
        self.assertIn('* compiler: `$HOME/agbcc/gcc/agbcc -mthumb-interwork -O0`', report)
        self.assertTrue(match_evidence.report_matches(report, self.root.path, F))
        self.assertIn('verify it with --unit-toolchain agbcc-O0-v1',
                      self.root.run(F, '--flags', '-mthumb-interwork -O0').stderr)

    def test_fixed_o0_selector_scope(self):
        from compiler_orphan_constants_native_profile import SELECTOR, FLAGS
        self.assertIsNone(units.gate(self.root.path, F, self.arguments(owner_runtime_profile=SELECTOR,
                                                                         flags=FLAGS)))
        with self.assertRaisesRegex(units.Refusal, 'verify it with --unit-toolchain agbcc-O1-v1'):
            units.gate(self.root.path, A, self.arguments(owner_runtime_profile=SELECTOR, flags=FLAGS))
        self.assertEqual(units.gate(self.root.path, C, self.arguments(flags=FLAGS)), 'exploratory')
        self.assertIsNone(units.gate(self.root.path, C, self.arguments(owner_runtime_profile=SELECTOR,
                                                                         flags=FLAGS)))


class OldCompilerProbeTests(unittest.TestCase):
    """The probe passes only -fprologue-bugfix; only a binary that names and refuses it is old."""

    def classify(self, body):
        with tempfile.TemporaryDirectory() as directory:
            script = Path(directory) / 'cc1'
            log = Path(directory) / 'argv'
            script.write_text(f'#!/bin/sh\necho "$@" > {log}\n{body}\n')
            script.chmod(0o755)
            result = units._rejects_new_option(str(script))
            return result, log.read_text().split()

    def test_probe_arguments_and_classification(self):
        new, argv = self.classify('exit 0')
        self.assertFalse(new)
        self.assertEqual(argv[0], '-fprologue-bugfix')
        self.assertNotIn('-quiet', argv)
        old, _ = self.classify('case "$*" in *-fprologue-bugfix*) echo "cc1: Invalid option '
                               '\\`-fprologue-bugfix\'" >&2; exit 1;; esac; exit 0')
        self.assertTrue(old)
        other, _ = self.classify('echo "cc1: Invalid option \\`-quiet\'" >&2; exit 1')
        self.assertFalse(other)


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class OldCompilerIdentityTests(unittest.TestCase):
    def test_a_new_compiler_installed_as_old_agbcc_is_refused(self):
        units._identities.clear()
        with patch.dict(units.TOOLCHAINS, {'old-agbcc-O2-v1': dict(units.TOOLCHAINS['old-agbcc-O2-v1'],
                                                                   cc=match.DEFAULT_CC)}):
            with self.assertRaisesRegex(units.Refusal, 'not the OLD_COMPILER build'):
                units.resolve('old-agbcc-O2-v1')
        units._identities.clear()


@unittest.skipUnless(HAVE_OLD, 'old_agbcc required')
class OldToolchainTests(unittest.TestCase):
    """old_agbcc inside a unit: admitted with --unit-toolchain only."""

    @classmethod
    def setUpClass(cls):
        cls.root = Root([(D, FIELDS, OLD_CC, '-mthumb-interwork -O2'),
                         (E, DIFFERENCE, match.DEFAULT_CC, match.DEFAULT_FLAGS),
                         (C, OUTSIDE, match.DEFAULT_CC, match.DEFAULT_FLAGS)], [])
        cls.row = row('oldlib', D, cls.root.end(E), 'old-agbcc-O2-v1', D,
                      [{'address': f'0x{D:08X}', 'size': cls.root.end(E) - D,
                        'sha256': hashlib.sha256((cls.root.path / 'baserom.bin').read_bytes()[
                            D - match.ROM_BASE:cls.root.end(E) - match.ROM_BASE]).hexdigest()}])
        cls.root.write_table([cls.row])
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root.path / 'baserom.bin'))
        cls.environment.start()

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.root.temporary.cleanup()

    def test_old_unit_toolchain_admits_the_proof_and_nothing_else_does(self):
        result = self.root.run(D, '--unit-toolchain', 'old-agbcc-O2-v1', write=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = self.root.report(D)
        self.assertIsNone(units.binding(report)[3])
        self.assertIn('* compiler: `$HOME/agbcc/gcc/old_agbcc -mthumb-interwork -O2`', report)
        self.assertTrue(match_evidence.report_matches(report, self.root.path, D))
        result = self.root.run(D)
        self.assertIn("differs from old-agbcc-O2-v1's", result.stderr)
        result = self.root.run(D, '--cc', OLD_CC)
        self.assertIn('verify it with --unit-toolchain old-agbcc-O2-v1', result.stderr)
        self.assertIn('verdict MATCH - byte identical', self.root.run(E).stdout.splitlines())
        result = self.root.run(C, '--cc', OLD_CC)
        self.assertTrue(any(line.startswith('verdict NOT VERIFIED') for line in result.stdout.splitlines()))
        functions = json.loads((self.root.path / 'config/functions.json').read_text())
        self.assertEqual(units.status_summary(self.root.path, functions, {D, E, C}, 0x08150000)[0], [])


class GateRuntimeErrorTests(unittest.TestCase):
    """match.py reports a RuntimeError that leaves the unit gate as a refusal."""

    def setUp(self):
        self.root = Root([], [])
        self.addCleanup(self.root.temporary.cleanup)

    def test_a_runtime_error_from_the_gate_is_a_refusal(self):
        # a plain RuntimeError, so the clause cannot be narrowed to one subclass
        with patch.object(sys, 'argv', [MATCH_PY, '--root', str(self.root.path), f'0x{A:08X}']), \
                patch.dict(os.environ, self.root.environment), patch.object(match, 'ROOT', match.ROOT), \
                patch.object(units, 'gate', side_effect=RuntimeError('the gate failed')) as gate, \
                self.assertRaises(SystemExit) as refused:
            match.main()
        self.assertEqual(gate.call_count, 1)
        self.assertEqual(refused.exception.code, 'refused: the gate failed')
        self.assertEqual(list((self.root.path / 'docs/match').iterdir()), [])

    def test_a_table_too_deep_to_decode_is_a_refusal(self):
        # The decoder stops this with RecursionError, a RuntimeError, at a fixed depth on CPython 3.12
        # and when the stack runs out on 3.14; with enough stack 3.14 reads to the end and the table
        # is invalid JSON.  Whichever happens and whichever layer words it: one refusal line, no report.
        (self.root.path / units.TABLE).write_text('[' * 1000000)
        result = self.root.run(A, write=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, '')
        self.assertRegex(result.stderr, r'\Arefused: [^\n]+\n\Z')
        self.assertEqual(list((self.root.path / 'docs/match').iterdir()), [])


if __name__ == '__main__':
    unittest.main()
