"""Opt-in exact unsigned-shift dividend bounds and unchanged prior policies."""
import argparse
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence as evidence
import owner_admission_profile as owner
import signed_divmod_profile as profile
import status

A, B = 0x08010000, 0x08011000
SOURCE = '''int func_08010000(int value, int divisor)
{
    unsigned short narrowed = value;
    int half = narrowed >> 1;
    if (divisor == 0)
        return 0;
    return half / 7 + half % divisor;
}
'''


class SignedDividendTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        selected = os.environ.get('FFTA_ROM')
        if not selected or not Path(selected).is_file():
            raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        cls.approved = Path(selected).read_bytes()
        if hashlib.sha256(cls.approved).hexdigest() != '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19':
            raise ValueError('fixture requires the approved full ROM identity')
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='signed_divmod_tests_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root / name).mkdir()
        cls.source = cls.root / 'src/08010000.c'
        cls.source.write_text(SOURCE)
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            cls.raw, _, cls.original = match.compile_object(runner, workspace, cls.args, cls.root, A, 'src/08010000.c')
            cls.assembly = runner.read_binary(f'{workspace}/f.s')
            cls.rows = [{'rom': f'0x{A:08X}', 'end': f'0x{A + len(cls.original["text"]):08X}', 'mode': 'thumb', 'instrs': 0}]
            decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            cls.rows += [{'rom': f'0x{lo:08X}', 'end': f'0x{hi:08X}', 'mode': 'thumb',
                          'instrs': len(list(decoder.disasm(cls.approved[lo-match.ROM_BASE:hi-match.ROM_BASE], lo)))}
                         for lo, hi, _ in sorted(set(profile.quotient.IDENTITIES + profile.remainder.IDENTITIES))]
            initial = (json.dumps(cls.rows, indent=2) + '\n').encode()
            cls.body, cls.calls, cls.bindings = profile.object_bytes(
                runner, workspace, cls.args, cls.original, A, cls.approved, initial, selector=profile.SHIFT_SELECTOR)
            cls.linked_raw = runner.read_binary(f'{workspace}/f.elf')
            cls.linked = match.elf_image(cls.linked_raw)
        cls.rows[0]['instrs'] = owner.refine(cls.body, A, initial)['instrs']
        cls.mapping, cls.index = cls.indexes(cls.rows)
        rom = bytearray(cls.approved)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        (cls.root / 'config/functions.json').write_bytes(cls.mapping)
        (cls.root / 'symbols/functions.txt').write_bytes(cls.index)
        (cls.root / 'config/data_symbols.json').write_text('{}\n')
        cls.rom_path = cls.root / 'baserom.bin'
        cls.rom_path.write_bytes(cls.rom)
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.rom_path))
        cls.environment.start()
        cls.addClassCleanup(cls.environment.stop)
        cls.manifest, cls.instructions = profile.verify(cls.body, A, cls.rom, cls.mapping, cls.index,
                                                       cls.calls, cls.bindings, selector=profile.SHIFT_SELECTOR)
        retained = os.environ.get('FFTA_SIGNED_DIVIDEND_RETAIN')
        if retained:
            destination = Path(retained)
            destination.mkdir(parents=True, exist_ok=True)
            for name, data in (('caller.c', SOURCE.encode()), ('original.o', cls.raw),
                               ('compiler.s', cls.assembly), ('linked.elf', cls.linked_raw)):
                path = destination / name
                if path.exists():
                    if path.read_bytes() != data:
                        raise ValueError('retained fixture differs from natural original')
                else:
                    path.write_bytes(data)

    @staticmethod
    def indexes(rows):
        return ((json.dumps(rows, indent=2) + '\n').encode(),
                ''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                        f'{int(r["end"], 16)-int(r["rom"], 16)} {r["instrs"]} return\n'
                        for r in rows).encode())

    def native(self, **changes):
        values = dict(data=self.body, address=A, rom=self.rom, mapping=self.mapping, index=self.index,
                      calls=self.calls, bindings=self.bindings)
        values.update(changes)
        return profile.verify(**values, selector=profile.SHIFT_SELECTOR)

    def machine(self, code):
        """Direct native negative bytes, with no source/ELF admission or assembler."""
        data, calls, bindings = bytearray(), {}, {}
        targets = {'div': profile.quotient.ADDRESS, 'mod': profile.remainder.ADDRESS, 'ordinary': B}
        for token in code:
            if type(token) is int:
                data += struct.pack('<H', token)
            else:
                site, target = A + len(data), targets[token]
                delta = target - site - 4
                data += struct.pack('<HH', 0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
                calls[site] = target
                if token != 'ordinary':
                    bindings[site] = '__divsi3' if token == 'div' else '__modsi3'
        rows = copy.deepcopy(self.rows)
        rows[0]['end'] = f'0x{A + len(data):08X}'
        rows += [{'rom': f'0x{B:08X}', 'end': f'0x{B+2:08X}', 'mode': 'thumb', 'instrs': 1}]
        mapping, index = self.indexes(rows)
        rom = bytearray(self.rom)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        return self.native(data=bytes(data), rom=bytes(rom), mapping=mapping, index=index,
                           calls=calls, bindings=bindings)

    def test_natural_shift_and_old_selector_refusal(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__divsi3', '__modsi3'})
        self.assertEqual((len(self.body), len(self.instructions)), (44, 20))
        self.assertEqual(self.manifest['schema'], profile.SHIFT_SCHEMA)
        self.assertEqual(self.manifest['logical_shift_signed16'], [[6, 'r5', 'r0', 17]])
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            profile.verify(self.body, A, self.rom, self.mapping, self.index, self.calls, self.bindings)

    def test_immediate_shift_boundaries_and_register_copy(self):
        head = [0xB510, 0x2004, 0x2107, 'div']
        tail = [0x2103, 'mod', 0xBC10, 0xBC02, 0x4708]
        for shift in (17, 18, 31, 32):
            with self.subTest(shift=shift):
                opcode = 0x0800 | ((shift % 32) << 6) | (2 << 3) | 4
                manifest, _ = self.machine(head + [opcode, 0x1C20] + tail)
                self.assertEqual(manifest['logical_shift_signed16'], [[10, 'r4', 'r2', shift]])
        for operation in (0x0C10, 0x0850, 0x40D0, 0x0450, 0x1450, 0x8810):
            with self.subTest(operation=operation), self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
                self.machine(head + [operation] + tail)

    def test_clobber_call_and_one_arm_unknown_are_refused(self):
        head = [0xB510, 0x2004, 0x2107, 'div']
        tail = [0x2103, 'mod', 0xBC10, 0xBC02, 0x4708]
        for middle in ([0x0C50, 0x4610], [0x0C50, 'ordinary'],
                       [0x2A00, 0xD001, 0x0C50, 0xE000, 0x4610]):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
                self.machine(head + middle + tail)
        self.machine(head + [0x2A00, 0xD001, 0x0C50, 0xE000, 0x0C90] + tail)
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            self.machine(head + [0x0C50, 0x2100, 'mod', 0xBC10, 0xBC02, 0x4708])

    def test_provenance_dependencies_and_frame_evidence_are_exact(self):
        for key, value in (('logical_shift_signed16', [[6, 'r5', 'r0', 16]]),
                           ('logical_shift_signed16', []), ('schema', profile.SCHEMA)):
            changed = copy.deepcopy(self.manifest); changed[key] = value
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=changed)
        for key in ('quotient', 'remainder'):
            changed = copy.deepcopy(self.manifest); changed['dependencies'][key][0][2] = '0' * 64
            with self.subTest(dependency=key), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=changed)
        with self.assertRaises(ValueError):
            self.machine([0xB510, 0x2004, 0x2107, 'div', 0x0C50, 0x2103, 'mod', 0xBC02, 0x4708])

    def test_new_selector_retains_helper_relocation_and_call_identity(self):
        for address in (profile.quotient.ADDRESS, profile.remainder.ADDRESS, 0x0814274C):
            rom = bytearray(self.rom); rom[address-match.ROM_BASE] ^= 1
            with self.subTest(helper=address), self.assertRaises(ValueError):
                self.native(rom=bytes(rom))
        changed = dict(self.calls); changed[next(iter(changed))] += 2
        with self.assertRaises(ValueError):
            self.native(calls=changed)
        for name, value in (('name', 'func_08142950'), ('value', 2), ('type', 1)):
            image = copy.deepcopy(self.original)
            for symbol in image['symbols']:
                if symbol['name'] == '__modsi3':
                    symbol[name] = value
            with self.subTest(field=name), self.assertRaises(ValueError):
                match.call_bindings(image, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                    divsi3_bindings={}, modsi3_bindings={}, signed_runtime_profile=profile.SHIFT_SELECTOR)
        image = copy.deepcopy(self.original)
        image['relocations'] = []
        with self.assertRaises(ValueError):
            match.call_bindings(image, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                divsi3_bindings={}, modsi3_bindings={}, signed_runtime_profile=profile.SHIFT_SELECTOR)

    def test_native_match_fresh_report_status_and_forged_provenance(self):
        options = ['--root', str(self.root), '--signed-runtime-profile', profile.SHIFT_SELECTOR, f'{A:08X}']
        output = io.StringIO()
        with patch.object(sys, 'argv', ['match.py'] + options), redirect_stdout(output):
            self.assertEqual(match.main(), 0)
        self.assertIn('verdict MATCH - byte identical', output.getvalue())
        report = (self.root / 'docs/match/08010000.md').read_text()
        self.assertIs(profile.selected(report), True)
        self.assertTrue(evidence.report_matches(report, self.root, A))
        for verify in (False, True):
            result = status.collect(str(self.root), verify=verify)
            self.assertEqual((result[1], result[3], result[4]), (1, 44, []))
        self.assertFalse(evidence.report_matches(report.replace(profile.SHIFT_SELECTOR, profile.SELECTOR), self.root, A))
        prefix = '* signed runtime evidence: `'
        line = next(row for row in report.splitlines() if row.startswith(prefix))
        saved = json.loads(line[len(prefix):-1])
        saved['manifest']['logical_shift_signed16'][0][3] = 16
        encoded = profile.text(saved)
        forged = report.replace(line, prefix + encoded + '`')
        from test_signed_divmod_profile import rehash_report
        self.assertFalse(evidence.report_matches(rehash_report(forged, encoded), self.root, A))
        self.source.write_text(SOURCE + '\n/* changed source */\n')
        try:
            self.assertFalse(evidence.report_matches(report, self.root, A))
        finally:
            self.source.write_text(SOURCE)
        retained = os.environ.get('FFTA_SIGNED_DIVIDEND_RETAIN')
        if retained:
            (Path(retained) / 'fresh-report.md').write_text(report)


if __name__ == '__main__':
    unittest.main()

