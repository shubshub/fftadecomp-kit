"""Separate canonical numeric div/mod composition and unchanged prior gates."""
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
    short narrowed = value;
    if (divisor == 0)
        return 0;
    return narrowed / 7 + narrowed % divisor;
}
'''


class SignedDivmodTests(unittest.TestCase):
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
                runner, workspace, cls.args, cls.original, A, cls.approved, initial)
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
                                                       cls.calls, cls.bindings)
        retained = os.environ.get('FFTA_SIGNED_DIVMOD_RETAIN')
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
        return profile.verify(**values)

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

    def test_natural_original_ELF_and_complete_native_positive(self):
        self.assertEqual(struct.unpack_from('<H', self.raw, 16)[0], 1)
        self.assertEqual(set(self.bindings.values()), {'__divsi3', '__modsi3'})
        self.assertEqual((len(self.body), len(self.instructions)), (52, 24))
        self.assertEqual(self.manifest['divisors'], [[20, 7]])
        self.assertEqual(self.manifest['remainder_operands'], [[34, 'signed16', 'nonzero']])
        self.assertEqual(self.manifest['frame']['preserved'], 'r4-r11,sp,entry-lr')
        self.assertEqual(self.native(manifest=self.manifest)[0], self.manifest)

    def test_selector_isolation_and_both_actual_runtime_sets(self):
        for bindings in ({}, {site: name for site, name in self.bindings.items() if name == '__divsi3'},
                         {site: name for site, name in self.bindings.items() if name == '__modsi3'},
                         {site: 'func_08142950' if name == '__modsi3' else name for site, name in self.bindings.items()}):
            with self.subTest(bindings=bindings), self.assertRaises(ValueError):
                self.native(bindings=bindings)
        context = (self.rom, self.mapping, self.index, self.bindings, {})
        for options in ({'divsi3_context': (self.rom, self.mapping, {}, {})}, {'double_context': ()},
                        {'signed_quotient_profile': profile.quotient.FRAMED_SELECTOR},
                        {'stack_pointer_compare_profile': match.sp_compare.SELECTOR}, {'buffer_proof': object()}):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'isolated canonical Thumb'):
                match.verify_leaf_instructions(self.body, A, True, self.calls,
                    signed_runtime_context=context, **options)

    def test_standalone_and_real_software_double_gates_unchanged(self):
        div = {s: n for s, n in self.bindings.items() if n == '__divsi3'}
        mod = {s: n for s, n in self.bindings.items() if n == '__modsi3'}
        with self.assertRaisesRegex(ValueError, 'isolated direct-call'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                divsi3_context=(self.rom, self.mapping, div, {}), modsi3_context=(self.rom, self.mapping, mod))
        with self.assertRaisesRegex(ValueError, 'excludes other runtimes'):
            match.verify_leaf_instructions(self.body, A, True, self.calls,
                divsi3_context=(self.rom, self.mapping, div, {}))
        double_rows = copy.deepcopy(self.rows)
        indexed = {int(row['rom'], 16) for row in double_rows}
        double_rows += [{'rom': f'0x{lo:08X}', 'end': f'0x{hi:08X}', 'mode': 'thumb', 'instrs': count}
                        for lo, hi, count, _ in match.software_double.IDENTITIES if lo not in indexed]
        double_mapping, double_index = self.indexes(double_rows)
        with self.assertRaisesRegex(ValueError, 'incomplete or mixed'):
            match.software_double.verify_context(self.body, A, self.calls,
                (self.rom, double_mapping, double_index, self.bindings))
        with self.assertRaisesRegex(ValueError, 'excludes other runtime'):
            match.call_bindings(self.original, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                divsi3_bindings={}, modsi3_bindings={})

    def test_exact_manifest_dependencies_operands_calls_and_frame(self):
        mutations = []
        for key, value in (('calls', self.manifest['calls'][:1]), ('divisors', [[20, 8]]),
                           ('remainder_operands', [[34, 'signed32', 'unknown']])):
            changed = copy.deepcopy(self.manifest); changed[key] = value; mutations.append(changed)
        changed = copy.deepcopy(self.manifest); changed['dependencies']['quotient'][0][2] = '0' * 64; mutations.append(changed)
        changed = copy.deepcopy(self.manifest); changed['frame']['preserved'] = 'assumed'; mutations.append(changed)
        changed = copy.deepcopy(self.manifest); changed['partition']['code_bytes'] -= 2; mutations.append(changed)
        for changed in mutations:
            with self.subTest(manifest=changed), self.assertRaisesRegex(ValueError, 'manifest differs'):
                self.native(manifest=changed)

    def test_missing_or_tampered_helpers_and_mapping(self):
        for start in (profile.quotient.ADDRESS, profile.remainder.ADDRESS, 0x0814274C):
            with self.subTest(start=start), self.assertRaises(ValueError):
                rom = bytearray(self.rom); rom[start-match.ROM_BASE] ^= 1
                self.native(rom=bytes(rom))
        for start in (profile.quotient.ADDRESS, profile.remainder.ADDRESS, 0x0814274C):
            rows = [row for row in self.rows if int(row['rom'], 16) != start]
            mapping, index = self.indexes(rows)
            with self.subTest(missing=start), self.assertRaises(ValueError):
                self.native(mapping=mapping, index=index)
        bad = dict(self.calls); bad[next(iter(bad))] += 2
        with self.assertRaises(ValueError): self.native(calls=bad)

    def test_original_symbol_addend_relocation_and_linked_effects(self):
        for name, value in (('name', 'func_08142950'), ('value', 2), ('type', 1)):
            image = copy.deepcopy(self.original)
            for symbol in image['symbols']:
                if symbol['name'] == '__modsi3': symbol[name] = value
            with self.subTest(field=name), self.assertRaises(ValueError):
                match.call_bindings(image, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                    divsi3_bindings={}, modsi3_bindings={}, signed_runtime_profile=profile.SELECTOR)
        image = copy.deepcopy(self.original)
        data = bytearray(image['text']); data[34] ^= 1; image['text'] = bytes(data)
        with self.assertRaises(ValueError):
            match.call_bindings(image, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                divsi3_bindings={}, modsi3_bindings={}, signed_runtime_profile=profile.SELECTOR)
        for missing in (False, True):
            image = copy.deepcopy(self.original)
            section_id = image['relocations'][0]
            section = list(image['sections'][section_id])
            entries = bytearray(image['section_data'][section_id])
            for position in range(0, len(entries), 8):
                offset, info = struct.unpack_from('<II', entries, position)
                if offset == 34:
                    if missing:
                        del entries[position:position+8]
                        section[5] -= 8
                    else:
                        struct.pack_into('<I', entries, position+4, (info & ~255) | 2)
                    break
            image['sections'][section_id] = tuple(section)
            image['section_data'][section_id] = bytes(entries)
            with self.subTest(missing_relocation=missing), self.assertRaises(ValueError):
                match.call_bindings(image, f'func_{A:08X}', A, self.mapping, len(self.rom), self.rom,
                    divsi3_bindings={}, modsi3_bindings={}, signed_runtime_profile=profile.SELECTOR)
        div, mod = {}, {}
        calls, targets, literals = match.call_bindings(self.original, f'func_{A:08X}', A, self.mapping,
            len(self.rom), self.rom, divsi3_bindings=div, modsi3_bindings=mod, signed_runtime_profile=profile.SELECTOR)
        linked = copy.deepcopy(self.linked)
        changed = bytearray(linked['text']); changed[0] ^= 1; linked['text'] = bytes(changed)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, linked, f'func_{A:08X}', A, calls, targets,
                literals, divsi3_bindings=div, modsi3_bindings=mod, signed_runtime_profile=profile.SELECTOR)
        with self.assertRaises(ValueError):
            match.linked_function_bytes(self.original, self.linked, f'func_{A:08X}', A, calls, targets,
                literals, divsi3_bindings=div, modsi3_bindings=mod, signed_runtime_profile='other')

    def test_zero_unknown_clobbered_and_path_varying_quotient_divisors(self):
        tail = [0x2004, 'div', 0x2004, 0x2103, 'mod', 0xBC10, 0xBC02, 0x4708]
        prefixes = [[0xB510, 0x2100], [0xB510], [0xB510, 0x2107, 'ordinary'],
                    [0xB510, 0x2A00, 0xD001, 0x2107, 0xE000, 0x2108]]
        for prefix in prefixes:
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'CFG-proven positive signed32'):
                self.machine(prefix + tail)

    def test_zero_unknown_clobbered_and_one_arm_remainder_facts(self):
        head = [0xB510, 0x2107, 0x2004, 'div']
        tail = ['mod', 0xBC10, 0xBC02, 0x4708]
        operands = [[0x2004, 0x2100], [0x2004], [0x4610, 0x2103],
                    [0x2004, 0x2103, 'ordinary'],
                    [0x2004, 0x2A00, 0xD001, 0x2103, 0xE000, 0x2100],
                    [0x2103, 0x2A00, 0xD001, 0x2004, 0xE000, 0x4610]]
        for middle in operands:
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
                self.machine(head + middle + tail)

    def test_SP_frame_saved_slots_and_one_bad_return(self):
        head = [0xB510, 0x2107, 0x2004, 'div', 0x2004, 0x2103, 'mod']
        for code in ([0xB510, 0xB081] + head[1:] + [0xB001, 0xBC10, 0xBC02, 0x4708],
                     [0xB510, 0x9000] + head[1:] + [0xBC10, 0xBC02, 0x4708],
                     head + [0xBC02, 0x4708],
                     head + [0x2A00, 0xD002, 0xBC10, 0xBC02, 0x4708, 0xBC02, 0x4708]):
            with self.subTest(code=code), self.assertRaises(ValueError): self.machine(code)

        with self.assertRaisesRegex(ValueError, 'unproved address literal provenance'):
            self.machine(head + [0x4C02, 0xBC10, 0xBC02, 0x4708, 0x0000, 0x0000, 0x0201])

    def test_native_match_fresh_report_status_and_source_binding(self):
        options = ['--root', str(self.root), '--signed-runtime-profile', profile.SELECTOR, f'{A:08X}']
        output = io.StringIO()
        with patch.object(sys, 'argv', ['match.py'] + options), redirect_stdout(output):
            self.assertEqual(match.main(), 0)
        self.assertIn('verdict MATCH - byte identical', output.getvalue())
        report_path = self.root / 'docs/match/08010000.md'
        report = report_path.read_text()
        self.assertTrue(evidence.report_matches(report, self.root, A))
        self.assertEqual(status.collect(str(self.root), verify=False)[1:4:2], (1, 52))
        result = status.collect(str(self.root), verify=True)
        self.assertEqual((result[1], result[3], result[4]), (1, 52, []))
        self.source.write_text(SOURCE + '\n/* changed source */\n')
        try: self.assertFalse(evidence.report_matches(report, self.root, A))
        finally: self.source.write_text(SOURCE)
        (self.root / 'include/changed.h').write_text('typedef int changed;\n')
        try: self.assertFalse(evidence.report_matches(report, self.root, A))
        finally: (self.root / 'include/changed.h').unlink()
        retained = os.environ.get('FFTA_SIGNED_DIVMOD_RETAIN')
        if retained: (Path(retained) / 'fresh-report.md').write_text(report)

    def test_forged_rehashed_report_and_mixed_schema_refused(self):
        report = profile.render(profile.build(self.root, A))
        self.assertFalse(evidence.report_matches(report.replace(profile.SCHEMA, profile.quotient.SCHEMA), self.root, A))
        self.assertFalse(evidence.report_matches(report + f'* verification: `{profile.quotient.SCHEMA}`\n', self.root, A))
        prefix = '* signed runtime evidence: `'
        line = next(row for row in report.splitlines() if row.startswith(prefix))
        saved = json.loads(line[len(prefix):-1]); saved['manifest']['frame']['preserved'] = 'assumed'
        changed = profile.text(saved)
        forged = report.replace(line, prefix + changed + '`')
        forged = rehash_report(forged, changed)
        self.assertFalse(evidence.report_matches(forged, self.root, A))


def rehash_report(report, encoded):
    prefix = '* signed runtime proof SHA-256: `'
    old = next(line for line in report.splitlines() if line.startswith(prefix))
    return report.replace(old, prefix + hashlib.sha256(encoded.encode()).hexdigest() + '`')


if __name__ == '__main__':
    unittest.main()
