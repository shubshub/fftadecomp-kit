"""Explicit target-state MOD composition; bounded numeric profiles stay strict."""
import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest.mock import patch
import test_software_double_division_profile as division_fixture

BASE = division_fixture.BASE
match, profile = division_fixture.match, division_fixture.profile
SOURCE = '''int func_08000000(double value, int numerator, int denominator)
{
    return (int)(value + (double)(numerator / denominator)) % denominator;
}
'''


class SoftwareDoubleTargetRemainderTests(division_fixture.SoftwareDoubleDivisionModTests):
    def fixture(self, source=SOURCE, *, target=True, assembly=None):
        (self.root / 'src/08000000.c').write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            if assembly is None:
                _, _, self.original = match.compile_object(
                    runner, workspace, self.args, self.root, BASE, 'src/08000000.c')
            else:
                text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n"
                        ".global func_08000000\n.type func_08000000, %function\n"
                        ".thumb_func\nfunc_08000000:\n" + assembly +
                        "\n.size func_08000000, . - func_08000000\n")
                path = Path(workspace) / 'f.s'
                path.write_text(text)
                subprocess.run([self.args.assembler, '-mthumb-interwork', str(path),
                                '-o', str(Path(workspace) / 'f.o')],
                               check=True, capture_output=True, timeout=120)
                self.original = match.elf_image((Path(workspace) / 'f.o').read_bytes())
            symbol, _ = match.function_record(self.original, 'func_08000000', BASE, True)
            self.indexes(symbol['size'], 1)
            self.body, self.calls, self.bindings = profile.object_bytes(
                runner, workspace, self.args, self.original, BASE, self.mapping,
                self.runtime_rom, self.index)
            self.linked = match.elf_image((Path(workspace) / 'f.elf').read_bytes())
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        context = (self.rom, self.mapping, self.index, self.bindings) + ((True,) if target else ())
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls, double_context=context)
        self.indexes(len(self.body), len(self.instructions))
        (self.root / 'config/functions.json').write_bytes(self.mapping)
        (self.root / 'symbols/functions.txt').write_bytes(self.index)
        self.manifest = profile.make_manifest(
            self.calls, BASE, self.bindings, self.instructions, remainder_target=target)

    def native_report(self, *, target=True):
        opening, reading = self.patched_rom()
        argv = ['match.py', '--root', str(self.root), '--software-double-profile', profile.SELECTOR]
        if target:
            argv += ['--software-double-remainder-profile', profile.REMAINDER_TARGET_SELECTOR]
        argv += ['0x08000000']
        with opening, reading, patch.object(sys, 'argv', argv), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / 'docs/match/08000000.md').read_text()

    def test_dynamic_natural_original_elf_full_native_and_source_replay(self):
        self.fixture()
        self.assertEqual(set(self.bindings.values()),
                         {'__divsi3', '__modsi3', '__floatsidf', '__adddf3', '__fixdfsi'})
        undefined = {s['name'] for s in self.original['symbols'] if s['name'] and not s['section']}
        self.assertEqual(undefined, set(self.bindings.values()))
        self.assertNotIn('remainder', self.manifest)
        self.assertEqual(self.manifest['target_remainder']['operands'], 'entry-register-state')
        self.assertEqual(self.manifest['target_remainder']['semantics'], 'target-machine-state-v1')
        self.assertEqual(len(self.verify()), len(self.instructions))
        report = self.native_report()
        self.assertIn("* software double: " + profile.summary(self.manifest), report)
        self.assertNotEqual(profile.summary(self.manifest), profile.SUMMARY)
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(profile.report_matches(report, self.root, BASE))
            self.assertFalse(profile.report_matches(
                report.replace(profile.summary(self.manifest), profile.SUMMARY), self.root, BASE))
            source = self.root / 'src/08000000.c'
            source.write_text(SOURCE.replace('% denominator', '% 7'))
            self.assertFalse(profile.report_matches(report, self.root, BASE))

    def test_old_bounded_policy_and_manifest_format_are_unchanged(self):
        self.fixture()
        with self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
            match.verify_leaf_instructions(self.body, BASE, True, self.calls,
                double_context=(self.rom, self.mapping, self.index, self.bindings))
        bounded = SOURCE.replace('(int)(value', '(short)(int)(value').replace('% denominator', '% 7')
        self.fixture(bounded, target=False)
        self.assertIn('remainder', self.manifest)
        self.assertNotIn('target_remainder', self.manifest)
        self.assertEqual(self.manifest['remainder']['dividend'], 'signed16')
        self.assertEqual(self.manifest['remainder']['divisor'], 'nonzero')
        old = profile.make_manifest(self.calls, BASE, self.bindings, self.instructions)
        self.assertEqual(old, self.manifest)
        self.verify()
        self.native_report(target=False)
        for unsafe in (SOURCE, bounded.replace('% 7', '% denominator')):
            with self.subTest(source=unsafe), self.assertRaisesRegex(ValueError, 'signed16 r0 and nonzero r1'):
                self.fixture(unsafe, target=False)

    def test_explicit_mode_requires_double_canonical_remainder_and_boolean_context(self):
        self.fixture()
        for value in (False, 1, 'target-state-v1', None):
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.verify_context(self.body, BASE, self.calls,
                    (self.rom, self.mapping, self.index, self.bindings, value))
        for value in (1, 'target-state-v1', None):
            with self.subTest(value=value), self.assertRaises(ValueError):
                profile.make_manifest(self.calls, BASE, self.bindings, self.instructions,
                                      remainder_target=value)
        for source in ('double func_08000000(double v,int n,int d){return v+(double)(n/d);}',
                       'int func_08000000(int n,int d){return n%d;}'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.fixture(source)
        self.fixture()
        opening, reading = self.patched_rom()
        with opening, reading, patch.object(sys, 'argv', ['match.py', '--root', str(self.root),
                '--software-double-remainder-profile', profile.REMAINDER_TARGET_SELECTOR, '0x08000000']), \
                self.assertRaisesRegex(SystemExit, 'explicit software-double profile'):
            match.main()

    def test_exact_manifest_record_rejects_stale_or_numeric_provenance(self):
        self.fixture()
        for kind in ('missing', 'runtime', 'semantics', 'operands', 'body', 'count', 'site', 'extra', 'bounded'):
            manifest = copy.deepcopy(self.manifest)
            record = manifest['target_remainder']
            if kind == 'missing': del manifest['target_remainder']
            elif kind in ('runtime', 'semantics', 'operands'): record[kind] = 'unproved'
            elif kind == 'body': record['dependencies'][0][3] = '0' * 64
            elif kind == 'count': record['dependencies'][0][2] = 103
            elif kind == 'site': record['calls'][0] += 2
            elif kind == 'extra': record['extra'] = True
            else: manifest['remainder'] = profile.remainder_record(self.calls, BASE, self.bindings)
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.verify(manifest)

    def test_original_alias_wrong_link_and_unsupported_mix_are_refused(self):
        self.fixture()
        for name in ('func_08142950', 'func_08142951', '__modsi3_alias', '__div0', '__umodsi3'):
            original = copy.deepcopy(self.original)
            next(s for s in original['symbols'] if s['name'] == '__modsi3')['name'] = name
            runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
            with self.subTest(name=name), runner.workspace() as workspace, self.assertRaises(ValueError):
                profile.object_bytes(runner, workspace, self.args, original, BASE,
                                     self.mapping, self.runtime_rom, self.index)
        site = next(s for s,n in self.bindings.items() if n == '__modsi3')
        for wrong in (0x08142952, 0x0814274C, 0x081426B8):
            linked = copy.deepcopy(self.linked)
            raw = bytearray(linked['text']); delta = wrong-site-4
            struct.pack_into('<HH', raw, site-BASE,
                             0xF000 | ((delta >> 12) & 0x7FF), 0xF800 | ((delta >> 1) & 0x7FF))
            linked['text'] = bytes(raw)
            next(s for s in linked['symbols'] if s['name'] == '__modsi3')['value'] = wrong | 1
            with self.subTest(wrong=wrong), self.assertRaises(ValueError):
                match.linked_function_bytes(self.original, linked, 'func_08000000', BASE,
                    self.calls, {n: profile.call_target(n) if n != '__modsi3' else match.modsi3.ADDRESS
                                 for n in self.bindings.values()}, double_bindings=self.bindings)
            calls = dict(self.calls); calls[site] = wrong
            with self.assertRaises(ValueError):
                match.verify_leaf_instructions(bytes(raw[:len(self.body)]), BASE, True, calls,
                    double_context=(self.rom, self.mapping, self.index, self.bindings, True))
        with self.assertRaises(ValueError):
            self.fixture('double func_08000000(double v,unsigned n,unsigned d){return v+(double)(n%d);}')

    def test_fixed_frame_restore_bounds_and_alias_guards_survive_opt_in(self):
        source = """extern double func_08000200(double);
int func_08000000(double v,int n,int d) {
    double a=func_08000200(v),b=func_08000200(v+1.0);
    double c=func_08000200(v+2.0),e=func_08000200(v+3.0);
    return (int)(a+b+c+e+v+(double)(n/d))%d;
}
"""
        self.fixture(source)
        self.assertTrue(self.manifest['frame'])
        self.verify()
        self.native_report()
        for assembly in (
            "push {lr}\nsub sp,#4\nbl __adddf3\nbl __fixdfsi\n"
            "movs r1,#7\nbl __modsi3\npop {r1}\nbx r1",
            "push {lr}\nsub sp,#4\nstr r0,[sp,#4]\nbl __adddf3\nbl __fixdfsi\n"
            "movs r1,#7\nbl __modsi3\nadd sp,#4\npop {r1}\nbx r1",
            "push {r4,lr}\nsub sp,#4\nmov r4,sp\nmovs r0,r4\nbl __adddf3\nbl __fixdfsi\n"
            "movs r1,#7\nbl __modsi3\nadd sp,#4\npop {r4}\npop {r1}\nbx r1"):
            with self.subTest(assembly=assembly), self.assertRaises(ValueError):
                self.fixture(assembly=assembly)

    def test_full_mod_zero_path_identity_ownership_returns_and_writes_are_proven(self):
        self.fixture()
        import software_float_profile as floating
        proofs = profile.prove_remainder_closure(self.rom, self.mapping, self.index)
        start, zero = 0x08142950, 0x0814274C
        self.assertEqual(set(proofs), {start, zero})
        self.assertEqual(set(proofs[start]['returns']), {0x08142A12, 0x08142A1C})
        self.assertFalse(proofs[start]['writes']); self.assertFalse(proofs[start]['stack_reads'])
        for address in (start, zero):
            rom = bytearray(self.rom); rom[address-BASE] ^= 1
            with self.subTest(address=address), self.assertRaises(ValueError):
                profile.verify(self.body, BASE, bytes(rom), self.mapping, self.index, self.manifest)
        entries = json.loads(self.mapping)
        for kind in ('count', 'mode', 'missing_zero', 'duplicate', 'overlap', 'span'):
            changed = copy.deepcopy(entries)
            row = next(r for r in changed if r['rom'] == '0x08142950')
            if kind == 'count': row['instrs'] = 103
            elif kind == 'mode': row['mode'] = 'arm'
            elif kind == 'missing_zero': changed.remove(next(r for r in changed if r['rom'] == '0x0814274C'))
            elif kind == 'duplicate': changed.append(copy.deepcopy(row))
            elif kind == 'overlap': changed.append(dict(rom='0x08142952',end='0x08142954',mode='thumb',instrs=1))
            else: row['end'] = '0x08142A1C'
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                profile.verify(self.body, BASE, self.rom, json.dumps(changed).encode(), self.index, self.manifest)
        kwargs = dict(call_edges=((0x08142A16, zero),), scalar_entries=(start,), allowed_writes=())
        for returns in ((), (0x08142A12,), (0x08142A10,0x08142A1C)):
            with self.subTest(returns=returns), self.assertRaises(ValueError):
                floating.prove_runtime(self.rom, entries, start, 0x08142A1E, 102, {zero:proofs[zero]},
                                       thumb_pc_returns=returns, **kwargs)
        with self.assertRaises(ValueError):
            floating.prove_runtime(self.rom, entries, start, 0x08142A1E, 102, {},
                thumb_pc_returns=(0x08142A12,0x08142A1C), **kwargs)
        for site, word in ((0x08142A12,0x46A7), (0x08142A10,0xBC20), (0x08142A1C,0xBC01),
                           (0x08142956,0x6008)):
            rom = bytearray(self.rom); struct.pack_into('<H', rom, site-BASE, word)
            with self.subTest(site=site), self.assertRaises(ValueError):
                floating.prove_runtime(bytes(rom), entries, start, 0x08142A1E, 102, {zero:proofs[zero]},
                    thumb_pc_returns=(0x08142A12,0x08142A1C), **kwargs)


def load_tests(loader, tests, pattern):
    return unittest.TestSuite(SoftwareDoubleTargetRemainderTests(name)
                             for name in sorted(vars(SoftwareDoubleTargetRemainderTests))
                             if name.startswith('test_'))


if __name__ == '__main__': unittest.main()
