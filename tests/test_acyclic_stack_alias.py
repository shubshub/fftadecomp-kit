"""Exact bounded path states retain every ordinary acyclic Thumb obligation."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

import test_stack_alias_join_lifetime as fixtures

match = fixtures.match
BASE = fixtures.BASE
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import owner_admission_profile as owner
import match_evidence

SOURCE = '''unsigned int func_08010000(unsigned int choose, unsigned int value)
{
    unsigned int samples[2];
    unsigned int *selected;
    samples[0] = value;
    samples[1] = value + 1;
    if (choose)
        selected = samples;
    else
        selected = samples + 1;
    *selected += 3;
    return samples[0] + samples[1];
}
'''
ESCAPE_SOURCE = '''unsigned int func_08010000(unsigned int choose, unsigned int *output)
{
    unsigned int samples[2];
    unsigned int *selected;
    if (choose)
        selected = samples;
    else
        selected = samples + 1;
    *output = (unsigned int)selected;
    return choose;
}
'''


class AcyclicPathTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def verify(self, source, budget=4096):
        data = self.body(source)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {i.address: i.operands[0].imm for i in decoder.disasm(data, BASE)
                 if match.CS_GRP_CALL in i.groups}
        return match.verify_leaf_instructions(data, BASE, True, calls,
                                              acyclic_state_budget=budget)

    def joined(self, first='mov r4, sp', second='add r4, sp, #4', after='str r1, [r4]'):
        return ('push {r4, lr}\nsub sp, #8\ncmp r0, #0\nbeq second\n' + first +
                '\nb joined\nsecond:\n' + second + '\njoined:\n' + after +
                '\nadd sp, #8\npop {r4}\npop {r1}\nbx r1')

    def test_distinct_offsets_preserve_their_own_frame_bounds(self):
        source = self.joined()
        with self.assertRaisesRegex(ValueError, 'inconsistent stack aliases'):
            self.verify(source, None)
        self.verify(source)

    def test_one_unsafe_access_path_fails_in_both_branch_orders(self):
        for first, second in (('mov r4, sp', 'add r4, sp, #16'),
                              ('add r4, sp, #16', 'mov r4, sp')):
            with self.subTest(first=first), self.assertRaises(ValueError):
                self.verify(self.joined(first, second))

    def test_scalar_and_alias_escape_path_fails_in_both_branch_orders(self):
        for first, second in (('mov r4, sp', 'movs r4, #0'),
                              ('movs r4, #0', 'mov r4, sp')):
            with self.subTest(first=first), self.assertRaisesRegex(ValueError, 'use or escape'):
                self.verify(self.joined(first, second, 'str r4, [r2]'))

    def test_one_call_escape_path_cannot_be_erased_at_join(self):
        with self.assertRaisesRegex(ValueError, 'stack aliases cannot cross calls'):
            self.verify(self.joined(after='movs r0, r4\nbl callee'))

    def test_any_unbalanced_or_unproven_return_fails(self):
        for source in (
                'push {lr}\ncmp r0, #0\nbeq good\nbx lr\ngood:\npop {r1}\nbx r1',
                'push {lr}\ncmp r0, #0\nbeq good\npop {r1}\nbx r0\ngood:\npop {r1}\nbx r1'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.verify(source)

    def test_frame_depth_join_remains_rejected(self):
        source = ('push {lr}\ncmp r0, #0\nbeq joined\nsub sp, #4\n'
                  'joined:\nmovs r0, #0\npop {r1}\nbx r1')
        with self.assertRaises(ValueError):
            self.verify(source)

    def test_cycles_rejected_even_when_repeated_states_are_identical(self):
        source = 'loop:\ncmp r0, #0\nbne loop\nbx lr'
        self.verify(source, None)
        with self.assertRaisesRegex(ValueError, 'reject reachable CFG cycles'):
            self.verify(source)

    def test_state_budget_boundary_and_invalid_values(self):
        source = 'movs r0, #1\nbx lr'
        self.verify(source, 2)
        with self.assertRaisesRegex(ValueError, 'budget exhausted'):
            self.verify(source, 1)
        for budget in (True, False, 0, -1, 4097, 1.5, '4096'):
            with self.subTest(budget=budget), self.assertRaisesRegex(ValueError, 'integer in 1..4096'):
                self.verify(source, budget)

    def test_unsupported_profile_composition_fails_closed(self):
        data = self.body('bx lr')
        for options in ({'buffer_proof': object()}, {'switch_relocations': {}},
                        {'function_thunk_context': {}}, {'double_context': ()}):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, 'ordinary isolated Thumb'):
                match.verify_leaf_instructions(data, BASE, True, acyclic_state_budget=4096, **options)


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which('arm-none-eabi-as'), 'fixed compiler required')
class CompilerAdmissionTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    A = 0x08010000

    def compile(self, source):
        for name in ('src', 'include', 'compile', 'config', 'symbols', 'build'):
            (self.root / name).mkdir(exist_ok=True)
        (self.root / 'src/08010000.c').write_text(source)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        raw, data, image = match.compile_object(runner, str(self.root / 'compile'), args,
                                               self.root, self.A, 'src/08010000.c')
        self.assertEqual(image['type'], 1)
        self.assertFalse(image['relocations'])
        symbol, offset = match.function_record(image, 'func_08010000', self.A, True)
        self.assertEqual(offset, 0)
        self.assertLessEqual(symbol['size'], len(data))
        return raw, match.function_bytes(raw, data, 'func_08010000', self.A, True), image

    def preserve(self, name):
        target = os.environ.get('FFTA_ACYCLIC_TEST_ARTIFACTS')
        if target:
            destination = Path(target) / name
            destination.mkdir(parents=True, exist_ok=True)
            for file in (self.root / 'compile').iterdir():
                if file.is_file():
                    shutil.copyfile(file, destination / file.name)
            shutil.copyfile(self.root / 'src/08010000.c', destination / 'source.c')
            report = self.root / 'docs/match/08010000.md'
            if report.exists():
                shutil.copyfile(report, destination / 'report.md')

    def test_fixed_O2_full_original_elf_match_report_status_and_rebuild(self):
        raw, data, _ = self.compile(SOURCE)
        self.assertEqual(len(data), 36)
        with self.assertRaisesRegex(ValueError, 'inconsistent stack aliases'):
            match.verify_leaf_instructions(data, self.A, True)
        instructions = match.verify_leaf_instructions(data, self.A, True, acyclic_state_budget=4096)
        self.assertEqual(len(instructions), 18)
        rows = [{'rom': f'0x{self.A:08X}', 'end': f'0x{self.A+len(data):08X}',
                 'mode': 'thumb', 'instrs': len(instructions)}]
        (self.root / 'config/functions.json').write_text(json.dumps(rows) + '\n')
        (self.root / 'symbols/functions.txt').write_text(
            f'{self.A:08X} {self.A+len(data):08X} {len(data)} {len(instructions)} return\n')
        (self.root / 'config/data_symbols.json').write_text('{}\n')
        (self.root / 'baserom.bin').write_bytes(bytes(self.A-BASE) + data)
        command = [sys.executable, str(Path(match.__file__)), '--root', str(self.root),
                   f'{self.A:08X}']
        default = subprocess.run(command + ['--no-write'], capture_output=True, text=True)
        self.assertNotEqual(default.returncode, 0)
        self.assertIn('inconsistent stack aliases', default.stdout + default.stderr)
        native = subprocess.run(command + ['--owner-runtime-profile', owner.ACYCLIC_SELECTOR],
                                capture_output=True, text=True)
        self.assertEqual(native.returncode, 0, native.stdout + native.stderr)
        self.assertIn('verdict MATCH - byte identical', native.stdout)
        report = (self.root / 'docs/match/08010000.md').read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, self.A))
        self.assertEqual(owner.selector_for_report(report), owner.ACYCLIC_SELECTOR)
        result = owner.build(self.root, self.A, selector=owner.ACYCLIC_SELECTOR)
        self.assertEqual(result[8], raw)
        self.assertEqual(owner.render(self.A, result), report)
        wrong = copy.deepcopy(result[1])
        wrong['proof']['state_budget'] -= 1
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(data, self.A, result[6], result[3], result[4], result[5], wrong,
                         bindings=result[1]['bindings'], selector=owner.ACYCLIC_SELECTOR)
        self.assertFalse(owner.report_matches(report.replace('"state_budget":4096',
                                                              '"state_budget":4095'), self.root, self.A))
        self.assertFalse(owner.report_matches(report.replace(owner.ACYCLIC_SCHEMA,
                                                              owner.SCHEMA), self.root, self.A))
        import status
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(report, self.root, self.A),
                         ['--owner-runtime-profile', owner.ACYCLIC_SELECTOR])
        totals = status.collect(str(self.root), True, quiet=True)
        self.assertEqual((totals[1], totals[3], totals[4]), (1, len(data), []))
        self.assertEqual(rebuild.compiled_rebuild(self.root), 0)
        self.assertEqual((self.root / 'compile/f.o').read_bytes(), raw)
        self.preserve('compiler-positive')

    def test_fixed_O2_actual_pointer_escape_is_rejected(self):
        _, data, _ = self.compile(ESCAPE_SOURCE)
        with self.assertRaisesRegex(ValueError, 'use or escape'):
            match.verify_leaf_instructions(data, self.A, True, acyclic_state_budget=4096)
        self.preserve('compiler-escape-negative')


if __name__ == '__main__':
    unittest.main(verbosity=2)
