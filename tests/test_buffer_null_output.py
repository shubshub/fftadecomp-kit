import argparse
import json
import os
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import test_buffer_index as fixtures

BASE = match.ROM_BASE


class BufferNullOutputTests(unittest.TestCase):
    def setUp(self):
        self.fixture_case = fixtures.BufferIndexTests('runTest')
        self.fixture_case.setUp()
        self.addCleanup(self.fixture_case.doCleanups)
        self.root = self.fixture_case.root

    def fixture(self, operation, **kwargs):
        return self.fixture_case.fixture(operation, **kwargs)

    def test_optional_output_null_test_and_legacy_refusal(self):
        operation = 'cmp r4, #0\nbeq done\nstrh r0, [r4]\ndone:'
        proof = self.fixture(operation)
        self.assertEqual(set(proof.dependencies), {BASE + 0x100})
        with self.assertRaisesRegex(ValueError, 'unsupported buffer pointer use or escape'):
            self.fixture(operation, stack_arguments=False)

    def test_copy_and_stack_passed_output_null_test(self):
        self.fixture('movs r5, r4\ncmp r5, #0\nbeq done\nstrh r0, [r5]\ndone:')
        caller = ('push {r4, lr}\nsub sp, #12\nadd r1, sp, #8\nstr r1, [sp]\n'
                  'movs r1, #0\nbl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0')
        self.fixture('ldr r4, [sp, #12]\ncmp r4, #0\nbeq done\n'
                     'strh r0, [r4]\ndone:', caller=caller)

    def test_nonzero_register_and_other_pointer_tests_rejected(self):
        for operation in ('cmp r4, #1', 'movs r2, #0\ncmp r4, r2',
                          'tst r4, r4', 'cmn r4, r1'):
            with self.subTest(operation=operation), self.assertRaisesRegex(
                    ValueError, 'unsupported buffer pointer use or escape'):
                self.fixture(operation)

    def test_wide_null_compare_rejected(self):
        with self.assertRaises(ValueError):
            self.fixture('cmp.w r4, #0', arch='armv7-m')

    def test_null_test_does_not_discard_alias_or_skip_either_branch(self):
        for operation in ('cmp r4, #0\nbeq done\nstrh r0, [r4, #8]\ndone:',
                          'cmp r4, #0\nbne done\nstrh r0, [r4, #8]\ndone:'):
            with self.subTest(operation=operation), self.assertRaisesRegex(
                    ValueError, 'unaligned or outside allocated local words'):
                self.fixture(operation)

    def test_null_test_does_not_allow_escape_or_protected_access(self):
        for operation in ('cmp r4, #0\nstr r4, [sp]',
                          'cmp r4, #0\nstr r4, [r4]',
                          'cmp r4, #0\nmov lr, r4'):
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.fixture(operation)
        caller = ('push {r4, lr}\nsub sp, #12\nmov r1, sp\nstr r1, [sp, #4]\n'
                  'movs r0, #0\nbl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0')
        with self.assertRaisesRegex(ValueError, 'overlaps a pointer-bearing argument slot'):
            self.fixture('cmp r4, #0\nbeq done\nstrh r0, [r4, #4]\ndone:', caller=caller)

    def test_natural_optional_outputs_original_elf_and_report_replay(self):
        for directory in ('config', 'src', 'include', 'build', 'symbols'):
            (self.root / directory).mkdir()
        source = self.root / 'src/08000000.c'
        source.write_text(
            'extern void func_08000100(unsigned value, unsigned second,\n'
            '    unsigned short *first, unsigned short *next,\n'
            '    unsigned short *third, unsigned short *fourth);\n'
            'extern unsigned func_08000200(unsigned a, unsigned b, unsigned c, unsigned d);\n'
            'unsigned func_08000000(void)\n{\n    unsigned short a, b, c, d;\n'
            '    func_08000100(1, 2, &a, &b, &c, &d);\n    return func_08000200(a, b, c, d);\n}\n')
        callee = self.root / 'src/08000100.c'
        callee.write_text(
            'void func_08000100(unsigned value, unsigned second,\n'
            '    unsigned short *first, unsigned short *next,\n'
            '    unsigned short *third, unsigned short *fourth)\n{\n'
            '    if (first) *first = value;\n    if (next) *next = second;\n'
            '    if (third) *third = value + second;\n'
            '    if (fourth) *fourth = value - second;\n}\n')
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=self.root,
                             wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            object_data, text, original = match.compile_object(
                runner, workspace, args, self.root, BASE + 0x100, 'src/08000100.c')
            child = match.function_bytes(object_data, text, 'func_08000100', BASE + 0x100, True)
        scalar = self.root / 'src/08000200.c'
        scalar.write_text('unsigned func_08000200(unsigned a, unsigned b, unsigned c, unsigned d)\n'
                          '{ return a + b + c + d; }\n')
        with runner.workspace() as workspace:
            object_data, text, _ = match.compile_object(
                runner, workspace, args, self.root, BASE + 0x200, 'src/08000200.c')
            scalar_body = match.function_bytes(object_data, text, 'func_08000200', BASE + 0x200, True)
        self.assertLess(len(child), 0x100)
        entries = [{'rom': f'0x{BASE:08X}', 'end': f'0x{BASE + 2:08X}', 'mode': 'thumb'},
                   {'rom': f'0x{BASE + 0x100:08X}',
                    'end': f'0x{BASE + 0x100 + len(child):08X}', 'mode': 'thumb'},
                   {'rom': f'0x{BASE + 0x200:08X}',
                    'end': f'0x{BASE + 0x200 + len(scalar_body):08X}', 'mode': 'thumb'}]
        rom = bytes(0x100) + child.ljust(0x100, b'\0') + scalar_body
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(
                runner, workspace, args, self.root, BASE, 'src/08000000.c')
            symbol, _ = match.function_record(original, 'func_08000000', BASE, True)
            entries[0]['end'] = f'0x{BASE + symbol["size"]:08X}'
            body, calls, _ = match.link_calls(runner, workspace, args, original, BASE,
                                              json.dumps(entries).encode(), len(rom), rom)
        self.assertLess(len(body), 0x100)
        rom = body.ljust(0x100, b'\0') + child.ljust(0x100, b'\0') + scalar_body
        mapping = json.dumps(entries).encode()
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True)
        match.verify_leaf_instructions(body, BASE, True, calls, buffer_proof=proof)
        self.assertEqual(proof.dependencies, {BASE + 0x100: child, BASE + 0x200: scalar_body})
        self.assertTrue(any(i.mnemonic == 'cmp' and i.operands[1].type == match.ARM_OP_IMM
                            and i.operands[1].imm == 0
                            for i in match.verify_leaf_instructions(child, BASE + 0x100, True)))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(body, BASE, True, calls,
                buffer_proof=match.BufferCallProof(rom, mapping))
        (self.root / 'baserom.bin').write_bytes(rom)
        (self.root / 'config/functions.json').write_bytes(mapping)
        (self.root / 'symbols/functions.txt').write_text(''.join(
            f'{int(row["rom"], 16):08X} {int(row["end"], 16):08X} '
            f'{int(row["end"], 16) - int(row["rom"], 16)} '
            f'{(int(row["end"], 16) - int(row["rom"], 16)) // 2} return\n' for row in entries))
        report = '\n'.join((
            f'* verification: `{evidence.STACK_BUFFER_SCHEMA}`',
            f'* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`',
            f'* mapping SHA-256: `{evidence.mapping_fingerprint(evidence.mapping_snapshot(self.root))}`',
            f'* stack frame: {evidence.STACK_SUMMARY}',
            f'* control flow: {evidence.CALL_SUMMARY}',
            f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY}',
            f'* buffer proof SHA-256: `{proof.fingerprint()}`',
            '* verified extent: complete ELF function symbol, including literal pools',
            f'* ROM bytes: `{body.hex()}` ({len(body)} bytes)',
            f'* compiled : `{body.hex()}`', '* source plausibility: plausible',
            '* relocations: none', f'**MATCH - byte identical** - {len(body)}/{len(body)} bytes'))
        self.assertTrue(evidence.report_matches(report, self.root, BASE))
        legacy = report.replace(evidence.STACK_BUFFER_SCHEMA, evidence.BUFFER_SCHEMA).replace(
            evidence.STACK_BUFFER_SUMMARY, evidence.BUFFER_SUMMARY)
        self.assertFalse(evidence.report_matches(legacy, self.root, BASE))
        for path in (source, self.root / 'config/functions.json'):
            saved = path.read_bytes()
            try:
                path.write_bytes(saved + b'\n')
                self.assertFalse(evidence.report_matches(report, self.root, BASE))
            finally:
                path.write_bytes(saved)
        # Replace a real null compare with a nonzero comparison, retaining the
        # same instruction width and complete mapped callee extent.
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        compare = next(i for i in decoder.disasm(child, BASE + 0x100)
                       if i.mnemonic == 'cmp' and i.size == 2 and len(i.operands) == 2
                       and i.operands[1].type == match.ARM_OP_IMM and i.operands[1].imm == 0)
        changed = bytearray(rom)
        changed[compare.address - BASE] = 1
        (self.root / 'baserom.bin').write_bytes(changed)
        self.assertFalse(evidence.report_matches(report, self.root, BASE))


if __name__ == '__main__':
    unittest.main(verbosity=2)
