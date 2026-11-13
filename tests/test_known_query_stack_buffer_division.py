"""Canonical unsigned quotient composition, native refusals and source replay."""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import known_query_stack_buffer_profile as stack
from test_known_query_stack_buffer import A, B, Q, fixture
from test_nested_known_query import assemble

UDIV, ZERO = 0x08142AB0, 0x0814274C
SELECTOR = stack.DIVISION_SELECTOR
SOURCE = '''extern int func_08099CDC(unsigned owner, unsigned *values);
extern unsigned func_08011000(unsigned value);
unsigned func_08010000(unsigned owner, unsigned divisor)
{
    unsigned values[13];
    unsigned total = 0;
    int count = func_08099CDC(owner, values);
    if (count > 0)
        total = values[0] / divisor;
    return func_08011000(total);
}
'''


def indexes(rows):
    return (json.dumps(rows).encode(), ''.join(
        f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
        f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode())


def with_runtime(f, approved):
    f = dict(f)
    rows, rom = json.loads(f['mapping']), bytearray(f['rom'])
    for address, end, count in ((UDIV, 0x08142B28, 59), (ZERO, ZERO+2, 1)):
        rom[address-match.ROM_BASE:end-match.ROM_BASE] = approved[address-match.ROM_BASE:end-match.ROM_BASE]
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{end:08X}', mode='thumb', instrs=count))
    f.update(rom=bytes(rom), selector=SELECTOR)
    f['mapping'], f['index'] = indexes(sorted(rows, key=lambda r: int(r['rom'], 16)))
    f['bindings'] = copy.deepcopy(f['bindings'])
    f['bindings']['calls'] = [[offset, '__udivsi3' if name == 'func_08142AB0' else name]
                             for offset, name in f['bindings']['calls']]
    return f


def machine(tokens, approved):
    f = with_runtime(fixture(), approved)
    data = assemble(A, tokens)
    rows = json.loads(f['mapping'])
    row = next(r for r in rows if int(r['rom'], 16) == A)
    row['end'], row['instrs'] = f'0x{A+len(data):08X}', 0
    mapping, _ = indexes(rows)
    refined = owner.refine(data, A, mapping)
    row['instrs'] = refined['instrs']
    f['mapping'], f['index'] = indexes(rows)
    rom = bytearray(f['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
    f['data'], f['rom'] = data, bytes(rom)
    f['bindings']['calls'] = [[int(call['site'], 16)-A,
        '__udivsi3' if int(call['target'], 16) == UDIV else f"func_{int(call['target'], 16):08X}"]
        for call in refined['calls']]
    return f


class KnownQueryDivisionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = os.environ.get('FFTA_ROM')
        if not path or not Path(path).is_file():
            raise unittest.SkipTest('FFTA_ROM must identify the approved canonical runtime')
        cls.approved = Path(path).read_bytes()
        assert hashlib.sha256(cls.approved).hexdigest() == '43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19'

    def native(self, before=(0x2064, 0x210a), after=(), divisor_call=UDIV):
        # A genuine bounded query, followed by the scalar runtime and a balanced return.
        return machine([0xb570, 0xb08d, 0x4669, Q,
            *before, divisor_call, *after, 0xb00d, 0xbc70, 0xbc01, 0x4700], self.approved)

    def test_native_preflight_and_manifest_replay(self):
        f = self.native()
        m, ins = owner.verify(**f)
        pre = dict(f); pre.pop('bindings')
        observed, _, _ = owner.preflight(**pre)
        self.assertEqual(m, observed)
        self.assertEqual(owner.verify(**f, manifest=m)[0], m)
        proof = m['proof']
        self.assertEqual(m['profile'], stack.DIVISION_SCHEMA)
        self.assertEqual(proof['runtime_calls'], [[14, '__udivsi3']])
        self.assertEqual(proof['caller']['ordinary_calls'], [])
        self.assertEqual(proof['unsigned_quotient']['maximum_additional_stack_bytes'], 4)
        self.assertEqual(proof['unsigned_quotient']['caller_memory_writes'], [])
        self.assertEqual(proof['caller']['returned_counts'], list(range(14)))
        self.assertIn('zero', proof['unsigned_quotient']['zero'])
        self.assertIn('software_float_profile.py', proof['producer_sha256'])

    def test_zero_unknown_and_max_unsigned_operands_keep_conservative_result(self):
        for before in ((0x2064, 0x2100), (0x2101,), (0x2000, 0x43c0, 0x2101)):
            with self.subTest(before=before):
                owner.verify(**self.native(before=before))
        # Unknown incoming divisor, preserved across the query in R4.
        f = machine([0xb570, 0x1c0c, 0xb08d, 0x4669, Q,
            0x2064, 0x1c21, UDIV, 0xb00d, 0xbc70, 0xbc01, 0x4700], self.approved)
        owner.verify(**f)

    def test_runtime_does_not_initialize_private_buffer(self):
        with self.assertRaisesRegex(ValueError, 'uninitialized'):
            owner.verify(**self.native(after=(0x9800,)))

    def test_runtime_does_not_havoc_initialized_scalar_stack_word(self):
        # Preserve a constant initialized before UDIV, then use it as a private
        # index. Ordinary-call havoc would incorrectly erase this evidence.
        f = self.native(before=(0x2000, 0x9000, 0x2064, 0x210a),
                        after=(0x9800, 0x4669, 0x5808, 0x2100))
        owner.verify(**f)

    def test_local_pointer_and_saved_operands_refuse(self):
        for before in ((0x4668, 0x210a), (0x2064, 0x4669), (0x4620, 0x210a)):
            with self.subTest(before=before), self.assertRaisesRegex(ValueError, 'passed to a call'):
                owner.verify(**self.native(before=before))

    def test_undefined_operands_and_clobbered_scratch_refuse(self):
        with self.assertRaisesRegex(ValueError, 'untracked register'):
            owner.verify(**self.native(before=(0x2064,)))  # query destroyed R1
        for after in ((0x1c08,), (0x1c10,), (0x1c18,), (0x4660,)):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, 'untracked register'):
                owner.verify(**self.native(after=after))

    def test_exact_runtime_bytes_extent_count_and_binding_required(self):
        f = self.native()
        for address in (UDIV, UDIV+20, 0x08142B24, ZERO):
            bad = dict(f); rom = bytearray(f['rom']); rom[address-match.ROM_BASE] ^= 1
            bad['rom'] = bytes(rom)
            with self.subTest(address=hex(address)), self.assertRaises(ValueError):
                owner.verify(**bad)
        for key, value in (('instrs', 58), ('end', '0x08142B26'), ('mode', 'arm')):
            bad = dict(f); rows = json.loads(f['mapping'])
            next(r for r in rows if int(r['rom'], 16) == UDIV)[key] = value
            bad['mapping'], bad['index'] = indexes(rows)
            with self.subTest(key=key), self.assertRaises(ValueError):
                owner.verify(**bad)
        bad = copy.deepcopy(f); bad['bindings']['calls'][-1][1] = 'func_08142AB0'
        with self.assertRaisesRegex(ValueError, 'call identities differ'):
            owner.verify(**bad)

    def test_stale_manifest_and_legacy_selector_refuse(self):
        f = self.native(); m, _ = owner.verify(**f)
        for mutate in ('closure', 'producer', 'binding'):
            bad = copy.deepcopy(m)
            if mutate == 'closure':
                bad['proof']['unsigned_quotient']['native_runtime_closure'] = []
            elif mutate == 'producer':
                bad['proof']['producer_sha256']['software_float_profile.py'] = '0'*64
            else:
                bad['bindings']['calls'][-1][1] = 'func_08142AB0'
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                owner.verify(**f, manifest=bad)
        f['selector'] = stack.SELECTOR
        with self.assertRaisesRegex(ValueError, 'canonical versioned proof'):
            owner.verify(**f)
        with self.assertRaisesRegex(ValueError, 'actual canonical division'):
            owner.verify(**with_runtime(fixture(), self.approved))

    def test_quotient_result_is_not_a_known_private_index(self):
        with self.assertRaisesRegex(ValueError, 'unknown index'):
            owner.verify(**self.native(after=(0x4669, 0x5808)))

    def test_other_reserved_division_is_not_an_ordinary_call(self):
        with self.assertRaises(ValueError):
            owner.verify(**self.native(after=(0x2064, 0x210a, 0x08142950)))
        with self.assertRaises(ValueError):
            owner.verify(**self.native(divisor_call=0x08142950))
        with self.assertRaisesRegex(ValueError, 'canonical versioned proof'):
            match.function_address_target('func_08142AB0', json.loads(self.native()['mapping']), A, 32, 0x150000)

    @unittest.skipUnless(importlib.util.find_spec('unicorn'), 'unicorn CPU oracle not installed')
    def test_canonical_runtime_cpu_zero_and_unsigned_extremes(self):
        from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
        from unicorn import arm_const as arm
        for dividend, divisor in ((0, 0), (0xffffffff, 0), (0xffffffff, 1),
                                   (0x80000000, 0xffffffff), (65535, 10), (0xffffffff, 10)):
            with self.subTest(dividend=dividend, divisor=divisor):
                cpu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
                cpu.mem_map(match.ROM_BASE, 0x150000)
                cpu.mem_write(match.ROM_BASE, self.native()['rom'])
                cpu.mem_map(0x02000000, 0x10000)
                cpu.reg_write(arm.UC_ARM_REG_SP, 0x02008000)
                cpu.reg_write(arm.UC_ARM_REG_R0, dividend)
                cpu.reg_write(arm.UC_ARM_REG_R1, divisor)
                cpu.reg_write(arm.UC_ARM_REG_LR, B|1)
                for n in range(4, 12):
                    cpu.reg_write(getattr(arm, f'UC_ARM_REG_R{n}'), 0x123400+n)
                cpu.emu_start(UDIV|1, B, count=4096)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_PC), B)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_R0), dividend//divisor if divisor else 0)
                self.assertEqual(cpu.reg_read(arm.UC_ARM_REG_SP), 0x02008000)
                for n in range(4, 12):
                    self.assertEqual(cpu.reg_read(getattr(arm, f'UC_ARM_REG_R{n}')), 0x123400+n)


class KnownQueryDivisionCompilerTests(unittest.TestCase):
    # Keep compiler setup separate from the native cases above.
    @classmethod
    def setUpClass(cls):
        KnownQueryDivisionTests.setUpClass()
        cls.approved = KnownQueryDivisionTests.approved
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', tempfile.gettempdir()))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='query_quotient_', dir=scratch)
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.root = Path(cls.temporary.name)
        retained = os.environ.get('FFTA_QUERY_DIVISION_RETAIN')
        cls.retained = Path(retained) if retained else None
        if cls.retained:
            cls.retained.mkdir(parents=True, exist_ok=True)
        for directory in ('src', 'include', 'config', 'symbols', 'build'):
            (cls.root/directory).mkdir()
        (cls.root/'src/08010000.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            raw, _, original = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            targets = {'__udivsi3': UDIV, 'func_08099CDC': Q, 'func_08011000': B}
            assert {r['name'] for r in original['symbols'] if not r['section'] and r['bind'] == 1} == set(targets)
            definitions = ['.syntax unified', '.thumb']
            for name, target in sorted(targets.items()):
                definitions += [f'.global {name}', f'.type {name}, %function', f'.thumb_set {name}, 0x{target|1:08X}']
            runner.write_text(f'{workspace}/f.known.s', '\n'.join(definitions)+'\n')
            runner.write_text(f'{workspace}/f.ld',
                f'SECTIONS {{ .text 0x{A:08X} : {{ *(.text) }} /DISCARD/ : {{ *(.comment) *(.note.GNU-stack) }} }}')
            q = shlex.quote(workspace)
            runner.sh(f'{args.assembler} -mthumb-interwork {q}/f.known.s -o {q}/f.known.o')
            runner.sh(f'{args.linker} --fatal-warnings --no-undefined --no-relax -T {q}/f.ld '
                      f'-e func_08010000 {q}/f.o {q}/f.known.o -o {q}/f.elf')
            linked_raw = runner.read_binary(f'{workspace}/f.elf')
            linked = match.elf_image(linked_raw)
            symbol, offset = match.function_record(linked, 'func_08010000', A, True)
            cls.body = linked['text'][offset:offset+symbol['size']]
            if cls.retained:
                (cls.retained/'caller.c').write_text(SOURCE)
                (cls.retained/'original.o').write_bytes(raw)
                (cls.retained/'compiler.s').write_bytes(runner.read_binary(f'{workspace}/f.s'))
                (cls.retained/'linked.elf').write_bytes(linked_raw)
        f = with_runtime(fixture(), cls.approved)
        rows = json.loads(f['mapping'])
        row = next(r for r in rows if int(r['rom'], 16) == A)
        row['end'], row['instrs'] = f'0x{A+len(cls.body):08X}', 0
        mapping, _ = indexes(rows)
        row['instrs'] = owner.refine(cls.body, A, mapping)['instrs']
        cls.mapping, cls.index = indexes(rows)
        rom = bytearray(f['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(cls.body)] = cls.body
        cls.rom = bytes(rom)
        (cls.root/'baserom.bin').write_bytes(cls.rom)
        (cls.root/'config/functions.json').write_bytes(cls.mapping)
        (cls.root/'config/data_symbols.json').write_bytes(b'{}')
        (cls.root/'symbols/functions.txt').write_bytes(cls.index)
        cls.original = original
        if cls.retained:
            for name, content in (('body.bin', cls.body), ('functions.json', cls.mapping), ('functions.txt', cls.index)):
                (cls.retained/name).write_bytes(content)

    def setUp(self):
        environment = patch.dict(os.environ, {'FFTA_ROM': str(self.root/'baserom.bin')})
        environment.start()
        self.addCleanup(environment.stop)

    def test_compiler_native_cli_and_source_bound_report_replay(self):
        bindings, _ = owner.original_bindings(self.original, A, self.rom, self.mapping, b'{}',
                                             selector=SELECTOR, index=self.index)
        m, _ = owner.verify(self.body, A, self.rom, self.mapping, self.index, b'{}',
                            bindings=bindings, selector=SELECTOR)
        self.assertTrue(m['proof']['caller']['local_reads'])
        cli = subprocess.run([sys.executable, str(Path(match.__file__)), '--root', str(self.root),
            '--owner-runtime-profile', SELECTOR, f'0x{A:08X}'], capture_output=True, text=True)
        if self.retained:
            (self.retained/'native-manifest.json').write_text(json.dumps(m, indent=2)+'\n')
            (self.retained/'cli.log').write_text(cli.stdout+cli.stderr)
            (self.retained/'cli.exit').write_text(str(cli.returncode)+'\n')
        self.assertEqual(cli.returncode, 0, cli.stdout+cli.stderr)
        report = (self.root/'docs/match/08010000.md').read_text()
        if self.retained:
            (self.retained/'report.md').write_text(report)
            shutil.copytree(self.root, self.retained/'fixture-root')
        self.assertEqual(owner.selector_for_report(report), SELECTOR)
        self.assertTrue(owner.selected(report))
        self.assertTrue(owner.report_matches(report, self.root, A))
        # Every hostile replay changes a bound input or claimed observation.
        self.assertFalse(owner.report_matches(report.replace('maximum_additional_stack_bytes":4',
                                                             'maximum_additional_stack_bytes":8'), self.root, A))
        source = self.root/'src/08010000.c'
        source.write_text(SOURCE+'\n')
        self.assertFalse(owner.report_matches(report, self.root, A))
        source.write_text(SOURCE)
        path = self.root/'config/functions.json'
        path.write_bytes(self.mapping+b' ')
        self.assertFalse(owner.report_matches(report, self.root, A))
        path.write_bytes(self.mapping)
        with self.assertRaises(ValueError):
            owner.original_bindings(self.original, A, self.rom, self.mapping, b'{}',
                                    selector=stack.SELECTOR, index=self.index)
        with self.assertRaisesRegex(ValueError, 'original ELF identity'):
            owner.fingerprint(A, self.body, m, 'source', self.mapping, self.index, b'{}', self.rom)


if __name__ == '__main__':
    unittest.main()
