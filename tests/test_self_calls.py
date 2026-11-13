"""Self-recursive Thumb calls on the default path, and clean selector refusals.

Synthetic bytes only: no game ROM or compiler.  The call to the exact own entry
binds to the function's own complete verified symbol; every other recursion
shape stays refused.
"""
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import match
import match_evidence as evidence
import entry_recursive_ordinary_call_profile as entry
from synthetic_entry_owner import ADDRESS as A, HELPER as H, body, bl, snapshots
import test_entry_native as native
from test_entry_native import elf, environment

NAME = f'func_{A:08X}'
HELPER_NAME = f'func_{H:08X}'
TOOLS = Path(__file__).resolve().parents[1] / 'tools'


def bindings(data=None, **kwargs):
    rom, mapping, _ = environment(data)
    image = match.elf_image(elf(data))
    return match.call_bindings(image, NAME, A, mapping, len(rom), rom, **kwargs)


class SelfCallBindingTests(unittest.TestCase):
    def test_default_refuses_self_call(self):
        with self.assertRaisesRegex(ValueError, 'undefined addressed function'):
            bindings()

    def test_opt_in_binds_self_to_own_symbol_only(self):
        calls, targets, data = bindings(allow_self_call=True)
        self.assertEqual(calls, {A + 8: A, A + 14: H})
        # the self symbol is the root itself, never an external definition
        self.assertEqual(targets, {HELPER_NAME: H})
        self.assertEqual(data, {})

    def test_opt_in_must_be_boolean(self):
        for value in (1, 'yes', object()):
            with self.assertRaises(ValueError):
                bindings(allow_self_call=value)

    def test_non_entry_or_foreign_defined_target_is_refused(self):
        # a relocation against a second defined function symbol is not self
        extra = [('func_08080004', 5, 0, 0x12, 1)]
        relocations = [(8, (3 << 8) | 10), (14, (2 << 8) | 10)]
        raw = elf(extra=extra, relocations=relocations)
        rom, mapping, _ = environment()
        with self.assertRaises(ValueError):
            match.call_bindings(match.elf_image(raw), NAME, A, mapping, len(rom), rom, allow_self_call=True)

    def test_mutual_recursion_target_stays_an_external_symbol(self):
        # a call to another function is an ordinary external binding, not self
        calls, targets, _ = bindings(allow_self_call=True)
        self.assertEqual([target for target in calls.values() if target != A], [H])
        self.assertNotIn(NAME, targets)


class SelfCallVerifierTests(unittest.TestCase):
    calls = {A + 8: A, A + 14: H}

    def verify(self, data=None, calls=None, **kwargs):
        return match.verify_leaf_instructions(body() if data is None else data, A, True,
                                              self.calls if calls is None else calls, **kwargs)

    def test_self_call_needs_explicit_site(self):
        self.assertTrue(self.verify(self_calls=frozenset({A + 8})))
        with self.assertRaisesRegex(ValueError, 'validated external direct Thumb BL'):
            self.verify()
        with self.assertRaisesRegex(ValueError, 'validated external direct Thumb BL'):
            self.verify(self_calls=frozenset({A + 14}))

    def test_site_set_shape_and_context_exclusion(self):
        for bad in (frozenset(), {A + 8}, [A + 8]):
            with self.assertRaises(ValueError):
                self.verify(self_calls=bad)
        with self.assertRaises(ValueError):
            self.verify(self_calls=frozenset({A + 8}), buffer_proof=match.BufferCallProof(b'', None))
        with self.assertRaises(ValueError):
            self.verify(self_calls=frozenset({A + 8}), divsi3_context=(b'', b'', {}, {}))

    def test_non_entry_self_call_is_refused(self):
        data = bytearray(body())
        data[8:12] = bl(A + 8, A + 4)
        with self.assertRaises(ValueError):
            self.verify(bytes(data), {A + 8: A + 4, A + 14: H}, self_calls=frozenset({A + 8}))
        with self.assertRaises(ValueError):
            self.verify(bytes(data), {A + 8: A, A + 14: H}, self_calls=frozenset({A + 8}))

    def test_indirect_call_is_refused(self):
        data = bytearray(body())
        data[8:12] = bytes.fromhex('98470000')  # blx r3; a halfword of padding
        with self.assertRaises(ValueError):
            self.verify(bytes(data), {A + 14: H}, self_calls=frozenset({A + 8}))

    def test_framed_self_call_is_admitted(self):
        # push {r4,lr}; sub sp,#8; frame without an alias crossing the call
        data = (bytes.fromhex('10b5' '82b0' '0028' '04d0' '041c' '0138') +
                bl(A + 12, A) + bytes.fromhex('0019' '02b0' '10bc' '02bc' '0847'))
        self.assertTrue(self.verify(data, {A + 12: A}, self_calls=frozenset({A + 12})))
        with self.assertRaisesRegex(ValueError, 'validated external direct Thumb BL'):
            self.verify(data, {A + 12: A})

    def test_framed_self_call_with_stack_alias_across_call_is_refused(self):
        # add r0,sp,#0 (the 0801F438 refusal) passes a stack address into the recursive call
        data = (bytes.fromhex('10b5' '82b0' '0028' '04d0' '041c' '00a8') +
                bl(A + 12, A) + bytes.fromhex('0019' '02b0' '10bc' '02bc' '0847'))
        with self.assertRaisesRegex(ValueError, 'stack aliases cannot cross calls'):
            self.verify(data, {A + 12: A}, self_calls=frozenset({A + 12}))

    def test_parameter_defaults_cannot_hide_a_new_context(self):
        # the self-call guard rejects any parameter outside SELF_CALL_PARAMETERS
        # whose value is not None or False, so every default must be one of those
        import inspect
        for name, parameter in inspect.signature(match.verify_leaf_instructions).parameters.items():
            if name not in match.SELF_CALL_PARAMETERS:
                with self.subTest(parameter=name):
                    self.assertIn(parameter.default, (None, False))
        self.assertLessEqual(set(match.SELF_CALL_PARAMETERS),
                             set(inspect.signature(match.verify_leaf_instructions).parameters))

    def test_resolver_path_requires_the_site_set(self):
        resolved = []
        self.assertTrue(self.verify(calls={}, call_resolver=resolved.append, self_calls=frozenset({A + 8})))
        self.assertEqual(resolved, [A, H])
        with self.assertRaises(ValueError):
            self.verify(calls={}, call_resolver=resolved.append)


class SelfCallLinkTests(unittest.TestCase):
    def test_linked_bytes_bind_the_self_call(self):
        rom, mapping, _ = environment()
        original = match.elf_image(elf())
        calls, targets, _ = match.call_bindings(original, NAME, A, mapping, len(rom), rom, allow_self_call=True)
        linked = match.elf_image(elf(linked=True))
        got = match.linked_function_bytes(original, linked, NAME, A, calls, targets)
        self.assertEqual(got, body())
        # the linked self BL must still decode to the exact own entry
        match.verify_leaf_instructions(got, A, True, calls, self_calls=frozenset({A + 8}))
        data = bytearray(body())
        data[8:12] = bl(A + 8, H)
        tampered = match.linked_function_bytes(original, match.elf_image(elf(bytes(data), linked=True)),
                                               NAME, A, calls, targets)
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(tampered, A, True, calls, self_calls=frozenset({A + 8}))


class SelfCallReportTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='self_calls_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        rom, mapping, _ = environment()
        self.rom = rom
        environment_patch = patch.dict(os.environ, {'FFTA_ROM': str(self.root / 'baserom.bin')})
        environment_patch.start()
        self.addCleanup(environment_patch.stop)
        (self.root / 'config').mkdir()
        (self.root / 'src').mkdir()
        (self.root / 'baserom.bin').write_bytes(rom)
        (self.root / 'config/functions.json').write_bytes(mapping)
        (self.root / f'src/{A:08X}.c').write_text(f'int {NAME}(int x) {{ return x + 1; }}\n')

    def report(self, data=None, *, sites='[8]', lines=True, schema=evidence.LINKED_SCHEMA):
        data = body() if data is None else data
        out = [f'* verification: `{schema}`',
               f'* source SHA-256: `{evidence.source_fingerprint(self.root, A)}`',
               f'* mapping SHA-256: `{evidence.mapping_fingerprint(evidence.mapping_snapshot(self.root))}`',
               f'* control flow: {evidence.CALL_SUMMARY}']
        if lines:
            out += [f'* self calls: {evidence.SELF_CALL_SUMMARY}', f'* self call sites: `{sites}`']
        out += ['* verified extent: complete ELF function symbol, including literal pools',
                '* relocations: none', f'* ROM bytes: `{data.hex()}` ({len(data)} bytes)',
                f'* compiled : `{data.hex()}`', '* source plausibility: plausible',
                f'**MATCH - byte identical** - {len(data)}/{len(data)} bytes']
        return '\n'.join(out)

    def test_canonical_report_is_accepted(self):
        self.assertEqual(evidence.self_call_sites_text([A + 8], A), '[8]')
        self.assertTrue(evidence.report_matches(self.report(), self.root, A))

    def test_self_call_without_its_explicit_binding_is_rejected(self):
        self.assertFalse(evidence.report_matches(self.report(lines=False), self.root, A))

    def test_tampered_bindings_are_rejected(self):
        good = self.report()
        for bad in (good.replace('`[8]`', '`[]`'), good.replace('`[8]`', '`[14]`'),
                    good.replace('`[8]`', '`[8,14]`'), good.replace('`[8]`', '`[ 8 ]`'),
                    good.replace('`[8]`', '`[8,8]`'), good.replace('partial correctness', 'total correctness'),
                    good + '\n* self call sites: `[8]`',
                    good.replace(f'* self calls: {evidence.SELF_CALL_SUMMARY}\n', '')):
            with self.subTest(bad=bad.splitlines()[5:7]):
                self.assertFalse(evidence.report_matches(bad, self.root, A))

    def test_claim_without_a_self_call_in_the_bytes_is_rejected(self):
        data = bytearray(body())
        data[8:12] = bl(A + 8, H)
        rom = bytearray(self.rom)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        (self.root / 'baserom.bin').write_bytes(rom)
        self.assertFalse(evidence.report_matches(self.report(bytes(data)), self.root, A))
        self.assertTrue(evidence.report_matches(self.report(bytes(data), lines=False), self.root, A))

    def test_claim_under_a_non_call_schema_is_rejected(self):
        self.assertFalse(evidence.report_matches(self.report(schema=evidence.SCHEMA), self.root, A))

    def test_stray_self_call_lines_on_other_profiles_are_rejected(self):
        for schema in (evidence.SCHEMA, evidence.FRAMED_SCHEMA, evidence.BUFFER_SCHEMA,
                       evidence.FUNCTION_ADDRESS_SCHEMA, evidence.SWITCH_SCHEMA):
            with self.subTest(schema=schema):
                self.assertFalse(evidence.report_matches(self.report(schema=schema), self.root, A))

    def test_a_second_verification_line_is_rejected(self):
        good = self.report()
        extra = f'* verification: `{evidence.SCHEMA}`'
        self.assertFalse(evidence.report_matches(good.replace('\n', f'\n{extra}\n', 1), self.root, A))

    def test_changed_mapping_or_rom_is_rejected(self):
        good = self.report()
        rom = bytearray(self.rom)
        rom[A - match.ROM_BASE + 10] ^= 1
        (self.root / 'baserom.bin').write_bytes(rom)
        self.assertFalse(evidence.report_matches(good, self.root, A))
        (self.root / 'baserom.bin').write_bytes(self.rom)
        self.assertTrue(evidence.report_matches(good, self.root, A))
        mapping = self.root / 'config/functions.json'
        mapping.write_bytes(mapping.read_bytes() + b'\n')
        self.assertFalse(evidence.report_matches(good, self.root, A))


class RefusalTests(unittest.TestCase):
    """Selectors refuse with ValueError; the command line reports it cleanly."""

    def entry_owner(self, data):
        rom, mapping, index = environment(body())
        with self.assertRaises(ValueError) as caught:
            entry.original_bindings(match.elf_image(elf(data, size=len(data))), A, rom, mapping, index)
        return str(caught.exception)

    def test_entry_profile_refuses_halfword_memory_access(self):
        data = body().replace(bytes.fromhex('201c'), bytes.fromhex('8888'), 1)
        self.assertIn('object-word loads', self.entry_owner(data))

    def test_entry_profile_refuses_a_literal_pool_tail(self):
        self.assertIn('undecoded', self.entry_owner(body() + bytes.fromhex('ffffffff')))

    def test_known_query_style_thunk_call_is_a_refusal(self):
        rom, mapping, _ = environment()
        thunk = next(iter(match.RUNTIME_HELPERS.values()))
        with self.assertRaisesRegex(ValueError, 'runtime call thunks'):
            match.function_address_target(f'func_{thunk:08X}', json.loads(mapping), A, 2, len(rom))

    def test_command_line_refusal_is_not_a_traceback(self):
        with tempfile.TemporaryDirectory() as root:
            Path(root, 'src').mkdir()
            Path(root, 'src', f'{A:08X}.c').write_text('void f(void){}\n')
            run = subprocess.run([sys.executable, str(TOOLS / 'match.py'), '--root', root, '--no-write',
                                  '--label', 'x', '--owner-runtime-profile', entry.SELECTOR, f'0x{A:08X}'],
                                 capture_output=True, text=True)
        self.assertEqual(run.returncode, 1)
        self.assertNotIn('Traceback', run.stderr)
        self.assertTrue(run.stderr.startswith('refused'))

    def test_command_line_labels_the_exception_type_and_can_traceback(self):
        # a plain ValueError (parse_args patched to raise one) is an error, not a refusal
        code = ('import argparse, runpy, sys\n'
                'def boom(*a, **k): raise ValueError("boom")\n'
                'argparse.ArgumentParser.parse_args = boom\n'
                f'sys.path.insert(0, {str(TOOLS)!r})\n'
                f'runpy.run_path({str(TOOLS / "match.py")!r}, run_name="__main__")\n')

        def run(**env):
            return subprocess.run([sys.executable, '-c', code], capture_output=True, text=True,
                                  env={k: v for k, v in {**os.environ, **env}.items() if v is not None})
        plain = run(FFTA_TRACEBACK=None)
        self.assertEqual(plain.returncode, 1)
        self.assertEqual(plain.stderr.strip(),
                         'error (ValueError): boom (set FFTA_TRACEBACK=1 for a traceback)')
        for off in ('', '0'):
            with self.subTest(FFTA_TRACEBACK=off):
                quiet = run(FFTA_TRACEBACK=off)
                self.assertEqual(quiet.returncode, 1)
                self.assertNotIn('Traceback', quiet.stderr)
        loud = run(FFTA_TRACEBACK='1')
        self.assertEqual(loud.returncode, 1)
        self.assertIn('Traceback', loud.stderr)

    def test_refusal_is_a_value_error_and_reported_without_a_type_label(self):
        self.assertTrue(issubclass(match.Refusal, ValueError))
        rom, mapping, _ = environment()
        thunk = next(iter(match.RUNTIME_HELPERS.values()))
        with self.assertRaises(match.Refusal):
            match.function_address_target(f'func_{thunk:08X}', json.loads(mapping), A, 2, len(rom))


class ProducerRefusalTests(unittest.TestCase):
    """main() must not admit a self call replay would refuse."""
    build_mocks = native.EntryBuildRoutingTests.build_mocks

    @contextlib.contextmanager
    def tree(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', Path(__file__).resolve().parents[1] / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='producer_refusal_', dir=scratch) as folder:
            root = Path(folder)
            for name in ('src', 'include', 'config', 'symbols'):
                (root / name).mkdir()
            (root / 'src' / f'{A:08X}.c').write_bytes(b'synthetic compiler input fixture\n')
            (root / 'include' / 'fixture.h').write_bytes(b'synthetic header input\n')
            rom, mapping, index = environment()
            (root / 'baserom.bin').write_bytes(rom)
            (root / 'config/functions.json').write_bytes(mapping)
            (root / 'config/data_symbols.json').write_bytes(b'{}')
            (root / 'symbols/functions.txt').write_bytes(index)
            yield root

    def run_main(self, calls):
        with self.tree() as root, self.build_mocks(), \
                patch.object(match, 'link_calls', return_value=(body(), calls, {})), \
                patch('sys.argv', ['match.py', '--root', str(root), '--no-write', f'0x{A:08X}']), \
                contextlib.redirect_stdout(io.StringIO()):
            return match.main()

    def test_self_call_with_a_runtime_helper_call_is_refused(self):
        thunk = next(iter(match.RUNTIME_HELPERS.values()))
        with self.assertRaises(SystemExit) as caught:
            self.run_main({A + 8: A, A + 14: thunk})
        self.assertIn('self calls are admitted only', str(caught.exception))

    def test_self_call_with_an_ordinary_call_passes_that_guard(self):
        try:
            result = self.run_main({A + 8: A, A + 14: H})
        except (ValueError, SystemExit) as error:
            self.assertNotIn('self calls are admitted only', str(error))
        else:
            self.assertIsNotNone(result)


if __name__ == '__main__':
    unittest.main()
