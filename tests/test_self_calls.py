"""Self-recursive Thumb calls on the default path, and clean selector refusals.

Synthetic bytes only: no game ROM or compiler.  The call to the exact own entry
binds to the function's own complete verified symbol; every other recursion
shape stays refused.
"""
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
        self.assertTrue(run.stderr.startswith('refused: '))


if __name__ == '__main__':
    unittest.main()
