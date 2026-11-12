"""CpuSet read sets require the selected native fill proof and explicit premise."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from contextlib import contextmanager
from unittest.mock import patch
import test_named_bios_fill_source as native
import test_volatile_semantics as fixtures
import volatile_semantics as semantics
import bios_cpuset_fill_profile as bios
import match
import match_evidence


class BiosVolatileInterfaceTests(unittest.TestCase):
    def setUp(self):
        self.base = native.NamedBiosFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def interface(self, **changes):
        f = self.base.fixture()
        f.update(changes)
        return bios.ConditionalVolatileInterfaces(
            semantics.RomInterfaces(f['rom'], json.loads(f['mapping'])),
            f['data'], f['address'], f['rom'], f['mapping'], f['index'], f['objects'])

    def bodies(self, suffix=()):
        prefix = ('push\t{lr}', 'ldr\tr1, .L3', 'add\tr1, r1, #60')
        tail = ('mov\tr0, #0', 'mov\tr1, #0', 'mov\tr2, #0',
                'bl\tfunc_0814186C', *suffix, 'pop\t{r0}', 'bx\tr0')
        real = fixtures.assembly(*prefix, 'ldrb\tr3, [r1]', 'mov\tr0, #1',
                                 'strb\tr0, [r1]', *tail)
        stripped = fixtures.assembly(*prefix, 'mov\tr0, #1', 'strb\tr0, [r1]', *tail)
        return real, stripped

    def compare(self, interfaces, suffix=()):
        real, stripped = self.bodies(suffix)
        declarations = fixtures.PREPROCESSED + '\nvoid func_0814186C(void *, void *, unsigned int);\n'
        return semantics._compare_compiles(real, stripped, declarations,
            fixtures.SYMBOL, fixtures.DECLARATION, interfaces=interfaces)

    def test_native_fill_authenticates_conditional_reads_without_writes(self):
        interface = self.interface()
        self.assertEqual(interface(bios.NAME), ({'r0', 'r1', 'r2'}, set()))
        self.assertIsNone(interface('unknown'))
        self.assertIn('conditional', interface.conditional_premises[bios.NAME])

    def test_dead_r3_is_accepted_only_with_explicit_conditional_interface(self):
        with self.assertRaises(semantics.SemanticError):
            self.compare(None)
        result = self.compare(self.interface())
        report = semantics.record(fixtures.SYMBOL, result)
        self.assertIn('conditional callee interfaces', report)
        self.assertIn('CpuSet consumes only r0-r2', report)
        self.assertNotIn('callee interfaces from ROM:', report)

    def test_preserved_r3_used_after_call_still_refuses(self):
        with self.assertRaises(semantics.SemanticError):
            self.compare(self.interface(), ('str\tr3, [r5]',))

    def test_unknown_call_and_changed_observable_store_stay_rejected(self):
        real, stripped = self.bodies()
        declarations = fixtures.PREPROCESSED + '\nvoid unknown(void *, void *, unsigned int);\n'
        with self.assertRaises(semantics.SemanticError):
            semantics._compare_compiles(real.replace(bios.NAME, 'unknown'),
                stripped.replace(bios.NAME, 'unknown'), declarations,
                fixtures.SYMBOL, fixtures.DECLARATION, interfaces=self.interface())
        with self.assertRaises(semantics.SemanticError):
            semantics._compare_compiles(real, stripped.replace('#1', '#2'),
                declarations.replace('unknown', bios.NAME), fixtures.SYMBOL,
                fixtures.DECLARATION, interfaces=self.interface())

    def test_profile_selection_is_required_and_native_inputs_are_rechecked(self):
        f = self.base.fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('src', 'symbols', 'config'):
                (root / name).mkdir()
            (root / 'src' / f'{f["address"]:08X}.c').write_text('')
            (root / 'symbols/functions.txt').write_bytes(f['index'])
            (root / 'config/functions.json').write_bytes(f['mapping'])
            (root / 'config/data_symbols.json').write_bytes(f['objects'])
            (root / 'baserom.bin').write_bytes(f['rom'])
            class Runner:
                @contextmanager
                def workspace(self):
                    yield directory
                def read_binary(self, path):
                    return b''
            entry = dict(symbol=fixtures.SYMBOL, declaration=fixtures.DECLARATION)
            with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')), \
                    patch.object(match.plausibility, 'allowlisted_volatile_used', return_value=[entry]), \
                    patch.object(match, 'compile_object'), \
                    patch.object(semantics, 'compare', return_value=[]) as compare:
                for selector in (None, native.buffers.SELECTOR, native.buffers.BIOS_FILL_SELECTOR):
                    match.allowlisted_volatile_semantics(root, f['address'], runner=Runner(),
                                                         owner_runtime_profile=selector)
                    provider = compare.call_args.args[-1]
                    if selector == native.buffers.BIOS_FILL_SELECTOR:
                        self.assertEqual(provider(bios.NAME), ({'r0', 'r1', 'r2'}, set()))
                    else:
                        self.assertIsNone(provider(bios.NAME))
                (root / 'symbols/functions.txt').write_bytes(f['index'].replace(b'08141870', b'08141872'))
                compare.reset_mock()
                with self.assertRaises(ValueError):
                    match.allowlisted_volatile_semantics(root, f['address'], runner=Runner(),
                        owner_runtime_profile=native.buffers.BIOS_FILL_SELECTOR)
                compare.assert_not_called()

    def test_report_replay_selects_only_the_exact_profile_and_still_validates_owner(self):
        import test_volatile_records_all_profiles as records
        base = records.owner_report(b'\x70\x47')
        bios_report = base.replace(f'`{records.owner.ACYCLIC_SCHEMA}`', f'`{native.buffers.BIOS_FILL_SCHEMA}`')
        self.assertNotEqual(base, bios_report)
        uses = '* allowlisted volatile: fixture'
        semantic = '* allowlisted volatile semantics: fixture'
        for report, selected in ((base, False), (bios_report, True)):
            carried = match_evidence.carry_volatile_records(report, [uses, semantic])
            with patch.object(match.plausibility, 'allowlisted_volatile_uses', return_value=[uses]), \
                    patch.object(match, 'allowlisted_volatile_semantics', return_value=[semantic]) as replay, \
                    patch.object(native.owner, 'report_matches', return_value=False) as owner_check:
                self.assertFalse(match_evidence.report_matches(carried, '.', native.A))
                self.assertEqual(replay.call_args.kwargs,
                    {'owner_runtime_profile': native.buffers.BIOS_FILL_SELECTOR} if selected else {})
                owner_check.assert_called_once()

    def test_wrong_wrapper_missing_index_and_fill_mode_refuse(self):
        for kind in ('wrapper', 'mapping', 'index', 'mode'):
            f = copy.deepcopy(self.base.fixture(control=0 if kind == 'mode' else 0x01000010))
            if kind == 'wrapper':
                rom = bytearray(f['rom'])
                rom[bios.ADDRESS-native.match.ROM_BASE] = 12
                f['rom'] = bytes(rom)
            elif kind == 'mapping':
                f['mapping'] = json.dumps([r for r in json.loads(f['mapping'])
                    if int(r['rom'], 16) != bios.ADDRESS]).encode()
            elif kind == 'index':
                f['index'] = f['index'].replace(b'08141870', b'08141872')
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.interface(**f)


if __name__ == '__main__':
    unittest.main()
