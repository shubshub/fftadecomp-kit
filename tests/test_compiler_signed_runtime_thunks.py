"""Real agbcc: compiler-emitted __divsi3/__modsi3 beside canonical _call_via_rN thunks (kit #134).

The default path's generic call binding refuses a signed runtime next to a
thunk.  ``COMPILER_THUNKS_POLICY`` hands that refused function to
``compiler-signed-runtime-thunks-data-v1``, which applies the compiler-runtime
binding of the compiler selectors and the thunk rule of the thunks selectors
together.  The ROM and runtime identities are the synthetic ones of
test_addressed_signed_runtime_thunks.
"""
import argparse
import hashlib
import copy
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

import test_addressed_signed_runtime_thunks as fixtures

match, profile, evidence, status = fixtures.match, fixtures.profile, fixtures.evidence, fixtures.status
import signed_remainder_leaf_profile as remainder_leaf
A, B, R2, R3 = fixtures.A, fixtures.B, fixtures.R2, fixtures.R3
SELECTOR, SCHEMA = profile.COMPILER_THUNKS_DATA_SELECTOR, profile.COMPILER_THUNKS_DATA_SCHEMA
POLICY = profile.COMPILER_THUNKS_POLICY
PLAIN = 'signed quotient excludes other runtime, literal, switch and thunk profiles'
# The default path's division leaf retry (signed_remainder_leaf_profile.DIVISION) also runs on PLAIN,
# after the route; its walk refuses the thunk owner, and the earlier refusals stay first.
LEAF = remainder_leaf.DIVISION_RETRY + 'call is not a validated external direct Thumb BL'

# fixtures.TABLE with the compiler's own `%` and `/` in place of the explicit runtime calls.
TABLE = fixtures.TABLE.replace('s32 func_08142950(s32 numerator, s32 denominator);\n', '').replace(
    'func_08142950(i, 3) == 0', 'i % 3 == 0').replace(
    'func_08142950(count, i + 1)', 'count / (i + 1) + count % (i + 2)')
# The compiler's unsigned `/` and `%` beside the signed ones.
UNSIGNED = TABLE.replace('data_02001004[0](record->values,',
                         'record->weight += (u32)record->weight / 20u + (u32)i % 7u;\n'
                         '        data_02001004[0](record->values,')
# Unsigned only: never routed, and the composed selector refuses it.
UNSIGNED_ONLY = UNSIGNED.replace('i % 3 == 0', '(u32)i % 3u == 0').replace(
    'count / (i + 1) + count % (i + 2)', '(u32)count / (u32)(i + 1)')
# fixtures.FIELD (a callback read from the incoming record, no named data) with the compiler's `%`.
FIELD = fixtures.FIELD.replace('CALL', fixtures.CALLBACK).replace(
    's32 func_08142950(s32 numerator, s32 denominator);\n', '').replace(
    'func_08142950(region->first + start + i, region->count)', '(region->first + start + i) % region->count')
# The callback receives the address of a local: no thunk contract admits it.
ALIAS = TABLE.replace('    s32 i;\n', '    s32 i;\n    s32 local[2];\n').replace(
    'data_02001000[0](record, sizeof(record->values));',
    'data_02001000[0](local, sizeof(local)); record->weight = local[1];')


def arguments(**changes):
    values = dict(mode='thumb', control_flow_profile='ordinary', label=None)
    values.update({name: None for name in (
        'signed_quotient_profile', 'unsigned_quotient_profile', 'signed_runtime_profile',
        'unsigned_runtime_profile', 'addressed_signed_runtime_profile', 'software_double_profile',
        'software_double_remainder_profile', 'function_address_profile', 'switch_profile',
        'switch_data_profile', 'owner_runtime_profile', 'palette_closure_bundle')})
    values.update(changes)
    return argparse.Namespace(**values)


def image(*names, section=0):
    return {'symbols': [{'name': '', 'section': 0}, {'name': 'func_08010000', 'section': 1},
                        *({'name': name, 'section': section} for name in names)]}


class RoutePolicyTests(unittest.TestCase):
    """applies(): no selector, fixed toolchain, outside every unit, runtime and thunk named."""

    def test_routes_only_a_compiler_runtime_beside_a_thunk(self):
        for runtime in ('__modsi3', '__divsi3'):
            with self.subTest(runtime=runtime):
                self.assertTrue(POLICY.applies(arguments(), None, image(runtime, '_call_via_r3', 'data_02001000')))
                self.assertTrue(POLICY.applies(arguments(), None, image(runtime, '_call_via_r1')))
        for names in (('__modsi3',), ('_call_via_r3',), ('func_08142950', '_call_via_r3'),
                      ('func_081426B8', '_call_via_r2'), ('__udivsi3', '_call_via_r2'),
                      ('__umodsi3', '_call_via_r2'), ('__modsi3', 'func_0814224C')):
            with self.subTest(names=names):
                self.assertFalse(POLICY.applies(arguments(), None, image(*names)))
        # Defined symbols are the object's own, not the calls it makes.
        self.assertFalse(POLICY.applies(arguments(), None, image('__modsi3', '_call_via_r3', section=1)))

    def test_any_selector_unit_or_other_mode_keeps_the_plain_refusal(self):
        original = image('__modsi3', '_call_via_r3')
        self.assertFalse(POLICY.applies(arguments(), None, None), 'no object')
        self.assertFalse(POLICY.applies(arguments(), None, {'relocations': [1]}), 'no parsed symbol table')
        for gate in ('exploratory', {'unit': 'x', 'tool': {}}, {'consistent': True, 'source': 'x'}):
            with self.subTest(gate=gate):
                self.assertFalse(POLICY.applies(arguments(), gate, original))
        for change in (dict(mode='arm'), dict(control_flow_profile='inert-spin-v1'), dict(label='x'),
                       dict(function_address_profile='canonical-thunks-v1'),
                       dict(addressed_signed_runtime_profile=profile.THUNKS_DATA_SELECTOR),
                       dict(switch_data_profile='x'), dict(unsigned_quotient_profile='x'),
                       dict(palette_closure_bundle='x')):
            with self.subTest(change=change):
                self.assertFalse(POLICY.applies(arguments(**change), None, original))
        with patch.object(POLICY, 'enabled', False):
            self.assertFalse(POLICY.applies(arguments(), None, original))


@unittest.skipUnless(fixtures.TOOLS, 'fixed compiler and binutils required')
class CompilerRuntimeThunkTests(unittest.TestCase):
    UNSIGNED_SPANS = tuple(match.UDIVSI3_IDENTITIES) + tuple(profile.unsigned_remainder.IDENTITIES)

    @classmethod
    def setUpClass(cls):
        fixtures.SignedRuntimeThunkTests.setUpClass.__func__(cls)
        # Synthetic unsigned runtime bodies: each zero-path BL, digests pinned in this process only.
        for site in (0x08142B20, 0x08142BE0):
            cls.rom[site-match.ROM_BASE:site-match.ROM_BASE+4] = fixtures.bl(site, 0x0814274C)
        for module, field in ((match, 'UDIVSI3_IDENTITIES'), (profile.unsigned_remainder, 'IDENTITIES')):
            ids = tuple((lo, hi, hashlib.sha256(cls.rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                        for lo, hi, _ in getattr(module, field))
            change = patch.object(module, field, ids)
            change.start()
            cls.patches.append(change)
        cls.table = cls.make_root('compiler', TABLE, SELECTOR)
        cls.unsigned = cls.make_root('unsigned', UNSIGNED, SELECTOR)

    @classmethod
    def make_root(cls, name, source, selector):
        """The fixture's root, with the unsigned runtime spans also indexed."""
        spans = set(profile.quotient.IDENTITIES + profile.remainder.IDENTITIES)
        extra = sorted({(lo, hi) for lo, hi, _ in cls.UNSIGNED_SPANS} - {(lo, hi) for lo, hi, _ in spans})
        with patch.object(profile.quotient, 'IDENTITIES', profile.quotient.IDENTITIES +
                          tuple((lo, hi, '') for lo, hi in extra)):
            return fixtures.SignedRuntimeThunkTests.make_root.__func__(cls, name, source, selector)

    @classmethod
    def tearDownClass(cls):
        fixtures.SignedRuntimeThunkTests.tearDownClass.__func__(cls)

    build = fixtures.SignedRuntimeThunkTests.build
    def inputs(self, root, selector):
        """The fixture's verify() inputs, binding every runtime the selector's operations name."""
        result, values = fixtures.SignedRuntimeThunkTests.inputs(self, root, selector)
        operations = profile.operations(selector)
        values['bindings'] = {A+offset: name for offset, name in result['manifest']['calls'] if name in operations}
        values['calls'] = {**values['calls'], **{site: operations[name] for site, name in values['bindings'].items()}}
        return result, values
    patched = fixtures.SignedRuntimeThunkTests.patched
    copy_root = fixtures.SignedRuntimeThunkTests.copy_root

    def main(self, root, *options):
        """match.main() on root; returns (exit code or message, stdout)."""
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(root), *options, f'0x{A:08X}']), \
                redirect_stdout(io.StringIO()) as output:
            try:
                code = match.main()
            except SystemExit as exit:
                code = exit.code
        return code, output.getvalue()

    # Positive -----------------------------------------------------------

    def test_default_path_routes_reports_premises_and_replays(self):
        root = self.copy_root(self.table)
        code, output = self.main(root)
        self.assertEqual(code, 0, output)
        self.assertIn('verdict MATCH - byte identical', output)
        report = (root/'docs/match/08010000.md').read_text()
        self.assertEqual(profile.selector_for_report(report), SELECTOR)
        self.assertIn(f'* verification: `{SCHEMA}`', report.splitlines())
        manifest = json.loads(report.split('* addressed signed runtime evidence: `')[1].split('`')[0])['manifest']
        premises = [line for line in report.splitlines() if line.startswith('* ') and ': ' in line]
        for line in ('* compiler runtime binding: ' + profile.COMPILER_THUNKS_CONTRACT,
                     '* canonical thunk callee ABI: ' + profile.THUNK_CONTRACT,
                     '* named data binding: ' + profile.DATA_CONTRACT):
            self.assertIn(line, premises)
        self.assertEqual(manifest['schema'], SCHEMA)
        self.assertEqual(sorted({name for _, name, _ in manifest['compiler_runtime']['calls']}),
                         ['__divsi3', '__modsi3'])
        self.assertEqual(sorted({alias for _, alias, _ in manifest['thunks']['sites']}),
                         ['_call_via_r2', '_call_via_r3'])
        self.assertEqual(manifest['thunks']['target_policy'], profile.THUNK_TARGET_POLICY)
        self.assertGreaterEqual(len(manifest['local_long_branches']['edges']), 1)
        self.assertEqual(sorted(name for _, name, _ in manifest['data_bindings']), sorted(fixtures.OBJECTS))
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertEqual(status.collect(str(root), verify=False)[1], 1)
            for schema in (profile.THUNKS_DATA_SCHEMA, profile.COMPILER_DATA_SCHEMA):
                with self.subTest(forged=schema):
                    self.assertFalse(evidence.report_matches(report.replace(SCHEMA, schema), root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                '* compiler runtime binding: ', '* compiler runtime: '), root, A))
        # Status restores the schema's selector by name; the explicit run gives the same report.
        (root/'docs/match/08010000.md').unlink()
        self.assertEqual(self.main(root, '--addressed-signed-runtime-profile', SELECTOR)[0], 0)
        self.assertEqual((root/'docs/match/08010000.md').read_text(), report)

    # The policy's boundaries on the real default path ---------------------

    def test_disabled_policy_or_another_selector_keeps_the_plain_refusal(self):
        root = self.copy_root(self.table)
        with patch.object(POLICY, 'enabled', False):
            self.assertEqual(self.main(root), (f'compile failed:\n{PLAIN}{LEAF}', self.main(root)[1]))
            with patch.object(remainder_leaf.DIVISION, 'enabled', False):
                self.assertEqual(self.main(root), (f'compile failed:\n{PLAIN}', self.main(root)[1]))
        for options in (('--function-address-profile', 'canonical-thunks-v1'),
                        ('--flags', '-mthumb-interwork -O1')):          # an exploratory toolchain
            with self.subTest(options=options):
                code, _ = self.main(root, *options)
                self.assertNotIn('compiler signed runtime thunks', str(code))
                self.assertNotEqual(code, 0)
        self.assertFalse((root/'docs/match/08010000.md').exists())

    def test_a_refused_route_reports_both_refusals(self):
        root = self.make_root('alias', ALIAS, SELECTOR)
        route = f'compile failed:\n{PLAIN}; compiler signed runtime thunks: ' \
                'stack aliases cannot cross calls in caller-clobbered registers'
        code, output = self.main(root)
        self.assertEqual(code, route + LEAF)
        self.assertNotIn('MATCH', output)
        self.assertFalse((root/'docs/match/08010000.md').exists())
        with patch.object(remainder_leaf.DIVISION, 'enabled', False):
            self.assertEqual(self.main(root)[0], route)

    def test_an_unexpected_error_in_the_routed_build_fails_closed(self):
        root = self.copy_root(self.table)
        for error in (struct.error('bad pack'), AttributeError('no attribute'), KeyError('symbols')):
            with self.subTest(error=type(error).__name__), patch.object(profile, 'build', side_effect=error), \
                    patch.dict(os.environ, FFTA_TRACEBACK='0'):
                code, output = self.main(root)
            # The route fails closed; the leaf retry then runs its own complete walk, which refuses.
            self.assertEqual(code, f'compile failed:\n{PLAIN}; compiler signed runtime thunks: '
                                   f'{type(error).__name__}: {error}{LEAF}')
            self.assertNotIn('MATCH', output)
            self.assertFalse((root/'docs/match/08010000.md').exists())
        with patch.object(profile, 'build', side_effect=struct.error('bad pack')), \
                patch.dict(os.environ, FFTA_TRACEBACK='0'), patch.object(remainder_leaf.DIVISION, 'enabled', False):
            self.assertEqual(self.main(root)[0], f'compile failed:\n{PLAIN}; compiler signed runtime thunks: '
                                                 'error: bad pack')
        with patch.object(profile, 'build', side_effect=KeyboardInterrupt), \
                self.assertRaises(KeyboardInterrupt):
            self.main(root)
        with patch.object(profile, 'build', side_effect=struct.error('bad pack')), \
                patch.dict(os.environ, FFTA_TRACEBACK='1'), self.assertRaises(struct.error):
            self.main(root)

    def test_a_compile_error_is_still_a_plain_refusal(self):
        root = self.copy_root(self.table)
        (root/'src/08010000.c').write_text(TABLE + '\nint broken(\n')
        code, _ = self.main(root)
        self.assertTrue(str(code).startswith('compile failed:\n'), code)
        self.assertNotIn('compiler signed runtime thunks', str(code))

    # The composed selector keeps both rules --------------------------------

    def test_compiler_rules_explicit_names_and_typed_data(self):
        explicit = fixtures.TABLE
        with self.assertRaisesRegex(ValueError, 'reserve runtime|compiler runtime identifiers'):
            self.make_root('explicit', explicit, SELECTOR)
        # Explicit runtime calls are not routed: they belong to the explicit thunks selectors.
        root = self.make_root('explicit_table', explicit, profile.THUNKS_DATA_SELECTOR)
        code, _ = self.main(root)
        self.assertNotIn('compiler signed runtime thunks', str(code))
        with self.assertRaisesRegex(ValueError, 'actual typed bindings'):
            profile.original_bindings({'symbols': []}, A, b'', b'[]', selector=SELECTOR)
        # The data-free shape is routed (it names a runtime and a thunk) but refused accurately.
        with self.assertRaisesRegex(ValueError, '^compiler runtime thunks require actual typed data$'):
            self.make_root('field', FIELD, SELECTOR)
        for selector in (profile.COMPILER_DATA_SELECTOR, profile.THUNKS_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.build(self.table, selector)

    def test_thunk_targets_and_runtime_identities_stay_checked(self):
        result, values = self.inputs(self.table, SELECTOR)
        manifest = result['manifest']
        self.assertEqual(profile.verify(**values, manifest=manifest, selector=SELECTOR)[0], manifest)
        site, _, loads = manifest['thunks']['sites'][0]
        register = (values['calls'][A+site] - match.function_thunk.START) // 4
        with self.assertRaisesRegex(ValueError, 'memory word load on every path'):
            profile.verify(**self.patched(values, site - 2, 0x2001 | register << 8), selector=SELECTOR)
        rom = bytearray(values['rom']); rom[profile.remainder.ADDRESS-match.ROM_BASE] ^= 1
        with self.assertRaises(ValueError):
            profile.verify(**dict(values, rom=bytes(rom)), selector=SELECTOR)
        for change in ('runtime', 'alias', 'contract'):
            bad = copy.deepcopy(manifest)
            if change == 'runtime': bad['compiler_runtime']['calls'][0][1] = '__udivsi3'
            elif change == 'alias': bad['thunks']['sites'][0][1] = '_call_via_r1'
            else: bad['compiler_runtime']['contract'] += ' '
            with self.subTest(change=change), self.assertRaises(ValueError):
                profile.verify(**values, manifest=bad, selector=SELECTOR)

    # Unsigned runtimes beside a signed one -------------------------------------

    def test_unsigned_runtimes_bind_beside_a_signed_one(self):
        root = self.copy_root(self.unsigned)
        code, output = self.main(root)
        self.assertEqual(code, 0, output)
        report = (root/'docs/match/08010000.md').read_text()
        manifest = json.loads(report.split('* addressed signed runtime evidence: `')[1].split('`')[0])['manifest']
        self.assertEqual(sorted({tuple(row[1:]) for row in manifest['compiler_runtime']['calls']}),
                         [('__divsi3', 'func_081426B8'), ('__modsi3', 'func_08142950'),
                          ('__udivsi3', 'func_08142AB0'), ('__umodsi3', 'func_08142B28')])
        self.assertEqual(manifest['compiler_runtime']['contract'], profile.COMPILER_THUNKS_CONTRACT)
        self.assertIn('* compiler runtime binding: ' + profile.COMPILER_THUNKS_CONTRACT, report.splitlines())
        spans = {tuple(row[:2]) for row in manifest['dependencies']}
        for lo, hi, _ in self.UNSIGNED_SPANS:
            self.assertIn((lo, hi), spans)
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')):
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertFalse(evidence.report_matches(
                report.replace('"__udivsi3","func_08142AB0"', '"__udivsi3","func_08142B28"', 1), root, A))

    def test_an_unsigned_alias_at_the_wrong_entry_or_an_unpinned_body_is_refused(self):
        result, values = self.inputs(self.unsigned, SELECTOR)
        self.assertEqual(profile.verify(**values, manifest=result['manifest'], selector=SELECTOR)[0],
                         result['manifest'])
        sites = {name: next(site for site, bound in values['bindings'].items() if bound == name)
                 for name in ('func_08142AB0', 'func_08142B28')}
        for name, wrong in (('func_08142AB0', 0x08142B28), ('func_08142B28', 0x08142AB0)):
            site = sites[name]
            data = bytearray(values['data']); data[site-A:site-A+4] = fixtures.bl(site, wrong)
            rom = bytearray(values['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            moved = dict(values, data=bytes(data), rom=bytes(rom), calls={**values['calls'], site: wrong})
            with self.subTest(bound=name, entry=hex(wrong)), self.assertRaises(ValueError):
                profile.verify(**moved, selector=SELECTOR)
            renamed = {**values['bindings'], site: next(other for other in sites if other != name)}
            with self.subTest(renamed=name), self.assertRaises(ValueError):
                profile.verify(**dict(values, bindings=renamed), selector=SELECTOR)
        for lo, _, _ in self.UNSIGNED_SPANS:
            rom = bytearray(values['rom']); rom[lo-match.ROM_BASE] ^= 1
            with self.subTest(unpinned=hex(lo)), self.assertRaisesRegex(ValueError, 'identity differs|dependency'):
                profile.verify(**dict(values, rom=bytes(rom)), selector=SELECTOR)

    def test_unsigned_names_stay_closed_elsewhere(self):
        self.assertEqual(profile.compiler_aliases(profile.COMPILER_DATA_SELECTOR), profile.COMPILER_ALIASES)
        self.assertEqual(profile.operations(profile.COMPILER_DATA_SELECTOR), profile.OPERATIONS)
        with self.assertRaisesRegex(ValueError, 'canonical addressed function'):
            self.make_root('unsigned_data', UNSIGNED, profile.COMPILER_DATA_SELECTOR)
        # Explicit unsigned runtime identifiers are not compiler emission.
        explicit = UNSIGNED.replace('typedef void (*Clear)', 'u32 func_08142AB0(u32, u32);\ntypedef void (*Clear)')
        with self.assertRaisesRegex(ValueError, 'reserve runtime|compiler runtime identifiers'):
            self.make_root('explicit_unsigned', explicit, SELECTOR)
        # An object naming the explicit unsigned entry at a BL relocation is refused by the
        # linker step itself, not only by the source namespace check that runs first.
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=self.unsigned, timeout=120)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, self.args, self.unsigned, A, 'src/08010000.c')
        for symbols in (image['symbols'], *image['symbol_tables'].values()):
            for item in symbols:
                if item['name'] == '__udivsi3':
                    item['name'] = 'func_08142AB0'
        rom, mapping = (self.unsigned/'baserom.bin').read_bytes(), (self.unsigned/'config/functions.json').read_bytes()
        with self.assertRaisesRegex(ValueError, 'original compiler-emitted names'):
            profile.original_bindings(image, A, rom, mapping, selector=SELECTOR,
                                      data_mapping=(self.unsigned/'config/data_symbols.json').read_bytes(),
                                      data_relocations={})
        # Unsigned runtimes alone are neither routed nor admitted by the composed selector.
        root = self.make_root('unsigned_only', UNSIGNED_ONLY, SELECTOR)
        with self.assertRaisesRegex(ValueError, 'actual signed runtime call'):
            self.build(root, SELECTOR)
        code, _ = self.main(root)
        self.assertNotIn('compiler signed runtime thunks', str(code))
        self.assertNotEqual(code, 0)


if __name__ == '__main__':
    unittest.main()
