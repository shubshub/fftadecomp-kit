"""Untyped fixed hardware addresses stay plain numbers in the BIOS fill selectors only."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import bios_fast_fill_source_profile as fast
import m4a_max_lines as max_lines
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_cpuset_fill_profile as fill
import test_bios_fast_fill_source as fast_tests
import test_bios_fill_readonly_four_words as four_words
import test_bios_fill_readonly_three_words as three_words
import test_bios_fill_readonly_word as one_word
import test_bios_function_literals as function_literals
import test_bios_mixed_cpuset_fast_fill as cpuset_tests
import test_bios_mixed_fast_fill_source as mixed_tests
import test_bios_numeric_mmio_literals as mmio
import test_bios_saved_scalar_mmio_literals as saved
import test_bios_scalar_control as scalar
import test_bios_scalar_function_literals as scalar_function_literals
import test_bios_zero_extended_control as zero_extended
import test_cpuset_code_image as code_image
import test_named_bios_fill_source as named_fill
import test_runtime_summary_profile as runtime_tests
import unsigned_thunk_profile

profile, match, bios, A, B = fill.profile, fill.match, fill.bios, fill.A, fill.B
indexes, bl = fill.fixtures.fixtures.indexes, fill.fixtures.fixtures.bl
VRAM, PALETTE, OAM, IO = 0x0600B1E0, 0x05000200, 0x07000000, 0x04000008
MOVS_R1_0, LDR_R1 = 0x2100, 0x4900
WRAPPERS = (bios.ADDRESS, fast.ADDRESS)
OWNER_SELECTORS = (buffers.BIOS_FILL_SELECTOR, buffers.BIOS_LOCAL_FILL_SELECTOR,
                   buffers.BIOS_OVERWRITE_SELECTOR, buffers.FAST_FILL_SELECTOR,
                   buffers.MIXED_FAST_FILL_SELECTOR, buffers.MIXED_CPUSET_FAST_FILL_SELECTOR,
                   buffers.RUNTIME_SUMMARY_FAST_FILL_SELECTOR)
ADDRESSED_SELECTORS = (
    profile.BIOS_DATA_SELECTOR, profile.BIOS_ZERO_EXTENDED_DATA_SELECTOR,
    profile.BIOS_SCALAR_DATA_SELECTOR, profile.BIOS_SCALAR_MMIO_DATA_SELECTOR,
    profile.BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR, profile.BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR,
    profile.BIOS_SCALAR_CODE_IMAGE_SELECTOR, profile.BIOS_READONLY_DATA_SELECTOR,
    profile.BIOS_READONLY_THREE_DATA_SELECTOR, profile.BIOS_READONLY_FOUR_DATA_SELECTOR,
    profile.BIOS_FUNCTION_DATA_SELECTOR, profile.BIOS_SCALAR_FUNCTION_DATA_SELECTOR)


def calls_of(f):
    if 'calls' in f:
        return dict(f['calls'])
    return {A + offset: int(name[5:], 16) for offset, name in f['bindings']['calls']}


def replace_word(f, data):
    rom = bytearray(f['rom'])
    rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
    rows = json.loads(f['mapping'])
    rows[0].update(end=f'0x{A+len(data):08X}')
    mapping, index = indexes(rows)
    return dict(f, data=bytes(data), rom=bytes(rom), mapping=mapping, index=index)


def numeric_destination(f, value, word=None):
    """Load the last fill's destination R1 from a pool word holding ``value``.

    The fixtures pass ``movs r1, #0``; it becomes ``ldr r1, [pc, #n]`` of the
    same size. ``word`` reuses an existing pool word instead of a new one.
    Returns the fixture, the pool offset and the load offset.
    """
    data = bytearray(f['data'])
    last = max(site for site, target in calls_of(f).items() if target in WRAPPERS) - A
    load = next(offset for offset in range(last-2, last-8, -2)
                if struct.unpack_from('<H', data, offset)[0] == MOVS_R1_0)
    if word is None:
        if len(data) % 4:
            data += b'\0\0'
        word = len(data)
        data += struct.pack('<I', value)
    struct.pack_into('<H', data, load, LDR_R1 | ((word - ((load+4) & ~3)) // 4))
    return replace_word(f, data), word, load


def record(rows):
    return dict(schema=owner.NUMERIC_HARDWARE_SCHEMA, words=rows, contract=owner.NUMERIC_HARDWARE_CONTRACT)


def helper(case, module_class):
    instance = module_class('runTest')
    instance.setUp()
    case.addCleanup(instance.doCleanups)
    return instance


class OwnerNumericHardwareWordTests(unittest.TestCase):
    def setUp(self):
        self.named = helper(self, named_fill.NamedBiosFillTests)
        self.fast = helper(self, fast_tests.FastFillSourceTests)
        self.mixed = helper(self, mixed_tests.MixedFastFillTests)
        self.cpuset = helper(self, cpuset_tests.MixedCpuSetFastFillTests)

    def fixture(self, selector, value=VRAM, **changes):
        base = self.named.fixture(**changes) if selector in (
            buffers.BIOS_FILL_SELECTOR, buffers.BIOS_LOCAL_FILL_SELECTOR, buffers.BIOS_OVERWRITE_SELECTOR) else \
            self.fast.fixture(**changes) if selector == buffers.FAST_FILL_SELECTOR else \
            self.mixed.fixture(**changes) if selector == buffers.MIXED_FAST_FILL_SELECTOR else \
            self.cpuset.fixture(**changes)
        return numeric_destination(dict(base, selector=selector), value)

    def test_each_owner_fill_selector_records_reached_untyped_hardware_words(self):
        for selector in OWNER_SELECTORS[:-1]:
            for value in (VRAM, PALETTE, OAM, IO, 0x04000000, 0x07FFFFFC):
                with self.subTest(selector=selector, value=hex(value)):
                    f, word, load = self.fixture(selector, value)
                    manifest, _ = owner.verify(**f)
                    self.assertEqual(manifest['proof']['numeric_hardware_words'],
                                     record([[word, value, [load]]]))
                    self.assertNotIn(word, [row[0] for row in f['bindings']['data']])
                    self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)

    def test_ram_and_rom_words_still_need_typed_provenance(self):
        for selector in OWNER_SELECTORS[:-1]:
            for value in (0x02000000, 0x03000020, 0x03FFFFFC, 0x08000000, 0x08010000):
                with self.subTest(selector=selector, value=hex(value)), \
                        self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
                    owner.verify(**self.fixture(selector, value)[0])

    def test_rom_wait_state_mirror_words_need_typed_provenance_as_rom_words(self):
        # 0x0A000000-0x0DFFFFFF maps the same ROM as 0x08000000-0x09FFFFFF (#377).
        for selector in OWNER_SELECTORS[:-1]:
            for value in (0x0A000000, 0x0A010000, 0x0C010000, 0x0AFFFFFC):
                with self.subTest(selector=selector, value=hex(value)):
                    f = self.fixture(selector, value)[0]
                    with self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
                        owner.verify(**f)
                    with self.assertRaisesRegex(ValueError, f'genuine named object proof at {value:08X}'):
                        owner.preflight(*(f[k] for k in ('data', 'address', 'rom', 'mapping', 'index', 'objects')),
                                        selector=selector)
            # SRAM/flash words, and mirrors of the space past the 16 MiB image, stay numbers.
            for value in (0x0E000000, 0x0FFFFFFF, 0x0BFFFFFC):
                with self.subTest(selector=selector, value=hex(value)):
                    f = self.fixture(selector, value)[0]
                    manifest, _ = owner.verify(**f)
                    self.assertNotIn('numeric_hardware_words', manifest['proof'])
                    owner.preflight(*(f[k] for k in ('data', 'address', 'rom', 'mapping', 'index', 'objects')),
                                    selector=selector)

    def test_a_typed_object_spelled_through_a_rom_mirror_is_refused(self):
        for selector in (buffers.BIOS_FILL_SELECTOR, buffers.MIXED_FAST_FILL_SELECTOR):
            for value in (0x08100000, 0x0A100000, 0x0C100000):
                with self.subTest(selector=selector, value=hex(value)):
                    f, word, _ = self.fixture(selector, value)
                    objects = dict(json.loads(f['objects']), data_06000000='0x06000000')
                    typed = copy.deepcopy(dict(f, objects=json.dumps(objects).encode()))
                    typed['bindings']['data'] = sorted(typed['bindings']['data'] +
                                                       [[word, 'data_06000000', value - 0x06000000]])
                    if value < 0x09000000:
                        owner.verify(**typed)
                        continue
                    with self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
                        owner.verify(**typed)

    def test_typed_hardware_words_stay_typed_and_old_manifests_keep_their_form(self):
        f, word, _ = self.fixture(buffers.BIOS_FILL_SELECTOR)
        objects = dict(json.loads(f['objects']), data_0600B1E0=f'0x{VRAM:08X}')
        typed = copy.deepcopy(dict(f, objects=json.dumps(objects).encode()))
        typed['bindings']['data'] = sorted(typed['bindings']['data'] + [[word, 'data_0600B1E0', 0]])
        self.assertNotIn('numeric_hardware_words', owner.verify(**typed)[0]['proof'])
        for selector, plain in ((buffers.BIOS_FILL_SELECTOR, self.named.fixture()),
                                (buffers.FAST_FILL_SELECTOR, self.fast.fixture()),
                                (buffers.MIXED_FAST_FILL_SELECTOR, self.mixed.fixture()),
                                (buffers.MIXED_CPUSET_FAST_FILL_SELECTOR, self.cpuset.fixture())):
            with self.subTest(selector=selector):
                self.assertNotIn('numeric_hardware_words', owner.verify(**plain)[0]['proof'])

    def test_edited_dropped_extended_or_relabelled_lists_fail_replay(self):
        f, word, load = self.fixture(buffers.BIOS_FILL_SELECTOR, control=0x05000010)
        manifest, _ = owner.verify(**f)
        proof = manifest['proof']
        [control] = proof['bios_scalar_control_words']
        self.assertEqual(control[1], 0x05000010)
        self.assertEqual(proof['numeric_hardware_words']['words'], [[word, VRAM, [load]]])
        typed = f['bindings']['data'][0][0]
        forgeries = []
        for change in ('value', 'drop', 'extend', 'typed', 'control', 'contract', 'schema'):
            forged = copy.deepcopy(manifest)
            hardware = forged['proof']['numeric_hardware_words']
            if change == 'value':
                hardware['words'][0][1] += 4
            elif change == 'drop':
                del forged['proof']['numeric_hardware_words']
            elif change == 'extend':
                hardware['words'].append([word+4, VRAM+4, [load]])
            elif change == 'typed':
                hardware['words'].insert(0, [typed, 0x03000020, [4]])
            elif change == 'control':
                hardware['words'].insert(0, [control[0], control[1], [load for load, _ in control[2]]])
                forged['proof']['bios_scalar_control_words'] = []
            elif change == 'contract':
                hardware['contract'] = 'forged'
            else:
                hardware['schema'] = 'forged'
            forgeries.append((change, forged))
        for change, forged in forgeries:
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**f, manifest=forged)
        plain = self.named.fixture()
        manifest, _ = owner.verify(**plain)
        forged = copy.deepcopy(manifest)
        forged['proof']['numeric_hardware_words'] = record([])
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**plain, manifest=forged)

    def test_word_loaded_as_scalar_control_and_as_address_refuses(self):
        base = self.named.fixture(control=0x05000010)
        control = owner.verify(**base)[0]['proof']['bios_scalar_control_words'][0][0]
        f, _, _ = numeric_destination(base, None, word=control)
        with self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
            owner.verify(**f)

    def test_other_owner_selectors_still_require_types_for_hardware_words(self):
        # An ordinary leaf in place of the wrapper: named-data-buffer-v1 admits
        # the owner with movs r1, #0 and refuses the numeric VRAM destination.
        def ordinary(f):
            data = bytearray(f['data'])
            [[offset, _]] = f['bindings']['calls']
            data[offset:offset+4] = bl(A+offset, B)
            return dict(replace_word(f, data), selector=buffers.SELECTOR,
                        bindings=dict(f['bindings'], calls=[[offset, f'func_{B:08X}']]))
        owner.verify(**ordinary(self.named.fixture()))
        with self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
            owner.verify(**ordinary(self.fixture(buffers.BIOS_FILL_SELECTOR)[0]))


class RuntimeSummaryNumericHardwareWordTests(unittest.TestCase):
    """Separate from the fill fixtures, which pin synthetic runtime identities."""

    def fixture(self, value):
        """A summarised __modsi3 call, then a CpuFastSet fill of R1 = value."""
        tests = runtime_tests.RuntimeSummaryTests('runTest')
        tests.setUpClass()  # skips without the approved ROM
        tests.setUp()
        self.addCleanup(tests.doCleanups)
        f = tests.fixture(f'.thumb_set fast_fill, 0x{fast.ADDRESS | 1:08X}\n'
            'push {r4, lr}\nsub sp, #8\nmov r0, sp\nbl callee\nmovs r0, #7\nmovs r1, #3\n'
            f'bl rt_{runtime_tests.MOD:08X}\nmov r0, sp\nldr r1, =0x{value:08X}\n'
            'movs r2, #0x80\nlsls r2, r2, #17\nbl fast_fill\n' + runtime_tests.EPILOGUE + '\n.ltorg',
            selector=buffers.RUNTIME_SUMMARY_FAST_FILL_SELECTOR)
        rows = json.loads(f['mapping'])
        rows.append(dict(rom=f'0x{fast.ADDRESS:08X}', end=f'0x{fast.ADDRESS+4:08X}', mode='thumb', instrs=2))
        rom = bytearray(f['rom'])
        rom[fast.ADDRESS-match.ROM_BASE:fast.ADDRESS-match.ROM_BASE+4] = fast.WRAPPER
        mapping, index = indexes(rows)
        f.update(rom=bytes(rom), mapping=mapping, index=index)
        word = len(f['data']) - 4
        load = next(offset for offset in range(0, word, 2)
                    if struct.unpack_from('<H', f['data'], offset)[0] & 0xFF00 == LDR_R1)
        return f, word, load

    def test_runtime_summary_fill_records_and_replays_a_numeric_destination(self):
        f, word, load = self.fixture(VRAM)
        manifest, _ = owner.verify(**f)
        self.assertEqual(manifest['proof']['numeric_hardware_words'], record([[word, VRAM, [load]]]))
        self.assertEqual(owner.verify(**f, manifest=manifest)[0], manifest)
        for value in (0x03000020, 0x08000000):
            with self.subTest(value=hex(value)), \
                    self.assertRaisesRegex(ValueError, 'exact typed object/function coverage'):
                owner.verify(**self.fixture(value)[0])


class AddressedNumericHardwareWordTests(unittest.TestCase):
    def setUp(self):
        self.fill = helper(self, fill.BiosCpuSetFillTests)
        self.zero = helper(self, zero_extended.BiosZeroExtendedControlTests)
        self.scalar = helper(self, scalar.BiosScalarControlTests)
        self.mmio = helper(self, mmio.BiosNumericMmioLiteralTests)
        self.saved = helper(self, saved.BiosSavedScalarMmioLiteralTests)
        self.code = helper(self, code_image.CpuSetCodeImageTests)
        self.one = helper(self, one_word.BiosReadonlyWordTests)
        self.three = helper(self, three_words.BiosReadonlyThreeWordsTests)
        self.four = helper(self, four_words.BiosReadonlyFourWordsTests)
        self.function = helper(self, function_literals.BiosFunctionLiteralTests)
        self.scalar_function = helper(self, scalar_function_literals.BiosScalarFunctionLiteralTests)

    def base(self, selector):
        if selector == profile.BIOS_DATA_SELECTOR:
            return self.fill.fixture(data=True)
        if selector == profile.BIOS_ZERO_EXTENDED_DATA_SELECTOR:
            return self.zero.fixture((zero_extended.LDRB_R1_R3, zero_extended.ORRS_R2_R1))
        if selector == profile.BIOS_SCALAR_DATA_SELECTOR:
            return self.scalar.fixture()
        if selector == profile.BIOS_SCALAR_MMIO_DATA_SELECTOR:
            return self.mmio.fixture()
        if selector == profile.BIOS_SAVED_SCALAR_MMIO_DATA_SELECTOR:
            return self.saved.fixture()
        if selector == profile.BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR:
            # The stored object word becomes a numeric MMIO literal.
            f = self.code.fixture(selector=selector)
            offset = f['data_bindings'][0][0]
            data = bytearray(f['data'])
            struct.pack_into('<I', data, offset, 0x04000134)
            return dict(replace_word(f, data), data_bindings=f['data_bindings'][1:])
        if selector == profile.BIOS_SCALAR_CODE_IMAGE_SELECTOR:
            return self.code.fixture()
        if selector == profile.BIOS_READONLY_DATA_SELECTOR:
            return self.one.fixture()
        if selector == profile.BIOS_READONLY_THREE_DATA_SELECTOR:
            return self.three.fixture()
        if selector == profile.BIOS_READONLY_FOUR_DATA_SELECTOR:
            return self.four.fixture()
        if selector == profile.BIOS_FUNCTION_DATA_SELECTOR:
            return self.function.fixture()
        return self.scalar_function.fixture()

    def fixture(self, selector, value=VRAM):
        f = self.base(selector)
        self.assertEqual(f['selector'], selector)
        return numeric_destination(f, value)

    def test_selector_set_is_exactly_the_bios_fill_data_selectors(self):
        # The MPlayExtender selector is a BIOS fill data selector under its own
        # name: its saved report records three numeric hardware words.
        self.assertEqual(set(profile.NUMERIC_HARDWARE_SELECTORS),
                         set(ADDRESSED_SELECTORS) | {max_lines.SELECTOR})
        self.assertEqual({selector for selector in profile.SCHEMAS
                          if selector.startswith('addressed-native-bios-fill-') and selector.endswith('-data-v1')},
                         set(ADDRESSED_SELECTORS))
        self.assertEqual(owner.NUMERIC_HARDWARE, unsigned_thunk_profile.HARDWARE)

    def test_each_addressed_fill_data_selector_records_untyped_hardware_words(self):
        for selector in ADDRESSED_SELECTORS:
            with self.subTest(selector=selector):
                f, word, load = self.fixture(selector)
                manifest, _ = profile.verify(**f)
                self.assertEqual(manifest['numeric_hardware_words'], record([[word, VRAM, [load]]]))
                self.assertNotIn(word, [row[0] for row in manifest['data_bindings']])
                self.assertEqual(profile.verify(**f, manifest=manifest)[0], manifest)
                plain = self.base(selector)
                self.assertNotIn('numeric_hardware_words', profile.verify(**plain)[0])

    def test_typed_hardware_words_stay_typed(self):
        for selector in (profile.BIOS_DATA_SELECTOR, profile.BIOS_SCALAR_DATA_SELECTOR,
                         profile.BIOS_SCALAR_MMIO_DATA_SELECTOR):
            with self.subTest(selector=selector):
                f, word, _ = self.fixture(selector)
                objects = dict(json.loads(f['data_mapping']), data_0600B1E0=f'0x{VRAM:08X}')
                typed = dict(f, data_mapping=json.dumps(objects).encode(),
                             data_bindings=sorted(f['data_bindings'] + [[word, 'data_0600B1E0', 0]]))
                manifest, _ = profile.verify(**typed)
                self.assertNotIn('numeric_hardware_words', manifest)
                self.assertIn([word, 'data_0600B1E0', 0], manifest['data_bindings'])

    def test_numeric_mmio_keeps_its_class_and_controls_stay_controls(self):
        f, word, load = self.fixture(profile.BIOS_SCALAR_MMIO_DATA_SELECTOR)
        manifest, _ = profile.verify(**f)
        mmio_words = manifest['numeric_mmio_literals']['words']
        self.assertEqual([row[1] for row in mmio_words], [0x04000134])
        self.assertEqual(manifest['numeric_hardware_words']['words'], [[word, VRAM, [load]]])
        controls = manifest['bios_scalar_control']['words']
        self.assertEqual([row[1] for row in controls], [0x05000010])
        offsets = [{row[0] for row in rows} for rows in (mmio_words, controls,
                   manifest['numeric_hardware_words']['words'])]
        self.assertFalse(offsets[0] & offsets[1] or offsets[0] & offsets[2] or offsets[1] & offsets[2])
        # Without a separate hardware word the MMIO selector records no new class.
        self.assertNotIn('numeric_hardware_words', profile.verify(**self.mmio.fixture())[0])
        # Outside the MMIO selectors a halfword-aligned I/O word is a hardware word.
        f, word, load = self.fixture(profile.BIOS_SCALAR_DATA_SELECTOR, 0x04000134)
        manifest, _ = profile.verify(**f)
        self.assertNotIn('numeric_mmio_literals', manifest)
        self.assertEqual(manifest['numeric_hardware_words']['words'], [[word, 0x04000134, [load]]])

    def test_hardware_range_control_is_a_control_or_stays_refused(self):
        # A 32-bit CpuSet fill control lies in the hardware window. The scalar
        # selectors record it as a control; the others still need a type.
        f = self.fill.fixture(data=True, control=0x05000010)
        with self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
            profile.verify(**f)
        manifest, _ = profile.verify(**dict(f, selector=profile.BIOS_SCALAR_DATA_SELECTOR))
        self.assertNotIn('numeric_hardware_words', manifest)
        self.assertEqual([row[1] for row in manifest['bios_scalar_control']['words']], [0x05000010])
        # A saved (r4-r7) control is computed only by the saved selector.
        f = self.saved.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual([row[1] for row in manifest['bios_saved_scalar_control']['words']], [0x05000001])
        self.assertNotIn('numeric_hardware_words', manifest)
        with self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
            profile.verify(**dict(f, selector=profile.BIOS_SCALAR_MMIO_DATA_SELECTOR))

    def test_word_loaded_as_scalar_control_and_as_address_refuses(self):
        # The direct control of the last fill is also loaded as its destination.
        base = self.saved.fixture()
        direct = profile.verify(**base)[0]['bios_scalar_control']['words'][0][0]
        f, _, _ = numeric_destination(base, None, word=direct)
        # The saved control still satisfies the selector; the mixed word is refused.
        with self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
            profile.verify(**f)
        base = self.scalar.fixture()
        control = profile.verify(**base)[0]['bios_scalar_control']['words'][0][0]
        f, _, _ = numeric_destination(base, None, word=control)
        with self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
            profile.verify(**dict(f, selector=profile.BIOS_DATA_SELECTOR))
        # The scalar selector loses its only control, which it already refuses.
        with self.assertRaisesRegex(ValueError, 'actual literal control use'):
            profile.verify(**f)

    def test_ram_rom_and_cartridge_words_still_need_typed_provenance(self):
        for selector in (profile.BIOS_DATA_SELECTOR, profile.BIOS_SCALAR_DATA_SELECTOR,
                         profile.BIOS_SCALAR_MMIO_DATA_SELECTOR):
            for value in (0x02000000, 0x03000020, 0x03FFFFFC, 0x08000000, 0x08010000, 0x0E000000):
                with self.subTest(selector=selector, value=hex(value)), \
                        self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
                    profile.verify(**self.fixture(selector, value)[0])

    def test_other_addressed_data_selectors_still_refuse_hardware_words(self):
        # With a non-local source the ordinary BIOS data selector admits the
        # plain owner and still refuses the numeric VRAM destination.
        plain = dict(self.fill.fixture(data=True, source=0x2000), selector=profile.BIOS_ORDINARY_DATA_SELECTOR)
        profile.verify(**plain)
        with self.assertRaisesRegex(ValueError, 'exact typed coverage of reached address words'):
            profile.verify(**numeric_destination(plain, VRAM)[0])
        # The data-free fill selector still excludes every address literal.
        plain = self.fill.fixture()
        self.assertEqual(plain['selector'], profile.BIOS_SELECTOR)
        profile.verify(**plain)
        with self.assertRaisesRegex(ValueError, 'exclude address literals and data bindings'):
            profile.verify(**numeric_destination(plain, VRAM)[0])

    def test_cli_report_replays_and_refuses_an_edited_numeric_list(self):
        f, word, load = self.fixture(profile.BIOS_SCALAR_DATA_SELECTOR)
        with self.fill.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            row = json.dumps([[word, VRAM, [load]]], separators=(',', ':'))
            self.assertIn(row, report)
            for forged in (row.replace(str(VRAM), str(VRAM+4)),
                           json.dumps([[word, VRAM, [load]], [word+4, VRAM, [load]]], separators=(',', ':')),
                           '[]'):
                with self.subTest(forged=forged):
                    self.assertFalse(evidence.report_matches(report.replace(row, forged), root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                owner.NUMERIC_HARDWARE_SCHEMA, 'forged-numeric-literals-v1'), root, A))


if __name__ == '__main__':
    unittest.main()
