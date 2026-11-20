"""Compiler-emitted signed arithmetic with a bounded CpuSet scalar fill."""
import copy
import json
import unittest

import test_bios_cpuset_fill_profile as fill

profile, bios, match = fill.profile, fill.bios, fill.match
A = fill.A
SELECTOR = profile.COMPILER_BIOS_SCALAR_DATA_SELECTOR


class CompilerBiosScalarControlTests(unittest.TestCase):
    def setUp(self):
        self.fill = fill.BiosCpuSetFillTests('runTest')
        self.fill.setUp()
        self.addCleanup(self.fill.doCleanups)

    def fixture(self, **kwargs):
        f = self.fill.fixture(prefix=('ordinary',), data=True, control=0x05000010, **kwargs)
        site = next(site for site, target in f['calls'].items() if target == fill.B)
        mod = profile.remainder.ADDRESS
        f['calls'][site] = mod
        f['bindings'][site] = profile.remainder.ADDRESSED_NAME
        raw = bytearray(f['data'])
        raw[site-A:site-A+4] = fill.fixtures.fixtures.bl(site, mod)
        f['data'] = bytes(raw)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(raw)] = raw
        rows = json.loads(f['mapping'])
        for lo, hi, _ in profile.remainder.IDENTITIES:
            start, end = lo - match.ROM_BASE, hi - match.ROM_BASE
            rom[start:end] = self.fill.base.rom[start:end]
            rows.append(dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb', instrs=(hi-lo)//2))
        f.update(rom=bytes(rom), selector=SELECTOR)
        f['mapping'], f['index'] = fill.fixtures.fixtures.indexes(rows)
        return f

    def test_native_composition_and_rejections(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        self.assertEqual(manifest['compiler_runtime']['calls'],
                         [[next(iter(f['calls'])) - A, '__modsi3', profile.remainder.ADDRESSED_NAME]])
        self.assertEqual(manifest['native_buffers']['bios_fill']['sites'][0][2], 4)
        self.assertEqual(manifest['bios_scalar_control']['words'][0][1], 0x05000010)
        self.assertFalse(manifest['arithmetic_C_equivalence'])
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data_bindings=[]))
        for name in ('__modsi3', profile.remainder.ADDRESSED_NAME):
            with self.assertRaises(ValueError):
                profile.compiler_namespace('extern int ' + name + '(int, int);', SELECTOR)
        only_fill = self.fill.fixture(data=True, control=0x05000010)
        only_fill['selector'] = SELECTOR
        for bad in (self.fixture(source=0xa801), only_fill, dict(f, selector=profile.COMPILER_DATA_SELECTOR)):
            with self.assertRaises(ValueError):
                profile.verify(**bad)
        for target in (profile.remainder.ADDRESS, bios.ADDRESS):
            rom = bytearray(f['rom'])
            rom[target-match.ROM_BASE] ^= 1
            with self.assertRaises(ValueError):
                profile.verify(**dict(f, rom=bytes(rom)))
        forged = copy.deepcopy(manifest)
        forged['compiler_runtime']['calls'][0][1] = '__divsi3'
        with self.assertRaises(ValueError):
            profile.verify(**f, manifest=forged)

    def test_compiler_alias_and_bios_relocations_are_distinct(self):
        f = self.fixture()
        image = self.fill.base.data_image(f)
        def bind(image, selector):
            return profile.original_bindings(image, A, f['rom'], f['mapping'],
                data_mapping=f['data_mapping'], data_relocations={}, selector=selector)
        with self.assertRaises(ValueError):
            bind(image, SELECTOR)
        symbol = next(sym for sym in image['symbols'] if sym['name'] == profile.remainder.ADDRESSED_NAME)
        symbol['name'] = '__modsi3'
        calls, _, targets = bind(image, SELECTOR)
        self.assertEqual(calls, f['calls'])
        self.assertEqual(targets['__modsi3'], profile.remainder.ADDRESS)
        self.assertEqual(targets[bios.NAME], bios.ADDRESS)
        with self.assertRaises(ValueError):
            bind(image, profile.BIOS_SCALAR_DATA_SELECTOR)
        for bad in ('__umodsi3', 'func_08142B28', 'func_08142952'):
            symbol['name'] = bad
            with self.assertRaises(ValueError):
                bind(image, SELECTOR)
