"""Mixed CpuFastSet calls retain native frame, effect and binding checks."""
import copy
import json
import unittest

import bios_fast_fill_source_profile as fast
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_cpuset_fill_profile as fixtures


class MixedFastFillTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, **changes):
        changes.setdefault('prefix', ('ordinary', 0x2280, 0x0452))
        f = self.base.fixture(**changes)
        data, rom = bytearray(f['data']), bytearray(f['rom'])
        calls = {}
        for site, target in f['calls'].items():
            target = fast.ADDRESS if target == fixtures.bios.ADDRESS else target
            data[site-fixtures.A:site-fixtures.A+4] = fixtures.fixtures.fixtures.bl(site, target)
            calls[site] = target
        rows = json.loads(f['mapping'])
        rows[-1].update(rom=f'0x{fast.ADDRESS:08X}', end=f'0x{fast.ADDRESS+4:08X}')
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        start = fixtures.A - fixtures.match.ROM_BASE
        rom[start:start+len(data)] = data
        start = fast.ADDRESS - fixtures.match.ROM_BASE
        rom[start:start+4] = fast.WRAPPER
        return dict(data=bytes(data), address=fixtures.A, rom=bytes(rom),
                    mapping=mapping, index=index,
                    objects=f.get('data_mapping', b'{}'),
                    selector=buffers.MIXED_FAST_FILL_SELECTOR,
                    bindings=dict(calls=[[site-fixtures.A, f'func_{target:08X}']
                        for site, target in sorted(calls.items())],
                        data=f.get('data_bindings', []), functions=[], switches=[]))

    def test_mixed_calls_and_typed_data_replay(self):
        for named in (False, True):
            with self.subTest(named=named):
                f = self.fixture(data=named)
                manifest, reached = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.MIXED_FAST_FILL_SCHEMA)
                proof = manifest['proof']['buffers']['bios_fast_fill']
                self.assertEqual(proof['schema'], fast.MIXED_SCHEMA)
                self.assertIn('ordinary returning ABI', proof['contract'])
                self.assertEqual(proof['sites'][0][2], 4)
                replay, instructions = owner.verify(**f, manifest=manifest)
                self.assertEqual(replay, manifest)
                self.assertEqual([(i.address, bytes(i.bytes)) for i in instructions],
                                 [(i.address, bytes(i.bytes)) for i in reached])
                self.assertEqual(owner.selector_for_report(
                    f'* verification: `{buffers.MIXED_FAST_FILL_SCHEMA}`\n'),
                    buffers.MIXED_FAST_FILL_SELECTOR)

    def test_legacy_selectors_still_refuse_mixed_fill(self):
        f = self.fixture()
        for selector in (buffers.FAST_FILL_SELECTOR, buffers.DATAFREE_SELECTOR,
                         buffers.SELECTOR, buffers.BIOS_FILL_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))

    def test_mode_is_killed_by_ordinary_call_and_unknown_write(self):
        for prefix in ((0x2280, 0x0452, 'ordinary'),
                       ('ordinary', 0x2280, 0x0452, 0x6812),
                       ('ordinary', 0x2B00, 0xD001, 0x2280, 0x0452)):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                owner.verify(**self.fixture(prefix=prefix))

    def test_source_bounds_and_destination_remain_strict(self):
        for change in (dict(source=0xA801), dict(source=0x2000),
                       dict(destination=0x4669)):
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**self.fixture(**change))

    def test_ordinary_pointer_effects_are_checked(self):
        f = self.fixture(prefix=(0x4668, 'ordinary', 0x2280, 0x0452))
        # The exact indexed ordinary leaf may preserve a local pointer.
        owner.verify(**f)
        # Saving it into external memory is still forbidden.
        rom = bytearray(f['rom'])
        start = fixtures.B - fixtures.match.ROM_BASE
        rom[start:start+4] = bytes.fromhex('08607047')
        rows = json.loads(f['mapping'])
        rows[1].update(end=f'0x{fixtures.B+4:08X}', instrs=2)
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        with self.assertRaises(ValueError):
            owner.verify(**dict(f, rom=bytes(rom), mapping=mapping, index=index))

    def test_wrapper_call_bindings_and_stale_proof_are_rejected(self):
        f = self.fixture(data=True)
        manifest, _ = owner.verify(**f)
        changed = copy.deepcopy(manifest)
        changed['proof']['buffers']['bios_fast_fill']['sites'][0][2] = 2
        with self.assertRaises(ValueError):
            owner.verify(**f, manifest=changed)
        for kind in ('wrapper', 'call', 'object', 'index'):
            bad = dict(f)
            if kind == 'wrapper':
                rom = bytearray(f['rom'])
                start = fast.ADDRESS - fixtures.match.ROM_BASE
                rom[start:start+4] = fixtures.bios.WRAPPER
                bad['rom'] = bytes(rom)
            elif kind == 'call':
                bad['bindings'] = copy.deepcopy(f['bindings'])
                bad['bindings']['calls'].pop(0)
            elif kind == 'object':
                bad['objects'] = b'{}'
            else:
                bad['index'] = f['index'].replace(b'0814186C', b'0814186E')
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.verify(**bad, manifest=manifest)

    def test_explicit_cli_and_report_selector(self):
        import argparse
        from unittest.mock import patch
        captured = {}
        def capture(parser, *args, **kwargs):
            captured['choices'] = next(a.choices for a in parser._actions
                                      if a.dest == 'owner_runtime_profile')
            raise RuntimeError('parser captured')
        with patch.object(argparse.ArgumentParser, 'parse_args', capture):
            with self.assertRaisesRegex(RuntimeError, 'parser captured'):
                fixtures.match.main()
        self.assertIn(buffers.MIXED_FAST_FILL_SELECTOR, captured['choices'])
        self.assertTrue(owner.selected(
            f'* verification: `{buffers.MIXED_FAST_FILL_SCHEMA}`\n'))


if __name__ == '__main__':
    unittest.main()
