"""CpuSet and CpuFastSet sites in one owner keep their own fill proofs."""
import copy
import json
import unittest

import bios_fast_fill_source_profile as fast
import bios_mixed_cpuset_fast_fill_profile as mixed
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_cpuset_fill_profile as fixtures

# movs r2,#0x80; lsls r2,r2,#17 -> 0x01000000 (bit24 set, bit26 clear)
CONTROL = (0x2280, 0x0452)
# mov r0,sp; movs r1,#0; bl CpuSet
CPUSET = (0x4668, 0x2100, 'bios')


class MixedCpuSetFastFillTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, first=('ordinary', *CONTROL, *CPUSET), second=CONTROL,
                fast_tail=True, **changes):
        """`first` ends in a CpuSet call; the final call becomes CpuFastSet."""
        f = self.base.fixture(prefix=(*first, *second), **changes)
        data, rom = bytearray(f['data']), bytearray(f['rom'])
        calls = dict(f['calls'])
        if fast_tail:
            last = max(site for site, target in calls.items()
                       if target == fixtures.bios.ADDRESS)
            data[last-fixtures.A:last-fixtures.A+4] = \
                fixtures.fixtures.fixtures.bl(last, fast.ADDRESS)
            calls[last] = fast.ADDRESS
        rows = json.loads(f['mapping'])
        rows.insert(-1, dict(rom=f'0x{fast.ADDRESS:08X}',
                             end=f'0x{fast.ADDRESS+4:08X}', mode='thumb', instrs=2))
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        start = fixtures.A - fixtures.match.ROM_BASE
        rom[start:start+len(data)] = data
        start = fast.ADDRESS - fixtures.match.ROM_BASE
        rom[start:start+4] = fast.WRAPPER
        return dict(data=bytes(data), address=fixtures.A, rom=bytes(rom),
                    mapping=mapping, index=index,
                    objects=f.get('data_mapping', b'{}'),
                    selector=buffers.MIXED_CPUSET_FAST_FILL_SELECTOR,
                    bindings=dict(calls=[[site-fixtures.A, f'func_{target:08X}']
                        for site, target in sorted(calls.items())],
                        data=f.get('data_bindings', []), functions=[], switches=[]))

    def test_both_wrappers_ordinary_calls_and_typed_data_replay(self):
        for named in (False, True):
            with self.subTest(named=named):
                f = self.fixture(data=named)
                manifest, reached = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.MIXED_CPUSET_FAST_FILL_SCHEMA)
                proofs = manifest['proof']['buffers']
                self.assertEqual(proofs['bios_fast_fill']['schema'], mixed.SCHEMA)
                self.assertEqual(proofs['bios_fill']['schema'], fixtures.bios.SCHEMA)
                # Known clear bit26 proves a halfword CpuSet unit; CpuFastSet
                # always reads one aligned word.
                self.assertEqual([row[2] for row in proofs['bios_fill']['sites']], [2])
                self.assertEqual([row[2] for row in proofs['bios_fast_fill']['sites']], [4])
                for proof in (proofs['bios_fill'], proofs['bios_fast_fill']):
                    self.assertIn('bios_mixed_cpuset_fast_fill_profile.py',
                                  proof['producer_sha256'])
                replay, instructions = owner.verify(**f, manifest=manifest)
                self.assertEqual(replay, manifest)
                self.assertEqual([(i.address, bytes(i.bytes)) for i in instructions],
                                 [(i.address, bytes(i.bytes)) for i in reached])

    def test_legacy_fill_selectors_still_refuse_the_mixture(self):
        f = self.fixture()
        for selector in (buffers.MIXED_FAST_FILL_SELECTOR, buffers.FAST_FILL_SELECTOR,
                         buffers.BIOS_FILL_SELECTOR, buffers.BIOS_LOCAL_FILL_SELECTOR,
                         buffers.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))

    def test_both_wrappers_are_required(self):
        # CpuSet only (no CpuFastSet), and CpuFastSet only (no CpuSet).
        for f in (self.fixture(fast_tail=False),
                  self.fixture(first=('ordinary',))):
            with self.assertRaisesRegex(ValueError, 'both wrappers'):
                owner.verify(**f)

    def test_each_site_keeps_its_own_control_and_source_proof(self):
        for first, second, changes in (
                # CpuSet bit24 is killed by the following ordinary call.
                ((*CONTROL, 'ordinary', *CPUSET), CONTROL, {}),
                # CpuFastSet control is not reloaded after the CpuSet call.
                (('ordinary', *CONTROL, *CPUSET), (), {}),
                # CpuSet source escapes the one-word frame.
                (('ordinary', *CONTROL, 0xA801, 0x2100, 'bios'), CONTROL, {}),
                # CpuSet destination is a local pointer.
                (('ordinary', *CONTROL, 0x4668, 0x4669, 'bios'), CONTROL, {}),
                # CpuFastSet source is not a local and its destination is.
                (('ordinary', *CONTROL, *CPUSET), CONTROL, dict(source=0x2000)),
                (('ordinary', *CONTROL, *CPUSET), CONTROL, dict(destination=0x4669))):
            with self.subTest(first=first, second=second, changes=changes), \
                    self.assertRaises(ValueError):
                owner.verify(**self.fixture(first=first, second=second, **changes))

    def test_stale_manifests_and_changed_wrappers_are_rejected(self):
        f = self.fixture(data=True)
        manifest, _ = owner.verify(**f)
        for key in ('bios_fill', 'bios_fast_fill'):
            changed = copy.deepcopy(manifest)
            changed['proof']['buffers'][key]['sites'][0][2] ^= 6
            with self.subTest(key=key), self.assertRaises(ValueError):
                owner.verify(**f, manifest=changed)
        for address, wrapper in ((fixtures.bios.ADDRESS, fast.WRAPPER),
                                 (fast.ADDRESS, fixtures.bios.WRAPPER)):
            rom = bytearray(f['rom'])
            start = address - fixtures.match.ROM_BASE
            rom[start:start+4] = wrapper
            with self.subTest(address=address), self.assertRaises(ValueError):
                owner.verify(**dict(f, rom=bytes(rom)), manifest=manifest)

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
        self.assertIn(buffers.MIXED_CPUSET_FAST_FILL_SELECTOR, captured['choices'])
        line = f'* verification: `{buffers.MIXED_CPUSET_FAST_FILL_SCHEMA}`\n'
        self.assertTrue(owner.selected(line))
        self.assertEqual(owner.selector_for_report(line),
                         buffers.MIXED_CPUSET_FAST_FILL_SELECTOR)
        self.assertEqual(owner.selector_for_report(
            f'* verification: `{buffers.MIXED_FAST_FILL_SCHEMA}`\n'),
            buffers.MIXED_FAST_FILL_SELECTOR)


if __name__ == '__main__':
    unittest.main()
