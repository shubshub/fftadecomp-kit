"""BgAffineSet local-buffer profile: exact wrapper, constant count, bounded disjoint frames."""
import copy
import json
import struct
import unittest

import bios_bg_affine_set_profile as affine
import named_data_buffer_profile as buffers
import owner_admission_profile as owner
import test_bios_cpuset_fill_profile as fixtures

A, B = fixtures.A, fixtures.B
match = fixtures.match


class BgAffineSetTests(unittest.TestCase):
    def setUp(self):
        self.base = fixtures.BiosCpuSetFillTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)

    def fixture(self, words=9, source=0, destination=5, count=1, middle=None,
                ordinary=False, wrapper=affine.WRAPPER):
        """push {lr}; sub sp; [ordinary call]; r2=count; r0=&sp[source]; r1=&sp[destination]."""
        tokens = [0xB500, 0xB080 | words]
        if ordinary:
            tokens.append('ordinary')
        tokens += [0x2200 | count] if middle is None else list(middle)
        tokens += [0xA800 | source, 0xA900 | destination]
        tokens += ['affine', 0xB000 | words, 0xBC01, 0x4700]
        body, calls = bytearray(), {}
        for token in tokens:
            if isinstance(token, int):
                body += struct.pack('<H', token)
            else:
                target = affine.ADDRESS if token == 'affine' else B
                site = A + len(body)
                calls[site] = target
                body += fixtures.fixtures.fixtures.bl(site, target)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb',
                     instrs=len(tokens)),
                dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1),
                dict(rom=f'0x{affine.ADDRESS:08X}', end=f'0x{affine.ADDRESS+4:08X}',
                     mode='thumb', instrs=2)]
        mapping, index = fixtures.fixtures.fixtures.indexes(rows)
        rom = bytearray(self.base.fixture()['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = b'\x70\x47'
        start = affine.ADDRESS - match.ROM_BASE
        rom[start:start+4] = wrapper
        return dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, objects=b'{}', selector=buffers.BG_AFFINE_SELECTOR,
                    bindings=dict(calls=[[site-A, f'func_{target:08X}']
                                         for site, target in sorted(calls.items())],
                                  data=[], functions=[], switches=[]))

    def test_positive_replay_and_report_selector(self):
        for kwargs in (dict(), dict(words=18, destination=10, count=2),
                       dict(ordinary=True)):
            with self.subTest(kwargs=kwargs):
                f = self.fixture(**kwargs)
                manifest, reached = owner.verify(**f)
                self.assertEqual(manifest['profile'], buffers.BG_AFFINE_SCHEMA)
                proof = manifest['proof']['buffers']['bios_bg_affine_set']
                self.assertEqual(proof['schema'], affine.SCHEMA)
                self.assertEqual(proof['dependency'][:2], [affine.ADDRESS, 4])
                self.assertEqual(len(proof['sites']), 1)
                self.assertEqual(proof['sites'][0][3], kwargs.get('count', 1))
                self.assertIn('no other memory', proof['contract'])
                replay, instructions = owner.verify(**f, manifest=manifest)
                self.assertEqual(replay, manifest)
                self.assertEqual([(i.address, bytes(i.bytes)) for i in instructions],
                                 [(i.address, bytes(i.bytes)) for i in reached])
        self.assertEqual(owner.selector_for_report(
            f'* verification: `{buffers.BG_AFFINE_SCHEMA}`\n'), buffers.BG_AFFINE_SELECTOR)
        self.assertTrue(owner.selected(f'* verification: `{buffers.BG_AFFINE_SCHEMA}`\n'))

    def test_other_selectors_still_refuse_the_wrapper(self):
        f = self.fixture()
        for selector in (buffers.SELECTOR, buffers.DATAFREE_SELECTOR,
                         buffers.MIXED_FAST_FILL_SELECTOR, buffers.BIOS_FILL_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.verify(**dict(f, selector=selector))

    def test_count_must_match_the_frame(self):
        # A count larger than the frame supports reads or writes past it.
        for kwargs in (dict(count=2), dict(words=18, destination=10, count=3),
                       dict(count=0), dict(count=255)):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                owner.verify(**self.fixture(**kwargs))

    def test_destination_must_stay_in_the_frame(self):
        for kwargs in (dict(destination=6), dict(destination=9), dict(words=8)):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                owner.verify(**self.fixture(**kwargs))
        # The source span is bounded too: 20 bytes starting at the last word.
        with self.assertRaises(ValueError):
            owner.verify(**self.fixture(source=5, destination=0))

    def test_source_and_destination_must_be_disjoint(self):
        for kwargs in (dict(destination=4), dict(destination=0), dict(source=2, destination=0),
                       dict(words=18, destination=8, count=2)):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                owner.verify(**self.fixture(**kwargs))
        # Destination-first layout is the same disjoint pair, reversed.
        owner.verify(**self.fixture(source=4, destination=0))

    def test_count_must_be_a_proven_constant(self):
        for middle in ((0x9A00,),                         # ldr r2,[sp]: unknown
                       (0x2201, 0x2B00, 0xD000, 0x2202),  # one path counts 2
                       (0x1C02,),                         # adds r2,r2,#0: unknown input
                       ()):                               # r2 never set
            with self.subTest(middle=middle), self.assertRaises(ValueError):
                owner.verify(**self.fixture(middle=middle))
        # Disagreeing paths drop the constant even when every candidate fits.
        with self.assertRaises(ValueError):
            owner.verify(**self.fixture(words=18, destination=10,
                middle=(0x2201, 0x2B00, 0xD000, 0x2202)))

    def test_wrapper_and_indexes_are_authenticated(self):
        for wrapper in (bytes.fromhex('0bdf7047'), bytes.fromhex('0edf0047'),
                        bytes.fromhex('0fdf7047'), bytes.fromhex('0e df 70 46'.replace(' ', ''))):
            with self.subTest(wrapper=wrapper.hex()), self.assertRaises(ValueError):
                owner.verify(**self.fixture(wrapper=wrapper))
        f = self.fixture()
        rows = json.loads(f['mapping'])
        for change in ('missing', 'end'):
            bad = [dict(r) for r in rows]
            if change == 'missing':
                bad = bad[:-1]
            else:
                bad[-1]['end'] = f'0x{affine.ADDRESS+2:08X}'
            mapping, index = fixtures.fixtures.fixtures.indexes(bad)
            with self.subTest(change=change), self.assertRaises(ValueError):
                owner.verify(**dict(f, mapping=mapping, index=index))

    def test_requires_actual_call_and_exact_bindings(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        bad = dict(f, bindings=dict(f['bindings'], calls=[]))
        with self.assertRaises(ValueError):
            owner.verify(**bad, manifest=manifest)
        bad = dict(f, bindings=dict(f['bindings'], functions=[[0, 'func_08010000']]))
        with self.assertRaises(ValueError):
            owner.verify(**bad)
        # An owner with no BgAffineSet call has nothing for this selector to prove.
        plain = self.base.fixture()
        plain = dict(data=plain['data'], address=A, rom=plain['rom'], mapping=plain['mapping'],
                     index=plain['index'], objects=b'{}', selector=buffers.BG_AFFINE_SELECTOR,
                     bindings=dict(calls=[], data=[], functions=[], switches=[]))
        with self.assertRaises(ValueError):
            owner.verify(**plain)

    def test_report_manifest_tampering_is_rejected(self):
        f = self.fixture()
        manifest, _ = owner.verify(**f)
        for path, value in ((('sites', 0, 3), 2), (('sites', 0, 2), 1),
                            (('sites', 0, 1), 4), (('schema',), 'x'),
                            (('dependency', 2), '00' * 32)):
            changed = copy.deepcopy(manifest)
            node = changed['proof']['buffers']['bios_bg_affine_set']
            for key in path[:-1]:
                node = node[key]
            node[path[-1]] = value
            with self.subTest(path=path), self.assertRaises(ValueError):
                owner.verify(**f, manifest=changed)
        for key in ('profile',):
            changed = copy.deepcopy(manifest)
            changed[key] = buffers.MIXED_FAST_FILL_SCHEMA
            with self.assertRaises(ValueError):
                owner.verify(**f, manifest=changed)
        for kind in ('wrapper', 'object', 'index'):
            bad = dict(f)
            if kind == 'wrapper':
                rom = bytearray(f['rom'])
                start = affine.ADDRESS - match.ROM_BASE
                rom[start:start+4] = bytes.fromhex('0cdf7047')
                bad['rom'] = bytes(rom)
            elif kind == 'object':
                bad['objects'] = b'{"x":"0x02000000"}'
            else:
                bad['index'] = f['index'].replace(b'08141868', b'0814186A')
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.verify(**bad, manifest=manifest)

    def test_explicit_cli_choice(self):
        import argparse
        from unittest.mock import patch
        captured = {}

        def capture(parser, *args, **kwargs):
            captured['choices'] = next(a.choices for a in parser._actions
                                      if a.dest == 'owner_runtime_profile')
            raise RuntimeError('parser captured')
        with patch.object(argparse.ArgumentParser, 'parse_args', capture):
            with self.assertRaisesRegex(RuntimeError, 'parser captured'):
                match.main()
        self.assertIn(buffers.BG_AFFINE_SELECTOR, captured['choices'])


if __name__ == '__main__':
    unittest.main()
