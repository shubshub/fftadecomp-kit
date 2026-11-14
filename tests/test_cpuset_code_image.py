"""A CpuSet copy source may name an indexed entry start, but only as a proven copy."""
from contextlib import redirect_stdout
import copy
import io
import json
import struct
import sys
import unittest
from unittest.mock import patch

import test_bios_numeric_mmio_literals as numeric
import test_bios_saved_scalar_mmio_literals as saved

profile, match, A = numeric.profile, numeric.match, numeric.A
fill = numeric.fixtures.functions.fill
bios = fill.bios
IMAGE = 0x08020000
DEST = 0x03002B70


def row(rom, end, mode, instrs):
    return dict(rom=f'0x{rom:08X}', end=f'0x{end:08X}', mode=mode, instrs=instrs)


class CpuSetCodeImageTests(unittest.TestCase):
    def setUp(self):
        self.case = saved.BiosSavedScalarMmioLiteralTests('runTest')
        self.case.setUp()
        self.addCleanup(self.case.doCleanups)

    def fixture(self, middle=(), pre=(), post=(), tail=None, control=0x20, destination=DEST, source=IMAGE, image_rows=None,
                selector=profile.BIOS_SCALAR_CODE_IMAGE_SELECTOR):
        tokens = [0xB520, 0xB081, ('load', 3, 'object'), 0x2000, 0x6018,
                  ('load', 0, 'image'), ('load', 1, 'dest'), *pre, ('load', 2, 'copy'), *middle, 'bios', *post,
                  0x4668, 0x2100, ('load', 2, 'direct'), 'bios',
                  0xB001, 0xBC20, 0xBC01, 0x4700]
        if tail is not None:  # the copy is the last call, so r0 is live unless the tail writes it
            tokens = [0xB520, 0xB081, ('load', 3, 'object'), 0x2000, 0x6018,
                      0x4668, 0x2100, ('load', 2, 'direct'), 'bios',
                      ('load', 0, 'image'), ('load', 1, 'dest'), ('load', 2, 'copy'), 'bios', *tail]
        body, calls, bindings, loads = bytearray(), {}, {}, []
        for token in tokens:
            if isinstance(token, int):
                body += struct.pack('<H', token)
            elif token == 'bios':
                site = A + len(body)
                calls[site], bindings[site] = bios.ADDRESS, bios.NAME
                body += fill.fixtures.fixtures.bl(site, bios.ADDRESS)
            else:
                loads.append((len(body), token[1], token[2]))
                body += b'\0\0'
        if len(body) % 4:
            body += b'\0\0'
        pools = {}
        for name, value in [('object', 0x03000020), ('image', source), ('dest', destination),
                            ('copy', control), ('direct', 0x05000056)]:
            pools[name] = len(body)
            body += struct.pack('<I', value)
        for site, register, name in loads:
            struct.pack_into('<H', body, site, 0x4800 | (register << 8) |
                             ((pools[name] - ((site+4)&~3)) // 4))
        if image_rows is None:
            image_rows = [row(IMAGE, IMAGE+0x40, 'arm', 15)]
        rows = [row(A, A+len(body), 'thumb', len(tokens)),
                row(bios.ADDRESS, bios.ADDRESS+4, 'thumb', 2), *image_rows]
        mapping, index = fill.fixtures.fixtures.indexes(rows)
        rom = bytearray(0x143000)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        at = bios.ADDRESS-match.ROM_BASE
        rom[at:at+4] = bios.WRAPPER
        return dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping,
                    index=index, calls=calls, bindings=bindings, selector=selector,
                    data_mapping=json.dumps({"destination": "0x03000020", "image_name": f"0x{source:08X}",
                                             "dest_name": f"0x{destination:08X}"}).encode(),
                    data_bindings=[[pools['object'], 'destination', 0],
                                   [pools['image'], 'image_name', 0],
                                   [pools['dest'], 'dest_name', 0]])

    def test_exact_entry_start_with_proven_copy_is_admitted_and_recorded(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        record = manifest['code_image_sources']
        self.assertEqual(record['schema'], 'rom-cpuset-code-image-source-v1')
        [copy_row] = record['copies']
        self.assertEqual((copy_row['source'], copy_row['destination'], copy_row['bytes'],
                          copy_row['width'], copy_row['units']), (IMAGE, DEST, 0x40, 2, 0x20))
        self.assertEqual(copy_row['rows'], [[IMAGE, IMAGE+0x40, 'arm', 0x40]])
        self.assertEqual((copy_row['overrun'], copy_row['unindexed_gaps']), (None, []))
        self.assertIn('no BIOS effect', record['contract'])
        self.assertFalse(manifest['arithmetic_C_equivalence'])

    def test_overrun_into_a_following_entry_is_recorded_not_hidden(self):
        rows = [row(IMAGE, IMAGE+0x40, 'arm', 15), row(IMAGE+0x40, IMAGE+0x100, 'thumb', 90)]
        manifest, _ = profile.verify(**self.fixture(control=0x30, image_rows=rows))
        [copy_row] = manifest['code_image_sources']['copies']
        self.assertEqual(copy_row['overrun'], [IMAGE+0x40, IMAGE+0x100, 'thumb', 0x20])
        self.assertEqual([r[0] for r in copy_row['rows']], [IMAGE, IMAGE+0x40])

    def test_alignment_gaps_between_rows_are_recorded(self):
        rows = [row(IMAGE, IMAGE+0x3E, 'thumb', 30), row(IMAGE+0x40, IMAGE+0x60, 'thumb', 15)]
        manifest, _ = profile.verify(**self.fixture(control=0x30, image_rows=rows))
        [copy_row] = manifest['code_image_sources']['copies']
        self.assertEqual(copy_row['unindexed_gaps'], [[IMAGE+0x3E, IMAGE+0x40]])
        self.assertIsNone(copy_row['overrun'])

    def test_subs_exemption_is_only_the_length_shape(self):
        # subs r2, r3, r0 whose result is overwritten by the control load: admitted
        profile.verify(**self.fixture(pre=(0x1A00 | (0 << 6) | (3 << 3) | 2,), post=(0x2900,)))
        cases = {
            'derived to r5 then stored': (0x2500, 0x1B45, 0x601D),
            'derived to r5 then stored on stack': (0x2500, 0x1B45, 0x9500),
            'subs with r0 as minuend': (0x1A00 | (3 << 6) | (0 << 3) | 2,),
            'subs destination not r2': (0x1A00 | (3 << 3) | 5,),
            'negs': (0x4240 | 5,),
            'adds copy': (0x1C05,),
        }
        for name, middle in cases.items():
            with self.subTest(name), self.assertRaisesRegex(ValueError, 'code-image'):
                profile.verify(**self.fixture(middle=middle))
        with self.assertRaisesRegex(ValueError, 'code-image'):
            profile.verify(**self.fixture(middle=(0x2500, 0x1B45), post=(0x2D00,)))
        # a derived r2 may only be read by r2 -> r2 steps
        for name, pre in {'copied': (0x1A00 | (3 << 3) | 2, 0x1C15),
                          'stored': (0x1A00 | (3 << 3) | 2, 0x6032)}.items():
            with self.subTest(name), self.assertRaisesRegex(ValueError, 'r2 step'):
                profile.verify(**self.fixture(pre=pre))

    def test_flags_and_r0_after_the_subtraction_do_not_leak_the_alias(self):
        subs = 0x1A1A  # subs r2, r3, r0
        cases = {
            'carry shifted out then captured': dict(pre=(0x2300, 0x2500, subs, 0x0852, 0x416D)),
            'compare capture adcs': dict(pre=(0x2310, subs, 0x416D, 0x2220)),
            'compare capture sbcs': dict(pre=(0x2310, subs, 0x41AD, 0x2220)),
            'ror': dict(pre=(0x2310, subs, 0x41C5)),
            'flags read after the call': dict(pre=(0x2310, subs), post=(0x416D,)),
            'later call with tainted flags': dict(pre=(0x2310, subs)),
            'r0 read after the call': dict(post=(0x1C05,)),
        }
        for name, options in cases.items():
            with self.subTest(name), self.assertRaisesRegex(ValueError, 'code-image'):
                profile.verify(**self.fixture(**options))
        # flags recomputed by CMP before the call's successors read them: admitted
        profile.verify(**self.fixture(pre=(0x2310, subs), post=(0x2900, 0x416D)))

    def test_exit_with_r0_live_refuses_and_pop_r0_exit_is_admitted(self):
        profile.verify(**self.fixture(tail=(0xB001, 0xBC20, 0xBC01, 0x4700)))
        with self.assertRaisesRegex(ValueError, 'live at a function exit'):
            profile.verify(**self.fixture(tail=(0xB001, 0xBC20, 0xBC02, 0x4708)))

    def test_join_into_the_load_to_call_chain_refuses(self):
        # cmp r1,#0 ; beq over one instruction: the control load then has two predecessors
        with self.assertRaisesRegex(ValueError, 'without joins|linear'):
            profile.verify(**self.fixture(pre=(0x2900, 0xD000, 0x1C09)))

    def test_span_must_stay_within_the_evidenced_image(self):
        def rows(n, size=0x10):
            return [row(IMAGE+size*i, IMAGE+size*(i+1), 'thumb', 7) for i in range(n)]
        cases = {
            'owner covered': dict(source=A-0x20, control=0x30,
                                  image_rows=[row(A-0x20, A, 'thumb', 15)]),
            'large interior gap': dict(control=0x30, image_rows=[
                row(IMAGE, IMAGE+0x20, 'arm', 7), row(IMAGE+0x40, IMAGE+0x60, 'arm', 7)]),
            'many unrelated rows': dict(control=0x48, image_rows=rows(9)),
            'oversized span': dict(control=0x101, image_rows=rows(4)),
            'overrun too large': dict(control=0x70, image_rows=[
                row(IMAGE, IMAGE+0x40, 'arm', 15), row(IMAGE+0x40, IMAGE+0x400, 'thumb', 400)]),
            'ends in reserved iwram': dict(destination=0x03007E00-0x20, control=0x30,
                                           image_rows=[row(IMAGE, IMAGE+0x60, 'arm', 20)]),
        }
        for name, options in cases.items():
            with self.subTest(name), self.assertRaises(ValueError):
                profile.verify(**self.fixture(**options))
        # the real 08004AC0 shape stays admissible: 0x140 bytes with a 68-byte overrun
        manifest, _ = profile.verify(**self.fixture(control=0xA0, image_rows=[
            row(IMAGE, IMAGE+0xFC, 'arm', 62), row(IMAGE+0xFC, IMAGE+0x250, 'thumb', 150)]))
        self.assertEqual(manifest['code_image_sources']['copies'][0]['overrun'][3], 0x44)

    def test_every_other_selector_still_refuses_the_alias(self):
        f = self.fixture()
        for selector in (profile.BIOS_SCALAR_DATA_SELECTOR, profile.BIOS_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'aliases indexed code'):
                profile.verify(**dict(f, selector=selector))

    def test_value_must_be_exactly_one_entry_start(self):
        for source in (IMAGE+2, IMAGE+4, IMAGE+0x3C):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'aliases indexed code'):
                profile.verify(**self.fixture(source=source))
        f = self.fixture()
        bound = [list(item) for item in f['data_bindings']]
        bound[1][2] = 4  # a nonzero addend cannot name an entry
        with self.assertRaisesRegex(ValueError, 'aliases indexed code'):
            profile.verify(**dict(f, data_mapping=json.dumps({
                "destination": "0x03000020", "image_name": f"0x{IMAGE-4:08X}",
                "dest_name": f"0x{DEST:08X}"}).encode(), data_bindings=bound))

    def test_unproven_or_unsafe_copy_refuses(self):
        cases = {'fill control': dict(control=0x01000020), 'zero count': dict(control=0),
                 'reserved bit': dict(control=0x08000020), 'oversize': dict(control=0x04008001),
                 'rom destination': dict(destination=0x08030000),
                 'span leaves iwram': dict(destination=0x03007FF0),
                 'unaligned width': dict(control=0x04000010, destination=DEST+2)}
        for name, options in cases.items():
            with self.subTest(name), self.assertRaises(ValueError):
                profile.verify(**self.fixture(**options))
        with self.assertRaisesRegex(ValueError, 'beyond ROM|outside ROM'):
            profile.verify(**self.fixture(source=IMAGE, control=0x1FFFFF,
                                          destination=DEST))

    def test_any_use_of_the_literal_other_than_the_copy_source_refuses(self):
        for name, middle in {'copied to r3': (0x1C03,), 'overwritten': (0x2000,),
                             'stored': (0x6008,), 'compared': (0x2800,),
                             'loaded twice': (('load', 3, 'image'),)}.items():
            with self.subTest(name), self.assertRaises(ValueError):
                profile.verify(**self.fixture(middle=middle))
        # The literal word loaded into a register that is not r0 is not a copy source.
        f = self.fixture()
        body = bytearray(f['data'])
        site = 10
        self.assertEqual(struct.unpack_from('<H', body, site)[0] & 0xFF00, 0x4800)
        struct.pack_into('<H', body, site, struct.unpack_from('<H', body, site)[0] | 0x0300)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        with self.assertRaises(ValueError):
            profile.verify(**dict(f, data=bytes(body), rom=bytes(rom)))

    def test_literal_without_a_copy_call_or_without_alias_refuses(self):
        # The selector demands an actual indexed entry literal.
        f = self.fixture(image_rows=[row(IMAGE+0x1000, IMAGE+0x1040, 'arm', 15)])
        with self.assertRaises(ValueError):
            profile.verify(**f)

    def test_manifest_is_bound_and_forgeries_refuse(self):
        f = self.fixture()
        manifest, _ = profile.verify(**f)
        for edit in (lambda m: m['code_image_sources']['copies'][0].update(bytes=0x20),
                     lambda m: m['code_image_sources']['copies'][0]['rows'][0].__setitem__(1, IMAGE+0x20),
                     lambda m: m['code_image_sources']['copies'][0].update(overrun=[1, 2, 'arm', 1]),
                     lambda m: m['code_image_sources']['copies'][0].update(source_sha256='0'*64),
                     lambda m: m.pop('code_image_sources')):
            forged = copy.deepcopy(manifest)
            edit(forged)
            with self.subTest(), self.assertRaisesRegex(ValueError, 'manifest differs'):
                profile.verify(**f, manifest=forged)

    def test_original_elf_binding_and_link_keep_entry_start_without_thumb_bit(self):
        f = self.fixture()
        helper = self.case.base.base
        original = self.case.data_image(f)
        linked = helper.linked_data_image(f, original)
        records = {}
        calls, _, targets = profile.original_bindings(original, A, f['rom'], f['mapping'],
            selector=f['selector'], data_mapping=f['data_mapping'], data_relocations=records)
        self.assertEqual(targets['image_name'], IMAGE)
        self.assertEqual(profile.linked_bytes(original, linked, A, calls, targets,
            data_relocations=records), f['data'])
        with self.assertRaisesRegex(ValueError, 'aliases indexed code'):
            profile.original_bindings(original, A, f['rom'], f['mapping'],
                selector=profile.BIOS_SCALAR_DATA_SELECTOR, data_mapping=f['data_mapping'],
                data_relocations={})

    def test_selector_cannot_be_relabelled_and_report_replays(self):
        f = self.fixture()
        with patch.object(self.case.base.base, "data_image", side_effect=self.case.data_image), \
                self.case.base.base.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1'*64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-runtime-profile', f['selector'], f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            evidence = fill.fixtures.fixtures.evidence
            self.assertTrue(evidence.report_matches(report, root, A))
            self.assertIn('code image source', report)
            for other in (profile.BIOS_SCALAR_DATA_SELECTOR, profile.BIOS_SCALAR_MMIO_CODE_IMAGE_SELECTOR):
                relabelled = report.replace(f['selector'], other).replace(
                    profile.SCHEMAS[f['selector']], profile.SCHEMAS[other])
                self.assertFalse(evidence.report_matches(relabelled, root, A))
            self.assertFalse(evidence.report_matches(report.replace(
                'Static source-span identity only', 'forged'), root, A))
            pins = profile.data_producer_fingerprint(f['selector'])
            self.assertIn('cpuset_code_image_profile.py', pins)
            self.assertNotIn('cpuset_code_image_profile.py',
                             profile.data_producer_fingerprint(profile.BIOS_SCALAR_DATA_SELECTOR))
            with patch.object(profile, 'data_producer_fingerprint', return_value=dict(
                    pins, **{'cpuset_code_image_profile.py': '0'*64})):
                self.assertFalse(evidence.report_matches(report, root, A))
            source = root/'src/08010000.c'
            source.write_bytes(source.read_bytes()+b' ')
            self.assertFalse(evidence.report_matches(report, root, A))


if __name__ == '__main__':
    unittest.main()
