"""Versioned r3-thunk switch with one numeric switch literal and external alignment."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import framed_switch_inventory as scalar
from test_switch_constants import assemble, fixed_args

A = 0x08010000
SELECTOR = owner.THUNK_SWITCH_ALIGNED_SELECTOR


class NumericThunkSwitchAlignedTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH',
            Path(__file__).resolve().parents[1] / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='numeric_r3_aligned_', dir=scratch)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, *, numeric='0x68C', tail='', case0_exit='b .Ldone', successor=2,
                selector=SELECTOR, gap=b'\0\0'):
        assembly = f'''.syntax unified
.arch armv4t
.thumb
.text
.global func_08010000
.type func_08010000,%function
.thumb_func
func_08010000:
push {{lr}}
sub sp,#4
ldr r1,.Lnumeric
adds r0,r0,r1
ldrh r0,[r0]
cmp r0,#1
bls .Lin
b .Ldefault
.Lin:
lsls r0,r0,#2
ldr r1,.Lpointer
adds r0,r0,r1
ldr r0,[r0]
mov pc,r0
.balign 4,0
.Lnumeric:
.word {numeric}
.Lpointer:
.word .Ltable
.Ltable:
.word .Lcase0
.word .Lcase1
.Lcase0:
ldr r3,.Lobject
ldr r3,[r3]
bl _call_via_r3
{case0_exit}
.Ldefault:
movs r0,#0
b .Ldone
.balign 4,0
.Lobject:
.word g_dispatch
.Lcase1:
bl func_08001000
.Ldone:
{tail}
add sp,#4
pop {{r1}}
bx r1
.size func_08010000,.-func_08010000
.Lpad:
.balign 4
'''
        original = assemble(self.root, assembly)
        known = self.root / 'known.s'
        known.write_text('''.syntax unified
.thumb
.global _call_via_r3
.type _call_via_r3,%function
.thumb_set _call_via_r3,0x08142251
.global func_08001000
.type func_08001000,%function
.thumb_set func_08001000,0x08001001
.global g_dispatch
.type g_dispatch,%object
.set g_dispatch,0x02000000
''')
        subprocess.run(['arm-none-eabi-as', str(known), '-o', str(self.root / 'known.o')],
                       check=True, capture_output=True)
        subprocess.run(['arm-none-eabi-ld', '--no-undefined', '--no-relax',
            f'-Ttext=0x{A:08X}', '-e', 'func_08010000', str(self.root / 'f.o'),
            str(self.root / 'known.o'), '-o', str(self.root / 'f.elf')],
            check=True, capture_output=True)
        linked = (self.root / 'f.elf').read_bytes()
        image = match.elf_image(linked)
        symbol, offset = match.function_record(image, 'func_08010000', A, True)
        data = image['text'][offset:offset + symbol['size']]
        follow = A + len(data) + successor
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(data):08X}', mode='thumb', instrs=0),
                dict(rom='0x08001000', end='0x08001002', mode='thumb', instrs=1),
                dict(rom=f'0x{follow:08X}', end=f'0x{follow+2:08X}', mode='thumb', instrs=1),
                dict(rom='0x08142250', end='0x08142252', mode='thumb', instrs=1)]
        rows[0]['instrs'] = owner.refine(data, A, json.dumps(rows).encode(),
            one_numeric_word_switch=True)['instrs']
        mapping = json.dumps(rows).encode()
        index = ''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
            f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode()
        rom = bytearray(0x142254)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
        rom[follow-match.ROM_BASE:follow-match.ROM_BASE+2] = b'\x70\x47'
        if successor == 2:
            rom[A+len(data)-match.ROM_BASE:follow-match.ROM_BASE] = gap
        rom[0x1000:0x1002] = b'\x70\x47'
        rom[0x142250:0x142254] = b'\x18\x47\xc0\x46'
        values = dict(data=data, address=A, rom=bytes(rom), mapping=mapping, index=index,
            objects=b'{"g_dispatch":"0x02000000"}', selector=selector)
        return original, linked, values

    def bindings(self, original, values):
        return owner.original_bindings(match.elf_image(original), A, values['rom'],
            values['mapping'], values['objects'], selector=values['selector'],
            index=values['index'])[0]

    def test_numeric_r3_switch_alignment_link_and_report(self):
        original, linked, values = self.fixture()
        image = match.elf_image(original)
        symbol, _ = match.function_record(image, 'func_08010000', A, True)
        self.assertEqual(symbol['size'] % 4, 2)
        self.assertEqual(image['text'][symbol['size']:], b'\xc0\x46')
        bindings = self.bindings(original, values)
        manifest, ins = owner.verify(**values, bindings=bindings)
        self.assertEqual(manifest['profile'], owner.THUNK_SWITCH_ALIGNED_SCHEMA)
        inventory = manifest['proof']['ordinary_switch_inventory']
        self.assertEqual(inventory['schema'], scalar.NUMERIC_THUNK_SCHEMA)
        self.assertEqual(inventory['interposed_constant_words'], 1)
        self.assertEqual(inventory['numeric_word']['value'], 0x68C)
        self.assertEqual([name for _, name in inventory['runtime_calls']], ['_call_via_r3'])
        end = A + len(values['data'])
        self.assertEqual(manifest['proof']['terminal_alignment_policy']['gap'],
                         [f'0x{end:08X}', f'0x{end+2:08X}'])
        report = owner.render(A, (values['data'], manifest, 'synthetic-source', values['mapping'],
            values['index'], values['objects'], values['rom'], len(ins), original))
        self.assertEqual(owner.selector_for_report(report), SELECTOR)
        self.assertIn(owner.THUNK_SWITCH_ALIGNED_CONTROL_FLOW, report)
        self.assertIn('original_elf_sha256', report)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            runner.write_text(workspace + '/f.i', '')
            Path(workspace + '/f.o').write_bytes(original)
            data, actual = owner.object_bytes(runner, workspace, fixed_args(), image, A,
                values['rom'], values['mapping'], values['objects'],
                selector=SELECTOR, index=values['index'])
            self.assertEqual(data, values['data'])
            self.assertEqual(actual, bindings)
            self.assertEqual(match.elf_image(runner.read_binary(workspace + '/f.elf'))['text'],
                             match.elf_image(linked)['text'])

    def test_existing_selectors_keep_refusing_this_shape(self):
        original, _, values = self.fixture()
        for selector in (owner.THUNK_SWITCH_SELECTOR, owner.DIRECT_SWITCH_SELECTOR, owner.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                owner.original_bindings(match.elf_image(original), A, values['rom'],
                    values['mapping'], values['objects'], selector=selector, index=values['index'])
        bindings = self.bindings(original, values)
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, selector=owner.THUNK_SWITCH_SELECTOR), bindings=bindings)

    def test_missing_pad_is_refused(self):
        original, _, values = self.fixture(tail='movs r2,#0')
        image = match.elf_image(original)
        symbol, _ = match.function_record(image, 'func_08010000', A, True)
        self.assertEqual(len(image['text']), symbol['size'])
        with self.assertRaisesRegex(ValueError, 'actual external two-byte'):
            self.bindings(original, values)

    def test_pad_that_is_not_a_canonical_nop_or_alignment_is_refused(self):
        original, _, values = self.fixture()
        image = match.elf_image(original)
        for kind in ('zero-pad', 'alignment', 'owned-pad'):
            altered = copy.deepcopy(image)
            if kind == 'zero-pad':
                altered['text'] = altered['text'][:-2] + b'\0\0'
            elif kind == 'alignment':
                section = list(altered['sections'][altered['text_index']]); section[8] = 2
                altered['sections'][altered['text_index']] = section
            else:
                altered['symbols'].append(dict(name='owned_tail', value=len(image['text'])-2,
                    size=2, type=0, bind=1, section=altered['text_index']))
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                owner.original_bindings(altered, A, values['rom'], values['mapping'],
                    values['objects'], selector=SELECTOR, index=values['index'])

    def test_reached_pad_is_refused(self):
        original, _, values = self.fixture(case0_exit='b .Lpad')
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=self.bindings(original, values))

    def test_successor_must_start_on_the_aligned_boundary(self):
        original, _, values = self.fixture()
        bindings = self.bindings(original, values)
        for successor in (0, 6):
            _, _, moved = self.fixture(successor=successor)
            with self.subTest(successor=successor), self.assertRaisesRegex(
                    ValueError, 'aligned next function'):
                owner.verify(**moved, bindings=bindings)
        rows = json.loads(values['mapping'])
        rows = [row for row in rows if int(row['rom'], 16) != A + len(values['data']) + 2]
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, mapping=json.dumps(rows).encode()), bindings=bindings)
        rows = json.loads(values['mapping'])
        rows.append(dict(rom=f'0x{A+len(values["data"]):08X}',
            end=f'0x{A+len(values["data"])+2:08X}', mode='thumb', instrs=1))
        with self.assertRaises(ValueError):
            owner.verify(**dict(values, mapping=json.dumps(rows).encode()), bindings=bindings)

    def test_rom_gap_must_be_zero_or_nop_and_is_bound(self):
        original, _, values = self.fixture()
        bindings = self.bindings(original, values)
        for gap in (b'\0\0', b'\xc0\x46'):
            _, _, allowed = self.fixture(gap=gap)
            manifest, _ = owner.verify(**allowed, bindings=bindings)
            self.assertEqual(manifest['proof']['terminal_alignment_policy']['rom_gap_bytes'], gap.hex())
        for gap in (b'\xff\xff', b'\xfe\xe7', b'\x70\x47', b'\x00\x46'):
            _, _, mutated = self.fixture(gap=gap)
            with self.subTest(gap=gap.hex()), self.assertRaisesRegex(ValueError, 'zero or NOP two-byte gap'):
                owner.verify(**mutated, bindings=bindings)
        manifest, _ = owner.verify(**values, bindings=bindings)
        altered = copy.deepcopy(manifest)
        altered['proof']['terminal_alignment_policy']['rom_gap_bytes'] = 'c046'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**values, bindings=bindings, manifest=altered)
        _, _, nop = self.fixture(gap=b'\xc0\x46')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            owner.verify(**nop, bindings=bindings, manifest=manifest)

    def test_numeric_word_must_be_a_reached_u16(self):
        original, _, values = self.fixture(numeric='0x12345')
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=self.bindings(original, values))

    def test_inventory_selectors_do_not_cross(self):
        original, _, values = self.fixture()
        graph = __import__('owner_graph_profile')
        refinement = owner.refine(values['data'], A, values['mapping'], one_numeric_word_switch=True)
        calls = graph.graph(values['data'], A, refinement, one_numeric_word_switch=True)[3]
        binds = scalar.bind_calls(calls, values['mapping'], A, len(values['data']),
            len(values['rom']), allow_r3=True)
        scalar.verify(values['data'], A, values['rom'], values['mapping'], values['index'],
            calls, binds, selector=scalar.NUMERIC_THUNK_SELECTOR)
        with self.assertRaises(ValueError):
            scalar.verify(values['data'], A, values['rom'], values['mapping'], values['index'],
                calls, binds, selector=scalar.THUNK_SELECTOR)

    def test_manifest_marker_and_tampering_are_exact(self):
        original, _, values = self.fixture()
        bindings = self.bindings(original, values)
        manifest, _ = owner.verify(**values, bindings=bindings)
        for path in (('terminal_alignment_policy', 'gap'),
                     ('terminal_alignment_policy', 'producer_sha256'),
                     ('terminal_alignment_policy', 'schema'),
                     ('ordinary_switch_inventory', 'interposed_constant_words'),
                     ('ordinary_switch_inventory', 'termination_claim')):
            altered = copy.deepcopy(manifest)
            altered['proof'][path[0]][path[1]] = 'tampered'
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'manifest differs'):
                owner.verify(**values, bindings=bindings, manifest=altered)
        relabelled = copy.deepcopy(manifest); relabelled['profile'] = owner.THUNK_SWITCH_SCHEMA
        with self.assertRaises(ValueError):
            owner.verify(**values, bindings=bindings, manifest=relabelled)
        for key in ('calls', 'data', 'switches'):
            changed = copy.deepcopy(bindings); changed[key] = []
            with self.subTest(key=key), self.assertRaises(ValueError):
                owner.verify(**values, bindings=changed)
        marker = f'* verification: `{owner.THUNK_SWITCH_ALIGNED_SCHEMA}`\n'
        self.assertEqual(owner.selector_for_report(marker), SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(marker * 2)
        args = (A, values['data'], {'profile': owner.THUNK_SWITCH_ALIGNED_SCHEMA}, 'source',
                values['mapping'], b'index', b'{}', b'rom')
        with self.assertRaisesRegex(ValueError, 'original ELF'):
            owner.fingerprint(*args)


if __name__ == '__main__':
    unittest.main(verbosity=2)
