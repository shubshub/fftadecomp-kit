"""Restoring owners outside the original runtime domain: same selector and proofs, own schema.

restoring-owner-runtime-v1 used to require both constant unsigned division and a
canonical thunk call, and refused agbcc's closing c0 46 halfword. Neither was a
proof: the frame, alias, buffer, partition and binding checks never depended on
them. Owners in the original domain keep their original schema and records; every
other owner the same proofs close is recorded under OPTIONAL_SCHEMA, with only the
runtimes it calls pinned. The fixtures are assembled, so each shape is exact.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import report_fixtures
import match_evidence
import owner_admission_profile as owner
import owner_runtime_profile as runtime

A, B = 0x08010000, 0x08011000
# The buffer callee at B: return values[0] + values[1].
LEAF = bytes.fromhex('016840684018' '7047')
ORIGINAL_KEYS = {'schema', 'address', 'end', 'bytes', 'instructions', 'body_sha256', 'mapping_sha256',
                 'calls', 'runtime_calls', 'thunk_ABI', 'thunk_dependencies', 'udiv_runtime',
                 'udiv_dependencies', 'divisors', 'frame', 'partition', 'buffer_dependencies',
                 'source_or_original_ELF_admission'}


def owner_assembly(pad=0, thunk=False, division=False, runtime_name=None, tail='.balign 4\n',
                   return_through_lr=False, stack_to_thunk=False, middle=(), pool=()):
    """A restoring owner: a local word buffer passed to an ordinary call, one local BL edge."""
    body = ['push {r4, r5, lr}', 'sub sp, #8', 'adds r4, r0, #0', 'adds r5, r1, #0']
    body += ['lsls r4, r4, #0'] * pad
    body += ['str r4, [sp]', 'adds r1, r4, #1', 'str r1, [sp, #4]', 'mov r0, sp',
             'bl func_08011000', 'adds r4, r0, #0']
    if thunk:
        body += ['mov r0, sp' if stack_to_thunk else 'adds r0, r4, #0', 'adds r3, r5, #0',
                 'bl _call_via_r3', 'adds r4, r0, #0']
    if division:
        body += ['adds r0, r4, #0', 'movs r1, #10', 'bl __udivsi3', 'adds r4, r0, #0']
    if runtime_name:
        body += ['adds r0, r4, #0', 'movs r1, #10', f'bl {runtime_name}', 'adds r4, r0, #0']
    body += list(middle)
    body += ['cmp r4, #0', 'beq .Lskip', 'bl .Lshared', '.Lskip:', 'adds r4, #1', '.Lshared:',
             'adds r0, r4, #0', 'add sp, #8']
    body += ['pop {r4, r5}', 'pop {r1}', 'bx lr'] if return_through_lr else \
        ['pop {r4, r5}', 'pop {r1}', 'bx r1']
    if pool:
        body += ['.balign 4, 0', *pool]
    return ('.syntax unified\n.arch armv4t\n.thumb\n.text\n.global func_08010000\n'
            '.type func_08010000, %function\n.thumb_func\nfunc_08010000:\n' +
            '\n'.join(body) + '\n.size func_08010000, .-func_08010000\n' + tail)


def runtime_rom(identities):
    """A ROM image holding only the given pinned runtime spans of the approved ROM, or None."""
    selected = os.environ.get('FFTA_ROM')
    if not selected or not Path(selected).is_file():
        return None
    rom = bytearray(max(end for _, end, _ in identities) - match.ROM_BASE)
    with open(selected, 'rb') as stream:
        for start, end, _ in identities:
            stream.seek(start - match.ROM_BASE)
            rom[start - match.ROM_BASE:end - match.ROM_BASE] = stream.read(end - start)
    return rom


class Fixture:
    def __init__(self, root, assembly, *, division=False, identities=()):
        self.root = root
        (root / 'f.s').write_text(assembly)
        subprocess.run([match.DEFAULT_AS, '-mthumb-interwork', str(root / 'f.s'), '-o',
                        str(root / 'f.o')], check=True, capture_output=True)
        self.original = (root / 'f.o').read_bytes()
        self.image = match.elf_image(self.original)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS)
        identities = tuple(identities) + (match.UDIVSI3_IDENTITIES if division else ())
        if identities:
            rom = runtime_rom(identities)
            if rom is None:
                raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
        else:
            rom = bytearray(B + len(LEAF) - match.ROM_BASE)
        if len(rom) < 0x142280:
            rom.extend(bytes(0x142280 - len(rom)))
        for name, address in match.function_thunk.ALIASES.items():
            register = int(name.removeprefix('_call_via_r'))
            rom[address - match.ROM_BASE:address - match.ROM_BASE + 4] = \
                (0x4700 + (register << 3)).to_bytes(2, 'little') + b'\xc0\x46'
        rom[B - match.ROM_BASE:B - match.ROM_BASE + len(LEAF)] = LEAF
        symbol, _ = match.function_record(self.image, 'func_08010000', A, True)
        self.size = symbol['size']
        self.rows = [dict(rom=f'0x{A:08X}', end=f'0x{A + self.size:08X}', mode='thumb', instrs=0),
                     dict(rom=f'0x{B:08X}', end=f'0x{B + len(LEAF):08X}', mode='thumb', instrs=4)]
        self.rows += [dict(rom=f'0x{address:08X}', end=f'0x{address + 4:08X}', mode='thumb', instrs=2)
                      for address in match.function_thunk.ALIASES.values()]
        for start, end, _ in dict.fromkeys(identities):
            self.rows.append(dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb',
                                  instrs=(end - start) // 2))
        self.rom = rom
        self.objects = b'{}'
        self.mapping = json.dumps(self.rows).encode()

    def link(self, selector=owner.SELECTOR, image=None, preprocessed=''):
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            Path(workspace, 'f.o').write_bytes(self.original)
            runner.write_text(workspace + '/f.i', preprocessed)
            self.data, self.bindings = owner.object_bytes(
                runner, workspace, self.args, image or self.image, A, bytes(self.rom),
                self.mapping, self.objects, selector=selector, index=b'')
            self.linked = match.elf_image(runner.read_binary(workspace + '/f.elf'))
        self.rom[A - match.ROM_BASE:A - match.ROM_BASE + len(self.data)] = self.data
        self.rows[0]['instrs'] = owner.refine(self.data, A, self.mapping)['instrs']
        self.mapping = json.dumps(self.rows).encode()
        self.index = ''.join(f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
                             f'{int(r["end"], 16) - int(r["rom"], 16)} {r["instrs"]} return\n'
                             for r in self.rows).encode()
        return self

    def inputs(self, **changes):
        values = dict(data=self.data, address=A, rom=bytes(self.rom), mapping=self.mapping,
                      index=self.index, objects=self.objects)
        values.update(changes)
        return values

    def verify(self, **changes):
        bindings = changes.pop('bindings', self.bindings)
        return owner.verify(**self.inputs(**changes), bindings=bindings, selector=owner.SELECTOR)

    def report(self, manifest, count):
        return owner.render(A, (self.data, manifest, 'synthetic-source', self.mapping, self.index,
                                self.objects, bytes(self.rom), count, self.original))


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class OptionalRuntimeTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='restoring_optional_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, *, align=0, division=False, **options):
        """A linked fixture whose size is `align` mod 4 (0 or 2)."""
        for pad in range(2):
            directory = self.root / f'pad{pad}-{len(list(self.root.iterdir()))}'
            directory.mkdir()
            fixture = Fixture(directory, owner_assembly(pad=pad, division=division, **options),
                              division=division)
            if fixture.size % 4 == align:
                return fixture.link()
        raise AssertionError('no fixture size has the requested alignment')

    def test_ordinary_owner_admitted_under_optional_schema(self):
        fixture = self.fixture()
        manifest, instructions = fixture.verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        proof = manifest['proof']
        self.assertEqual(proof['schema'], runtime.OPTIONAL_SCHEMA)
        self.assertEqual(proof['runtime_calls'], [])
        self.assertEqual([name for _, name in proof['calls']], ['func_08011000'])
        self.assertFalse({'thunk_ABI', 'thunk_dependencies', 'udiv_runtime', 'udiv_dependencies',
                          'divisors', 'terminal_alignment'} & proof.keys())
        self.assertEqual(len(proof['frame']['local_aliases']['buffer_calls']), 1)
        self.assertEqual(len(proof['local_branches']), 1)
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
        report = fixture.report(manifest, len(instructions))
        self.assertIn(f'* verification: `{owner.OPTIONAL_SCHEMA}`', report.splitlines())
        self.assertIn(f'* owner runtime: {owner.SELECTOR}', report.splitlines())
        self.assertIn(f'* control flow: {owner.OPTIONAL_CONTROL_FLOW}', report.splitlines())
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), owner.SELECTOR)
        self.assertEqual(match_evidence.saved_selectors(report).arguments,
                         ['--owner-runtime-profile', owner.SELECTOR])

    def test_thunk_without_division_pins_only_the_thunk(self):
        manifest, _ = self.fixture(thunk=True).verify()
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual([name for _, name in proof['runtime_calls']], ['_call_via_r3'])
        self.assertEqual(proof['thunk_ABI'], match.function_thunk.ABI)
        self.assertEqual([row[0] for row in proof['thunk_dependencies']], ['_call_via_r3'])
        self.assertFalse({'udiv_runtime', 'udiv_dependencies', 'divisors'} & proof.keys())

    def test_division_without_thunk_pins_only_the_division(self):
        manifest, _ = self.fixture(division=True).verify()
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual([name for _, name in proof['runtime_calls']], ['__udivsi3'])
        self.assertEqual([value for _, value in proof['divisors']], [10])
        self.assertEqual(proof['udiv_runtime'], match.UDIVSI3_RUNTIME)
        self.assertFalse({'thunk_ABI', 'thunk_dependencies'} & proof.keys())

    def test_original_domain_keeps_original_schema_and_records(self):
        manifest, instructions = self.fixture(thunk=True, division=True).verify()
        self.assertEqual(manifest['profile'], owner.SCHEMA)
        self.assertEqual(manifest['proof']['schema'], runtime.SCHEMA)
        self.assertEqual(set(manifest['proof']), ORIGINAL_KEYS)
        report = self.fixture(thunk=True, division=True).report(manifest, len(instructions))
        self.assertIn(f'* control flow: {owner.CONTROL_FLOW}', report.splitlines())
        # The same runtimes in a size that is 2 mod 4 were never in that domain.
        manifest, _ = self.fixture(thunk=True, division=True, align=2).verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertIn('terminal_alignment', manifest['proof'])

    def test_closing_alignment_halfword_stays_outside_the_symbol(self):
        fixture = self.fixture(align=2)
        self.assertEqual(fixture.image['text'][fixture.size:], b'\xc0\x46')
        self.assertEqual(fixture.linked['text'][fixture.size:], b'\xc0\x46')
        self.assertEqual(len(fixture.data), fixture.size)
        manifest, _ = fixture.verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(manifest['proof']['terminal_alignment']['schema'],
                         owner.TERMINAL_ALIGNMENT_SCHEMA)
        altered = copy.deepcopy(manifest)
        del altered['proof']['terminal_alignment']
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            fixture.verify(manifest=altered)

    def test_other_closing_tails_refused(self):
        fixture = self.fixture(align=2)
        text = fixture.image['text']
        size = fixture.size
        for tail in (b'', b'\x00\x00', b'\x70\x47', b'\xc0\x46\xc0\x46\xc0\x46', b'\xc0'):
            image = copy.deepcopy(fixture.image)
            image['text'] = text[:size] + tail
            section = list(image['sections'][image['text_index']])
            section[5] = len(image['text'])
            image['sections'][image['text_index']] = tuple(section)
            with self.subTest(tail=tail), self.assertRaises(ValueError):
                owner.original_bindings(image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                        selector=owner.SELECTOR)
        whole = self.fixture(align=0)
        image = copy.deepcopy(whole.image)
        image['text'] = image['text'] + b'\xc0\x46'
        with self.assertRaises(ValueError):
            owner.original_bindings(image, A, bytes(whole.rom), whole.mapping, b'{}',
                                    selector=owner.SELECTOR)

    def test_closing_halfword_section_and_symbol_checked(self):
        fixture = self.fixture(align=2)
        for kind in ('alignment', 'symbol-owner'):
            image = copy.deepcopy(fixture.image)
            if kind == 'alignment':
                section = list(image['sections'][image['text_index']])
                section[8] = 2
                image['sections'][image['text_index']] = tuple(section)
            else:
                image['symbols'].append(dict(name='owned_tail', value=fixture.size + 1, size=2, type=0,
                                             bind=1, section=image['text_index']))
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'terminal alignment'):
                owner.original_bindings(image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                        selector=owner.SELECTOR)

    def test_runtime_identities_pinned_where_called(self):
        fixture = self.fixture(thunk=True)
        rom = bytearray(fixture.rom)
        rom[match.function_thunk.ALIASES['_call_via_r3'] - match.ROM_BASE] ^= 1
        with self.assertRaisesRegex(ValueError, 'thunk identity'):
            fixture.verify(rom=bytes(rom))
        fixture = self.fixture(division=True)
        rom = bytearray(fixture.rom)
        rom[match.UDIVSI3_ADDRESS - match.ROM_BASE + 8] ^= 1
        with self.assertRaisesRegex(ValueError, 'identity differs'):
            fixture.verify(rom=bytes(rom))
        # Without a thunk call no thunk body is read; without a division call no division span.
        fixture = self.fixture()
        rom = bytearray(fixture.rom)
        rom[match.function_thunk.ALIASES['_call_via_r3'] - match.ROM_BASE] ^= 1
        self.assertEqual(fixture.verify(rom=bytes(rom))[0]['profile'], owner.OPTIONAL_SCHEMA)

    def test_acyclic_owner_keeps_its_extent_contract(self):
        fixture = self.fixture(align=2)
        with self.assertRaisesRegex(ValueError, 'sole complete Thumb ELF'):
            owner.original_bindings(fixture.image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                    selector=owner.ACYCLIC_SELECTOR)

    def test_manifest_and_binding_tampering_refused(self):
        fixture = self.fixture()
        manifest, _ = fixture.verify()
        for change in ('schema', 'runtime', 'divisor'):
            altered = copy.deepcopy(manifest)
            if change == 'schema':
                altered['profile'] = owner.SCHEMA
            elif change == 'runtime':
                altered['proof']['udiv_runtime'] = match.UDIVSI3_RUNTIME
            else:
                altered['proof']['divisors'] = []
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=altered)
        bindings = copy.deepcopy(fixture.bindings)
        bindings['calls'].append([0, '__udivsi3'])
        with self.assertRaisesRegex(ValueError, 'bindings do not cover'):
            fixture.verify(bindings=bindings)

    def test_count_and_return_frame_still_checked(self):
        fixture = self.fixture()
        with self.assertRaises(ValueError):
            fixture.verify(index=fixture.index.replace(f' {fixture.rows[0]["instrs"]} return'.encode(),
                                                       f' {fixture.rows[0]["instrs"] + 1} return'.encode(), 1))
        # Every return must restore the entry LR from the saved frame: LR itself holds a
        # call's or a local BL edge's continuation by then.
        with self.assertRaises(ValueError):
            self.fixture(return_through_lr=True).verify()

    def test_stack_address_in_a_thunk_argument_refused(self):
        with self.assertRaisesRegex(ValueError, 'carry local stack provenance'):
            self.fixture(thunk=True, stack_to_thunk=True).verify()

    def test_other_runtimes_still_refused(self):
        for name in ('__divsi3', '__umodsi3', 'func_08142AB0'):
            directory = self.root / name
            directory.mkdir()
            fixture = Fixture(directory, owner_assembly(runtime_name=name))
            with self.subTest(name=name), self.assertRaises(ValueError):
                owner.original_bindings(fixture.image, A, bytes(fixture.rom), fixture.mapping, b'{}',
                                        selector=owner.SELECTOR)


SOURCE = '''typedef unsigned int u32;
extern u32 func_08011000(u32 *values);
extern u32 data_02010000[8];
u32 func_08010000(u32 value) {
    u32 values[2];
    values[0] = value;
    values[1] = value + 1;
    value = func_08011000(values);
    switch (value & 7) {
    case 0: value += data_02010000[0]; break;
    case 1: value -= data_02010000[1]; break;
    case 2: value ^= data_02010000[2]; break;
    case 3: value |= data_02010000[3]; break;
    case 4: value &= data_02010000[4]; break;
    case 5: value *= data_02010000[5]; break;
    case 6: value = data_02010000[6] - value; break;
    default: value = data_02010000[7]; break;
    }
    return value;
}
'''


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which(match.DEFAULT_LD), 'the fixed compiler is required')
class CompiledOwnerTests(unittest.TestCase):
    """A natural C owner with ordinary calls, a stack buffer and a guarded switch only."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='restoring_optional_c_', dir=scratch)
        cls.root = Path(cls.temporary.name)
        for name in ('src', 'config', 'symbols', 'include', 'build', 'docs/match'):
            (cls.root / name).mkdir(parents=True)
        (cls.root / 'src/08010000.c').write_text(SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS)
        objects = b'{"data_02010000":"0x02010000"}\n'
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH,
                              root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            symbol, _ = match.function_record(image, 'func_08010000', A, True)
            rows = [dict(rom=f'0x{A:08X}', end=f'0x{A + symbol["size"]:08X}', mode='thumb', instrs=0),
                    dict(rom=f'0x{B:08X}', end=f'0x{B + len(LEAF):08X}', mode='thumb', instrs=4)]
            mapping = json.dumps(rows).encode()
            rom = bytearray(B + len(LEAF) - match.ROM_BASE)
            rom[B - match.ROM_BASE:] = LEAF
            data, _ = owner.object_bytes(runner, workspace, args, image, A, bytes(rom), mapping,
                                         objects, index=b'')
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
        (cls.root / 'config/functions.json').write_text(json.dumps(rows))
        (cls.root / 'symbols/functions.txt').write_text(''.join(
            f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
            f'{int(r["end"], 16) - int(r["rom"], 16)} {r["instrs"]} return\n' for r in rows))
        (cls.root / 'config/data_symbols.json').write_bytes(objects)
        (cls.root / 'baserom.bin').write_bytes(rom)
        cls.environment = patch.dict(os.environ, FFTA_ROM=str(cls.root / 'baserom.bin'))
        cls.environment.start()
        cls.result = owner.build(cls.root, A)
        cls.report = owner.render(A, cls.result)
        (cls.root / 'docs/match/08010000.md').write_text(cls.report)

    @classmethod
    def tearDownClass(cls):
        cls.environment.stop()
        cls.temporary.cleanup()

    def test_compiled_owner_admitted_and_report_replays(self):
        manifest = self.result[1]
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(manifest['proof']['runtime_calls'], [])
        self.assertTrue(manifest['bindings']['switches'])
        self.assertTrue(manifest['bindings']['data'])
        self.assertTrue(match_evidence.report_matches(report_fixtures.carried(self.report, self.root, A), self.root, A))
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(report_fixtures.carried(self.report, self.root, A),
                                                         self.root, A),
                         ['--owner-runtime-profile', owner.SELECTOR])

    def test_changed_source_refused_on_replay(self):
        source = self.root / 'src/08010000.c'
        original = source.read_bytes()
        try:
            source.write_bytes(original + b'\n/* changed source identity */\n')
            self.assertFalse(match_evidence.report_matches(self.report, self.root, A))
        finally:
            source.write_bytes(original)


if __name__ == '__main__':
    unittest.main()
