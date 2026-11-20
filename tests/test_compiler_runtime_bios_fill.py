"""Compiler-emitted runtime names under the plain BIOS fill buffer data selector.

`addressed-native-bios-fill-buffer-data-v1` binds an explicit call of a pinned
runtime entry; agbcc emits the same direct BL for `/` and `%`, naming
__udivsi3, __umodsi3, __divsi3 or __modsi3.  These tests show that the two
spellings get the same bindings, walk and verdict, that the report differs
only where it records the spelling, and that the hostile shapes refuse for
both spellings.  The first class is synthetic (no compiler); the second
compiles with the fixed agbcc against a synthetic ROM.
"""
import argparse
import copy
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import addressed_signed_runtime_profile as profile
import bios_cpuset_fill_profile as bios
import match
import match_evidence as evidence
import test_addressed_signed_runtime_two_words_data as boundary
import test_addressed_unsigned_runtime_profile as fixtures

A, B = fixtures.A, fixtures.B
SELECTOR = profile.BIOS_DATA_SELECTOR
POLICY = profile.COMPILER_BIOS_FILL
CANONICAL = {'udiv': 'func_08142AB0', 'umod': 'func_08142B28', 'div': 'func_081426B8', 'mod': 'func_08142950'}
ALIAS = {'udiv': '__udivsi3', 'umod': '__umodsi3', 'div': '__divsi3', 'mod': '__modsi3'}
IDENTITY = {'udiv': 'agbcc-thumb-udivsi3-v1', 'umod': 'agbcc-thumb-umodsi3-v1',
            'div': 'agbcc-thumb-divsi3-v1', 'mod': 'agbcc-thumb-modsi3-v1'}
OBJECTS = b'{"destination":"0x03000020"}'
RUNTIME_SPANS = sorted(set(match.UDIVSI3_IDENTITIES + profile.unsigned_remainder.IDENTITIES +
                           profile.quotient.IDENTITIES + profile.remainder.IDENTITIES))


def tokens(op='udiv', r0=0x2009, r1=0x2103, before=()):
    """push {lr}; sub sp, #4; r0, r1; bl runtime; ldr r3, =destination; str r0, [r3];
    r2 = 0x01000000; mov r0, sp; movs r1, #0; bl CpuSet; add sp, #4; pop {r0}; bx r0"""
    return (0xB500, 0xB081, *before, r0, r1, op, ('ldr', 3), 0x6018, 0x2280, 0x0452,
            0x4668, 0x2100, 'bios', 0xB001, 0xBC01, 0x4700)


class CompilerRuntimeBiosFillTests(unittest.TestCase):
    build_boundary = boundary.TwoWordsDataTests.build_boundary

    def setUp(self):
        self.base = fixtures.AddressedUnsignedRuntimeTests('runTest')
        self.base.setUp()
        self.addCleanup(self.base.doCleanups)
        self.fixtures = self
        self.spelling = 'explicit'

    def fixture(self, items=None):
        items = tokens() if items is None else items
        body, calls, bindings, loads = bytearray(), {}, {}, []
        for item in items:
            if type(item) is int:
                body += struct.pack('<H', item)
            elif type(item) is tuple:
                loads.append((len(body), item[1]))
                body += b'\0\0'
            else:
                name = bios.NAME if item == 'bios' else CANONICAL.get(item, f'func_{B:08X}')
                site, target = A + len(body), int(name[5:], 16)
                calls[site] = target
                if item != 'ordinary':
                    bindings[site] = name
                body += fixtures.fixtures.bl(site, target)
        if len(body) % 4:
            body += b'\0\0'
        pool = len(body)
        for offset, register in loads:
            struct.pack_into('<H', body, offset, 0x4800 | register << 8 | (pool - ((offset + 4) & ~3)) // 4)
        body += struct.pack('<I', 0x03000020)
        rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+len(body):08X}', mode='thumb', instrs=len(items)),
                dict(rom=f'0x{B:08X}', end=f'0x{B+2:08X}', mode='thumb', instrs=1),
                dict(rom=f'0x{bios.ADDRESS:08X}', end=f'0x{bios.ADDRESS+4:08X}', mode='thumb', instrs=2)]
        rows += [dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb', instrs=(hi-lo)//2)
                 for lo, hi, _ in RUNTIME_SPANS]
        mapping, index = fixtures.fixtures.indexes(rows)
        rom = bytearray(self.base.rom)
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rom[B-match.ROM_BASE:B-match.ROM_BASE+2] = b'\x70\x47'
        rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4] = bios.WRAPPER
        return dict(data=bytes(body), address=A, rom=bytes(rom), mapping=mapping, index=index,
                    calls=calls, bindings=bindings, selector=SELECTOR,
                    data_mapping=OBJECTS, data_bindings=[[pool, 'destination', 0]])

    @staticmethod
    def compiler_calls(f):
        names = {name: alias for alias, name in profile.COMPILER_THUNK_ALIASES.items()}
        return {site: names[name] for site, name in f['bindings'].items() if name in names}

    def rename(self, image, reverse=False):
        names = profile.COMPILER_THUNK_ALIASES if reverse else \
            {name: alias for alias, name in profile.COMPILER_THUNK_ALIASES.items()}
        for symbol in image['symbols']:
            symbol['name'] = names.get(symbol['name'], symbol['name'])
        return image

    # The two methods build_boundary calls: the original and linked ELF of either spelling.
    def data_image(self, f):
        image = self.base.data_image(f)
        return self.rename(image) if self.spelling == 'compiler' else image

    def linked_data_image(self, f, original):
        if self.spelling != 'compiler':
            return self.base.linked_data_image(f, original)
        canonical = self.rename(copy.deepcopy(original), reverse=True)
        return self.rename(self.base.linked_data_image(f, canonical))

    def bindings(self, image, f, selector=SELECTOR, compiler_calls=None):
        return profile.original_bindings(image, A, f['rom'], f['mapping'], selector=selector,
                                         data_mapping=f['data_mapping'], data_relocations={},
                                         compiler_calls=compiler_calls)

    def report(self, f, spelling):
        self.spelling = spelling
        with self.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            with patch.object(sys, 'argv', ['match.py', '--root', str(root),
                    '--addressed-signed-runtime-profile', SELECTOR, f'{A:08X}']), redirect_stdout(io.StringIO()):
                self.assertEqual(match.main(), 0)
            report = (root / 'docs/match/08010000.md').read_text()
            self.assertTrue(evidence.report_matches(report, root, A))
            return report, root

    def test_compiler_names_bind_the_explicit_entries(self):
        for op in CANONICAL:
            with self.subTest(op=op):
                f = self.fixture(tokens(op))
                explicit = self.base.data_image(f)
                sites = {}
                self.assertEqual(self.bindings(self.rename(copy.deepcopy(explicit)), f, compiler_calls=sites)[:2],
                                 (f['calls'], f['bindings']))
                site = next(site for site, name in f['bindings'].items() if name == CANONICAL[op])
                self.assertEqual(sites, {site: ALIAS[op]})
                unchanged = {}
                self.assertEqual(self.bindings(explicit, f, compiler_calls=unchanged)[:2],
                                 (f['calls'], f['bindings']))
                self.assertEqual(unchanged, {})

    def test_other_selectors_disabled_policy_and_unrecorded_sites_refuse(self):
        f = self.fixture()
        compiler = self.rename(self.base.data_image(f))
        # The compiler scalar-control selector keeps its own signed-only binding.
        self.assertFalse(POLICY.applies(profile.COMPILER_BIOS_SCALAR_DATA_SELECTOR))
        for selector in (profile.BIOS_SCALAR_DATA_SELECTOR, profile.BIOS_ZERO_EXTENDED_DATA_SELECTOR,
                         profile.BIOS_READONLY_DATA_SELECTOR, profile.UNSIGNED_BUFFER_DATA_SELECTOR,
                         profile.INTEGER_DATA_SELECTOR, profile.DATA_SELECTOR,
                         profile.COMPILER_BIOS_SCALAR_DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                self.bindings(copy.deepcopy(compiler), f, selector, {})
        with patch.object(POLICY, 'enabled', False), \
                self.assertRaisesRegex(ValueError, 'canonical addressed function'):
            self.bindings(copy.deepcopy(compiler), f, compiler_calls={})
        with self.assertRaisesRegex(ValueError, 'recorded call sites'):
            self.bindings(copy.deepcopy(compiler), f)
        with self.assertRaisesRegex(ValueError, 'fresh empty'):
            self.bindings(copy.deepcopy(compiler), f, compiler_calls={A: '__udivsi3'})
        sized = copy.deepcopy(compiler)
        next(symbol for symbol in sized['symbols'] if symbol['name'] == '__udivsi3')['size'] = 4
        with self.assertRaisesRegex(ValueError, 'zero original size'):
            self.bindings(sized, f, compiler_calls={})
        for alias in ('__udivsi30', '__div0', '_call_via_r3', 'udivsi3'):
            bad = copy.deepcopy(compiler)
            next(symbol for symbol in bad['symbols'] if symbol['name'] == '__udivsi3')['name'] = alias
            with self.subTest(alias=alias), self.assertRaises(ValueError):
                self.bindings(bad, f, compiler_calls={})

    def test_manifest_equals_the_explicit_one_plus_each_compiler_site(self):
        for op in CANONICAL:
            with self.subTest(op=op):
                f = self.fixture(tokens(op))
                explicit, _ = profile.verify(**f)
                manifest, _ = profile.verify(**f, compiler_calls=self.compiler_calls(f))
                record = manifest.pop('compiler_runtime')
                self.assertEqual(manifest, explicit)
                site = next(site for site, name in f['bindings'].items() if name == CANONICAL[op])
                self.assertEqual(record['calls'], [[site - A, ALIAS[op], CANONICAL[op], IDENTITY[op]]])
                self.assertEqual(record['contract'], POLICY.contract)
                self.assertNotIn('compiler_runtime', explicit)
        f = self.fixture()
        manifest, _ = profile.verify(**f, compiler_calls=self.compiler_calls(f))
        self.assertEqual(profile.verify(**f, compiler_calls=self.compiler_calls(f), manifest=manifest)[0], manifest)
        forged = copy.deepcopy(manifest)
        forged['compiler_runtime']['calls'][0][1] = '__umodsi3'
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, compiler_calls=self.compiler_calls(f), manifest=forged)
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            profile.verify(**f, manifest=manifest)

    def test_every_runtime_call_must_be_one_recorded_compiler_site_of_its_own_name(self):
        f = self.fixture(tokens('udiv', before=(0x2009, 0x2103, 'mod')))
        complete = self.compiler_calls(f)
        self.assertEqual(sorted(complete.values()), ['__modsi3', '__udivsi3'])
        profile.verify(**f, compiler_calls=complete)
        udiv, mod = sorted(complete, key=complete.get, reverse=True)
        bios_site = next(site for site, name in f['bindings'].items() if name == bios.NAME)
        for calls in ({udiv: '__udivsi3'}, {mod: '__modsi3'}, {udiv: '__umodsi3', mod: '__modsi3'},
                      {udiv: '__udivsi3', mod: '__divsi3'}, {**complete, bios_site: '__udivsi3'},
                      {}, {udiv: 'func_08142AB0', mod: '__modsi3'}):
            with self.subTest(calls=calls), self.assertRaisesRegex(ValueError, 'compiler-emitted'):
                profile.verify(**f, compiler_calls=calls)
        for selector in (profile.BIOS_SCALAR_DATA_SELECTOR, profile.DATA_SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                profile.verify(**dict(f, selector=selector), compiler_calls=complete)

    def refused(self, f, message):
        """Both spellings give the same refusal."""
        for calls in (None, self.compiler_calls(f) or None):
            with self.subTest(spelling='compiler' if calls else 'explicit'), \
                    self.assertRaisesRegex(ValueError, message):
                profile.verify(**f, compiler_calls=calls)

    def test_runtime_bytes_one_instruction_from_the_pin_refuse(self):
        for op in CANONICAL:
            f = self.fixture(tokens(op))
            entry = int(CANONICAL[op][5:], 16)
            rom = bytearray(f['rom'])
            struct.pack_into('<H', rom, entry + 2 - match.ROM_BASE, 0x2001)   # one movs r0, #1
            with self.subTest(op=op):
                self.refused(dict(f, rom=bytes(rom)), 'runtime or (zero-path )?dependency identity differs')

    def test_stack_addresses_reaching_the_runtime_refuse(self):
        # mov r0, sp / mov r1, sp / add r0, sp, #0 at the runtime call.
        for r0, r1 in ((0x4668, 0x2103), (0x2009, 0x4669), (0xA800, 0x2103)):
            with self.subTest(r0=hex(r0), r1=hex(r1)):
                self.refused(self.fixture(tokens(r0=r0, r1=r1)), 'division runtime is outside buffer-call')
        # A dead stack address left in r2, r3 or r12 is refused as well.
        for before in ((0x466A,), (0x466B,), (0x46EC,)):
            with self.subTest(before=before):
                self.refused(self.fixture(tokens(before=before)), 'division runtime is outside buffer-call')

    def test_operands_loaded_from_stack_the_proof_does_not_cover_refuse(self):
        # ldr r1, [sp, #8] and ldr r0, [sp, #16] read above the 4-byte frame and saved LR.
        for r0, r1 in ((0x2009, 0x9902), (0x9804, 0x2103)):
            with self.subTest(r0=hex(r0), r1=hex(r1)):
                self.refused(self.fixture(tokens(r0=r0, r1=r1)), 'leaves its established frame')
        # The allocated local word itself is covered: ldr r1, [sp].
        f = self.fixture(tokens(r1=0x9900))
        profile.verify(**f, compiler_calls=self.compiler_calls(f))

    def test_runtime_reached_through_a_thunk_or_register_refuses(self):
        thunk = match.function_thunk.ALIASES['_call_via_r3']
        f = self.fixture()
        site = next(site for site, name in f['bindings'].items() if name == 'func_08142AB0')
        body = bytearray(f['data'])
        body[site-A:site-A+4] = fixtures.fixtures.bl(site, thunk)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        rows = json.loads(f['mapping']) + [dict(rom=f'0x{thunk:08X}', end=f'0x{thunk+4:08X}',
                                                 mode='thumb', instrs=2)]
        mapping, index = fixtures.fixtures.indexes(rows)
        struct.pack_into('<HH', rom, thunk - match.ROM_BASE, 0x4718, 0x46C0)
        bindings = {key: value for key, value in f['bindings'].items() if key != site}
        thunked = dict(f, data=bytes(body), rom=bytes(rom), mapping=mapping, index=index,
                       calls={**f['calls'], site: thunk}, bindings=bindings)
        with self.assertRaisesRegex(Exception, 'runtime call thunks'):
            profile.verify(**thunked)
        with self.assertRaisesRegex(ValueError, 'compiler-emitted'):
            profile.verify(**thunked, compiler_calls={site: '__udivsi3'})
        original = self.base.data_image(thunked)
        next(symbol for symbol in original['symbols'] if symbol['name'] == f'func_{thunk:08X}')['name'] = \
            '_call_via_r3'
        with self.assertRaisesRegex(ValueError, 'canonical addressed function'):
            self.bindings(original, thunked, compiler_calls={})
        # mov lr, pc; bx r3 in place of the BL: an indirect transfer the walk never takes as a call.
        body = bytearray(f['data'])
        body[site-A:site-A+4] = struct.pack('<HH', 0x46FE, 0x4718)
        rom = bytearray(f['rom'])
        rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        register = dict(f, data=bytes(body), rom=bytes(rom), bindings=bindings,
                        calls={key: value for key, value in f['calls'].items() if key != site})
        with self.assertRaisesRegex(ValueError, 'structural inventory is not closed'):
            profile.verify(**register)
        with self.assertRaisesRegex(ValueError, 'compiler-emitted'):
            profile.verify(**register, compiler_calls={site: '__udivsi3'})

    def test_reports_differ_only_where_they_record_the_spelling(self):
        f = self.fixture(tokens('udiv', before=(0x2009, 0x2103, 'mod')))
        explicit, _ = self.report(f, 'explicit')
        compiler, root = self.report(f, 'compiler')
        sites = sorted(self.compiler_calls(f).items())
        line = ('* compiler runtime binding: ' + ', '.join(
            f'0x{site:08X} {name} -> {profile.COMPILER_THUNK_ALIASES[name]} '
            f'({IDENTITY[next(op for op, alias in ALIAS.items() if alias == name)]})'
            for site, name in sites) + '; ' + POLICY.contract)
        self.assertIn(line, compiler.splitlines())
        self.assertNotIn('compiler runtime', explicit)
        evidence_prefix = ('* addressed signed runtime evidence: ', '* addressed signed runtime proof SHA-256: ')
        strip = lambda report: [row for row in report.splitlines()
                                if row != line and not row.startswith(evidence_prefix)]
        self.assertEqual(strip(compiler), strip(explicit))

        def saved(report):
            row = next(row for row in report.splitlines() if row.startswith(evidence_prefix[0]))
            return json.loads(row[len(evidence_prefix[0]) + 1:-1])
        recorded = saved(compiler)
        record = recorded['manifest'].pop('compiler_runtime')
        self.assertEqual(recorded, saved(explicit))
        self.assertEqual([row[:2] for row in record['calls']], [[site - A, name] for site, name in sites])

    def test_report_replay_needs_the_premise_and_the_compiler_names(self):
        f = self.fixture()
        self.spelling = 'compiler'
        report, _ = self.report(f, 'compiler')
        with self.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            self.assertTrue(evidence.report_matches(report, root, A))
            premise = next(row for row in report.splitlines() if row.startswith('* compiler runtime binding:'))
            self.assertFalse(evidence.report_matches(report.replace(premise + '\n', ''), root, A))
            self.assertFalse(evidence.report_matches(report.replace('__udivsi3 ->', '__umodsi3 ->'), root, A))
            with patch.object(POLICY, 'enabled', False):
                self.assertFalse(evidence.report_matches(report, root, A))
        self.spelling = 'explicit'
        with self.build_boundary(f) as (root, _, _), patch.object(
                profile, 'toolchain_fingerprint', return_value=[['synthetic', '1' * 64]]):
            self.assertFalse(evidence.report_matches(report, root, A))

    def test_compiler_names_need_a_source_without_runtime_identifiers(self):
        f = self.fixture()
        self.spelling = 'compiler'
        for source in ('unsigned __udivsi3(unsigned, unsigned);', 'unsigned func_08142AB0(unsigned, unsigned);',
                       'int __modsi3(int, int);'):
            with self.subTest(source=source), self.build_boundary(f) as (root, _, commands):
                original = match.Runner.read_binary

                def preprocessed(runner, path, source=source):
                    return source.encode() if path.endswith('f.i') else original(runner, path)
                with patch.object(match.Runner, 'read_binary', preprocessed), \
                        self.assertRaisesRegex(ValueError, 'preprocessed C'):
                    profile.build(root, A, selector=SELECTOR)
                self.assertEqual(commands, [])


TOOLS = Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and all(
    shutil.which(tool) for tool in ('cpp', 'arm-none-eabi-as', 'arm-none-eabi-ld', 'arm-none-eabi-objcopy'))
# agbcc may move a load across a runtime call that it keeps after an ordinary call
# (it hoists the address of a stored-to object above `bl __udivsi3`), so the
# quotient stays in a local across the CpuSet call, where both spellings compile
# to the same bytes.
SOURCE = '''typedef unsigned short u16;
typedef unsigned int u32;
extern u32 data_02001000;
extern u16 data_02001100[];
void func_0814186C(const void *source, void *destination, u32 control);
DECLARATION
void func_08010000(u32 value)
{
    u16 blank = 0;
    u32 quotient = QUOTIENT;

    func_0814186C(&blank, data_02001100, 0x01000010);
    data_02001000 = quotient;
}
'''
SPELLINGS = {
    'slash': ('', 'value / 0x108'),
    'explicit': ('u32 func_08142AB0(u32 value, u32 divisor);', 'func_08142AB0(value, 0x108)'),
    'declared': ('u32 __udivsi3(u32 value, u32 divisor);', '__udivsi3(value, 0x108)'),
    'mixed': ('u32 func_08142AB0(u32 value, u32 divisor);', 'value / 0x108 + func_08142AB0(value, 3)'),
}
NATIVE_OBJECTS = {'data_02001000': '0x02001000', 'data_02001100': '0x02001100'}


@unittest.skipUnless(TOOLS, 'fixed compiler and binutils required')
class CompiledSpellingTests(unittest.TestCase):
    """The fixed agbcc compiles both spellings to the same bytes and the same verdict."""

    @classmethod
    def setUpClass(cls):
        cls.rom = bytearray(0x143000)
        cls.rom[0x14274C:0x14274E] = bytes.fromhex('7047')
        cls.rom[0x142B20:0x142B24] = fixtures.fixtures.bl(0x08142B20, 0x0814274C)
        cls.rom[bios.ADDRESS-match.ROM_BASE:bios.ADDRESS-match.ROM_BASE+4] = bios.WRAPPER
        spans = tuple((lo, hi, hashlib.sha256(cls.rom[lo-match.ROM_BASE:hi-match.ROM_BASE]).hexdigest())
                      for lo, hi, _ in match.UDIVSI3_IDENTITIES)
        cls.patch = patch.object(match, 'UDIVSI3_IDENTITIES', spans)
        cls.patch.start()
        cls.scratch = tempfile.TemporaryDirectory(prefix='compiler_bios_fill_')
        cls.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
            objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        root = cls.make_root('slash')
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root, timeout=120)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, cls.args, root, A, 'src/08010000.c')
            size = match.function_record(image, f'func_{A:08X}', A, True)[0]['size']
            cls.rows = [dict(rom=f'0x{A:08X}', end=f'0x{A+size:08X}', mode='thumb', instrs=0),
                        dict(rom=f'0x{bios.ADDRESS:08X}', end=f'0x{bios.ADDRESS+4:08X}', mode='thumb', instrs=2),
                        *(dict(rom=f'0x{lo:08X}', end=f'0x{hi:08X}', mode='thumb', instrs=(hi-lo)//2)
                          for lo, hi, _ in match.UDIVSI3_IDENTITIES)]
            sites = {}
            body = profile.object_bytes(runner, workspace, cls.args, image, A, bytes(cls.rom),
                json.dumps(cls.rows).encode(), selector=SELECTOR,
                data_mapping=json.dumps(NATIVE_OBJECTS).encode(), compiler_calls=sites)[0]
        cls.sites = sites
        cls.rom[A-match.ROM_BASE:A-match.ROM_BASE+len(body)] = body
        import owner_admission_profile as owner
        cls.rows[0]['instrs'] = owner.refine(body, A, json.dumps(cls.rows).encode())['instrs']

    @classmethod
    def tearDownClass(cls):
        cls.patch.stop()
        cls.scratch.cleanup()

    @classmethod
    def make_root(cls, spelling):
        declaration, quotient = SPELLINGS[spelling]
        root = Path(tempfile.mkdtemp(prefix=spelling + '_', dir=cls.scratch.name))
        for sub in ('src', 'include', 'build', 'config', 'symbols', 'docs/match'):
            (root/sub).mkdir(parents=True)
        (root/'src/08010000.c').write_text(SOURCE.replace('DECLARATION', declaration).replace('QUOTIENT', quotient))
        (root/'config/data_symbols.json').write_text(json.dumps(NATIVE_OBJECTS))
        if hasattr(cls, 'rows'):
            (root/'config/functions.json').write_text(json.dumps(cls.rows))
            (root/'symbols/functions.txt').write_text(boundary.fixtures.indexes(cls.rows)[1].decode())
            (root/'baserom.bin').write_bytes(cls.rom)
        return root

    def report(self, spelling):
        root = self.make_root(spelling)
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')), patch.object(sys, 'argv', [
                'match.py', '--root', str(root), '--addressed-signed-runtime-profile', SELECTOR,
                f'{A:08X}']), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
            report = (root/'docs/match/08010000.md').read_text()
            self.assertTrue(evidence.report_matches(report, root, A))
        return report

    def refusal(self, spelling):
        root = self.make_root(spelling)
        with patch.dict(os.environ, FFTA_ROM=str(root/'baserom.bin')), \
                self.assertRaises(ValueError) as caught:
            profile.build(root, A, selector=SELECTOR)
        return str(caught.exception)

    def test_both_spellings_match_and_differ_only_where_the_spelling_is_recorded(self):
        self.assertEqual(list(self.sites.values()), ['__udivsi3'])
        slash, explicit = self.report('slash'), self.report('explicit')
        site = next(iter(self.sites))
        line = next(row for row in slash.splitlines() if row.startswith('* compiler runtime binding:'))
        self.assertTrue(line.startswith(f'* compiler runtime binding: 0x{site:08X} __udivsi3 -> func_08142AB0 '
                                        '(agbcc-thumb-udivsi3-v1); '))
        self.assertNotIn('compiler runtime', explicit)
        prefix = '* addressed signed runtime evidence: `'
        rows = lambda report: [row for row in report.splitlines() if row != line and
                               not row.startswith((prefix, '* addressed signed runtime proof SHA-256'))]
        self.assertEqual(rows(slash), rows(explicit))
        saved = [json.loads(next(row for row in report.splitlines() if row.startswith(prefix))[len(prefix):-1])
                 for report in (slash, explicit)]
        self.assertEqual(saved[0]['manifest'].pop('compiler_runtime')['calls'],
                         [[site - A, '__udivsi3', 'func_08142AB0', 'agbcc-thumb-udivsi3-v1']])
        spelled = ('source_sha256', 'assembly_sha256', 'original_elf_sha256', 'linked_elf_sha256')
        for record in saved:
            for key in spelled:
                record.pop(key)
        self.assertEqual(saved[0], saved[1])

    def test_declared_and_mixed_runtime_spellings_refuse(self):
        for spelling in ('declared', 'mixed'):
            with self.subTest(spelling=spelling):
                self.assertIn('preprocessed C', self.refusal(spelling))

    def test_the_disabled_policy_keeps_the_plain_refusal(self):
        with patch.object(POLICY, 'enabled', False):
            self.assertIn('canonical addressed function', self.refusal('slash'))
            self.report('explicit')


if __name__ == '__main__':
    unittest.main()
