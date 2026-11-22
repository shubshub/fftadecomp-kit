"""A compiler-emitted memcpy in a restoring owner, bound to the pinned ROM copy helper.

agbcc copies a structure by assignment with a call to memcpy that the source
never names; in the ROM that call reaches the 98-byte helper at 0x081443FC.
The restoring owner refused the name, so the struct copies of 0807A79C could
not be bound.  The fixtures are assembled, so each shape is exact; the helper
bytes come from the approved ROM.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import copy_helper_summary_profile as summary
import match
import owner_admission_profile as owner
import owner_copy_calls as copy_calls
import rom_table_copy_profile as rom_copy
import test_restoring_owner_optional_runtime as base
from local_rom_halfword_table_profile import COPY_SHA256

A = base.A
HELPER = rom_copy.HELPER
IDENTITY = ((HELPER, HELPER + 98, COPY_SHA256),)
OBJECTS = b'{"data_03002818":"0x03002818"}'
POOL = ['.Lstate:', '.word data_03002818']
# A structure copy between two members of *data_03002818, as agbcc emits it.
STATE = ['ldr r0, .Lstate', 'ldr r0, [r0]', 'adds r1, r0, #0', 'adds r1, #0xcc']
COPY = STATE + ['movs r2, #0xcc', 'bl memcpy']


def helper_body():
    rom = base.runtime_rom(IDENTITY)
    if rom is None:
        raise unittest.SkipTest('FFTA_ROM must reference the approved ROM')
    return bytes(rom[HELPER - match.ROM_BASE:HELPER - match.ROM_BASE + 98])


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class CompilerMemcpyTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='owner_compiler_memcpy_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle=COPY, pool=POOL, *, align=None, change=None, preprocessed='', **options):
        for pad in range(2):
            directory = self.root / f'f{len(list(self.root.iterdir()))}'
            directory.mkdir()
            fixture = base.Fixture(directory, base.owner_assembly(pad=pad, middle=middle, pool=pool, **options),
                                   division=options.get('division', False), identities=IDENTITY)
            if align is None or fixture.size % 4 == align:
                break
        else:
            raise AssertionError('no fixture size has the requested alignment')
        fixture.objects = OBJECTS
        if change:
            change(fixture)
        fixture.mapping = json.dumps(fixture.rows).encode()
        return fixture.link(preprocessed=preprocessed)

    def refused(self, message, middle=COPY, pool=POOL, **options):
        with self.assertRaisesRegex(ValueError, message):
            self.fixture(middle, pool, **options).verify()

    def test_struct_copy_bound_proved_and_recorded(self):
        fixture = self.fixture()
        sites = [site for site, name in fixture.bindings['calls'] if name == 'memcpy']
        self.assertEqual(len(sites), 1)
        manifest, instructions = fixture.verify()
        proof = manifest['proof']
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertIn([sites[0], 'memcpy'], proof['calls'])
        self.assertNotIn(f'func_{HELPER:08X}', [name for _, name in proof['calls']])
        record = proof['compiler_memcpy']
        self.assertEqual(record['schema'], copy_calls.MEMCPY_SCHEMA)
        self.assertEqual(record['helper']['body_sha256'], COPY_SHA256)
        self.assertEqual((record['source_named'], record['overlap_proved'], record['object_extent_proved']),
                         (False, False, False))
        [contract] = record['contracts']
        self.assertEqual((contract['count'], contract['cases']), (0xCC, 16))
        [load] = [item.address - A for item in instructions if item.mnemonic == 'ldr' and item.op_str == 'r0, [r0]']
        self.assertEqual(record['calls'], [dict(site=sites[0], count=0xCC,
            destination={'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0},
            source={'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0xCC})])
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
        report = fixture.report(manifest, len(instructions))
        lines = [line for line in report.splitlines() if line.startswith('* compiler memcpy:')]
        self.assertEqual(lines, [f'* compiler memcpy: 0x{HELPER:08X} at call +0x{sites[0]:X}: count 204, '
                                 f'destination *(data_03002818+0x0)@+0x{load:X}+0x0, '
                                 f'source *(data_03002818+0x0)@+0x{load:X}+0xCC; '
                                 f'contract 16 cases {contract["execution_sha256"][:16]}; '
                                 'overlap and extent not proved'])
        self.assertIn(f'* compiler memcpy helper: 0x{HELPER:08X} is the toolchain newlib libc/string/memcpy.c '
                      '(89ee5338c9b7afed) compiled -O2 -fno-builtin -mthumb-interwork: 98 bytes aa822d873bad381a',
                      report.splitlines())
        self.assertEqual(record['library_identity'], copy_calls.LIBRARY_MEMCPY)
        self.assertEqual(owner.selector_for_report(report), owner.SELECTOR)

    def test_loaded_provenance_names_its_load_across_a_call_and_a_store(self):
        middle = ['ldr r0, .Lstate', 'ldr r4, [r0]', 'mov r0, sp', 'bl func_08011000', 'movs r1, #0',
                  'ldr r0, .Lstate', 'str r1, [r0]', 'adds r0, r4, #0', 'adds r1, r4, #0', 'adds r1, #0xcc',
                  'movs r2, #0xcc', 'bl memcpy']
        manifest, instructions = self.fixture(middle).verify()
        [load] = [item.address - A for item in instructions if item.mnemonic == 'ldr' and item.op_str == 'r4, [r0]']
        [call] = manifest['proof']['compiler_memcpy']['calls']
        self.assertEqual((call['destination'], call['source']),
                         ({'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0},
                          {'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0xCC}))

    def test_count_above_the_buffer_summary_bound(self):
        middle = STATE + ['ldr r2, .Lsize', 'bl memcpy']
        manifest, _ = self.fixture(middle, POOL + ['.Lsize:', '.word 0x108']).verify()
        self.assertEqual([row['count'] for row in manifest['proof']['compiler_memcpy']['contracts']], [0x108])

    def test_count_must_be_an_exact_bounded_constant(self):
        cases = {
            'variable': (STATE + ['ldrb r2, [r5]', 'bl memcpy'], POOL),
            'zero': (STATE + ['movs r2, #0', 'bl memcpy'], POOL),
            'above the limit': (STATE + ['ldr r2, .Lsize', 'bl memcpy'], POOL + ['.Lsize:', '.word 0x401']),
            'one path': (STATE + ['movs r2, #8', 'cmp r4, #0', 'beq .Lcall', 'movs r2, #4', '.Lcall:',
                                  'bl memcpy'], POOL),
        }
        for name, (middle, pool) in cases.items():
            with self.subTest(name=name):
                self.refused('exact constant from 1 to 1024 on every path', middle, pool)

    def test_source_that_names_memcpy_refused(self):
        for call in ('memcpy(a, b, 204)', '__builtin_memcpy(a, b, 204)'):
            with self.subTest(call=call), \
                    self.assertRaisesRegex(ValueError, 'compiler-emitted, not named in the source'):
                self.fixture(preprocessed='void f(char *a, char *b) { ' + call + '; }')
        # Comments and strings are not source names.
        self.fixture(preprocessed='/* memcpy */ const char *s = "__builtin_memcpy";')

    def test_helper_under_another_name_refused(self):
        middle = COPY + STATE + ['movs r2, #4', f'bl func_{HELPER:08X}']
        with self.assertRaisesRegex(ValueError, 'laundered through another call identity'):
            self.fixture(middle)

    def test_helper_identity_required(self):
        def altered(fixture):
            fixture.rom[HELPER - match.ROM_BASE + 20] ^= 1

        def recounted(fixture):
            next(row for row in fixture.rows if row['rom'] == f'0x{HELPER:08X}')['instrs'] = 48
        self.refused('canonical copy helper differs', change=altered)
        with self.assertRaises(ValueError):
            self.fixture(change=recounted).verify()

    def test_original_runtime_domain_refused(self):
        self.refused('requires the optional-runtime schema', thunk=True, division=True, align=0)

    def test_stack_buffer_still_goes_through_the_frame_proof(self):
        middle = ['mov r0, sp', 'ldr r1, .Lstate', 'ldr r1, [r1]', 'movs r2, #8', 'bl memcpy']
        with self.assertRaises(ValueError):
            self.fixture(middle).verify()

    def test_manifest_tampering_refused(self):
        fixture = self.fixture()
        manifest, _ = fixture.verify()
        for change in ('count', 'helper', 'contract', 'destination', 'name', 'library'):
            altered = copy.deepcopy(manifest)
            record = altered['proof']['compiler_memcpy']
            if change == 'count':
                record['calls'][0]['count'] = 0xC8
            elif change == 'helper':
                record['helper']['body_sha256'] = '0' * 64
            elif change == 'contract':
                record['contracts'][0]['execution_sha256'] = '0' * 64
            elif change == 'destination':
                record['calls'][0]['destination'] = {'unknown': True}
            elif change == 'library':
                record['library_identity']['cc1_flags'] = ['-O2']
            else:
                altered['proof']['calls'] = [[site, f'func_{HELPER:08X}' if name == 'memcpy' else name]
                                             for site, name in altered['proof']['calls']]
            with self.subTest(change=change), self.assertRaises(ValueError):
                fixture.verify(manifest=altered)


class ForwardContractTests(unittest.TestCase):
    def test_contract_agrees_with_the_buffer_summary_and_extends_past_it(self):
        body = helper_body()
        for count in (1, 3, 16, 0xCC):
            with self.subTest(count=count):
                self.assertEqual(copy_calls.forward_contract(body, count), summary.contract(body, count))
        self.assertEqual(copy_calls.forward_contract(body, 0x108)['cases'], 16)
        with self.assertRaises(ValueError):
            summary.contract(body, 0x108)

    def test_backward_destination_writes_refused(self):
        body = helper_body()
        original = summary.run

        def backward(*args, **options):
            case = original(*args, **options)
            case['writes'] = list(reversed(case['writes']))
            return case
        with patch.object(summary, 'run', backward), \
                self.assertRaisesRegex(ValueError, 'does not write the destination forward'):
            copy_calls.forward_contract(body, 16)

    def test_incomplete_destination_refused(self):
        body = helper_body()
        original = summary.run

        def short(*args, **options):
            case = original(*args, **options)
            last = max(i for i, row in enumerate(case['writes']) if row[0] == 'destination')
            case['writes'] = case['writes'][:last] + case['writes'][last + 1:]
            return case
        with patch.object(summary, 'run', short), \
                self.assertRaisesRegex(ValueError, 'does not write the whole destination'):
            copy_calls.forward_contract(body, 16)



AGBCC = Path(os.path.expandvars('$HOME/agbcc'))


@unittest.skipUnless((AGBCC / copy_calls.LIBRARY_MEMCPY['source']).is_file() and
                     Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_OBJCOPY),
                     'the agbcc tree with its libc sources is required; verification itself checks only the '
                     'pinned body digest, and only this test recompiles the library memcpy')
class ToolchainMemcpyTests(unittest.TestCase):
    """The ROM helper is the toolchain's own library memcpy, recompiled from its source."""

    def compile(self, tree=AGBCC):
        with tempfile.TemporaryDirectory(prefix='toolchain_memcpy_') as scratch:
            return copy_calls.toolchain_memcpy(tree, os.path.expandvars(match.DEFAULT_CC), match.DEFAULT_CPP,
                                               match.DEFAULT_AS, match.DEFAULT_OBJCOPY, scratch)

    def test_rom_helper_is_the_toolchain_newlib_memcpy(self):
        text = self.compile()
        record = copy_calls.LIBRARY_MEMCPY
        self.assertEqual(len(text), record['body_bytes'] + 2)
        self.assertEqual(hashlib.sha256(text[:98]).hexdigest(), record['body_sha256'])
        self.assertEqual(record['body_sha256'], COPY_SHA256)
        # The object's fill after the code is the assembler's, not the ROM's padding, and is not compared.
        self.assertEqual(text[98:].hex(), record['object_fill'])
        self.assertEqual(text[:98], helper_body())
        rom = base.runtime_rom(((HELPER, HELPER + 100, None),))
        self.assertEqual(bytes(rom[HELPER - match.ROM_BASE + 98:HELPER - match.ROM_BASE + 100]), b'\0\0')

    def test_a_different_library_source_refused(self):
        with tempfile.TemporaryDirectory(prefix='toolchain_tree_') as tree:
            source = Path(tree) / copy_calls.LIBRARY_MEMCPY['source']
            source.parent.mkdir(parents=True)
            source.write_bytes((AGBCC / copy_calls.LIBRARY_MEMCPY['source']).read_bytes() + b'\n')
            with self.assertRaisesRegex(ValueError, 'library memcpy source differs'):
                self.compile(Path(tree))


if __name__ == '__main__':
    unittest.main()
