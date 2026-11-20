"""Orphan prerequisite: compiler _call_via_rN calls and one trailing alignment halfword.

agbcc -O1 objects carry orphan .rodata, so library-unit functions pass the
compiler-orphan prerequisite.  These tests compile the two shapes from kit
issue #214 (a call through a function pointer, and a function whose size is
2 mod 4) and mutate the original ELF and the ROM around each admission.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import compiler_orphan_constants_prerequisite as orphan
import library_units as units

A, B, C = 0x08001000, 0x08001100, 0x08001200
IDENTITY = 0x08003000
FLAGS = '-mthumb-interwork -O1'
SYMBOLS = {'data_03001000': 0x03001000, 'data_03001004': 0x03001004}
OBJECTS = json.dumps({name: f'0x{value:08X}' for name, value in SYMBOLS.items()}).encode()
THUNK_R1 = match.RUNTIME_HELPERS['_call_via_r1']
ROM_SIZE = max(match.RUNTIME_HELPERS.values()) + 4 - match.ROM_BASE
# a call through a function pointer: bl _call_via_r1, and an orphan .rodata
THUNK = '''extern unsigned char (*data_03001000)(unsigned char *address);
extern void func_08001100(void);

unsigned short func_{address:08X}(unsigned char *address, unsigned char last)
{{
    func_08001100();
    while (data_03001000(address) != last)
        ;
    return 0;
}}
'''
# 0x08141E30's shape: two calls through the same pointer, bl _call_via_r1 twice
TWO_CALLS = '''extern unsigned char (*data_03001000)(unsigned char *address);
extern unsigned char data_03001004;
extern void func_08001100(void);

unsigned short func_{address:08X}(unsigned char phase, unsigned char *address, unsigned char last)
{{
    unsigned short result = 0;

    func_08001100();
    while (data_03001000(address) != last) {{
        if (data_03001004) {{
            if (data_03001000(address) == last)
                break;
            result = phase | 0xC000u;
            break;
        }}
    }}
    return result;
}}
'''
# 58 bytes, so `as` pads .text to 60 with c046
FILL = '''extern unsigned char data_03001000;
extern unsigned short *data_03001004;
extern void func_08001100(void);

unsigned short func_{address:08X}(unsigned char number, void (**handler)(void))
{{
    if (number >= 4)
        return 1;
    data_03001000 = number;
    data_03001004 = (unsigned short *)(0x04000100 + data_03001000 * 4);
    *handler = func_08001100;
    return 0;
}}
'''
HAVE_COMPILER = Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which('arm-none-eabi-ld')


def compile_original(root, address, source):
    (root / 'src').mkdir(exist_ok=True)
    (root / 'include').mkdir(exist_ok=True)
    (root / 'src' / f'{address:08X}.c').write_text(source.format(address=address))
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=FLAGS)
    runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root)
    with runner.workspace() as workspace:
        original, _, image = match.compile_object(runner, workspace, args, root, address,
                                                  f'src/{address:08X}.c')
        preprocessed = runner.read_binary(workspace + '/f.i')
    return original, image, preprocessed


def bl(site, target):
    offset = target - (site + 4)
    return struct.pack('<HH', 0xF000 | (offset >> 12) & 0x7FF, 0xF800 | (offset >> 1) & 0x7FF)


def blx(site, target):
    """The BLX form (an ARMv5 instruction) of a call from site to a word-aligned target."""
    offset = target - ((site + 4) & ~3)
    return struct.pack('<HH', 0xF000 | (offset >> 12) & 0x7FF, 0xE800 | (offset >> 1) & 0x7FE)


def text_relocations(image):
    rows = []
    for index in image['relocations']:
        section = image['sections'][index]
        if section[7] != image['text_index']:
            continue
        symbols = image['symbol_tables'][section[6]]
        for site, info in struct.iter_unpack('<II', image['section_data'][index]):
            rows.append((site, info & 255, symbols[info >> 8]['name']))
    return rows


def rom_body(image, address):
    """The function as the ROM holds it: relocations resolved, no alignment fill."""
    function, _ = match.function_record(image, f'func_{address:08X}', address, True)
    body = bytearray(image['text'][:function['size']])
    targets = dict(SYMBOLS, func_08001100=B | 1, **match.RUNTIME_HELPERS)
    for site, kind, name in text_relocations(image):
        if kind == 10:
            body[site:site + 4] = bl(address + site, targets[name] & ~1)
        else:
            struct.pack_into('<I', body, site, targets[name] + struct.unpack_from('<I', body, site)[0])
    return bytes(body)


def base_rom():
    rom = bytearray(ROM_SIZE)
    rom[B - match.ROM_BASE:B - match.ROM_BASE + 2] = b'\x70\x47'
    for name, address in match.RUNTIME_HELPERS.items():
        register = int(name[len('_call_via_r'):])
        struct.pack_into('<HH', rom, address - match.ROM_BASE, 0x4700 | register << 3, 0x46C0)
    return rom


def renamed(original, image, old, new):
    """The original ELF with one string-table name replaced by another of the same length."""
    assert len(old) == len(new)
    table = next(iter(image['symbol_tables']))
    strings = image['sections'][image['sections'][table][6]]
    data = image['section_data'][image['sections'][table][6]]
    position = data.index(b'\0' + old.encode() + b'\0') + 1
    raw = bytearray(original)
    raw[strings[4] + position:strings[4] + position + len(new)] = new.encode()
    return bytes(raw)


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class CallThunkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.original, cls.image, cls.preprocessed = compile_original(Path(cls.temporary.name), A, THUNK)
        calls = [site for site, kind, name in text_relocations(cls.image) if name == '_call_via_r1']
        assert len(calls) == 1 and cls.image['section_names'].count('.rodata') == 1
        cls.site = calls[0]
        rom = base_rom()
        body = rom_body(cls.image, A)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        cls.rom = bytes(rom)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def verify(self, **changes):
        values = dict(original_elf=self.original, address=A, objects=OBJECTS,
                      preprocessed_source=self.preprocessed, selector=orphan.SELECTOR, rom=self.rom)
        values.update(changes)
        return orphan.verify(**values)

    def rom_with(self, address, raw):
        rom = bytearray(self.rom)
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
        return bytes(rom)

    def refused(self, message, **changes):
        with self.assertRaisesRegex(ValueError, message):
            self.verify(**changes)

    def test_thunk_call_is_bound_to_its_rom_thunk(self):
        proof = self.verify()
        self.assertEqual(proof['call_thunks'], dict(
            calls=[dict(offset=self.site, symbol='_call_via_r1', thunk=THUNK_R1)],
            rom_sha256=orphan.sha(self.rom)))
        self.assertEqual(proof['complete_text_bytes'], len(self.image['text']))
        self.assertNotIn('alignment_fill', proof)
        self.assertEqual(self.verify(manifest=proof), proof)
        changed = self.rom_with(match.ROM_BASE, b'\1')
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            self.verify(rom=changed, manifest=proof)

    def test_rom_thunk_for_another_register_is_refused(self):
        for register in (3, 9):
            with self.subTest(register=register):
                self.refused('orphan call thunk differs',
                             rom=self.rom_with(THUNK_R1, struct.pack('<H', 0x4700 | register << 3)))

    def test_call_site_reaching_another_thunk_is_refused(self):
        other = match.RUNTIME_HELPERS['_call_via_r3']
        self.refused('orphan call thunk differs', rom=self.rom_with(A + self.site, bl(A + self.site, other)))

    def test_thunk_name_without_a_rom_thunk_is_refused(self):
        self.refused('orphan call thunk differs', rom=self.rom_with(THUNK_R1, bytes(4)))
        self.refused('orphan call thunk differs', rom=self.rom[:A + self.site + 2 - match.ROM_BASE])
        self.refused('require the immutable ROM', rom=None)
        self.refused('require the immutable ROM', rom=bytearray(self.rom))

    def test_call_site_that_is_not_a_bl_to_the_thunk_is_refused(self):
        exchange = blx(A + self.site, THUNK_R1)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        item = next(decoder.disasm(exchange, A + self.site, count=1))
        self.assertEqual((item.mnemonic, item.operands[0].imm), ('blx', THUNK_R1))
        for raw in (bl(A + self.site, B), bl(A + self.site, THUNK_R1 + 2), bytes(4), exchange):
            with self.subTest(raw=raw.hex()):
                self.refused('orphan call thunk differs', rom=self.rom_with(A + self.site, raw))

    def test_high_register_thunk_is_bound_by_its_full_register(self):
        # agbcc emits _call_via_r8 and _call_via_r9 too; r9 must be checked as r9, not r9 & 7
        r9 = match.RUNTIME_HELPERS['_call_via_r9']
        original = renamed(self.original, self.image, '_call_via_r1', '_call_via_r9')
        rom = self.rom_with(A + self.site, bl(A + self.site, r9))
        proof = self.verify(original_elf=original, rom=rom)
        self.assertEqual(proof['call_thunks']['calls'], [dict(offset=self.site, symbol='_call_via_r9', thunk=r9)])
        rom = bytearray(rom)
        struct.pack_into('<H', rom, r9 - match.ROM_BASE, 0x4708)  # bx r1 in r9's slot
        self.refused('orphan call thunk differs', original_elf=original, rom=bytes(rom))

    def test_named_thunk_must_be_the_one_the_rom_reaches(self):
        self.refused('orphan call thunk differs',
                     original_elf=renamed(self.original, self.image, '_call_via_r1', '_call_via_r9'))

    def test_other_call_names_keep_the_identity_refusal(self):
        for name in ('_call_via_lr', '_call_via_rx', 'xcall_via_r1', '_call_via_1r'):
            with self.subTest(name=name):
                self.refused('unsupported orphan prerequisite call identity',
                             original_elf=renamed(self.original, self.image, '_call_via_r1', name))


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class TwoCallThunkTests(unittest.TestCase):
    """Every thunk call is bound, not only the first."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.original, cls.image, cls.preprocessed = compile_original(Path(cls.temporary.name), A, TWO_CALLS)
        cls.sites = [site for site, kind, name in text_relocations(cls.image) if name == '_call_via_r1']
        assert len(cls.sites) == 2 and cls.image['section_names'].count('.rodata') == 1
        rom = base_rom()
        body = rom_body(cls.image, A)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        cls.rom = bytes(rom)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def verify(self, rom):
        return orphan.verify(self.original, A, OBJECTS, self.preprocessed, selector=orphan.SELECTOR, rom=rom)

    def test_both_calls_are_recorded(self):
        self.assertEqual(self.verify(self.rom)['call_thunks']['calls'],
                         [dict(offset=site, symbol='_call_via_r1', thunk=THUNK_R1) for site in self.sites])

    def test_either_call_site_reaching_another_thunk_is_refused(self):
        other = match.RUNTIME_HELPERS['_call_via_r3']
        for site in self.sites:
            rom = bytearray(self.rom)
            rom[A + site - match.ROM_BASE:A + site + 4 - match.ROM_BASE] = bl(A + site, other)
            with self.subTest(site=site), self.assertRaisesRegex(ValueError, 'orphan call thunk differs'):
                self.verify(bytes(rom))


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class AlignmentFillTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.original, cls.image, cls.preprocessed = compile_original(Path(cls.temporary.name), A, FILL)
        function, _ = match.function_record(cls.image, 'func_08001000', A, True)
        cls.size = function['size']
        assert cls.size % 4 == 2 and cls.image['text'][cls.size:] == orphan.ALIGNMENT_FILL
        cls.text_offset = cls.image['sections'][cls.image['text_index']][4]
        rom = base_rom()
        body = rom_body(cls.image, A)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
        cls.rom = bytes(rom)
        cls.spans = [(A, A + cls.size), (B, B + 2)]
        cls.mapping, cls.index = cls.indices(cls.spans)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @staticmethod
    def indices(spans):
        rows = [dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb', instrs=(end - start) // 2)
                for start, end in spans]
        index = ''.join(f'{start:08X} {end:08X} {end - start} {(end - start) // 2} bx\n' for start, end in spans)
        return json.dumps(rows).encode(), index.encode()

    def verify(self, **changes):
        values = dict(original_elf=self.original, address=A, objects=OBJECTS,
                      preprocessed_source=self.preprocessed, selector=orphan.SELECTOR,
                      mapping=self.mapping, index=self.index, rom=self.rom)
        values.update(changes)
        return orphan.verify(**values)

    def refused(self, message, **changes):
        with self.assertRaisesRegex(ValueError, message):
            self.verify(**changes)

    def patched(self, *edits):
        raw = bytearray(self.original)
        for offset, value in edits:
            raw[offset:offset + len(value)] = value
        return bytes(raw)

    def text_size(self, size):
        """An edit of the .text section header's sh_size."""
        headers = struct.unpack_from('<I', self.original, 32)[0]
        return headers + 40 * self.image['text_index'] + 20, struct.pack('<I', size)

    def test_one_fill_halfword_is_not_function_bytes(self):
        proof = self.verify()
        self.assertEqual(proof['complete_text_bytes'], self.size)
        self.assertEqual(proof['alignment_fill'], dict(offset=self.size, hex='c046'))
        self.assertNotIn('call_thunks', proof)
        owner = [span for span in proof['function_addresses']['spans'] if span['address'] == A]
        self.assertEqual(owner[0]['end'], A + self.size)
        self.assertEqual(proof['input_pins']['text_sha256'], orphan.sha(self.image['text']))
        self.assertEqual(self.verify(manifest=proof), proof)
        # the ROM after the indexed span is not compared
        rom = bytearray(self.rom)
        rom[A + self.size - match.ROM_BASE:A + self.size + 2 - match.ROM_BASE] = b'\xff\xff'
        other = self.verify(rom=bytes(rom))
        other['function_addresses']['rom_sha256'] = proof['function_addresses']['rom_sha256']
        self.assertEqual(other, proof)

    def test_fill_other_than_the_assembler_nop_is_refused(self):
        for fill in (b'\0\0', b'\x70\x47', b'\x00\x46', b'\xc0\x47'):
            with self.subTest(fill=fill.hex()):
                self.refused('sole complete sized Thumb function',
                             original_elf=self.patched((self.text_offset + self.size, fill)))

    def test_two_trailing_halfwords_are_refused(self):
        self.refused('sole complete sized Thumb function', original_elf=self.patched(
            self.text_size(self.size + 4), (self.text_offset + self.size + 2, orphan.ALIGNMENT_FILL)))

    def test_fill_after_a_word_sized_function_is_refused(self):
        symbol = next(number for number, row in enumerate(self.image['symbol_tables'][
            next(iter(self.image['symbol_tables']))]) if row['name'] == 'func_08001000')
        table = self.image['sections'][next(iter(self.image['symbol_tables']))][4]
        self.refused('sole complete sized Thumb function', original_elf=self.patched(
            (table + 16 * symbol + 8, struct.pack('<I', self.size - 2)),
            self.text_size(self.size),
            (self.text_offset + self.size - 2, orphan.ALIGNMENT_FILL)))

    def test_branch_into_the_fill_is_refused(self):
        sites = [offset for offset in range(0, self.size, 2)
                 if struct.unpack_from('<H', self.image['text'], offset)[0] >> 11 == 0x1C]
        self.assertEqual(len(sites), 1)
        branch = 0xE000 | (self.size - sites[0] - 4) >> 1
        self.refused('orphan inventory CFG leaves complete function',
                     original_elf=self.patched((self.text_offset + sites[0], struct.pack('<H', branch))))

    def test_relocation_on_the_fill_is_refused(self):
        section = next(self.image['sections'][index] for index in self.image['relocations']
                       if self.image['sections'][index][7] == self.image['text_index'])
        sites = [site for site, kind, name in text_relocations(self.image)]
        last = section[4] + 8 * sites.index(max(sites))
        self.refused('unsupported partial or overlapping orphan relocation',
                     original_elf=self.patched((last, struct.pack('<I', self.size - 2))))

    def test_literal_load_reaching_the_fill_is_refused(self):
        loads = [offset for offset in range(0, self.size, 2)
                 if struct.unpack_from('<H', self.image['text'], offset)[0] >> 11 == 0x09]
        site = loads[-1]
        register = struct.unpack_from('<H', self.image['text'], site)[0] & 0x0700
        word = (self.size - 2 - ((site + 4) & ~3)) >> 2
        self.refused('complete aligned in-function literal', original_elf=self.patched(
            (self.text_offset + site, struct.pack('<H', 0x4800 | register | word))))

    def test_owner_index_span_past_the_symbol_is_refused(self):
        mapping, index = self.indices([(A, A + self.size + 2), (B, B + 2)])
        self.refused('complete aligned owner/target span', mapping=mapping, index=index)

    def test_named_data_through_a_rom_mirror_of_the_owner_is_refused(self):
        # 0x0A000000-0x0DFFFFFF maps the same ROM as 0x08000000 (#377): an addend that
        # carries named data into a mirror of the owner refers to the owner.
        image, text = self.image, self.image['text_index']
        site = next(struct.unpack_from('<I', image['section_data'][index], position)[0]
                    for index in image['relocations'] if image['sections'][index][7] == text
                    for position in range(0, image['sections'][index][5], 8)
                    if image['symbol_tables'][image['sections'][index][6]][struct.unpack_from(
                        '<I', image['section_data'][index], position + 4)[0] >> 8]['name'] == 'data_03001000')
        for target in (A + self.size + 0x02000000, A + 0x04000000):
            addend = struct.pack('<I', target - SYMBOLS['data_03001000'])
            with self.subTest(target=hex(target)):
                self.refused('refers to owner', original_elf=self.patched((self.text_offset + site, addend)))

    def test_data_or_function_address_at_the_fill_is_refused(self):
        fill = A + self.size
        objects = json.dumps({'data_03001000': f'0x{fill:08X}', 'data_03001004': '0x03001004'}).encode()
        self.refused('refers to owner', objects=objects)
        mapping, index = self.indices(self.spans + [(fill, fill + 2)])
        self.refused('orphan function address refers to owner', mapping=mapping, index=index,
                     original_elf=renamed(self.original, self.image, 'func_08001100', f'func_{fill:08X}'))


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class FixedO0SelectorTests(unittest.TestCase):
    """The fixed-O0 selector shares the prerequisite; its own linker still refuses thunk calls."""

    def test_prerequisite_binds_the_thunk_and_the_native_link_refuses_it(self):
        import compiler_orphan_constants_native_profile as native
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'src').mkdir()
            (root / 'include').mkdir()
            (root / 'src/08001000.c').write_text(THUNK.format(address=A))
            runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root)
            with runner.workspace() as workspace:
                original, _, image = match.compile_object(runner, workspace, native.configuration(), root, A,
                                                          'src/08001000.c')
                rom = base_rom()
                body = rom_body(image, A)
                rom[A - match.ROM_BASE:A - match.ROM_BASE + len(body)] = body
                spans = [(A, A + len(body)), (B, B + 2)]
                mapping, index = AlignmentFillTests.indices(spans)
                inventory = orphan.verify(original, A, OBJECTS, runner.read_binary(workspace + '/f.i'),
                                          selector=orphan.SELECTOR, mapping=mapping, index=index, rom=bytes(rom))
                self.assertEqual([row['symbol'] for row in inventory['call_thunks']['calls']], ['_call_via_r1'])
                with self.assertRaisesRegex(ValueError, 'function address requires a canonical addressed function'):
                    native.object_bytes(runner, workspace, native.configuration(), original, A, mapping, bytes(rom),
                                        OBJECTS, selector=native.SELECTOR, index=index)


@unittest.skipUnless(HAVE_COMPILER, 'fixed compiler required')
class UnitToolchainTests(unittest.TestCase):
    """Both shapes end to end through match.py --unit-toolchain agbcc-O1-v1."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.root = root = Path(cls.temporary.name)
        for folder in ('src', 'include', 'config', 'symbols', 'build', 'docs/match'):
            (root / folder).mkdir(parents=True, exist_ok=True)
        rom = base_rom()
        rom[IDENTITY - match.ROM_BASE:IDENTITY - match.ROM_BASE + 13] = b'TESTLIB_V100\0'
        spans = [(B, B + 2)]
        for address, source in ((A, THUNK), (C, FILL)):
            _, image, _ = compile_original(root, address, source)
            body = rom_body(image, address)
            rom[address - match.ROM_BASE:address - match.ROM_BASE + len(body)] = body
            spans.append((address, address + len(body)))
        spans.sort()
        cls.rom = bytes(rom)
        (root / 'baserom.bin').write_bytes(cls.rom)
        (root / 'config/data_symbols.json').write_bytes(OBJECTS)
        (root / 'config/functions.json').write_text(json.dumps(
            [dict(rom=f'0x{start:08X}', end=f'0x{end:08X}', mode='thumb', instrs=(end - start) // 2,
                  kind='return') for start, end in spans]))
        (root / 'symbols/functions.txt').write_text('# test index\n' + ''.join(
            f'{start:08X} {end:08X} {end - start} {(end - start) // 2} return\n' for start, end in spans))
        cls.row = {'name': 'testlib', 'start': f'0x{A:08X}', 'end': f'0x{spans[-1][1]:08X}',
                   'toolchain': 'agbcc-O1-v1',
                   'identity': [{'address': f'0x{IDENTITY:08X}', 'ascii': 'TESTLIB_V100'}],
                   'proof': f'0x{A:08X}', 'evidence': 'synthetic library object for the tests'}
        (root / units.TABLE).write_text(json.dumps({'units': [cls.row]}))
        cls.environment = dict(os.environ, FFTA_ROM=str(root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1')

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def run_match(self, address, write=False):
        command = [sys.executable, str(Path(match.__file__)), '--root', str(self.root), f'0x{address:08X}',
                   '--unit-toolchain', 'agbcc-O1-v1']
        if not write:
            command.append('--no-write')
        return subprocess.run(command, capture_output=True, text=True, env=self.environment, timeout=300)

    def test_thunk_call_matches_and_records_the_thunk(self):
        result = self.run_match(A, write=True)
        self.assertIn('verdict MATCH - byte identical', result.stdout.splitlines(), result.stdout + result.stderr)
        report = (self.root / 'docs/match/08001000.md').read_text()
        inventory = json.loads(units.binding(report)[3])['prerequisite']
        self.assertEqual([row['symbol'] for row in inventory['call_thunks']['calls']], ['_call_via_r1'])
        self.assertEqual(inventory['call_thunks']['calls'][0]['thunk'], THUNK_R1)

    def test_fill_function_matches_without_crediting_the_fill(self):
        result = self.run_match(C, write=True)
        self.assertIn('verdict MATCH - byte identical', result.stdout.splitlines(), result.stdout + result.stderr)
        report = (self.root / 'docs/match/08001200.md').read_text()
        inventory = json.loads(units.binding(report)[3])['prerequisite']
        size = inventory['complete_text_bytes']
        self.assertEqual(inventory['alignment_fill'], dict(offset=size, hex='c046'))
        self.assertIn(f'**MATCH - byte identical** - {size}/{size} bytes', report)
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            self.assertTrue(match_evidence.report_matches(report, str(self.root), C))

    def test_rom_thunk_for_another_register_is_refused(self):
        rom = bytearray(self.rom)
        struct.pack_into('<H', rom, THUNK_R1 - match.ROM_BASE, 0x4718)
        (self.root / 'baserom.bin').write_bytes(bytes(rom))
        try:
            result = self.run_match(A)
        finally:
            (self.root / 'baserom.bin').write_bytes(self.rom)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('orphan call thunk differs from its ROM call site or thunk', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
