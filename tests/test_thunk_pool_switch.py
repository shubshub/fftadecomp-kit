"""Synthetic bounded canonical-thunk switch CFGs; no game bytes or C credit."""
import copy
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import analyze
import match
import function_thunk_profile as profile
import thunk_pool_switch as pool


class ThunkPoolSwitchTests(unittest.TestCase):
    address = 0x08001000

    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='pool_switch_', dir=scratch)
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)

    def fixture(self, *, address=None, missing_load=False, restore=True, bypass=False, stack_error=""):
        address = self.address if address is None else address
        prefix = 'cmp r1,#0\nbeq dispatch\n' if bypass else ''
        loads = '\n'.join(f'ldr r{index % 4},pool{index}' for index in range(5 - missing_load))
        assembly = f'''.syntax unified
.arch armv4t
.thumb
.text
.global caller
.type caller,%function
.thumb_func
caller:
push {{r4,lr}}
sub sp,#4
{prefix}
{loads}
{stack_error}
bl _call_via_r2
cmp r0,#1
bls dispatch
b default_case
dispatch:
lsls r0,r0,#2
ldr r1,table_pointer
adds r0,r0,r1
ldr r0,[r0]
mov pc,r0
.balign 4,0
pool0:.word 0x11111111
pool1:.word 0x22222222
pool2:.word 0x33333333
pool3:.word 0x44444444
pool4:.word 0x55555555
table_pointer:.word table
table:.word case0,case1
case0:movs r0,#1
b done
case1:movs r0,#2
b done
default_case:movs r0,#0
done:
{'add sp,#4' if restore else ''}
pop {{r4}}
pop {{r1}}
bx r1
.size caller,.-caller
'''
        assembly = assembly.replace('caller', f'func_{address:08X}')
        if address % 4:
            assembly = assembly.replace('.thumb_func\n', '.balign 4,0\n.space 2,0\n.thumb_func\n', 1)
        known_source, known_obj = self.root / 'known.s', self.root / 'known.o'
        known_source.write_text('.syntax unified\n.thumb\n.global _call_via_r2\n'
                                '.type _call_via_r2,%function\n'
                                f'.thumb_set _call_via_r2,0x{profile.ALIASES["_call_via_r2"] | 1:08X}\n')
        source, obj, linked, binary = (self.root / name for name in ('f.s', 'f.o', 'f.elf', 'f.bin'))
        source.write_text(assembly)
        for command in ([match.DEFAULT_AS, '-mthumb-interwork', str(source), '-o', str(obj)],
                        [match.DEFAULT_AS, '-mthumb-interwork', str(known_source), '-o', str(known_obj)],
                        [match.DEFAULT_LD, '--no-undefined', '--no-relax', '-Ttext', hex(address & ~3),
                         '-e', f'func_{address:08X}', str(obj), str(known_obj), '-o', str(linked)],
                        [match.DEFAULT_OBJCOPY, '-O', 'binary', '--only-section=.text', str(linked), str(binary)]):
            subprocess.run(command, check=True, capture_output=True, timeout=30)
        self.original = match.elf_image(obj.read_bytes())
        image = match.elf_image(linked.read_bytes())
        symbols = {item['name']: item['value'] & ~1 for item in image['symbols']}
        size = next(item['size'] for item in image['symbols'] if item['name'] == f'func_{address:08X}')
        self.body = binary.read_bytes()[address % 4:address % 4 + size]
        self.address = address
        self.offsets = {name: value - address for name, value in symbols.items() if address <= value < address + len(self.body)}
        self.relocations = {self.offsets['table_pointer']: self.offsets['table'],
                            self.offsets['table']: self.offsets['case0'],
                            self.offsets['table'] + 4: self.offsets['case1']}
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        self.calls = {item.address: profile.ALIASES['_call_via_r2']
                      for item in decoder.disasm(self.body, address) if item.id == match.ARM_INS_BL}
        rom = bytearray(profile.END - match.ROM_BASE)
        struct.pack_into('<HH', rom, profile.ALIASES['_call_via_r2'] - match.ROM_BASE, 0x4710, 0x46C0)
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(self.body)] = self.body
        self.rom = bytes(rom)
        self.mapping = json.dumps([{'rom': f'0x{address:08X}',
                                   'end': f'0x{address + len(self.body):08X}', 'mode': 'thumb'},
                                  {'rom': f'0x{profile.ALIASES["_call_via_r2"]:08X}',
                                   'end': f'0x{profile.ALIASES["_call_via_r2"] + 4:08X}', 'mode': 'thumb'}]).encode()
        self.index = f'{address:08X} {address + len(self.body):08X} {len(self.body)}\n'.encode()
        return self.body

    def leaf(self, data=None):
        return match.verify_leaf_instructions(self.body if data is None else data,
                self.address, True, self.calls, function_thunk_context={'pool_switch': self.relocations})

    def manifest(self):
        return profile.make_manifest(self.calls, {}, {}, self.address, self.rom, None,
                                     self.leaf(), pool_switch=self.relocations)

    def verify(self, manifest, *, rom=None, mapping=None):
        return profile.verify(self.body, self.address, self.rom if rom is None else rom,
                self.mapping if mapping is None else mapping, self.index, None, manifest)

    def test_complete_cfg_abi_and_manifest_at_both_thumb_alignments(self):
        for address in (0x08001000, 0x08001002):
            with self.subTest(address=address):
                self.fixture(address=address)
                instructions = self.leaf()
                self.assertEqual(len(self.verify(self.manifest())), len(instructions))
                refined = analyze.refine_function(self.body, address, json.loads(self.mapping))
                self.assertTrue(refined['cfg_closed'], refined)
                self.assertEqual(refined['instrs'], len(instructions))
                self.assertEqual(refined['word_switches'][0]['interposed_words'], 5)

    def test_default_profiles_remain_conservative_and_local_words_need_opt_in(self):
        self.fixture()
        self.assertEqual(len(match.verify_leaf_instructions(self.body, self.address, True,
                         self.calls, function_thunk_context={})), len(self.leaf()))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(self.body, self.address, True, self.calls)
        switches = {}
        calls, functions, literals = profile.original_bindings(
            self.original, self.address, self.mapping, self.rom, None,
            switch_relocations=switches)
        self.assertEqual((calls, functions, literals), (self.calls, {}, {}))
        self.assertEqual(switches, self.relocations)
        with self.assertRaises(ValueError):
            match.call_bindings(self.original, f'func_{self.address:08X}', self.address,
                                self.mapping, len(self.rom), self.rom, None, {})
        manifest = self.manifest()
        self.assertEqual(profile.make_manifest(self.calls, {}, {}, self.address, self.rom, None,
                                               self.leaf()), manifest)
        del manifest['pool_switch']
        with self.assertRaises(ValueError):
            self.verify(manifest)

    def test_all_five_words_require_reached_loads(self):
        self.fixture(missing_load=True)
        with self.assertRaisesRegex(ValueError, 'every interposed pool word'):
            self.leaf()
        result = analyze.refine_function(self.body, self.address, json.loads(self.mapping))
        self.assertFalse(result['cfg_closed'], result)

    def test_guard_bypass_and_unbalanced_frame_remain_rejected(self):
        for options in ({'bypass': True}, {'restore': False}):
            with self.subTest(options=options):
                self.fixture(**options)
                with self.assertRaises(ValueError):
                    self.leaf()

    def test_stack_alias_escape_and_out_of_frame_write_remain_rejected(self):
        for operation in ('add r0,sp,#0', 'str r0,[sp,#12]'):
            with self.subTest(operation=operation):
                self.fixture(stack_error=operation)
                with self.assertRaises(ValueError):
                    self.leaf()

    def test_signed_guard_and_wrong_bound_are_rejected(self):
        self.fixture()
        descriptor = pool.layout(self.body, self.address, self.relocations)
        for offset, word in ((descriptor['comparison'] + 2, 0xDD00),
                             (descriptor['comparison'], 0x2802)):
            data = bytearray(self.body)
            struct.pack_into('<H', data, offset, word)
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                self.leaf(bytes(data))

    def test_odd_outside_pool_and_dispatch_table_targets_are_rejected(self):
        self.fixture()
        descriptor = pool.layout(self.body, self.address, self.relocations)
        for target in (self.address + self.offsets['case0'] + 1,
                       self.address + len(self.body), self.address + self.offsets['pool0'],
                       self.address + descriptor['dispatch']):
            data = bytearray(self.body)
            struct.pack_into('<I', data, self.offsets['table'], target)
            with self.subTest(target=target), self.assertRaises(ValueError):
                self.leaf(bytes(data))

    def test_manifest_body_pool_table_and_dependency_tampering_are_rejected(self):
        self.fixture()
        original = self.manifest()
        for field in ('body_sha256', 'table_sha256', 'pool', 'schema'):
            manifest = copy.deepcopy(original)
            manifest['pool_switch'][field] = 'forged'
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.verify(manifest)
        for value in (True, 1.0):
            manifest = copy.deepcopy(original)
            manifest['pool_switch']['layout']['bound'] = value
            with self.subTest(bound=value), self.assertRaises(ValueError):
                self.verify(manifest)
        rom = bytearray(self.rom)
        rom[profile.ALIASES['_call_via_r2'] - match.ROM_BASE] ^= 1
        with self.assertRaisesRegex(ValueError, 'thunk identity differs'):
            self.verify(original, rom=bytes(rom))
        foreign = json.loads(self.mapping)
        foreign.append({'rom': hex(self.address + self.offsets['table']),
                        'end': hex(self.address + self.offsets['table'] + 4), 'mode': 'thumb'})
        with self.assertRaises(ValueError):
            self.verify(original, mapping=json.dumps(foreign).encode())


if __name__ == '__main__':
    unittest.main()
