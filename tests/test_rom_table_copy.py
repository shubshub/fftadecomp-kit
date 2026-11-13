"""Constant ROM tables copied into private stack objects by the pinned copy helper."""
import copy
import hashlib
import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import rom_table_copy_profile as rtc
from test_nested_known_query import assemble
from test_local_shadow_halfword_matrix import fixture as helper_fixture

OWNER, LEAK, FAKE, TABLE = 0x08010000, 0x08012000, 0x08013000, 0x08020000
HELPER = rtc.HELPER
ROM_SIZE = 0x150000
TABLE_BYTES = bytes(range(0x30, 0x38))

# push {r4,lr}; sub sp,#8; mov r0,sp; ldr r1,[pc,#20]; movs r2,#N; bl HELPER;
# mov r0,sp; ldrb r0,[r0,#1]; lsls r0,r0,#24; add sp,#8; pop {r4}; pop {r1}; bx r1; .word TABLE
def owner_code(count=3, target=HELPER, tail=(0x4668, 0x7840, 0x0600), frame=0xb082, load=0x4905):
    return [0xb510, frame, 0x4668, load, 0x2200 | count, target, *tail,
            0xb002, 0xbc10, 0xbc02, 0x4708]


def fixture(code=None, *, literal=TABLE, names=None, selector=rtc.SELECTOR, rodata=None,
            patch_rom=None, extra_functions=(), bindings_data=None):
    code = owner_code() if code is None else code
    raw = assemble(OWNER, code)
    raw += b'\0' * (-len(raw) % 4) + struct.pack('<I', literal)
    literal_offset = len(raw) - 4
    rom = bytearray(ROM_SIZE)
    rom[OWNER-match.ROM_BASE:OWNER-match.ROM_BASE+len(raw)] = raw
    helper = helper_fixture()
    rom[HELPER-match.ROM_BASE:HELPER-match.ROM_BASE+98] = helper['rom'][helper['helper']-match.ROM_BASE:
                                                                       helper['helper']-match.ROM_BASE+98]
    rom[TABLE-match.ROM_BASE:TABLE-match.ROM_BASE+8] = TABLE_BYTES
    leak = struct.pack('<2H', 0x6008, 0x4770)          # str r0,[r1]: stores the alias
    rom[LEAK-match.ROM_BASE:LEAK-match.ROM_BASE+4] = leak
    fake = helper['rom'][helper['helper']-match.ROM_BASE:helper['helper']-match.ROM_BASE+98]
    rom[FAKE-match.ROM_BASE:FAKE-match.ROM_BASE+98] = fake  # identical copy at the wrong address
    for address, value in (patch_rom or {}).items():
        rom[address-match.ROM_BASE] = value
    spans = [(OWNER, len(raw), 0), (HELPER, 98, 49), (LEAK, 4, 2), (FAKE, 98, 49), *extra_functions]
    rows = [dict(rom=f'0x{a:08X}', end=f'0x{a+n:08X}', mode='thumb', instrs=c)
            for a, n, c in sorted(spans)]
    mapping = json.dumps(rows).encode()
    row = next(r for r in rows if int(r['rom'], 16) == OWNER)
    row['instrs'] = owner.refine(raw, OWNER, mapping)['instrs']
    mapping = json.dumps(rows).encode()
    _, _, _, calls, _ = graph.graph(raw, OWNER, owner.refine(raw, OWNER, mapping))
    objects = json.dumps({'data_table': f'0x{TABLE:08X}'} if names is None else names).encode()
    data = [[literal_offset, 'data_table', 0]] if rodata is None else []
    return dict(data=raw, address=OWNER, rom=bytes(rom), mapping=mapping,
        index=''.join(f'{int(r["rom"],16):08X} {int(r["end"],16):08X} '
                      f'{int(r["end"],16)-int(r["rom"],16)} {r["instrs"]} return\n' for r in rows).encode(),
        objects=objects,
        bindings=dict(calls=[[site-OWNER, f'func_{target:08X}'] for site, target in sorted(calls.items())],
                      data=data if bindings_data is None else bindings_data, functions=[], switches=[]),
        selector=selector, rodata=rodata), literal_offset


def initializer(literal_offset, rom_bytes=TABLE_BYTES):
    return dict(base=TABLE, size=len(rom_bytes), sha256=hashlib.sha256(rom_bytes).hexdigest(),
                sites=[[literal_offset, 0]])


def evidence(manifest):
    return manifest['proof']['buffers']['rom_table_copies']


class RomTableCopyTests(unittest.TestCase):
    def test_named_table_copy_may_not_run_into_the_next_named_object(self):
        names = {'data_table': f'0x{TABLE:08X}', 'data_next': f'0x{TABLE + 2:08X}'}
        arguments, _ = fixture(names=names)
        with self.assertRaisesRegex(ValueError, 'past the named ROM table'):
            owner.verify(**arguments)
        arguments, _ = fixture(names=dict(names, data_next=f'0x{TABLE + 3:08X}'))
        owner.verify(**arguments)

    def test_named_table_copy_is_admitted(self):
        arguments, _ = fixture()
        manifest, _ = owner.verify(**arguments)
        self.assertEqual(manifest['profile'], rtc.SCHEMA)
        copies = evidence(manifest)['copies']
        self.assertEqual(len(copies), 1)
        self.assertEqual((copies[0]['source'], copies[0]['count'], copies[0]['source_kind']),
                         (TABLE, 3, 'named-rom-table'))
        self.assertEqual(copies[0]['bytes_sha256'], hashlib.sha256(TABLE_BYTES[:3]).hexdigest())
        self.assertEqual(evidence(manifest)['helper']['written_registers'], ['r0', 'r1', 'r2', 'r3', 'r4', 'r5'])
        self.assertFalse(evidence(manifest)['physical_access_proved'])

    def test_object_initializer_is_bound_to_rom_bytes(self):
        arguments, site = fixture(rodata=True)
        arguments['rodata'] = initializer(site)
        manifest, _ = owner.verify(**arguments)
        self.assertEqual(evidence(manifest)['copies'][0]['source_kind'], 'object-initializer')
        self.assertEqual(evidence(manifest)['object_initializer']['base'], TABLE)

    def test_default_walk_still_refuses_the_helper(self):
        arguments, _ = fixture(selector='named-data-buffer-v1')
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC'):
            owner.verify(**arguments)

    def test_wrong_length_refuses(self):
        for count in (0, 16, 80):
            with self.subTest(count=count):
                arguments, _ = fixture(owner_code(count=count))
                with self.assertRaisesRegex(ValueError, 'count an exact constant from 1 to 15'):
                    owner.verify(**arguments)

    def test_non_constant_count_refuses(self):
        # movs r2,#3 replaced by adds r2,r4,#0: the count is not a constant.
        code = owner_code(); code[4] = 0x1c22
        arguments, _ = fixture(code)
        with self.assertRaisesRegex(ValueError, 'count an exact constant'):
            owner.verify(**arguments)

    def test_destination_overflowing_the_frame_refuses(self):
        arguments, _ = fixture(owner_code(count=12))   # 12 bytes into an 8-byte local frame
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**arguments)

    def test_destination_covering_saved_words_refuses(self):
        # Eight local bytes are fine; the copy at count nine reaches the saved R4.
        arguments, _ = fixture(owner_code(count=9))
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            owner.verify(**arguments)
        arguments, _ = fixture(owner_code(count=8))
        owner.verify(**arguments)

    def test_escape_to_unbounded_callee_refuses(self):
        # After the copy the object address is handed to a callee that stores it.
        code = owner_code(tail=(0x4668, LEAK, 0x4668, 0x7840), load=0x4906)
        arguments, _ = fixture(code)
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{LEAK:08X}'):
            owner.verify(**arguments)

    def test_tampered_object_initializer_refuses(self):
        arguments, site = fixture(rodata=True)
        arguments['rodata'] = initializer(site)
        tampered = bytearray(arguments['rom'])
        tampered[TABLE-match.ROM_BASE+1] ^= 1
        arguments['rom'] = bytes(tampered)
        with self.assertRaisesRegex(ValueError, 'ROM table bytes differ from the compiler initialiser bytes'):
            owner.verify(**arguments)

    def test_tampered_initializer_binding_refuses(self):
        arguments, site = fixture(rodata=True)
        for key, value in (('base', TABLE + 4), ('size', 4), ('sha256', '0' * 64), ('sites', [[site, 1]])):
            with self.subTest(key=key):
                binding = initializer(site)
                binding[key] = value
                arguments['rodata'] = binding
                with self.assertRaises(ValueError):
                    owner.verify(**arguments)

    def test_tampered_table_byte_makes_the_manifest_stale(self):
        arguments, _ = fixture()
        manifest, _ = owner.verify(**arguments)
        tampered = bytearray(arguments['rom'])
        tampered[TABLE-match.ROM_BASE+1] ^= 1
        with self.assertRaisesRegex(ValueError, 'stale|differ|mismatch|expected'):
            owner.verify(**dict(arguments, rom=bytes(tampered)), manifest=copy.deepcopy(manifest))

    def test_unnamed_source_refuses(self):
        arguments, _ = fixture(names={})
        with self.assertRaises(ValueError):
            owner.verify(**arguments)
        arguments, _ = fixture(literal=TABLE + 1, names={'data_table': f'0x{TABLE + 1:08X}'})
        owner.verify(**arguments)          # a different named point is admitted ...
        arguments, _ = fixture(literal=TABLE + 1, names={'data_table': f'0x{TABLE:08X}'})
        with self.assertRaises(ValueError):  # ... an unnamed one is not
            owner.verify(**arguments)

    def test_source_outside_rom_refuses(self):
        for literal in (0x02000000, 0x09000000):
            with self.subTest(literal=hex(literal)):
                arguments, _ = fixture(literal=literal, names={'data_table': f'0x{literal:08X}'})
                with self.assertRaises(ValueError):
                    owner.verify(**arguments)

    def test_non_memcpy_callee_is_not_summarized(self):
        # An identical routine at another address is walked by the ordinary rules, which refuse it.
        arguments, _ = fixture(owner_code(target=FAKE))
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{FAKE:08X}'):
            owner.verify(**arguments)

    def test_tampered_helper_refuses(self):
        arguments, _ = fixture(patch_rom={HELPER + 0x40: 0x00})
        with self.assertRaisesRegex(ValueError, 'helper|instruction|differs'):
            owner.verify(**arguments)

    def test_helper_writing_a_high_register_refuses(self):
        # Replace the final `adds r0,r5,#0` (offset 90) by `adds r6,r5,#0`: no longer the canonical helper.
        arguments, _ = fixture(patch_rom={HELPER + 90: 0x2e})
        with self.assertRaises(ValueError):
            owner.verify(**arguments)

    def test_calls_must_name_the_helper_for_memcpy_renaming(self):
        calls = [[10, 'func_08012000']]
        with self.assertRaisesRegex(ValueError, 'pinned copy helper'):
            rtc.name_calls(calls, dict(calls=[[10, 'memcpy']]))
        self.assertEqual(rtc.name_calls([[10, f'func_{HELPER:08X}']], dict(calls=[[10, 'memcpy']])),
                         [[10, 'memcpy']])


if __name__ == '__main__':
    unittest.main()
