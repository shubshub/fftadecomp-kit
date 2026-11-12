import json
from pathlib import Path
import struct
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import compiler_copy80_caller_prerequisite as caller
from test_local_shadow_halfword_matrix import fixture as helper_fixture


def fixture(root=0x08000200, helper=0x08000400, source=0x03002000, branch_delta=None):
    env = helper_fixture(root=root, helper=helper, source=source)
    if branch_delta is None:
        words = [0xB570, 0xB083, 0x1C16, 0x4C05, 0x1C30, 0x3064, 0x1C21,
                 0x2250, 0, 0, 0xB003, 0xBC70, 0xBC02, 0x4708, 0, 0]
        site, count = 16, 13
    else:
        words = [0xB570, 0xB083, 0x1C16, 0x4C07, 0x1C30, 0x3064, 0x1C21,
                 0x2250, 0x2B00, 0xD001, 0x3000+branch_delta, 0xE7FF,
                 0, 0, 0xB003, 0xBC70, 0xBC02, 0x4708, 0, 0]
        site, count = 24, 17
    data = bytearray(struct.pack('<'+'H'*len(words), *words))
    delta = helper-(root+site)-4
    struct.pack_into('<HH', data, site, 0xF000 | ((delta >> 12) & 2047), 0xF800 | ((delta >> 1) & 2047))
    struct.pack_into('<I', data, len(data)-4, source)
    rom = bytearray(env['rom'])
    rom[root-0x08000000:root-0x08000000+len(data)] = data
    rows = json.loads(env['mapping'])
    rows[0].update(end=f'0x{root+len(data):08X}', instrs=count)
    env.update(data=bytes(data), rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=f'{root:08X} {root+len(data):08X} {len(data)} {count} bx\n{helper:08X} {helper+98:08X} 98 49 bx\n'.encode())
    return env


def verify(env):
    return caller.verify(*(env[key] for key in ('data', 'root', 'rom', 'mapping', 'index', 'objects')))


def change_word(env, offset, value):
    data, rom = bytearray(env['data']), bytearray(env['rom'])
    struct.pack_into('<H', data, offset, value)
    rom[env['root']-0x08000000:env['root']-0x08000000+len(data)] = data
    return dict(env, data=bytes(data), rom=bytes(rom))


class CallerTests(unittest.TestCase):
    def test_actual_inputs_and_frame_derived(self):
        env = fixture()
        proof = verify(env)
        self.assertEqual(proof['destination'], dict(entry_register=2, offset=100))
        self.assertEqual(proof['count'], 80)
        self.assertEqual(proof['source_point'], env['source'])
        self.assertEqual(proof['call_site'], env['root']+16)
        self.assertEqual(proof['caller_frame_bytes'], 28)
        self.assertEqual(proof['combined_frame_bytes'], 40)
        self.assertFalse(proof['complete_caller_admission'])
        self.assertFalse(proof['source_or_ELF_admission'])
        self.assertFalse(proof['physical_access_proved'])

    def test_relocated_owner_helper_and_data(self):
        proof = verify(fixture(root=0x08001000, helper=0x08000800, source=0x02002000))
        self.assertEqual(proof['helper']['helper'], 0x08000800)
        self.assertEqual(proof['source_point'], 0x02002000)

    def test_real_join_accepts_only_agreeing_arguments(self):
        self.assertEqual(verify(fixture(branch_delta=0))['count'], 80)
        with self.assertRaisesRegex(ValueError, 'actual entry_R2'):
            verify(fixture(branch_delta=4))

    def test_count_and_destination_not_guessed(self):
        for offset, value in ((14, 0x224F), (10, 0x3068), (4, 0x1C1E)):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, 'actual entry_R2'):
                verify(change_word(fixture(), offset, value))

    def test_missing_ambiguous_and_unaligned_source(self):
        env = fixture()
        for objects in (b'{}', json.dumps({'first': f'0x{env["source"]:08X}', 'second': f'0x{env["source"]:08X}'}).encode()):
            with self.assertRaises(ValueError):
                verify(dict(env, objects=objects))
        with self.assertRaises(ValueError):
            verify(fixture(source=0x03002002))

    def test_complete_body_must_equal_rom(self):
        env = fixture()
        with self.assertRaises(ValueError):
            verify(dict(env, data=env['data'][:-2]))
        with self.assertRaises(ValueError):
            verify(dict(env, data=bytes([env['data'][0] ^ 1])+env['data'][1:]))

    def test_helper_mutation_refused(self):
        env = fixture()
        rom = bytearray(env['rom'])
        rom[env['helper']-0x08000000+42] ^= 1
        with self.assertRaisesRegex(ValueError, 'canonical copy-helper'):
            verify(dict(env, rom=bytes(rom)))

    def test_saved_frame_cannot_be_deallocated_before_call(self):
        with self.assertRaises(ValueError):
            verify(change_word(fixture(), 2, 0xB005))

    def test_stack_provenance_cannot_be_discarded_by_arithmetic(self):
        for left, right in ((('constant', 4), ('stack', -8)),
                            (('stack', -8), ('entry', 0, 0)),
                            (('stack', -8), None)):
            with self.subTest(left=left, right=right), self.assertRaisesRegex(ValueError, 'stack alias'):
                caller.add(left, right)

    def test_duplicate_named_point_refused(self):
        env = fixture()
        with self.assertRaisesRegex(ValueError, 'duplicate data symbol'):
            verify(dict(env, objects=b'{"point":"0x03002000","point":"0x03002004"}'))


if __name__ == '__main__':
    unittest.main()
