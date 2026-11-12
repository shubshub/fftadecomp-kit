"""Synthetic native composition and real compiler transport boundary tests."""
import argparse
import copy
import json
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import small_local_copy_caller_profile as caller
from test_local_shadow_halfword_matrix import fixture as helper_fixture

A, H, S = 0x08000200, 0x08000400, 0x08000801


def fixture(count=8, *, root=A, target=H, source=S):
    env = helper_fixture(root=root, helper=target, source=source)
    frame = (count+3)//4
    words = [0xB500, 0xB080+frame, 0x4904, 0x4668, 0x2200+count,
             0, 0, 0x4669, 0x8808, 0xB000+frame, 0xBC02, 0x4708, 0, 0]
    data = bytearray(struct.pack('<14H', *words))
    delta = target-root-10-4
    struct.pack_into('<HH', data, 10, 0xF000|((delta>>12)&2047), 0xF800|((delta>>1)&2047))
    struct.pack_into('<I', data, 24, source)
    rom = bytearray(env['rom'])
    rom.extend(bytes(max(0, source-match.ROM_BASE+16-len(rom))))
    rom[source-match.ROM_BASE:source-match.ROM_BASE+16] = bytes(range(19, 35))
    rom[root-match.ROM_BASE:root-match.ROM_BASE+len(data)] = data
    rows = json.loads(env['mapping'])
    rows[0].update(end=f'0x{root+len(data):08X}', instrs=11)
    env.update(data=bytes(data), rom=bytes(rom), mapping=json.dumps(rows).encode(),
        index=f'{root:08X} {root+len(data):08X} {len(data)} 11 bx\n{target:08X} {target+98:08X} 98 49 bx\n'.encode())
    return env


def prove(env, *, native=False, **changes):
    args = {name: env[name] for name in ('data', 'rom', 'mapping', 'index', 'objects')}
    args.update(address=env['root'], selector=caller.SELECTOR)
    args.update(changes)
    return (caller.verify if native else caller.prerequisite)(**args)


def change_word(env, offset, value):
    data, rom = bytearray(env['data']), bytearray(env['rom'])
    struct.pack_into('<H', data, offset, value)
    rom[env['root']-match.ROM_BASE:env['root']-match.ROM_BASE+len(data)] = data
    return dict(env, data=bytes(data), rom=bytes(rom))


class SmallCallerTests(unittest.TestCase):
    def test_all_exact_counts_local_window_rom_values_and_native_replay(self):
        for count in (2, 4, 8, 10):
            with self.subTest(count=count):
                env = fixture(count)
                result, instructions = prove(env, native=True)
                proof = result['caller']
                frame = ((count+3)//4)*4
                self.assertEqual(proof['local_window_entry_sp'], [-frame-4, -4])
                self.assertEqual(proof['destination_entry_sp_offset'], -frame-4)
                self.assertEqual(proof['source_point'], S)
                self.assertEqual(proof['initialized_bytes_at_copy_return'],
                    [[-frame-4+i, 19+i] for i in range(count)])
                self.assertEqual(len(instructions), 11)
                self.assertTrue(result['native_frame_alias_replay'])
                self.assertFalse(result['suffix_initialization_proved'])
                self.assertFalse(result['source_or_ELF_admission'])
                self.assertFalse(result['physical_access_proved'])
                prove(env, native=True, manifest=json.loads(json.dumps(result)))

    def test_relocated_identities_no_address_whitelist(self):
        proof = prove(fixture(root=0x08001000, target=0x08000600, source=0x08002003))
        self.assertEqual(proof['source_point'], 0x08002003)
        self.assertEqual(proof['target'], 0x08000600)

    def test_count_window_and_saved_word_overlap(self):
        for count in (1, 3, 15, 16, 80):
            with self.subTest(count=count), self.assertRaises(ValueError):
                prove(change_word(fixture(), 8, 0x2200+count))
        # Shrink frame beneath count, or direct destination to saved LR.
        for offset, word in ((2, 0xB081), (6, 0xA802), (2, 0xB002)):
            with self.subTest(offset=offset, word=word), self.assertRaises(ValueError):
                prove(change_word(fixture(), offset, word))

    def test_rom_source_is_complete_named_unique_and_unchanged(self):
        env = fixture()
        for objects in (b'{}', b'{"a":"0x08000801","b":"0x08000801"}',
                        b'{"a":"0x08000801","a":"0x08000803"}'):
            with self.subTest(objects=objects), self.assertRaises(ValueError):
                prove(env, objects=objects)
        for source in (0x03002000, S+15, A, H):
            data = bytearray(env['data']); struct.pack_into('<I', data, 24, source)
            rom = bytearray(env['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
            with self.subTest(source=source), self.assertRaises(ValueError):
                prove(env, data=bytes(data), rom=bytes(rom), objects=json.dumps({'source':f'0x{source:08X}'}).encode())

    def test_exact_manifest_binds_source_values_all_inputs_and_source_files(self):
        env = fixture(); result = prove(env)
        for field in ('producer_sha256', 'input_pins', 'initialized_bytes_at_copy_return', 'conditions'):
            stale = copy.deepcopy(result); stale[field] = {}
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'stale'):
                prove(env, manifest=stale)
        for key in ('rom', 'mapping', 'index', 'objects'):
            changed = dict(env)
            if key == 'rom':
                raw = bytearray(env[key]); raw[S-match.ROM_BASE] ^= 1; changed[key] = bytes(raw)
            else:
                changed[key] = env[key]+b'\n'
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'stale'):
                prove(changed, manifest=result)
        self.assertIn('small_local_copy_caller_profile.py', result['producer_sha256'])

    def test_helper_complete_bytes_counts_and_owner_extent_stay_strict(self):
        env = fixture()
        for offset in (20, 78, 96):
            rom = bytearray(env['rom']); rom[H-match.ROM_BASE+offset] ^= 1
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                prove(env, rom=bytes(rom))
        for old, new in ((b'98 49', b'98 48'), (b'08000462', b'08000460')):
            with self.subTest(old=old), self.assertRaises(ValueError):
                prove(env, index=env['index'].replace(old, new))
        with self.assertRaises(ValueError): prove(env, data=env['data'][:-2])

    def test_prefix_memory_and_saved_alias_escape_refused(self):
        for offset, word in ((6, 0x6008), (4, 0x6809), (2, 0x466C)):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                prove(change_word(fixture(), offset, word))

    def test_suffix_alias_escape_unbalanced_frame_and_wrong_native_arguments(self):
        for offset, word in ((16, 0x6001), (18, 0xB001), (22, 0x4700)):
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                prove(change_word(fixture(), offset, word), native=True)
        env = fixture()
        proof = caller.SmallLocalCopyProof(env['data'], A, env['rom'], env['mapping'], env['index'], env['objects'], selector=caller.SELECTOR)
        stack = [(False, False, True)]*2+[(True, True, False)]
        for aliases, slots, site in (({match.ARM_REG_R0:-8}, {}, A+10),
                                     ({match.ARM_REG_R0:-12}, {-12:-12}, A+10),
                                     ({match.ARM_REG_R0:-12}, {}, A+12)):
            with self.subTest(aliases=aliases, slots=slots, site=site), self.assertRaises(ValueError):
                proof.check_call(H, aliases, stack, slots, site=site)

    def test_explicit_selector_and_immutable_inputs(self):
        env = fixture()
        with self.assertRaises(ValueError): prove(env, selector='named-data-buffer-v1')
        with self.assertRaises(ValueError): prove(env, data=bytearray(env['data']))

    def test_changed_live_producer_bytes_invalidate_manifest(self):
        env = fixture(); result = prove(env)
        read_bytes = Path.read_bytes
        def changed(path):
            raw = read_bytes(path)
            return raw+b'\n' if path.name == 'small_local_copy_caller_profile.py' else raw
        with patch.object(Path, 'read_bytes', changed), self.assertRaisesRegex(ValueError, 'stale'):
            prove(env, manifest=result)

    def test_supplied_concrete_sp_checks_whole_frame_and_no_permissions(self):
        env = fixture()
        args = {name:env[name] for name in ('data','rom','mapping','index','objects')}
        args.update(address=A, selector=caller.SELECTOR)
        result = caller.concrete_domain(**args, entry_sp=0x03007000)
        self.assertEqual(result['complete_frame_range'], [0x03007000-24, 0x03007000])
        self.assertTrue(result['caller_window_authenticated'])
        self.assertFalse(result['actual_entry_sp_proved'])
        self.assertFalse(result['physical_access_proved'])
        for entry_sp in (True, 3, 16, A+24, H+24, S+3):
            with self.subTest(entry_sp=entry_sp), self.assertRaises(ValueError):
                caller.concrete_domain(**args, entry_sp=entry_sp)


class ActualCompilerTests(unittest.TestCase):
    def test_real_agbcc_local_array_call_and_post_copy_load_all_counts(self):
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY,
            linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root/'src').mkdir(); (root/'include').mkdir()
            runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=root)
            with runner.workspace() as workspace:
                for count in (2, 4, 8, 10):
                    with self.subTest(count=count):
                        source = ('extern unsigned char source_bytes[];\n'
                            'extern void *memcpy(void *, const void *, unsigned int);\n'
                            'unsigned int func_08000200(void) {\n'
                            f'unsigned char bytes[{count}];\n'
                            f'memcpy(bytes, source_bytes, {count});\n'
                            'return bytes[0];\n}\n')
                        (root/'src/08000200.c').write_text(source)
                        _, body, image = match.compile_object(runner, workspace, args, root, A, 'src/08000200.c')
                        data = bytearray(body)
                        for section_id in image['relocations']:
                            section = image['sections'][section_id]
                            symbols = image['symbol_tables'][section[6]]
                            raw = image['section_data'][section_id]
                            for position in range(0, len(raw), 8):
                                site, info = struct.unpack_from('<II', raw, position)
                                name = symbols[info>>8]['name']
                                if info&255 == 10:
                                    self.assertEqual(name, 'memcpy')
                                    delta = H-A-site-4
                                    struct.pack_into('<HH', data, site, 0xF000|((delta>>12)&2047), 0xF800|((delta>>1)&2047))
                                elif info&255 == 2:
                                    self.assertEqual(name, 'source_bytes'); struct.pack_into('<I', data, site, S)
                                else:
                                    self.fail(f'unexpected relocation {info&255}')
                        env = fixture(count)
                        rom = bytearray(env['rom']); rom[A-match.ROM_BASE:A-match.ROM_BASE+len(data)] = data
                        rows = json.loads(env['mapping']); rows[0].update(end=f'0x{A+len(data):08X}', instrs=0)
                        env.update(data=bytes(data), rom=bytes(rom), mapping=json.dumps(rows).encode(),
                            index=f'{A:08X} {A+len(data):08X} {len(data)} 0 bx\n{H:08X} {H+98:08X} 98 49 bx\n'.encode())
                        result, _ = prove(env, native=True)
                        self.assertEqual(result['caller']['count'], count)
                        self.assertEqual(result['caller']['helper_effects']['destination_bytes'], list(range(19,19+count)))
                        self.assertFalse(result['source_or_ELF_admission'])


if __name__ == '__main__':
    unittest.main()
