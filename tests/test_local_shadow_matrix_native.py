"""New native integration checks; prior matrix and identity suites stay saved."""
import argparse
import copy
import io
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from test_local_shadow_halfword_matrix import fixture
from test_local_shadow_matrix_elf_binding import original_elf
import local_shadow_matrix_native_profile as native
import local_shadow_matrix_elf_binding as binding
import match
import owner_admission_profile as owner


def bindings(env, raw=None, selector=native.SELECTOR):
    return owner.original_bindings(match.elf_image(original_elf(env) if raw is None else raw),
        env['root'], env['rom'], env['mapping'], env['objects'], selector=selector, index=env['index'])


def prove(env, manifest=None, fingerprint='a'*64, selector=native.SELECTOR, given=None):
    typed = bindings(env)[0] if given is None else given
    return owner.verify(env['data'], env['root'], env['rom'], env['mapping'], env['index'],
        env['objects'], manifest, bindings=typed, selector=selector, source_fingerprint=fingerprint)


def linked_elf(env, raw):
    image = match.elf_image(raw)
    result = bytearray(raw)
    struct.pack_into('<H', result, 16, 2)
    section_start = struct.unpack_from('<I', raw, 32)[0]
    struct.pack_into('<I', result, section_start + 40*image['text_index'] + 12, env['root'])
    text = image['sections'][image['text_index']][4]
    result[text:text+96] = env['data']
    for index in image['relocations']:
        struct.pack_into('<I', result, section_start + 40*index + 20, 0)
    symbols = next(section for section in image['sections'] if section[1] == 2)[4]
    struct.pack_into('<I', result, symbols + 16 + 4, env['root'] | 1)
    for ordinal, point in ((2, env['helper'] | 1), (3, env['source'])):
        struct.pack_into('<I', result, symbols + ordinal*16 + 4, point)
        struct.pack_into('<H', result, symbols + ordinal*16 + 14, 0xfff1)
    return bytes(result)


class NativeMatrixTests(unittest.TestCase):
    def test_original_image_adapter_preserves_genuine_identities(self):
        env = fixture();raw = original_elf(env, 0, 0)
        typed, targets = bindings(env, raw)
        prior = binding.binding_plan(raw, env['root'], env['rom'], env['mapping'], env['index'], env['objects'])
        self.assertEqual(typed, prior['bindings'])
        self.assertEqual(targets, {'memcpy': (env['helper'], False), 'shadow_state': (env['source'], True)})
        self.assertEqual(match.elf_image(raw)['text'][92:], bytes(4))
        for ft, dt, addend in ((1,1,0),(2,2,0),(2,1,4)):
            with self.subTest(ft=ft, dt=dt, addend=addend), self.assertRaises(ValueError):
                bindings(env, original_elf(env, ft, dt, addend))

    def test_new_native_selector_closes_all_eight_cases_without_memory_grant(self):
        env = fixture();manifest, instructions = prove(env)
        self.assertEqual(manifest['profile'], native.SCHEMA)
        self.assertEqual(len(instructions), 45)
        proof = manifest['proof']['local_shadow_halfword_matrix']
        self.assertEqual(len(proof['cases']), 8)
        self.assertFalse(proof['source_bytes_known'])
        self.assertFalse(proof['actual_entry_SP_known'])
        self.assertFalse(proof['physical_access_proved'])
        self.assertEqual(proof['source_sha256'], 'a'*64)
        for case in proof['cases']:
            self.assertEqual(case['final_R3']['lifetime'], 'expired')
            self.assertFalse(case['final_R3']['dereference_permission'])
        self.assertEqual(set(proof['producer_sha256']),
            {'local_shadow_halfword_matrix.py', 'local_shadow_matrix_elf_binding.py'})

    def test_native_binding_roles_and_source_identity_cannot_be_forged(self):
        env = fixture();typed, _ = bindings(env)
        for role in ('calls', 'data', 'functions', 'switches'):
            changed = copy.deepcopy(typed)
            changed[role] = [] if changed[role] else [[92, 'forged']]
            with self.subTest(role=role), self.assertRaises(ValueError):
                prove(env, given=changed)
        for fingerprint in (None, 'b'*63, 'G'*64):
            with self.subTest(fingerprint=fingerprint), self.assertRaises(ValueError):
                prove(env, fingerprint=fingerprint)

    def test_changed_native_manifest_or_source_refuses_replay(self):
        env = fixture();manifest, _ = prove(env)
        changed = copy.deepcopy(manifest)
        changed['proof']['local_shadow_halfword_matrix']['cases'][0]['final_R3']['dereference_permission'] = True
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            prove(env, changed)
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            prove(env, manifest, fingerprint='b'*64)

    def test_default_policies_and_original_free_preflight_stay_closed(self):
        env = fixture()
        for selector in (owner.ACYCLIC_SELECTOR, owner.rom_table.SELECTOR):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                bindings(env, selector=selector)
        with self.assertRaisesRegex(ValueError, 'original ELF'):
            owner.preflight(env['data'], env['root'], env['rom'], env['mapping'], env['index'],
                            env['objects'], selector=native.SELECTOR)

    def test_native_report_retains_conditions_original_and_strict_dispatch(self):
        env = fixture();manifest, _ = prove(env);raw = original_elf(env)
        result = (env['data'], manifest, 'a'*64, env['mapping'], env['index'], env['objects'], env['rom'], 45, raw)
        report = owner.render(env['root'], result)
        self.assertIn(native.CONTROL_FLOW, report)
        self.assertIn('source halfwords', report)
        self.assertIn('expired R3 frame pointer', report)
        self.assertIn(owner.sha(raw), report)
        self.assertEqual(owner.selector_for_report(report), native.SELECTOR)
        with patch.object(owner, 'build', return_value=result) as build:
            self.assertTrue(owner.report_matches(report, ROOT, env['root']))
        self.assertEqual(build.call_args.kwargs['selector'], native.SELECTOR)
        with self.assertRaises(ValueError):
            owner.selected(report + f'\n* verification: `{owner.SCHEMA}`')
        with self.assertRaisesRegex(ValueError, 'original ELF'):
            owner.fingerprint(env['root'], env['data'], manifest, 'a'*64, env['mapping'],
                              env['index'], env['objects'], env['rom'])

    def test_strict_link_preserves_original_and_only_two_relocation_sites(self):
        env = fixture();raw = original_elf(env);linked = linked_elf(env, raw)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS)
        class Runner:
            def __init__(self, output):
                self.output, self.files, self.commands = output, {}, []
            def read_binary(self, path):
                return b'int fixture(void);' if path.endswith('/f.i') else self.output
            def write_text(self, path, text):
                self.files[path] = text
            def sh(self, command):
                self.commands.append(command)
        runner = Runner(linked)
        result, typed = owner.object_bytes(runner, '/fixture', args, match.elf_image(raw), env['root'],
            env['rom'], env['mapping'], env['objects'], selector=native.SELECTOR, index=env['index'])
        self.assertEqual(result, env['data'])
        self.assertEqual(typed, bindings(env)[0])
        self.assertIn('.type memcpy, %function', runner.files['/fixture/f.known.s'])
        self.assertIn('.type shadow_state, %object', runner.files['/fixture/f.known.s'])
        self.assertIn('--fatal-warnings --no-undefined --no-relax --orphan-handling=error', runner.commands[1])
        image = match.elf_image(linked);text = image['sections'][image['text_index']][4]
        for offset in (0, 66, 92):
            changed = bytearray(linked);changed[text+offset] ^= 2
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                owner.object_bytes(Runner(bytes(changed)), '/fixture', args, match.elf_image(raw),
                    env['root'], env['rom'], env['mapping'], env['objects'],
                    selector=native.SELECTOR, index=env['index'])

    def test_cli_keeps_mixed_policy_exclusion_before_compiler(self):
        env = fixture()
        args = dict(mode='thumb', control_flow_profile='ordinary', software_double_profile=None,
            software_double_remainder_profile=None, function_address_profile=None, switch_profile=None,
            label=None, wsl='Ubuntu', wsl_path=match.DEFAULT_WSL_PATH, owner_runtime_profile=native.SELECTOR,
            signed_quotient_profile=None, signed_runtime_profile=None, unsigned_runtime_profile=None,
            addressed_signed_runtime_profile=None, switch_data_profile=None)
        for key in ('function_address_profile','signed_runtime_profile','unsigned_runtime_profile','switch_data_profile'):
            with self.subTest(key=key), patch.object(owner, 'build') as build, self.assertRaises(ValueError):
                owner.issue(ROOT, env['root'], argparse.Namespace(**dict(args, **{key:'mixed'})))
            build.assert_not_called()


if __name__ == '__main__':
    unittest.main(verbosity=2)
