"""New330 interaction checks on the merged executable, without game workflows."""
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / 'tools'))
import match
import report_fixtures
import match_evidence as evidence
import owner_admission_profile as owner
import local_long_branch_profile as frame
import entry_recursive_ordinary_call_profile as entry
import mutable_stack_index_profile as finite
import mutable_three_call_native_profile as mutable
import standalone_local_output_word_profile as resident
import static_callback_r6_frame_profile as restored
import word_result_callback_profile as nested
import static_callback_target_preservation_profile as r7
# Frozen constructors and ELF serializers only, never old test methods.
import test_combined_restored_standalone as support
import test_native_three_call as three_fixture
import test_static_callback_r6_frame as r6_fixture
import test_standalone_word_output as word_fixture


def f0_environment(**changes):
    proof, *_ = three_fixture.fixture(**changes)
    body = proof.body.replace(bytes.fromhex('07200880'), bytes.fromhex('09200880'), 1)
    rom = bytearray(proof.rom)
    offset = three_fixture.A - match.ROM_BASE
    rom[offset:offset + len(body)] = body
    return dict(data=body, address=three_fixture.A, rom=bytes(rom),
        mapping=proof.mapping, index=proof.index, objects=proof.objects,
        selector=mutable.SELECTOR, bindings=dict(calls=[
            [site-three_fixture.A, f'func_{target:08X}']
            for site, target in sorted(proof.calls.items())],
            functions=[], data=[], switches=[]))


def environments():
    restored_env = r6_fixture.fixture(callback=bytes.fromhex('03220a6000207047'))
    resident_env = word_fixture.environment({4: 0x2009})
    resident_env.update(address=word_fixture.ROOT, selector=resident.SELECTOR)
    return f0_environment(), restored_env, resident_env


def prove(env, manifest=None, selector=None):
    return support.prove(env, manifest, selector)


class MergedNativeTests(unittest.TestCase):
    def test_three_cli_resident_elf_reports_status_and_publisher_dispatch(self):
        import status
        import push
        for env in environments():
            address = env['address']
            with self.subTest(selector=env['selector']), support.tree(env) as root, \
                    support.build_mocks(env, root) as runner, \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                argv = ['match.py', '--root', str(root), '--owner-runtime-profile',
                        env['selector'], hex(address)]
                with patch.object(sys, 'argv', argv):
                    self.assertEqual(match.main(), 0)
                self.assertIn('verdict MATCH', output.getvalue())
                report = (root / 'docs/match' / f'{address:08X}.md').read_text()
                self.assertEqual(owner.selector_for_report(report), env['selector'])
                self.assertIn('original_elf_sha256', report)
                self.assertEqual(len(runner.commands), 2)
                self.assertTrue(evidence.report_matches(report, root, address))
                commands = []

                def matcher(command, **unused):
                    commands.append(command)
                    with patch.object(sys, 'argv', command[1:]), \
                            contextlib.redirect_stdout(io.StringIO()) as captured:
                        code = match.main()
                    return subprocess.CompletedProcess(command, code, captured.getvalue(), '')

                with patch.object(status.subprocess, 'run', side_effect=matcher):
                    values = status.collect(str(root), True, quiet=True, jobs=1)
                self.assertEqual(values[1], 1)
                self.assertEqual(values[4], [])
                self.assertEqual(len(commands), 1)
                command = commands[0]
                self.assertEqual(command[command.index('--owner-runtime-profile') + 1], env['selector'])
                self.assertIn('--no-write', command)
                self.assertTrue(push.check_reports(str(root)))
                bad = report.replace('**MATCH - byte identical**', '**IMPLAUSIBLE**')
                (root / 'docs/match' / f'{address:08X}.md').write_text(bad)
                self.assertFalse(push.check_reports(str(root)))

    def test_cross_selector_and_cli_policy_exclusivity_survive_union(self):
        envs = environments()
        manifests = [prove(env)[0] for env in envs]
        for number, env in enumerate(envs):
            for other, wrong in enumerate(envs):
                if number == other:
                    continue
                with self.subTest(root=env['selector'], wrong=wrong['selector']), self.assertRaises(ValueError):
                    prove(env, selector=wrong['selector'])
                with self.assertRaises(ValueError):
                    prove(env, manifests[other])
            for selector in (owner.SELECTOR, owner.ACYCLIC_SELECTOR, entry.SELECTOR, nested.SELECTOR, r7.SELECTOR):
                with self.subTest(root=env['selector'], legacy=selector), self.assertRaises(ValueError):
                    prove(env, selector=selector)
            for field in ('function_address_profile', 'addressed_signed_runtime_profile',
                          'signed_runtime_profile', 'signed_quotient_profile', 'switch_data_profile'):
                args = word_fixture.args(owner_runtime_profile=env['selector'], **{field: 'mixed'})
                with self.subTest(root=env['selector'], field=field), \
                        patch.object(owner, 'build') as build, self.assertRaises(ValueError):
                    owner.issue(HERE, env['address'], args)
                build.assert_not_called()
        schemas = [mutable.SCHEMA, restored.SCHEMA, resident.SCHEMA, entry.NATIVE_SCHEMA, nested.SCHEMA]
        for first in schemas[:3]:
            for second in schemas:
                with self.subTest(first=first, second=second), self.assertRaises(ValueError):
                    owner.selected(f'* verification: `{first}`\n* verification: `{second}`\n')

    def test_original_elf_resident_link_and_manifest_tamper_rejected(self):
        for env in environments():
            with self.subTest(selector=env['selector']):
                image = match.elf_image(support.elf(env, wrong_type=True))
                with self.assertRaises(ValueError):
                    owner.original_bindings(image, env['address'], env['rom'], env['mapping'],
                        env['objects'], selector=env['selector'], index=env['index'])
                with support.tree(env) as root, support.build_mocks(env, root) as runner:
                    original_read = runner.read_binary
                    runner.read_binary = lambda path: support.elf(env, linked=True, changed=True) \
                        if path.endswith('/f.elf') else original_read(path)
                    with self.assertRaisesRegex(ValueError, 'outside exact original relocations'):
                        owner.object_bytes(runner, str(root / 'build'), word_fixture.args(),
                            match.elf_image(support.elf(env)), env['address'], env['rom'], env['mapping'],
                            env['objects'], selector=env['selector'], index=env['index'])
                manifest, _ = prove(env)
                stale = copy.deepcopy(manifest)
                stale['unattested_new_field'] = True
                with self.assertRaises(ValueError):
                    prove(env, stale)
                changed = copy.deepcopy(env['bindings'])
                changed['calls'][0][0] += 2
                bad = dict(env, bindings=changed)
                with self.assertRaises(ValueError):
                    prove(bad)

    def test_captured_input_changes_and_saved_report_replay_are_fresh(self):
        for env in environments():
            for kind in ('source', 'header', 'mapping', 'index', 'objects', 'rom'):
                with self.subTest(selector=env['selector'], kind=kind), support.tree(env) as root:
                    target = {'source': root / 'src' / f'{env["address"]:08X}.c',
                        'header': root / 'include/fixture.h', 'mapping': root / 'config/functions.json',
                        'index': root / 'symbols/functions.txt', 'objects': root / 'config/data_symbols.json',
                        'rom': root / 'fixture.bin'}[kind]

                    def change():
                        target.write_bytes(target.read_bytes() + b'\n')

                    with support.build_mocks(env, root, change), self.assertRaisesRegex(ValueError, 'changed'):
                        owner.build(root, env['address'], selector=env['selector'])
            with support.tree(env) as root, support.build_mocks(env, root):
                report = owner.render(env['address'], owner.build(root, env['address'], selector=env['selector']))
                stale = report.replace('"source_sha256":"', '"source_sha256":"stale', 1)
                self.assertFalse(report_fixtures.replay(stale, root, env['address']))
                (root / 'include/fixture.h').write_bytes(b'new combined fixture header\n')
                self.assertFalse(report_fixtures.replay(report, root, env['address']))

    def test_live_alias_effect_and_saved_frame_refusals_still_apply(self):
        for case in (dict(missing_init=True), dict(bad_consumer=True), dict(extra_call=True)):
            with self.subTest(mutable=case), self.assertRaises(ValueError):
                prove(f0_environment(**case))
        for callback in (bytes.fromhex('002603220a6000207047'), bytes.fromhex('016000207047')):
            with self.subTest(callback=callback.hex()), self.assertRaises(ValueError):
                prove(r6_fixture.fixture(callback=callback))
        for changes in ({4: 0x2009, 18: 0x4668}, {4: 0x2009, 17: 0x6062}):
            env = word_fixture.environment(changes)
            env.update(address=word_fixture.ROOT, selector=resident.SELECTOR)
            with self.subTest(resident=changes), self.assertRaises(ValueError):
                prove(env)
        env = f0_environment()
        rows = json.loads(env['mapping'])
        old = rows[0]['instrs']
        rows[0]['instrs'] += 1
        env['mapping'] = json.dumps(rows).encode()
        env['index'] = env['index'].replace(f' {old} return'.encode(), f' {old+1} return'.encode(), 1)
        with self.assertRaisesRegex(ValueError, 'instruction counts'):
            prove(env)

    def test_entry_saved_frame_and_mutable_type_boundaries_remain_closed(self):
        address = 0x08030000
        body = bytes.fromhex('00b5') + r6_fixture.bl(address + 2, address) + bytes.fromhex('01bc0047')
        mapping = json.dumps([dict(rom=f'0x{address:08X}', end=f'0x{address+len(body):08X}',
                                  mode='thumb', instrs=4)]).encode()
        index = f'{address:08X} {address+len(body):08X} {len(body)} 4 return\n'.encode()
        record = entry.prove(body, address, mapping, index, address-match.ROM_BASE+len(body),
                             selector=entry.SELECTOR)
        self.assertIn('entry_calls', record['frame'])
        context = entry.prepare(body, address, mapping, index, address-match.ROM_BASE+len(body),
                                selector=entry.SELECTOR)
        ins = entry._decode(body, address)
        calls = dict(context.calls)
        for policy in (mutable.SELECTOR, 'forged'):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                frame.prove_frame(ins, entry._edges(ins, calls), address, {}, calls,
                    entry_recursive_calls=context, native_three_call_policy=policy)
        proof, instructions, edges, branches, calls = three_fixture.fixture()
        for extra in (dict(entry_recursive_calls=context), dict(buffer_proof=object()),
                      dict(call_preservation={site: set() for site in calls})):
            with self.subTest(extra=list(extra)), self.assertRaises(ValueError):
                frame.prove_frame(instructions, edges, three_fixture.A, branches, calls,
                    stack_aliases=True, mutable_stack_index_policy=finite.THREE_CALL_SELECTOR,
                    consumer_scratch_proof=proof, native_three_call_policy=mutable.SELECTOR, **extra)

    def test_combined_producer_fingerprints_bind_new_frame_and_policy_chain(self):
        production = mutable.environment_fingerprint()
        for name in ('match.py', 'owner_admission_profile.py', 'local_long_branch_profile.py',
                     'mutable_three_call_native_profile.py'):
            self.assertEqual(production['producers'][name], hashlib.sha256((HERE/'tools'/name).read_bytes()).hexdigest())
        manifest, _ = prove(environments()[1])
        sources = manifest['proof']['buffers']['r6_restoration']['policy']['source_sha256']
        self.assertEqual(sources['local_long_branch_profile.py'], hashlib.sha256((HERE/'tools/local_long_branch_profile.py').read_bytes()).hexdigest())
        manifest, _ = prove(environments()[2])
        sources = manifest['proof']['standalone_word_return']['local_effects']['engine_sources']
        self.assertEqual(sources['match.py'], hashlib.sha256((HERE/'tools/match.py').read_bytes()).hexdigest())
        env = environments()[0]
        state = {'generation': 'before'}
        with support.tree(env) as root:
            def change():
                state['generation'] = 'after'
            with support.build_mocks(env, root, change), \
                    patch.object(mutable, 'environment_fingerprint', side_effect=lambda: dict(state)), \
                    self.assertRaisesRegex(ValueError, 'producers.*changed'):
                owner.build(root, env['address'], selector=env['selector'])


if __name__ == '__main__':
    unittest.main()
