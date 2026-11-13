"""Closed scalar-bias policy: native source replay and adversarial machine shapes."""
import contextlib
import copy
from dataclasses import replace
import io
import json
import os
from pathlib import Path
import struct
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import match
import match_evidence
import switch_constants_profile as profile
from test_switch_constants import assemble, fixture_assembly, ordinary_link
import test_switch_placement as placement_tests

SOURCE = 'extern unsigned int func_08001000(unsigned int);\nunsigned int func_08000000(unsigned int *input, int count, unsigned int *output, int quota)\n{\n    unsigned int total = 0;\n    unsigned int rejected = 0;\n    unsigned int *origin = input;\n    int i;\n    for (i = 0; i < count; i++, input++) {\n        unsigned int value = *input;\n        switch (value) {\n        case 300: value = func_08001000(value + total); break;\n        case 301: value = func_08001000(value - total); break;\n        case 302: value = func_08001000(value ^ total); break;\n        case 303: value = func_08001000(value | total); break;\n        case 304: value = func_08001000(value & total); break;\n        case 305: value = func_08001000(value * total); break;\n        default: rejected++; value = 0; break;\n        }\n        if (value) {\n            *output++ = value;\n            total += value;\n            *origin ^= total;\n            if (--quota == 0) break;\n        }\n    }\n    return total + rejected;\n}\n'
ADDRESS = 0x08000000


def assembly():
    result = fixture_assembly(call=True, prefix='sub sp, #8\nstr r3, [sp]',
        first='ldr r2, .Lconstant0', second='adds r0, r0, r2')
    result = result.replace('.word 0xFF00FF00', '.word -300').replace('.Lconstant1:\n.word 0x0F0F0F0F\n', '')
    return result.replace('bl func_08001000\npop', 'ldr r3, [sp]\nstmia r1!, {r3}\nbl func_08001000\nadd sp, #8\npop')


class OneConstantTests(unittest.TestCase):
    policy = profile.ONE_FRAME_POLICY
    setUp = placement_tests.PlacementTests.setUp
    trusted_fixture = placement_tests.PlacementTests.trusted_fixture
    admit = placement_tests.PlacementTests.admit

    def prepare(self):
        return placement_tests.PlacementTests.prepare(self, ADDRESS, SOURCE, self.policy)

    def structural(self, source=None):
        original = assemble(self.root, assembly() if source is None else source)
        _, body = ordinary_link(self.root, original)
        image = match.elf_image(original)
        relocations = {}
        for index in image['relocations']:
            section = image['sections'][index]
            for position in range(0, section[5], 8):
                site, info = struct.unpack_from('<II', image['section_data'][index], position)
                if info & 255 == 2:
                    relocations[site] = struct.unpack_from('<I', image['text'], site)[0]
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        calls = {i.address: i.operands[0].imm for i in decoder.disasm(body, ADDRESS) if i.mnemonic == 'bl'}
        return body, calls, relocations

    def manifest(self, source=None, policy=None):
        body, calls, relocations = self.structural(source)
        return profile._manifest(body, ADDRESS, calls, relocations, policy or self.policy)

    def test_native_cli_and_exactly_one_fresh_source_replay(self):
        root, rom, captured = self.prepare()
        argv = ['match.py', '--root', str(root), '--switch-profile', self.policy.selector, '08000000']
        with self.trusted_fixture(root, rom), patch.object(sys, 'argv', argv), \
                contextlib.redirect_stdout(io.StringIO()) as output, \
                patch.object(profile, '_compile_object', wraps=profile._compile_object) as compiled:
            self.assertEqual(match.main(), 0)
            self.assertEqual(compiled.call_count, 1)
            report = (root / 'docs/match/08000000.md').read_text()
            self.assertTrue(match_evidence.report_matches(report, root, ADDRESS))
            self.assertEqual(compiled.call_count, 2)
        self.assertIn('MATCH - byte identical', output.getvalue())
        self.assertIn('stmia', captured['raw'])
        self.assertEqual(len(captured['manifest']['constants']), 1)
        self.assertTrue(captured['manifest']['frame']['accesses'])
        destination = os.environ.get('FFTA_ONE_CONSTANT_EVIDENCE')
        if destination:
            captured.update(report=report, stdout=output.getvalue(), native_compiles=1,
                            fresh_report_replays=1, total_native_and_replay_compiles=2)
            Path(destination).write_text(json.dumps(captured, indent=2) + '\n')

    def test_structural_positive_and_legacy_rejection(self):
        manifest, count = self.manifest()
        self.assertEqual(len(manifest['constants']), 1)
        self.assertGreater(count, 20)
        for policy in (profile.LEGACY_POLICY, profile.FRAME_POLICY):
            with self.subTest(policy=policy.selector), self.assertRaisesRegex(ValueError, 'two-word'):
                self.manifest(policy=policy)
        with self.assertRaises(ValueError):
            profile.checked_policy(replace(self.policy))
        body, calls, relocations = self.structural()
        for value in (True, False, 'one-constant-frame-v1', replace(self.policy)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                match.verify_leaf_instructions(body, ADDRESS, True, calls,
                    switch_relocations=relocations, allow_switch_constants=True,
                    allow_switch_scalar_frame=True, switch_constants_policy=value)

    def test_scalar_constant_count_use_and_pointer_masquerade(self):
        initial = assembly()
        variants = [initial.replace('.word -300', '.word -300\n.word -301'),
                    initial.replace('.word -300\n', ''),
                    initial.replace('ldr r2, .Lconstant0', 'movs r2, #0'),
                    initial.replace('adds r0, r0, r2', 'subs r0, r0, r2'),
                    initial.replace('adds r0, r0, r2', 'adds r0, r0, r3'),
                    initial.replace('str r3, [sp]', 'ldr r3, .Lconstant0\nstr r3, [sp]'),
                    initial.replace('.Lcase0:\n', '.Lcase0:\nb func_08000000+8\n')]
        variants += [initial.replace('.word -300', f'.word {word}')
                     for word in ('0x08000000', '0x02000000', '0x03000000', '0', '-1', '-65537')]
        for variant in variants:
            with self.subTest(variant=variant), self.assertRaises(ValueError):
                self.manifest(variant)

    def test_guard_table_and_unreachable_bytes(self):
        initial = assembly()
        for old, new in [('cmp r0, #1', 'cmp r0, #2'), ('bhi .Ldefault', 'bgt .Ldefault'),
                         ('lsls r0, r0, #2', 'lsls r0, r0, #1'),
                         ('.word .Lcase0', '.word .Lpointer'),
                         ('.word .Lcase1', '.word .Lcase1+1'),
                         ('.Lcase0:\n', '.Lcase0:\nb .Ldispatch\n'),
                         ('.size func_08000000', 'movs r0, #0\n.size func_08000000')]:
            with self.subTest(change=new), self.assertRaises(ValueError):
                self.manifest(initial.replace(old, new))

    def test_frame_alias_escape_and_unbalanced_return(self):
        initial = assembly()
        for operation in ('mov r2, sp', 'add r2, sp, #4', 'mov r2, sp\nstr r2, [sp]',
                          'mov r2, sp\nbl func_08001000', 'mov sp, r0',
                          'str r3, [sp, #8]', 'str r3, [sp, #12]'):
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.manifest(initial.replace('str r3, [sp]', operation, 1))
        for old, new in [('add sp, #8', 'add sp, #12'), ('bx r1', 'bx r0'),
                         ('.Lcase0:\n', '.Lcase0:\nsub sp, #4\n'),
                         ('sub sp, #8', 'sub sp, #0')]:
            with self.subTest(change=new), self.assertRaises(ValueError):
                self.manifest(initial.replace(old, new))

    def test_single_stm_control_pointers_and_saved_registers(self):
        initial = assembly()
        for operation in ('stmia r1!, {r2,r3}', 'ldmia r1!, {r3}', 'stmia r1!, {r1}',
                          'mov r1, lr\nstmia r1!, {r3}', 'mov r3, lr\nstmia r1!, {r3}',
                          'mov r3, sp\nstmia r1!, {r3}', 'stmia r4!, {r3}'):
            with self.subTest(operation=operation), self.assertRaises(ValueError):
                self.manifest(initial.replace('stmia r1!, {r3}', operation))
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        ins = next(decoder.disasm(bytes.fromhex('08c1'), ADDRESS))
        for aliases, returns in [({match.ARM_REG_R1: -4}, set()),
                                 ({match.ARM_REG_R3: -4}, set()),
                                 ({}, {match.ARM_REG_R1}), ({}, {match.ARM_REG_R3})]:
            with self.assertRaises(ValueError):
                profile.verify_external_single_stm(ins, aliases, returns)

    def test_local_loop_partial_correctness_and_frame_join(self):
        initial = assembly()
        stable = initial.replace('.Ldone:\n', '.Ldone:\n.Lloop:\nsubs r3, #1\nbne .Lloop\n')
        self.manifest(stable)
        with self.assertRaises(ValueError):
            self.manifest(stable.replace('subs r3, #1', 'sub sp, #4\nsubs r3, #1'))

    def test_complete_owner_and_relocation_rejections(self):
        original = assemble(self.root, assembly())
        image = match.elf_image(original)
        symbol = next(s for s in image['symbols'] if s['type'] == 2)
        for field, value in [('size', symbol['size'] - 2), ('bind', 0), ('value', 3)]:
            changed = copy.deepcopy(image)
            next(s for s in changed['symbols'] if s['type'] == 2)[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                profile._envelope(changed, ADDRESS)
        for word in ('.Lcase0', 'g_external', 'func_08001000'):
            obj = assemble(self.root, assembly().replace('.word -300', '.word ' + word))
            mapping = b'[{"rom":"0x08001000","end":"0x08001002","mode":"thumb"}]'
            with self.subTest(word=word), self.assertRaises(ValueError):
                self.admit(obj, ADDRESS, mapping)

    def test_stale_source_mapping_index_and_producer(self):
        root, rom, _ = self.prepare()
        with self.trusted_fixture(root, rom):
            result = profile._build_from_source(root, ADDRESS, self.policy)
            report = profile.render_report(ADDRESS, result, self.policy)
            for name in ('src/08000000.c', 'config/functions.json', 'symbols/functions.txt'):
                path = root / name
                old = path.read_bytes()
                path.write_bytes(old + b'\n')
                with self.subTest(name=name):
                    self.assertFalse(match_evidence.report_matches(report, root, ADDRESS))
                path.write_bytes(old)
            resolver = profile._resolve_tools
            ticks = 0
            def drift():
                nonlocal ticks
                ticks += 1
                tools = resolver()
                return tools if ticks == 1 else (*tools[:-1], (*tools[-1][:-1], '0' * 64))
            with patch.object(profile, '_resolve_tools', side_effect=drift):
                self.assertFalse(match_evidence.report_matches(report, root, ADDRESS))
            changed = json.loads(result.manifest_json)
            changed['placement']['original_elf_sha256'] = '0' * 64
            stale = profile.render_report(ADDRESS, replace(result, manifest_json=profile.canonical(changed)), self.policy)
            self.assertFalse(match_evidence.report_matches(stale, root, ADDRESS))

    def test_strict_schema_no_fallback_or_report_field_laundering(self):
        root, rom, _ = self.prepare()
        with self.trusted_fixture(root, rom):
            result = profile._build_from_source(root, ADDRESS, self.policy)
            report = profile.render_report(ADDRESS, result, self.policy)
            changes = [report.replace(self.policy.schema, profile.FRAME_POLICY.schema),
                report.replace(self.policy.selector, profile.FRAME_POLICY.selector),
                report.replace(self.policy.schema, self.policy.schema + '-future'),
                report.replace(profile.ONE_CONTROL_FLOW, profile.CONTROL_FLOW),
                report.replace('* switch constants: ' + self.policy.selector + '\n', ''),
                report + '* scalar frame: ' + profile.FRAME_SUMMARY + '\n',
                report.replace('**MATCH - byte identical**', '**NOT MATCHING**')]
            for field in ('constants', 'frame'):
                changed = json.loads(result.manifest_json)
                del changed[field]
                changes.append(profile.render_report(ADDRESS, replace(result, manifest_json=profile.canonical(changed)), self.policy))
            for field, value in [('constants', []), ('constants', [[0, 0, [0]], [4, 0, [0]]])]:
                changed = json.loads(result.manifest_json)
                changed[field] = value
                changes.append(profile.render_report(ADDRESS, replace(result, manifest_json=profile.canonical(changed)), self.policy))
            for changed in changes:
                with self.subTest(report=changed), patch.object(match_evidence, 'switch_report_matches') as fallback:
                    self.assertFalse(match_evidence.report_matches(changed, root, ADDRESS))
                    fallback.assert_not_called()


if __name__ == '__main__':
    unittest.main()
