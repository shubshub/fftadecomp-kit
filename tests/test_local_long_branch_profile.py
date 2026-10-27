"""Local Thumb BL edges retain machine LR and complete-frame semantics."""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import software_double_profile as double
import local_long_branch_profile as local
import test_software_double_profile as double_tests

BASE = 0x08000000


class LocalFrameTests(unittest.TestCase):
    def assemble(self, source):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='long_branch_', dir=scratch) as directory:
            path = Path(directory)
            (path / 'fixture.s').write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n' + source)
            subprocess.run(['arm-none-eabi-as', '-mthumb-interwork', str(path / 'fixture.s'),
                            '-o', str(path / 'fixture.o')], check=True, capture_output=True)
            image = match.elf_image((path / 'fixture.o').read_bytes())
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        instructions = {item.address: item for item in decoder.disasm(image['text'], BASE)}
        edges, branches = {}, {}
        for site, item in instructions.items():
            if item.mnemonic == 'bl':
                branches[site] = local.target(item, BASE, BASE + len(image['text']))
                edges[site] = (branches[site],)
            elif item.mnemonic == 'bx':
                edges[site] = ()
            else:
                edges[site] = (site + item.size,)
        # Omit assembler alignment after the return and unreachable blocks.
        reached, pending = set(), [BASE]
        while pending:
            site = pending.pop()
            if site in reached:
                continue
            reached.add(site)
            pending.extend(edges[site])
        return ({site: instructions[site] for site in reached},
                {site: edges[site] for site in reached}, branches)

    def proof(self, source):
        instructions, edges, branches = self.assemble(source)
        return local.prove_frame(instructions, edges, BASE, branches, {})

    def test_local_bl_preserves_argument_registers_but_overwrites_lr(self):
        proof = self.proof('push {lr}\nmovs r0,r4\nmovs r4,#3\nbl tail\n'
                           'movs r0,#0\ntail:\nmovs r4,r0\npop {r1}\nbx r1\n')
        self.assertEqual(proof['maximum_frame_bytes'], 4)
        self.assertEqual(proof['preserved'], 'r4-r11,sp,entry-lr')

    def test_local_bl_does_not_admit_return_to_its_continuation(self):
        with self.assertRaisesRegex(ValueError, 'original entry LR'):
            self.proof('push {lr}\nbl tail\nmovs r0,#0\ntail:\npop {r1}\nbx lr\n')

    def test_callee_saved_corruption_rejects(self):
        with self.assertRaisesRegex(ValueError, 'r4-r11'):
            self.proof('push {lr}\nbl tail\nmovs r0,#0\ntail:\nmovs r4,#0\npop {r1}\nbx r1\n')

    def test_saved_stack_write_rejects(self):
        with self.assertRaisesRegex(ValueError, 'overwrites a saved'):
            self.proof('push {lr}\nbl tail\nmovs r0,#0\ntail:\nstr r0,[sp]\npop {r1}\nbx r1\n')

    def test_stack_alias_rejects(self):
        with self.assertRaisesRegex(ValueError, 'stack-address'):
            self.proof('push {lr}\nbl tail\nmovs r0,#0\ntail:\nmov r0,sp\npop {r1}\nbx r1\n')

    def test_false_standalone_tail_rejects(self):
        with self.assertRaisesRegex(ValueError, 'established frame'):
            self.proof('str r0,[sp]\npop {r1}\nbx r1\n')

    def test_self_entry_rejects(self):
        with self.assertRaisesRegex(ValueError, 'non-entry'):
            self.assemble('entry:\npush {lr}\nbl entry\npop {r1}\nbx r1\n')

    def test_local_edge_fallthrough_rejects(self):
        instructions, edges, branches = self.assemble('push {lr}\nbl tail\nmovs r0,#0\n'
                                                     'tail:\npop {r1}\nbx r1\n')
        site = next(iter(branches))
        edges[site] += (site + 4,)
        with self.assertRaisesRegex(ValueError, 'without fallthrough'):
            local.prove_frame(instructions, edges, BASE, branches, {})

    def test_default_non_double_context_still_rejects(self):
        instructions, _, _ = self.assemble('push {lr}\nbl tail\nmovs r0,#0\n'
                                           'tail:\npop {r1}\nbx r1\n')
        data = b''.join(bytes(item.bytes) for _, item in sorted(instructions.items()))
        with self.assertRaises(ValueError):
            match.verify_leaf_instructions(data, BASE, True)


class LocalDoubleTests(unittest.TestCase):
    # Reuse the existing original-ELF fixture/linker and actual pinned runtime.
    setUpClass = classmethod(double_tests.SoftwareDoubleTests.setUpClass.__func__)
    setUp = double_tests.SoftwareDoubleTests.setUp
    indexes = double_tests.SoftwareDoubleTests.indexes
    fixture = double_tests.SoftwareDoubleTests.fixture
    verify = double_tests.SoftwareDoubleTests.verify
    def local_fixture(self):
        self.fixture(assembly='push {r4,lr}\nbl __floatsidf\nbl tail\n'
                              'movs r0,#0\ntail:\npop {r4}\npop {r1}\nbx r1')

    def test_versioned_local_branch_manifest(self):
        self.local_fixture()
        self.assertEqual(len(self.verify()), len(self.instructions))
        self.assertEqual(self.manifest['local_branches']['schema'], local.SCHEMA)
        self.assertEqual(self.manifest['local_branches']['edges'], [[6, 12]])

    def test_stale_or_missing_local_manifest_rejects(self):
        self.local_fixture()
        for change in ('missing', 'target', 'schema', 'extra', 'float', 'bool'):
            manifest = copy.deepcopy(self.manifest)
            if change == 'missing':
                del manifest['local_branches']
            elif change == 'target':
                manifest['local_branches']['edges'][0][1] += 2
            elif change == 'schema':
                manifest['local_branches']['schema'] += '-forged'
            elif change == 'float':
                manifest['local_branches']['edges'][0][0] = 6.0
            elif change == 'bool':
                manifest['local_branches']['edges'][0][0] = False
            else:
                manifest['local_branches']['extra'] = True
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.verify(manifest)

    def test_independent_owner_at_local_target_rejects(self):
        self.local_fixture()
        entries = json.loads(self.mapping)
        entries.append({'rom': f'0x{BASE + 12:08X}', 'end': f'0x{BASE + 18:08X}',
                        'mode': 'thumb', 'instrs': 3})
        self.mapping = json.dumps(entries).encode()
        with self.assertRaisesRegex(ValueError, 'nonoverlapping'):
            self.verify()

    def test_wrong_complete_count_rejects(self):
        self.local_fixture()
        self.indexes(len(self.body), len(self.instructions) + 1)
        with self.assertRaisesRegex(ValueError, 'count'):
            self.verify()

    def test_original_compiler_local_edges_and_fresh_report_replay(self):
        source = ('struct record { int values[64]; double total; };\n'
                  'extern int func_08010000(int, int);\n'
                  'int func_08000000(struct record *record, unsigned event)\n'
                  '{\n    switch (event) {\n')
        for event in range(64):
            source += (f'    case {event}:\n'
                       f'        record->values[{event}] = func_08010000(record->values[{event}], {event});\n'
                       f'        record->total += (double)record->values[{event}] * {event + 1}.0;\n'
                       '        break;\n')
        source += '    }\n    return record->values[0];\n}\n'
        (self.root / 'src/08000000.c').write_text(source)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root,
                                                   BASE, 'src/08000000.c')
            symbol, _ = match.function_record(original, 'func_08000000', BASE, True)
            self.indexes(symbol['size'], 1)
            entries = json.loads(self.mapping)
            entries[1] = dict(entries[1], rom='0x08010000', end='0x08010002')
            self.mapping = json.dumps(entries).encode()
            self.index = self.index.replace(b'08000200 08000202', b'08010000 08010002')
            words = {}
            self.body, self.calls, self.bindings = double.object_bytes(
                runner, workspace, self.args, original, BASE, self.mapping, self.runtime_rom,
                self.index, switch_relocations=words)
            assembly = runner.read_binary(f'{workspace}/f.s').decode()
            self.assertIn('@far jump', assembly)
            definitions = [item for item in original['symbols'] if item['type'] == 2 and item['section']]
            self.assertEqual(definitions, [symbol])
        rom = bytearray(self.runtime_rom)
        rom[:len(self.body)] = self.body
        self.rom = bytes(rom)
        self.instructions = match.verify_leaf_instructions(
            self.body, BASE, True, self.calls, switch_relocations=words,
            double_context=(self.rom, self.mapping, self.index, self.bindings))
        entries[0]['instrs'] = len(self.instructions)
        self.mapping = json.dumps(entries).encode()
        self.index = ''.join(f"{int(item['rom'], 16):08X} {int(item['end'], 16):08X} "
                             f"{int(item['end'], 16) - int(item['rom'], 16)} {item['instrs']} return\n"
                             for item in entries).encode()
        self.manifest = double.make_manifest(self.calls, BASE, self.bindings, self.instructions,
                                             switch=double.switch_record(self.body, BASE, words))
        self.assertGreater(len(self.manifest['local_branches']['edges']), 1)
        self.assertEqual(len(self.verify()), len(self.instructions))
        (self.root / 'config/functions.json').write_bytes(self.mapping)
        (self.root / 'symbols/functions.txt').write_bytes(self.index)
        report = double_tests.SoftwareDoubleTests.native_report(self)
        self.assertIn('MATCH - byte identical', report)
        self.assertIn(local.SCHEMA, report)
        opening, reading = self.patched_rom()
        with opening, reading:
            self.assertTrue(double_tests.evidence.report_matches(report, self.root, BASE))

    patched_rom = double_tests.SoftwareDoubleTests.patched_rom


if __name__ == '__main__':
    unittest.main()
