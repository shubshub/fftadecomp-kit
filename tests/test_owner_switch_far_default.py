"""The owner switch's own far default arm in the default typed-data buffer walk (owner_switch_buffer_profile)."""
import contextlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import interposed_pool_switch as pool
import owner_graph_profile as graph
import owner_switch_buffer_profile as owner_switch
# Modules, not their classes: importing a TestCase class would make it run here again.
import test_data_buffer_calls as data_calls
import test_interposed_pool_switch as pool_tests

A, B = pool_tests.A, pool_tests.B
FAR = 'bls dispatch\nbl default'


class FarDefaultTests(pool_tests.PoolFixture):
    """The walk takes the guard's far default BL as a jump that loses LR, and nothing else."""

    def linked(self, f):
        _, _, _, calls, words = graph.graph(f['data'], A, self.placed(f)[0])
        return calls, words

    def walk(self, f, calls=None, linked=None):
        if calls is None:
            calls, linked = self.linked(f)
        proof = match.BufferCallProof(f['rom'], f['mapping'], stack_arguments=True, loop_replay=True,
                                      bios_wrappers=True, copy_helper_index=f['index'],
                                      switch_callee_index=f['index'])
        owner_switch.walk(proof, f['data'], A, calls, linked)
        return proof

    def test_the_far_default_arm_is_walked(self):
        for name, change in (('adjacent table', dict(loads='', words='')), ('pool', {})):
            with self.subTest(name=name):
                f = self.fixture(guard=FAR, **change)
                proof = self.walk(f)
                record = proof.owner_switch.evidence()
                site, target = f['symbols']['dispatch'] - 4, f['symbols']['default']
                self.assertEqual(record['far_default'],
                                 dict(policy=owner_switch.FAR_DEFAULT_NAME, site=site, target=target))
                line, = proof.loop_replay_lines()
                self.assertIn('; ' + owner_switch.FAR_DEFAULT_RULE.format(
                    name=owner_switch.FAR_DEFAULT_NAME, site=site, target=target), line)

    def test_kit_main_refuses_the_far_default(self):
        f = self.fixture(guard=FAR)
        calls, words = self.linked(f)
        with patch.object(owner_switch.FAR_DEFAULT, 'enabled', False), self.assertRaisesRegex(
                ValueError, 'owner switch excludes local BL control'):
            self.walk(f, calls, words)

    def test_an_owner_without_the_arm_is_unchanged(self):
        f = self.fixture()
        record = self.walk(f).owner_switch.evidence()
        self.assertNotIn('far_default', record)
        self.assertEqual(self.walk(f).owner_switch.branches, {})

    def test_any_other_local_bl_refuses(self):
        for name, change in (('in a case', dict(guard=FAR, case1='movs r0, #1\nbl done')),
                             ('without the far guard', dict(case1='movs r0, #1\nbl done'))):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
                self.walk(self.fixture(**change))

    def test_a_case_bl_to_the_default_is_no_arm(self):
        # Under the far guard, a case that also reaches the default by BL: only the guard's BL is the arm.
        with self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
            self.walk(self.fixture(guard=FAR, case1='movs r0, #1\nbl default'))

    def test_a_bounded_index_leaf_takes_no_arm(self):
        # The stack-index leaf's owner switch keeps "no local BL", with or without the far guard.
        from stack_index_precondition_profile import StackIndexV2BufferProof
        for guard, refused in (('bls dispatch\nb default', False), (FAR, True)):
            with self.subTest(guard=guard):
                f = self.fixture(guard=guard, loads='', words='', case0='movs r0, #2', case2='movs r0, #3')
                _, _, _, calls, words = graph.graph(f['data'], A, self.placed(f)[0])
                self.assertEqual(calls, {})
                proof = StackIndexV2BufferProof(f['rom'], f['mapping'], f['index'], b'{}', data=f['data'], address=A)
                if refused:
                    with self.assertRaisesRegex(ValueError, 'owner switch excludes local BL control'):
                        owner_switch.OwnerSwitch(proof, f['data'], A, calls, words)
                else:
                    self.assertEqual(owner_switch.OwnerSwitch(proof, f['data'], A, calls, words).branches, {})

    def test_the_arm_cannot_return_through_its_own_lr(self):
        # After the far BL, LR holds the dispatch's address: `bx lr` there is no return.
        f = self.fixture(guard='bls dispatch\nbl far', extra='far: movs r0, #0\nbx lr\n')
        with self.assertRaisesRegex(ValueError, 'non-leaf indirect control flow requires linked CFG verification'):
            self.walk(f)

    def test_the_arm_cannot_save_and_pop_its_lr_into_pc(self):
        popped = self.fixture(guard='bls dispatch\nbl far',
                              extra='far: add sp, #8\npop {r4}\npush {lr}\npop {pc}\n')
        with self.assertRaisesRegex(ValueError, 'unproven program-counter stack return'):
            self.walk(popped)
        # Reading the clobbered LR as data is no return and leaves the saved entry LR intact.
        self.walk(self.fixture(guard='bls dispatch\nbl far', extra='far: push {lr}\npop {r0}\nb done\n'))

    def test_the_walk_rederives_the_arm(self):
        f = self.fixture(guard=FAR)
        calls, words = self.linked(f)
        real = owner_switch.OwnerSwitch.__init__

        def moved(self, *args, **kwargs):
            real(self, *args, **kwargs)
            (site, target), = self.branches.items()
            self.branches = {site: target + 2}

        with patch.object(owner_switch.OwnerSwitch, '__init__', moved), self.assertRaisesRegex(
                ValueError, 'owner switch far default differs from its authenticated owner graph'):
            self.walk(f, calls, words)

    def test_the_fingerprint_binds_the_arm(self):
        proof = self.walk(self.fixture(guard=FAR))
        before = proof.fingerprint()
        record = proof.owner_switch.record
        proof.owner_switch.record = dict(record, far_default=dict(record['far_default'], target=0))
        self.assertNotEqual(proof.fingerprint(), before)


FAR_CALLEE = 0x08004000
# A typed-data owner whose switch default is out of a narrow branch's reach: agbcc guards the
# dispatch with `bls dispatch; bl default` (a far jump), as 080B0E78 does.
FAR_SWITCH = data_calls.HEADER + """extern void func_08004000(u16 value, u16 *out);
#define C4(n) func_08004000(n, buffer); func_08004000(n + 1, buffer); \\
    func_08004000(n + 2, buffer); func_08004000(n + 3, buffer);
#define C16(n) C4(n) C4(n + 4) C4(n + 8) C4(n + 12)
#define C64(n) C16(n) C16(n + 16) C16(n + 32) C16(n + 48)
u32 func_08000200(u32 phase%(parameters)s)
{
    u16 buffer[4];
%(before)s
    switch (phase) {
    case 0:
        C64(1) C64(70) C64(140) C64(210)
        return buffer[0];
    case 1:
        data_02000000[0] = 5;
        return 1;
    case 2:
        func_08004000(2, buffer);
        return buffer[3];
    case 3:
        return 7;
    case 4:
        data_02000000[1] = 3;
        return 2;
    }
    return 0;
}
"""


def build_far(root, source):
    """data_calls.build for an owner too large for its callee at 0x08000400: the callee sits at FAR_CALLEE."""
    import argparse
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build'):
        (root / name).mkdir(parents=True, exist_ok=True)
    work = root / 'build'
    (work / 'callee.s').write_text('.syntax unified\n.arch armv4t\n.thumb\n.text\n.global callee, callee_end\n'
                                   f'callee:\n{data_calls.STORES}\ncallee_end:\n')
    for command in (
            [match.DEFAULT_AS, '-mthumb-interwork', str(work / 'callee.s'), '-o', str(work / 'callee.o')],
            [match.DEFAULT_LD, f'-Ttext=0x{FAR_CALLEE:08X}', '-e', 'callee', str(work / 'callee.o'),
             '-o', str(work / 'callee.elf')],
            [match.DEFAULT_OBJCOPY, '-O', 'binary', '--only-section=.text', str(work / 'callee.elf'),
             str(work / 'callee.bin')]):
        subprocess.run(command, check=True, capture_output=True)
    code = (work / 'callee.bin').read_bytes()
    rom = bytearray(FAR_CALLEE - match.ROM_BASE + 0x100)
    rom[FAR_CALLEE - match.ROM_BASE:FAR_CALLEE - match.ROM_BASE + len(code)] = code
    entries = [{'rom': f'0x{FAR_CALLEE:08X}', 'end': f'0x{FAR_CALLEE + len(code):08X}', 'mode': 'thumb'}]
    (root / 'src/08000200.c').write_text(source)
    (root / 'include/types.h').write_text('/* fixture */\n')
    objects = json.dumps(data_calls.OBJECTS).encode()
    (root / 'config/data_symbols.json').write_bytes(objects)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, data_calls.A, 'src/08000200.c')
        symbol, _ = match.function_record(original, 'func_08000200', data_calls.A, True)
        entries.insert(0, {'rom': f'0x{data_calls.A:08X}', 'end': f'0x{data_calls.A + symbol["size"]:08X}',
                           'mode': 'thumb'})
        mapping = json.dumps(entries).encode()
        body, _, _ = match.link_calls(runner, workspace, args, original, data_calls.A, mapping, len(rom),
                                      bytes(rom), objects, {}, {}, allow_switch_data=True)
    assert data_calls.A + len(body) <= FAR_CALLEE
    rom[data_calls.A - match.ROM_BASE:data_calls.A - match.ROM_BASE + len(body)] = body
    (root / 'config/functions.json').write_bytes(mapping)
    (root / 'symbols/functions.txt').write_text(''.join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    (root / 'baserom.bin').write_bytes(bytes(rom))
    return root


@unittest.skipUnless(data_calls.tools_present(), "fixed compiler and ARM tools required")
class NativeFarDefaultTests(unittest.TestCase):
    """match.py's default path on compiled owners whose switch default agbcc reaches with a far BL."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='owner_switch_far_', dir=scratch)
        cls.runs = {}
        for name, values in (('far', dict(parameters='', before='')),
                             ('far pool', dict(parameters=', u16 *out', before='\n    out[0] = 0x1234;\n'))):
            root = build_far(Path(cls.temporary.name) / name.replace(' ', '-'), FAR_SWITCH % values)
            cls.runs[name] = (root, *data_calls.run(root))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, report):
        root = self.runs[name][0]
        with patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')):
            return evidence.report_matches(report, root, data_calls.A)

    def test_agbcc_guards_with_a_far_bl(self):
        import owner_admission_profile as owner
        for name in self.runs:
            with self.subTest(name=name):
                root = self.runs[name][0]
                rom = (root / 'baserom.bin').read_bytes()
                mapping = (root / 'config/functions.json').read_bytes()
                end = int(json.loads(mapping)[0]['end'], 16)
                data = rom[data_calls.A - match.ROM_BASE:end - match.ROM_BASE]
                switch, = owner.refine(data, data_calls.A, mapping)['word_switches']
                self.assertEqual(switch['dispatch'] - switch['comparison'], 8)
                self.assertEqual('pool_policy' in switch, name == 'far pool')

    def test_each_owner_matches_reports_and_replays(self):
        for name in self.runs:
            with self.subTest(name=name):
                _, code, output, report = self.runs[name]
                self.assertEqual(code, 0, output)
                self.assertIn('verdict MATCH - byte identical', output)
                self.assertEqual(data_calls.verification(report), data_buffer.SCHEMA)
                line, = [line for line in report.splitlines() if line.startswith(owner_switch.LINE)]
                self.assertIn('far default arm (' + owner_switch.FAR_DEFAULT_NAME + ')', line)
                self.assertEqual('literal pool (' + pool.NAME + ')' in line, name == 'far pool')
                self.assertTrue(self.replays(name, report))
                with patch.object(owner_switch.FAR_DEFAULT, 'enabled', False):
                    self.assertFalse(self.replays(name, report))

    def test_kit_main_refuses_each_owner_at_the_arm(self):
        root = self.runs['far'][0]
        with patch.object(owner_switch.FAR_DEFAULT, 'enabled', False), \
                patch.dict(os.environ, FFTA_ROM=str(root / 'baserom.bin')), \
                patch.object(sys, 'argv', ['match.py', '--root', str(root), '--no-write', '0x08000200']), \
                contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as stop:
            match.main()
        self.assertIn('owner-switch data-buffer proof: owner switch excludes local BL control', str(stop.exception.code))

    def test_a_tampered_arm_line_fails(self):
        lines = self.runs['far'][3].splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith(owner_switch.LINE))
        for change, edited in (('target', re.sub(r'to 0x([0-9A-F]{8})', 'to 0x08000200', lines[at])),
                               ('removed', lines[at][:lines[at].index('; far default arm')])):
            with self.subTest(change=change):
                self.assertFalse(self.replays('far', '\n'.join(lines[:at] + [edited] + lines[at + 1:]) + '\n'))


if __name__ == '__main__':
    unittest.main()
