"""Fixed hardware addresses written as numbers in a restoring owner.

A source may name a VRAM, palette, OAM or I/O address as a plain number, such
as `(u16 *)0x0600B000 + n * 0x80`; the compiler folds it into one pool word
with no relocation, and a data symbol for it is a different source (0806B6D0's
0x0600AE00). Under the optional-runtime schema of restoring-owner-runtime-v1
an untyped reached word in [0x04000000,0x08000000) is now recorded as a
numeric hardware word, the default path's class
(`reached-numeric-hardware-literals-v1`); a word with a load that may reach
CpuSet's r2 is left to the copy controls, and RAM and ROM words keep needing a
type. The fixtures are assembled, so each shape is exact.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_cpuset_fill_profile as cpuset
import match
import report_fixtures
import named_data_buffer_profile as buffers
import match_evidence
import owner_admission_profile as owner
import owner_copy_calls as copy_calls
import test_restoring_owner_optional_runtime as base

A = base.A
COVERAGE = 'exact typed object/function coverage'
OBJECTS = (b'{"data_03002818":"0x03002818","data_03003860":"0x03003860",'
           b'"data_0600B000":"0x0600B000"}')
VRAM = 0x0600AE00
# A read and a write through one pool word: 0x0600AE00 is ((u16 *)0x0600B000 - 0x100).
ACCESS = ['ldr r0, .Lhw', 'ldrh r1, [r0]', 'adds r4, r4, r1', 'strh r4, [r0, #2]']
HARDWARE = ['.Lhw:', f'.word 0x{VRAM:08X}']
# test_owner_cpuset_copy_control's 08078818 shape: 0x04000080 only ever CpuSet's r2.
SOURCE = ['ldr r0, .Lstate', 'ldr r0, [r0]', 'adds r0, #0x28', 'ldr r1, .Ldest']
COPY = SOURCE + ['ldr r5, .Lcontrol', 'adds r2, r5, #0', 'bl func_0814186C']
COPY_POOL = ['.Lstate:', '.word data_03002818', '.Ldest:', '.word data_03003860',
             '.Lcontrol:', '.word 0x04000080']
# A CpuSet call whose control is computed: the owner calls CpuSet, no pool word is its r2.
COMPUTED = SOURCE + ['movs r2, #0x80', 'lsls r2, r2, #2', 'bl func_0814186C']
LINES = '* numeric hardware literal'


def pc_loads(instructions, register):
    """Owner offsets of the PC-relative loads into ``register``."""
    return [item.address - A for item in instructions
            if item.mnemonic == 'ldr' and item.op_str.startswith(f'{register}, [pc')]


def record(rows):
    return dict(schema=owner.NUMERIC_HARDWARE_SCHEMA, words=rows, contract=owner.NUMERIC_HARDWARE_CONTRACT)


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class NumericHardwareTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='owner_numeric_hardware_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle=ACCESS, pool=HARDWARE, *, align=None, **options):
        for pad in range(2):
            directory = self.root / f'f{len(list(self.root.iterdir()))}'
            directory.mkdir()
            fixture = base.Fixture(directory, base.owner_assembly(pad=pad, middle=middle, pool=pool, **options),
                                   division=options.get('division', False))
            if align is None or fixture.size % 4 == align:
                break
        else:
            raise AssertionError('no fixture size has the requested alignment')
        fixture.objects = OBJECTS
        start = cpuset.ADDRESS - match.ROM_BASE
        fixture.rom[start:start + len(cpuset.WRAPPER)] = cpuset.WRAPPER
        fixture.rows.append(dict(rom=f'0x{cpuset.ADDRESS:08X}', end=f'0x{cpuset.ADDRESS + 4:08X}',
                                 mode='thumb', instrs=2))
        fixture.mapping = json.dumps(fixture.rows).encode()
        return fixture.link()

    def admitted(self, middle=ACCESS, pool=HARDWARE, **options):
        fixture = self.fixture(middle, pool, **options)
        manifest, instructions = fixture.verify()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        return fixture, manifest, instructions

    def refused(self, message, middle=ACCESS, pool=HARDWARE, **options):
        with self.assertRaisesRegex(ValueError, message):
            self.fixture(middle, pool, **options).verify()

    def word(self, manifest, value):
        [row] = [row for row in manifest['proof']['partition']['words'] if row['value'] == value]
        return row['address'] - A

    def test_window_words_are_recorded_replayed_and_reported(self):
        for value in (0x04000000, 0x04000008, 0x040000D4, 0x04000200, 0x05000200, VRAM, 0x0600B000,
                      0x07000000, 0x07FFFFFC, 0x07FFFFFF):
            with self.subTest(value=hex(value)):
                fixture, manifest, instructions = self.admitted(pool=['.Lhw:', f'.word 0x{value:08X}'])
                word, [load] = self.word(manifest, value), pc_loads(instructions, 'r0')
                self.assertEqual(manifest['proof']['numeric_hardware_words'], record([[word, value, [load]]]))
                self.assertEqual(fixture.bindings['data'], [])
                self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
                report = fixture.report(manifest, len(instructions))
                self.assertEqual([line for line in report.splitlines() if line.startswith(LINES)], [
                    f'* numeric hardware literal premises: {owner.NUMERIC_HARDWARE_CONTRACT}',
                    f'* numeric hardware literal: word +0x{word:X} = 0x{value:08X}, loaded at +0x{load:X}'])
                self.assertTrue(owner.selected(report))
                self.assertEqual(owner.selector_for_report(report), owner.SELECTOR)

    def test_every_load_of_a_word_is_recorded(self):
        middle = ACCESS + ['ldr r1, .Lhw', 'ldrh r1, [r1, #4]', 'adds r4, r4, r1']
        fixture, manifest, instructions = self.admitted(middle)
        loads = pc_loads(instructions, 'r0') + pc_loads(instructions, 'r1')
        self.assertEqual(manifest['proof']['numeric_hardware_words']['words'],
                         [[self.word(manifest, VRAM), VRAM, sorted(loads)]])
        report = fixture.report(manifest, len(instructions))
        self.assertIn(', '.join(f'+0x{site:X}' for site in sorted(loads)), report)

    def test_ram_rom_and_mirror_words_still_need_typed_provenance(self):
        for value in (0x02000000, 0x0203FFFC, 0x03000020, 0x03007FF0, 0x03FFFFFC, 0x03FFFFFF,
                      0x08000000, 0x08100000, 0x08FFFFFC, 0x0A000000, 0x0C100000):
            with self.subTest(value=hex(value)):
                self.refused(COVERAGE, pool=['.Lhw:', f'.word 0x{value:08X}'])

    def test_only_complete_reached_pool_words_are_classed(self):
        # The partition admits only aligned words a PC-relative LDR reads whole; anything
        # else holding a hardware value is refused before any class is chosen.
        cases = {
            'adr then ldrh': (['adr r0, .Lhw', 'ldrh r1, [r0]', 'adds r4, r4, r1'], HARDWARE,
                              'structural inventory is not closed'),
            'adr then ldr': (['adr r0, .Lhw', 'ldr r1, [r0]', 'adds r4, r4, r1'], HARDWARE,
                             'structural inventory is not closed'),
            'unreached word': ([], HARDWARE, 'unowned complete-owner bytes'),
            'halfwords of the value': (ACCESS, ['.hword 0x0600', '.hword 0xAE00'] + HARDWARE,
                                       'unowned complete-owner bytes'),
        }
        for name, (middle, pool, message) in cases.items():
            with self.subTest(name=name):
                self.refused(message, middle, pool)

    def test_scalars_outside_the_typed_domain_stay_plain(self):
        for value in (0x00000080, 0x01FFFFFC, 0x09000000, 0x0E000000):
            with self.subTest(value=hex(value)):
                _, manifest, _ = self.admitted(pool=['.Lhw:', f'.word 0x{value:08X}'])
                self.assertNotIn('numeric_hardware_words', manifest['proof'])

    def test_a_named_hardware_word_stays_a_typed_object(self):
        for spelling, addend in (('data_0600B000', 0), ('data_0600B000+0x100', 0x100), ('data_0600B000-0x200', -0x200)):
            with self.subTest(spelling=spelling):
                fixture, manifest, _ = self.admitted(pool=['.Lhw:', f'.word {spelling}'])
                [binding] = fixture.bindings['data']
                self.assertEqual(binding[1:], ['data_0600B000', addend])
                self.assertNotIn('numeric_hardware_words', manifest['proof'])
        # A number inside or at a named object is still a number: no type is inferred from a value.
        for value in (0x0600B000, 0x0600B100):
            with self.subTest(value=hex(value)):
                fixture, manifest, _ = self.admitted(pool=['.Lhw:', f'.word 0x{value:08X}'])
                self.assertEqual(fixture.bindings['data'], [])
                self.assertEqual([row[1] for row in manifest['proof']['numeric_hardware_words']['words']], [value])

    def test_typed_and_numeric_words_of_one_owner_stay_disjoint(self):
        middle = ACCESS + ['ldr r1, .Lnamed', 'strh r4, [r1]', 'ldr r1, .Lstate', 'ldr r1, [r1]']
        pool = HARDWARE + ['.Lnamed:', '.word data_0600B000+0x40', '.Lstate:', '.word data_03002818']
        fixture, manifest, _ = self.admitted(middle, pool)
        typed = {row[0] for row in fixture.bindings['data']}
        numeric = {row[0] for row in manifest['proof']['numeric_hardware_words']['words']}
        self.assertEqual(len(typed), 2)
        self.assertEqual(numeric, {self.word(manifest, VRAM)})
        self.assertFalse(typed & numeric)

    def test_a_cpuset_copy_control_keeps_its_own_class(self):
        fixture, manifest, _ = self.admitted(COPY, COPY_POOL)
        [word] = manifest['proof']['cpuset_copy_controls']['words']
        self.assertEqual(word['control'], 0x04000080)
        self.assertNotIn('numeric_hardware_words', manifest['proof'])
        # With a numeric VRAM word beside it, each word has exactly one class.
        fixture, manifest, _ = self.admitted(COPY + ACCESS, COPY_POOL + HARDWARE)
        [word] = manifest['proof']['cpuset_copy_controls']['words']
        self.assertEqual(word['control'], 0x04000080)
        self.assertEqual([row[1] for row in manifest['proof']['numeric_hardware_words']['words']], [VRAM])
        # The copy record names typed objects only: a numeric destination is refused there.
        pool = COPY_POOL[:3] + [f'.word 0x{VRAM:08X}'] + COPY_POOL[4:]
        self.refused('CpuSet copy argument names an unbound literal', COPY, pool)

    def test_words_that_may_reach_cpuset_r2_are_never_numbers(self):
        cases = {
            # Fill, reserved-bit, zero-count and non-control words passed as CpuSet's r2.
            'fill control': (SOURCE + ['ldr r2, .Lhw', 'bl func_0814186C'], 0x05000080, COVERAGE),
            'reserved bit': (SOURCE + ['ldr r5, .Lhw', 'adds r2, r5, #0', 'bl func_0814186C'], 0x04400080, COVERAGE),
            'zero count': (SOURCE + ['ldr r5, .Lhw', 'adds r2, r5, #0', 'bl func_0814186C'], 0x04000000, COVERAGE),
            'VRAM value': (SOURCE + ['ldr r2, .Lhw', 'bl func_0814186C'], VRAM, COVERAGE),
            # Through mov and movs copies, and on one path only.
            'copies': (SOURCE + ['ldr r3, .Lhw', 'mov r12, r3', 'mov r5, r12', 'movs r2, r5',
                                 'bl func_0814186C'], 0x06000080, COVERAGE),
            'one path': (SOURCE + ['ldr r5, .Lhw', 'movs r2, #1', 'cmp r4, #0', 'beq .Lcall', 'adds r2, r5, #0',
                                   '.Lcall:', 'bl func_0814186C'], VRAM, COVERAGE),
            # A copy control that is also read as an address: the copy controls refuse it.
            'control and address': (SOURCE + ['ldr r5, .Lhw', 'ldrh r3, [r5]', 'adds r2, r5, #0',
                                              'bl func_0814186C'], 0x04000080, 'read other than by a register copy'),
        }
        for name, (middle, value, message) in cases.items():
            with self.subTest(name=name):
                pool = ['.Lstate:', '.word data_03002818', '.Ldest:', '.word data_03003860',
                        '.Lhw:', f'.word 0x{value:08X}']
                self.refused(message, middle, pool)
        # A word with one address load and one load that reaches r2 is not a number either.
        middle = ACCESS + SOURCE + ['ldr r2, .Lhw', 'bl func_0814186C']
        pool = HARDWARE + ['.Lstate:', '.word data_03002818', '.Ldest:', '.word data_03003860']
        self.refused(COVERAGE, middle, pool)

    def test_a_control_shaped_word_that_never_reaches_cpuset_is_a_number(self):
        # Formerly refused by the copy controls; I/O register words such as 0x04000080 are
        # numbers, as on the default path, unless a load of them may reach CpuSet's r2.
        cases = {
            'address only': COMPUTED + ACCESS,
            'loaded and unused': COMPUTED + ['ldr r5, .Lhw'],
            'arithmetic': SOURCE + ['ldr r5, .Lhw', 'adds r2, r5, #4', 'bl func_0814186C'],
            'other callee': SOURCE + ['ldr r5, .Lhw', 'adds r2, r5, #0', 'bl func_08011000'],
            'overwritten before the call': SOURCE + ['ldr r2, .Lhw', 'ldrh r3, [r2]', 'movs r2, #1',
                                                     'bl func_0814186C'],
            'after the call': COMPUTED + ['ldr r2, .Lhw', 'ldrh r3, [r2]'],
        }
        for name, middle in cases.items():
            with self.subTest(name=name):
                pool = ['.Lstate:', '.word data_03002818', '.Ldest:', '.word data_03003860',
                        '.Lhw:', '.word 0x04000080']
                _, manifest, _ = self.admitted(middle, pool)
                self.assertEqual([row[1] for row in manifest['proof']['numeric_hardware_words']['words']],
                                 [0x04000080])
                self.assertNotIn('cpuset_copy_controls', manifest['proof'])

    def test_a_number_passed_as_cpuset_source_or_destination_stays_a_number(self):
        # 0806B6D0 copies from (void *)0x0600B000 with a computed control: only r2 makes a control.
        for register, middle in (('r0', ['ldr r1, .Lstate', 'ldr r1, [r1]', 'ldr r0, .Lhw'] + COMPUTED[4:]),
                                 ('r1', SOURCE[:3] + ['ldr r1, .Lhw'] + COMPUTED[4:])):
            with self.subTest(register=register):
                _, manifest, _ = self.admitted(middle, ['.Lstate:', '.word data_03002818'] + HARDWARE)
                self.assertEqual([row[1] for row in manifest['proof']['numeric_hardware_words']['words']], [VRAM])

    def test_only_optional_schema_reports_print_the_lines(self):
        # The BIOS fill owners and the original schema keep the record in the evidence only.
        fixture, manifest, instructions = self.admitted()
        for profile in (owner.SCHEMA, buffers.BIOS_FILL_SCHEMA):
            with self.subTest(profile=profile):
                report = fixture.report(dict(manifest, profile=profile), len(instructions))
                self.assertIn('"numeric_hardware_words"', report)
                self.assertFalse([line for line in report.splitlines() if line.startswith(LINES)])

    def test_original_runtime_domain_is_unchanged(self):
        fixture = self.fixture(thunk=True, division=True, align=0)
        with self.assertRaisesRegex(ValueError, COVERAGE):
            fixture.verify()

    def test_the_class_alone_admits_the_word(self):
        fixture = self.fixture()
        fixture.verify()
        with patch.object(owner, 'numeric_hardware_words', return_value=[]), \
                self.assertRaisesRegex(ValueError, COVERAGE):
            fixture.verify()

    def test_owner_without_hardware_words_keeps_its_manifest_and_report(self):
        fixture, manifest, instructions = self.admitted([], [])
        self.assertNotIn('numeric_hardware_words', manifest['proof'])
        report = fixture.report(manifest, len(instructions))
        self.assertFalse([line for line in report.splitlines() if line.startswith(LINES)])

    def test_manifest_tampering_refused(self):
        fixture, manifest, _ = self.admitted(COPY + ACCESS, COPY_POOL + HARDWARE)
        word = self.word(manifest, VRAM)
        control = manifest['proof']['cpuset_copy_controls']['words'][0]['offset']
        typed = fixture.bindings['data'][0][0]
        for change in ('value', 'offset', 'loads', 'drop', 'extend', 'typed', 'control', 'empty', 'contract',
                       'schema'):
            forged = copy.deepcopy(manifest)
            rows = forged['proof']['numeric_hardware_words']
            if change == 'value':
                rows['words'][0][1] += 4
            elif change == 'offset':
                rows['words'][0][0] += 4
            elif change == 'loads':
                rows['words'][0][2] = []
            elif change == 'drop':
                del forged['proof']['numeric_hardware_words']
            elif change == 'extend':
                rows['words'].append([word + 4, VRAM + 4, rows['words'][0][2]])
            elif change == 'typed':
                rows['words'].insert(0, [typed, 0x03002818, [0]])
            elif change == 'control':
                rows['words'].insert(0, [control, 0x04000080, [0]])
            elif change == 'empty':
                rows['words'] = []
            elif change == 'contract':
                rows['contract'] = 'forged'
            else:
                rows['schema'] = 'forged'
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=forged)
        plain, manifest, _ = self.admitted([], [])
        forged = copy.deepcopy(manifest)
        forged['proof']['numeric_hardware_words'] = record([])
        with self.assertRaisesRegex(ValueError, 'manifest differs'):
            plain.verify(manifest=forged)


class ReachTests(unittest.TestCase):
    """reaches_cpuset_control over straight-line graphs: a may-analysis that never refuses."""

    def graph(self, code, calls=None, extra_edges=None):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        raw = b''.join(bytes.fromhex(word) for word in code)
        instructions = {item.address: item for item in decoder.disasm(raw, A)}
        sites = sorted(instructions)
        edges = {site: (sites[i + 1],) if i + 1 < len(sites) else () for i, site in enumerate(sites)}
        edges.update(extra_edges or {})
        return instructions, edges, {A + offset: target for offset, target in (calls or {}).items()}

    def reaches(self, code, calls, extra_edges=None, branches=()):
        instructions, edges, calls = self.graph(code, calls, extra_edges)
        return copy_calls.reaches_cpuset_control(instructions, edges, {A + offset for offset in branches},
                                                 calls, A)

    def test_direct_and_copied_values(self):
        # ldr r2, [pc]; bl CpuSet
        self.assertTrue(self.reaches(['004a', '00f0', '00f8'], {2: cpuset.ADDRESS}))
        # ldr r5, [pc]; adds r2, r5, #0; bl CpuSet
        self.assertTrue(self.reaches(['004d', '2a1c', '00f0', '00f8'], {4: cpuset.ADDRESS}))
        # ldr r6, [pc]; mov r8, r6; mov r2, r8; bl CpuSet
        self.assertTrue(self.reaches(['004e', 'b046', '4246', '00f0', '00f8'], {6: cpuset.ADDRESS}))

    def test_overwrites_calls_and_other_targets_end_the_value(self):
        # ldr r2, [pc]; movs r2, #1; bl CpuSet
        self.assertFalse(self.reaches(['004a', '0122', '00f0', '00f8'], {4: cpuset.ADDRESS}))
        # ldr r2, [pc]; bl other; bl CpuSet: the first call ends r0-r3
        self.assertFalse(self.reaches(['004a', '00f0', '00f8', '00f0', '00f8'],
                                      {2: 0x08011000, 6: cpuset.ADDRESS}))
        # ldr r5, [pc]; adds r2, r5, #4; bl CpuSet: arithmetic is not a copy
        self.assertFalse(self.reaches(['004d', '2a1d', '00f0', '00f8'], {4: cpuset.ADDRESS}))
        # ldr r2, [pc]; bl other
        self.assertFalse(self.reaches(['004a', '00f0', '00f8'], {2: 0x08011000}))

    def test_a_path_that_skips_the_copy_does_not_hide_one_that_takes_it(self):
        # ldr r5, [pc]; adds r2, r5, #0; bl CpuSet, with an edge from the load over the copy.
        # The skipping path reaches the call first; the copying path must still be seen.
        self.assertTrue(self.reaches(['004d', '2a1c', '00f0', '00f8'], {4: cpuset.ADDRESS},
                                     {A: (A + 2, A + 4)}))

    def test_a_local_bl_jump_keeps_the_argument_registers(self):
        # ldr r2, [pc]; bl (same-owner jump); bl CpuSet: a local BL edge writes only LR.
        self.assertTrue(self.reaches(['004a', '00f0', '00f8', '00f0', '00f8'], {6: cpuset.ADDRESS},
                                     branches=(2,)))
        # The same BL as a call to another function ends r2.
        self.assertFalse(self.reaches(['004a', '00f0', '00f8', '00f0', '00f8'],
                                      {2: 0x08011000, 6: cpuset.ADDRESS}))

    def test_saved_registers_survive_a_call_and_paths_join_by_union(self):
        # ldr r5, [pc]; bl other; adds r2, r5, #0; bl CpuSet
        self.assertTrue(self.reaches(['004d', '00f0', '00f8', '2a1c', '00f0', '00f8'],
                                     {2: 0x08011000, 8: cpuset.ADDRESS}))
        # ldr r5, [pc]; [0x2: jump over] movs r5, #1; adds r2, r5, #0; bl CpuSet
        self.assertTrue(self.reaches(['004d', '0125', '2a1c', '00f0', '00f8'], {6: cpuset.ADDRESS},
                                     {A: (A + 2, A + 4)}))


SOURCE_C = '''typedef unsigned short u16;
typedef unsigned int u32;
extern u32 func_08011000(u32 *values);
u32 func_08010000(u32 value, u32 slot) {
    u32 values[2];
    values[0] = value;
    values[1] = value + 1;
    value = func_08011000(values);
    ((u16 *)0x0600B000)[slot - 0x100] = value;
    value += *(u16 *)0x04000004;
    switch (value & 3) {
    case 0: value += 7; break;
    case 1: value -= 9; break;
    case 2: value ^= 5; break;
    default: value = 3; break;
    }
    return value;
}
'''


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which(match.DEFAULT_LD), 'the fixed compiler is required')
class CompiledNumericOwnerTests(unittest.TestCase):
    """A C owner naming VRAM and an I/O register as numbers: admitted, reported and replayed."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('TMPDIR', Path.cwd() / 'build/tests'))
        scratch.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix='owner_numeric_hardware_c_', dir=scratch)
        cls.addClassCleanup(temporary.cleanup)
        cls.root = Path(temporary.name)
        for name in ('src', 'config', 'symbols', 'include', 'build', 'docs/match'):
            (cls.root / name).mkdir(parents=True)
        (cls.root / 'src/08010000.c').write_text(SOURCE_C)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS, objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS)
        objects = b'{}\n'
        runner = match.Runner(match.DEFAULT_CC, 'Ubuntu', match.DEFAULT_WSL_PATH, root=cls.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(runner, workspace, args, cls.root, A, 'src/08010000.c')
            symbol, _ = match.function_record(image, 'func_08010000', A, True)
            rows = [dict(rom=f'0x{A:08X}', end=f'0x{A + symbol["size"]:08X}', mode='thumb', instrs=0),
                    dict(rom=f'0x{base.B:08X}', end=f'0x{base.B + len(base.LEAF):08X}', mode='thumb', instrs=4)]
            mapping = json.dumps(rows).encode()
            rom = bytearray(base.B + len(base.LEAF) - match.ROM_BASE)
            rom[base.B - match.ROM_BASE:] = base.LEAF
            data, _ = owner.object_bytes(runner, workspace, args, image, A, bytes(rom), mapping, objects, index=b'')
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        rows[0]['instrs'] = owner.refine(data, A, mapping)['instrs']
        (cls.root / 'config/functions.json').write_text(json.dumps(rows))
        (cls.root / 'symbols/functions.txt').write_text(''.join(
            f'{int(r["rom"], 16):08X} {int(r["end"], 16):08X} '
            f'{int(r["end"], 16) - int(r["rom"], 16)} {r["instrs"]} return\n' for r in rows))
        (cls.root / 'config/data_symbols.json').write_bytes(objects)
        (cls.root / 'baserom.bin').write_bytes(rom)
        # Class cleanups run even when this method raises, so FFTA_ROM never leaks to later tests.
        environment = patch.dict(os.environ, FFTA_ROM=str(cls.root / 'baserom.bin'))
        environment.start()
        cls.addClassCleanup(environment.stop)
        cls.result = owner.build(cls.root, A)
        cls.report = owner.render(A, cls.result)
        (cls.root / 'docs/match/08010000.md').write_text(cls.report)

    def test_numbers_admitted_and_report_replays(self):
        manifest = self.result[1]
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(manifest['bindings']['data'], [])
        words = manifest['proof']['numeric_hardware_words']['words']
        self.assertEqual(sorted(row[1] for row in words), [0x04000004, 0x0600AE00])
        lines = [line for line in self.report.splitlines() if line.startswith(LINES)]
        self.assertEqual(len(lines), 3)
        self.assertTrue(match_evidence.report_matches(report_fixtures.carried(self.report, self.root, A), self.root, A))

    def test_edited_or_dropped_lines_fail_replay(self):
        line = next(line for line in self.report.splitlines() if line.startswith(f'{LINES}: '))
        for forged in (self.report.replace(line + '\n', ''),
                       self.report.replace(line, line.replace('= 0x', '= 0x1')),
                       self.report.replace(owner.NUMERIC_HARDWARE_CONTRACT, 'forged')):
            with self.subTest(forged=forged != self.report):
                self.assertNotEqual(forged, self.report)
                self.assertFalse(report_fixtures.replay(forged, self.root, A))


if __name__ == '__main__':
    unittest.main()
