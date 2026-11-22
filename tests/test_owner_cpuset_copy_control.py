"""A CpuSet copy control in the address domain, in a restoring owner (owner_copy_calls).

0x04000080 asks CpuSet for 0x80 32-bit units; as a PC word it lies in the typed
address domain, so the owner's typed coverage refused it as an unnamed address.
It is taken out of that coverage only when the owner CFG proves the word is
never anything but CpuSet's r2.  The fixtures are assembled, so each shape is
exact.
"""
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_cpuset_fill_profile as cpuset
import match
import owner_admission_profile as owner
import owner_copy_calls as copy_calls
import test_restoring_owner_optional_runtime as base

A = base.A
OBJECTS = b'{"data_03002818":"0x03002818","data_03003860":"0x03003860","data_04000080":"0x04000080"}'
POOL = ['.Lstate:', '.word data_03002818', '.Ldest:', '.word data_03003860', '.Lcontrol:', '.word 0x04000080']
# The 08078818 shape: source read from a typed object, destination a typed object,
# the control kept in r5 across an ordinary call and used twice.
SOURCE = ['ldr r0, .Lstate', 'ldr r0, [r0]', 'adds r0, #0x28', 'ldr r1, .Ldest']
COPY = SOURCE + ['ldr r5, .Lcontrol', 'adds r2, r5, #0', 'bl func_0814186C']
TWICE = COPY + ['mov r0, sp', 'bl func_08011000', 'ldr r0, .Lstate', 'ldr r0, [r0]',
                'movs r2, #0x80', 'lsls r2, r2, #2', 'adds r0, r0, r2', 'ldr r1, .Ldest',
                'adds r1, r1, r2', 'adds r2, r5, #0', 'bl func_0814186C']
COVERAGE = 'exact typed object/function coverage'


def loads(instructions, text):
    """Owner offsets of the instructions whose operands read exactly ``text``."""
    return [item.address - A for item in instructions if item.mnemonic == 'ldr' and item.op_str == text]


@unittest.skipUnless(shutil.which(match.DEFAULT_AS) and shutil.which(match.DEFAULT_LD),
                     'the fixed binutils are required')
class CopyControlTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='owner_copy_control_')
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def fixture(self, middle=COPY, pool=POOL, *, wrapper=cpuset.WRAPPER, row=4, align=None, **options):
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
        fixture.rom[start:start + len(wrapper)] = wrapper
        if row:
            fixture.rows.append(dict(rom=f'0x{cpuset.ADDRESS:08X}', end=f'0x{cpuset.ADDRESS + row:08X}',
                                     mode='thumb', instrs=row // 2))
        fixture.mapping = json.dumps(fixture.rows).encode()
        return fixture.link()

    def controls(self, middle=COPY, pool=POOL, **options):
        fixture = self.fixture(middle, pool, **options)
        manifest, instructions = fixture.verify()
        return fixture, manifest, instructions

    def refused(self, message, middle, pool=POOL, **options):
        with self.assertRaisesRegex(ValueError, message):
            self.fixture(middle, pool, **options).verify()

    def test_copy_control_admitted_and_recorded(self):
        fixture, manifest, instructions = self.controls()
        self.assertEqual(manifest['profile'], owner.OPTIONAL_SCHEMA)
        self.assertEqual(sorted(name for _, name, _ in fixture.bindings['data']),
                         ['data_03002818', 'data_03003860'])
        record = manifest['proof']['cpuset_copy_controls']
        self.assertEqual(record['schema'], copy_calls.CONTROL_SCHEMA)
        self.assertEqual(record['wrapper'][:2], [cpuset.ADDRESS, 4])
        self.assertFalse(record['object_extent_proved'])
        [word] = record['words']
        self.assertEqual((word['control'], word['unit_bytes'], word['units'], word['bytes']),
                         (0x04000080, 4, 0x80, 0x200))
        [call] = word['calls']
        [load] = loads(instructions, 'r0, [r0]')
        self.assertEqual(call['source'], {'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0x28})
        self.assertEqual(call['destination'], {'object': 'data_03003860', 'offset': 0})
        self.assertEqual(fixture.verify(manifest=manifest)[0], manifest)
        report = fixture.report(manifest, len(instructions))
        lines = [line for line in report.splitlines() if line.startswith('* CpuSet copy control')]
        self.assertEqual(lines, [f'* CpuSet copy control premises: {copy_calls.CONTROL_PREMISES}',
                                 f'* CpuSet copy control: word +0x{word["offset"]:X} = 0x04000080 '
                                 f'(128 x 4 = 512 bytes) at call +0x{call["site"]:X}: source '
                                 f'*(data_03002818+0x0)@+0x{load:X}+0x28, destination data_03003860+0x0; '
                                 'extent not proved'])
        self.assertTrue(owner.selected(report))
        self.assertEqual(owner.selector_for_report(report), owner.SELECTOR)

    def test_control_kept_across_an_ordinary_call_and_used_twice(self):
        _, manifest, instructions = self.controls(TWICE)
        [word] = manifest['proof']['cpuset_copy_controls']['words']
        first, second = loads(instructions, 'r0, [r0]')
        self.assertEqual([(call['source'], call['destination']) for call in word['calls']], [
            ({'loaded_from': 'data_03002818', 'field': 0, 'load': first, 'offset': 0x28},
             {'object': 'data_03003860', 'offset': 0}),
            ({'loaded_from': 'data_03002818', 'field': 0, 'load': second, 'offset': 0x200},
             {'object': 'data_03003860', 'offset': 0x200})])

    def test_loaded_provenance_names_its_load_across_a_call_and_a_store(self):
        # The pointer is read, then a call and a store may change data_03002818: the
        # record names the load that produced the value, not the object's later contents.
        middle = ['ldr r0, .Lstate', 'ldr r4, [r0]', 'mov r0, sp', 'bl func_08011000',
                  'movs r1, #0', 'ldr r0, .Lstate', 'str r1, [r0]',
                  'adds r0, r4, #0', 'adds r0, #0x28', 'ldr r1, .Ldest', 'ldr r5, .Lcontrol',
                  'adds r2, r5, #0', 'bl func_0814186C']
        fixture, manifest, instructions = self.controls(middle)
        [load] = loads(instructions, 'r4, [r0]')
        [call] = manifest['proof']['cpuset_copy_controls']['words'][0]['calls']
        self.assertEqual(call['source'], {'loaded_from': 'data_03002818', 'field': 0, 'load': load, 'offset': 0x28})
        report = fixture.report(manifest, len(instructions))
        self.assertIn(f'source *(data_03002818+0x0)@+0x{load:X}+0x28,', report)

    def test_loads_from_two_sites_join_to_unknown(self):
        middle = ['ldr r0, .Lstate', 'cmp r4, #0', 'beq .Lsecond', 'ldr r0, [r0]', 'b .Ljoin', '.Lsecond:',
                  'ldr r0, [r0]', '.Ljoin:', 'adds r0, #0x28', 'ldr r1, .Ldest', 'ldr r5, .Lcontrol',
                  'adds r2, r5, #0', 'bl func_0814186C']
        _, manifest, _ = self.controls(middle)
        [call] = manifest['proof']['cpuset_copy_controls']['words'][0]['calls']
        self.assertEqual(call['source'], {'unknown': True})

    def test_count_is_read_from_the_control(self):
        pool = POOL[:-1] + ['.word 0x04000010']
        _, manifest, _ = self.controls(pool=pool)
        [word] = manifest['proof']['cpuset_copy_controls']['words']
        self.assertEqual((word['units'], word['bytes']), (0x10, 0x40))

    def test_unknown_pointer_provenance_is_recorded_not_invented(self):
        middle = ['ldrb r0, [r5]', 'adds r1, r4, #0'] + COPY[4:]
        _, manifest, _ = self.controls(middle, POOL[-2:])
        [call] = manifest['proof']['cpuset_copy_controls']['words'][0]['calls']
        self.assertEqual((call['source'], call['destination']), ({'unknown': True}, {'unknown': True}))

    def test_without_the_rule_the_word_was_refused_as_an_address(self):
        # Fill, reserved-bit and zero-count words are not copy controls: coverage still refuses them.
        for control in ('0x05000080', '0x04400080', '0x04000000', '0x06000080'):
            with self.subTest(control=control):
                self.refused(COVERAGE, COPY, POOL[:-1] + [f'.word {control}'])

    def test_named_control_object_stays_a_typed_object(self):
        fixture, manifest, _ = self.controls(pool=POOL[:-1] + ['.word data_04000080'])
        self.assertIn('data_04000080', [name for _, name, _ in fixture.bindings['data']])
        self.assertNotIn('cpuset_copy_controls', manifest['proof'])

    def test_control_used_other_than_as_cpuset_r2_refused(self):
        load = SOURCE + ['ldr r5, .Lcontrol']
        cases = {
            'address': (load + ['ldr r3, [r5]', 'adds r2, r5, #0', 'bl func_0814186C'],
                        'read other than by a register copy'),
            'arithmetic': (load + ['adds r2, r5, #4', 'bl func_0814186C'], 'read other than by a register copy'),
            'compare': (load + ['cmp r5, #0', 'adds r2, r5, #0', 'bl func_0814186C'],
                        'read other than by a register copy'),
            'store': (load + ['str r5, [sp]', 'adds r2, r5, #0', 'bl func_0814186C'],
                      'read other than by a register copy'),
            'other argument': (load + ['adds r3, r5, #0', 'adds r2, r5, #0', 'bl func_0814186C'],
                               'other than as the CpuSet r2 control'),
            'source argument': (load + ['adds r0, r5, #0', 'adds r2, r5, #0', 'bl func_0814186C'],
                                'other than as the CpuSet r2 control'),
            'other callee': (load + ['adds r2, r5, #0', 'bl func_08011000'], 'other than as the CpuSet r2 control'),
            'flags': (load + ['adds r2, r5, #0', 'beq .Lnext', '.Lnext:', 'bl func_0814186C'],
                      'flags set from a CpuSet copy control are read'),
            'flags after the call': (COPY + ['beq .Lnext', '.Lnext:'], 'flags set from a CpuSet copy control are read'),
            'other argument on one path': (load + ['cmp r4, #0', 'beq .Lcall', 'adds r3, r5, #0', '.Lcall:',
                                                   'adds r2, r5, #0', 'bl func_0814186C'],
                                           'other than as the CpuSet r2 control'),
            'returned': (COPY + ['adds r3, r5, #0'], 'survives a return'),
            'left in r2': (COPY + ['adds r0, r2, #0'], 'read before it is rewritten'),
            'unused': (SOURCE + ['ldr r5, .Lcontrol', 'movs r2, #1', 'bl func_0814186C'], 'reaches no CpuSet call'),
            'one path': (load + ['adds r2, r5, #0', 'cmp r4, #0', 'beq .Lcall', 'movs r2, #1', '.Lcall:',
                                 'bl func_0814186C'], 'not r2 on every path'),
        }
        for name, (middle, message) in cases.items():
            with self.subTest(name=name):
                self.refused(message, middle)

    def test_wrapper_identity_required(self):
        self.refused('exact CpuSet SWI 0x0B wrapper', COPY, wrapper=bytes.fromhex('0cdf7047'))
        with self.assertRaises(ValueError):
            self.fixture(COPY, row=False).verify()
        # A row that is not exactly the four wrapper bytes does not index the wrapper.
        self.refused('exact unique nonoverlapping Thumb span', COPY, row=8)

    def test_original_runtime_domain_is_unchanged(self):
        # The original udiv-and-thunk domain keeps its records; the control still needs a name there.
        fixture = self.fixture(COPY, thunk=True, division=True, align=0)
        with self.assertRaisesRegex(ValueError, COVERAGE):
            fixture.verify()

    def test_manifest_tampering_refused(self):
        fixture, manifest, _ = self.controls()
        for change in ('control', 'bytes', 'source', 'destination', 'wrapper'):
            altered = copy.deepcopy(manifest)
            record = altered['proof']['cpuset_copy_controls']
            if change == 'control':
                record['words'][0]['control'] = 0x04000081
            elif change == 'bytes':
                record['words'][0]['bytes'] = 0x100
            elif change == 'source':
                record['words'][0]['calls'][0]['source'] = {'unknown': True}
            elif change == 'destination':
                record['words'][0]['calls'][0]['destination']['offset'] = 4
            else:
                record['wrapper'][2] = '0' * 64
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'manifest differs'):
                fixture.verify(manifest=altered)


class ArgumentFactTests(unittest.TestCase):
    """The must-analysis keeps only facts every path agrees on."""

    def graph(self, assembly):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        code = b''.join(bytes.fromhex(word) for word in assembly)
        instructions = {item.address: item for item in decoder.disasm(code, A)}
        sites = sorted(instructions)
        edges = {site: (sites[i + 1],) if i + 1 < len(sites) else () for i, site in enumerate(sites)}
        return instructions, edges, code

    def test_values_through_copies_shifts_and_adds(self):
        # movs r2,#0x80; lsls r2,r2,#2; adds r3,r2,#0; adds r3,#4; bx lr
        instructions, edges, code = self.graph(['8022', '9200', '131c', '0433', '7047'])
        facts = copy_calls.states(instructions, edges, A, set(), {}, code)
        self.assertEqual(facts[A + 8][match.ARM_REG_R0 + 3], 0x204)
        self.assertEqual(facts[A + 8][match.ARM_REG_R0 + 2], 0x200)

    def test_join_keeps_only_agreed_facts(self):
        # movs r0,#1; movs r1,#2; movs r1,#3; bx lr, with movs r1,#2 also jumping to bx lr
        instructions, edges, code = self.graph(['0120', '0221', '0321', '7047'])
        edges = dict(edges)
        edges[A + 2] = (A + 4, A + 6)
        facts = copy_calls.states(instructions, edges, A, set(), {}, code)
        self.assertEqual(facts[A + 6], {match.ARM_REG_R0: 1})

    def test_call_clobbers_arguments_and_keeps_saved_registers(self):
        # movs r0,#1; movs r4,#2; bl (call); bx lr
        instructions, edges, code = self.graph(['0120', '0224', '00f0', '00f8', '7047'])
        call = A + 4
        facts = copy_calls.states(instructions, edges, A, set(), {call: 0x08011000}, code)
        self.assertEqual(facts[A + 8], {match.ARM_REG_R0 + 4: 2})


if __name__ == '__main__':
    unittest.main()
