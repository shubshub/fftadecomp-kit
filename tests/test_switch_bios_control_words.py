"""BIOS CpuSet and CpuFastSet control words in u16 scalar switch pools (switch_bios_control_words)."""
import copy
import json
from pathlib import Path
import re
import struct
import sys
import unittest

from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import switch_bios_control_words as control_words
# Imported as a module for its assembler, descriptor() and issue(); its TestCase classes would run here again.
import test_switch_data_thunks as thunk_tests

BASE = thunk_tests.BASE
CPUSET, CPUFASTSET, ARCTAN2 = 0x0814186C, 0x08141868, 0x08141860
OTHER = BASE + 0x1000
OBJECT = 0x02002000
CONTROL = 0x04000080
ROM_SIZE = 0x142000
POLICY = 'bios-copy-control-words-v1'
PREMISE = '* switch control word premise: '
WORD = '* switch control word: '
WRAPPERS = {CPUSET: bytes.fromhex('0bdf7047'), CPUFASTSET: bytes.fromhex('0cdf7047'),
            ARCTAN2: bytes.fromhex('0adf7047')}
# The argument words the source's prototypes declare: OTHER takes two, and the wrappers three.
PROTOTYPES = {OTHER: 2, CPUSET: 3, CPUFASTSET: 3, ARCTAN2: 2}


def declaring(table):
    return lambda target: table.get(target)


def build(case0, *, value=CONTROL, case1=(('h', 0x2402),), uses=(('load', 'call'),), passes=(), words=False):
    """A guarded two-case switch (the u16-scalars-v1 fixed pool) whose case 0 runs `case0`.

    Case 0 starts with r0 and r1 loaded from a typed object; the control word
    `value` sits after the object. `uses` names the (load, call) label pairs the
    manifest records for it, and `passes` the (call label, argument words) of
    each next call a copy left in r2 reaches. With `words`, a u16 word (0x1234,
    label `u16`) and a wide word (0.5f, label `wide`) follow, recorded as such.
    """
    items = [('h', 0xB530),  # push {r4, r5, lr}
             ('label', 'comparison'), ('h', 0x2801), ('label', 'guard'), ('bhi', 'default'),
             ('label', 'dispatch'), ('h', 0x0080), ('ldr', 1, 'pointer'), ('h', 0x1840), ('h', 0x6800),
             ('h', 0x4687), ('align',), ('label', 'pointer'), ('address', 'table'),
             ('label', 'table'), ('address', 'case0'), ('address', 'case1'),
             ('label', 'case0'), ('ldr', 0, 'object'), ('ldr', 1, 'object'), *case0, ('b', 'done'),
             ('label', 'case1'), *case1, ('b', 'done'),
             ('label', 'default'), ('h', 0x2400),
             ('label', 'done'), ('h', 0xBC30), ('h', 0xBC01), ('h', 0x4700),  # pop {r4, r5}; pop {r0}; bx r0
             ('align',), ('label', 'object'), ('word', OBJECT), ('label', 'control'), ('word', value)]
    if words:
        items += [('label', 'u16'), ('word', 0x1234), ('label', 'wide'), ('word', 0x3F000000)]
    body, labels, calls = thunk_tests.assemble(items)
    manifest = {'calls': [[at, f'func_{target:08X}'] for at, target in calls],
                'switch': thunk_tests.descriptor(labels), 'data': [[labels['object'], 'g_object', 0]],
                'data_policy': 'complete-reachable-object-words-v1',
                'scalar_policy': 'complete-reachable-u16-scalar-words-v1', 'scalars': [],
                'control_word_policy': POLICY,
                'control_words': [[labels['control'], value, [[labels[load], labels[call]] for load, call in uses],
                                   [[labels[call], arguments] for call, arguments in passes]]]}
    if words:
        manifest.update(scalars=[[labels['u16'], 0x1234]], wide_scalar_policy='unmapped-bus-scalar-words-v1',
                        wide_scalars=[[labels['wide'], 0x3F000000]])
    return body, labels, manifest


def rom_image(body, wrappers=WRAPPERS):
    rom = bytearray(ROM_SIZE)
    rom[:len(body)] = body
    struct.pack_into('<H', rom, OTHER - BASE, 0x4770)
    for target, data in wrappers.items():
        rom[target - BASE:target - BASE + len(data)] = data
    return bytes(rom)


def mapping(body, wrappers=WRAPPERS):
    rows = [(BASE, len(body)), (OTHER, 2), *((target, len(data)) for target, data in wrappers.items())]
    return json.dumps([{'rom': f'0x{start:08X}', 'end': f'0x{start + size:08X}', 'mode': 'thumb'}
                       for start, size in rows]).encode()


def verify(fixture, manifest=None, *, wrappers=WRAPPERS, prototypes=PROTOTYPES):
    body, _, expected = fixture
    return match.verify_switches(bytes(body), BASE, rom_image(body, wrappers), mapping(body, wrappers),
                                 expected if manifest is None else manifest,
                                 data_mapping=json.dumps({'g_object': f'0x{OBJECT:08X}'}).encode(),
                                 declared=declaring(prototypes))


def walked(fixture, *, end=None, prototypes=PROTOTYPES, rows=WRAPPERS):
    """switch_bios_control_words.uses() alone on the fixture's case code, decoded up to `end` (the label
    `object` by default): what the walk admits whatever the switch verifier around it refuses. `rows` are
    the indexed rows span() gives."""
    body, labels, manifest = fixture
    engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    engine.detail = True
    start, stop = labels['case0'], labels[end or 'object']
    instructions = list(engine.disasm(bytes(body[start:stop]), BASE + start))
    calls = {BASE + at: int(name[5:], 16) for at, name in manifest['calls']}

    def span(target):
        if target not in rows:
            raise ValueError('not indexed')
        return rows[target]

    [[offset, value, *_]] = manifest['control_words']
    return control_words.uses(bytes(body), BASE, instructions, calls, span, offset, value, declaring(prototypes))


DIRECT = (('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', CPUSET))
# 0807478C and 080775A8: one load into callee-saved r5, copied to r2 for two CpuSet calls; an ordinary
# call follows with r2 still holding the word, and the epilogue's pop overwrites r5.
SAVED = (('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('label', 'call'), ('bl', CPUSET),
         ('ldr', 0, 'object'), ('ldr', 1, 'object'), ('h', 0x1C2A), ('label', 'call2'), ('bl', CPUSET),
         ('h', 0x2004), ('h', 0x2101), ('label', 'next'), ('bl', OTHER))
SAVED_USES = dict(uses=(('load', 'call'), ('load', 'call2')), passes=(('next', 2),))
# A second call of OTHER right after the CpuSet call, with the word left in r2.
NEXT = (('h', 0x2004), ('label', 'next'), ('bl', OTHER))


class AdmissionTests(unittest.TestCase):
    def test_a_direct_cpuset_control_word_binds(self):
        instructions, summary = verify(build(DIRECT))
        self.assertEqual(summary, evidence.CALL_SUMMARY)
        self.assertTrue(any(item.mnemonic == 'bl' for item in instructions))

    def test_a_callee_saved_copy_reaching_two_calls_binds(self):
        verify(build(SAVED, **SAVED_USES))

    def test_a_high_register_copy_binds(self):
        # mov r8, r5; mov r2, r8; the walk ends at the pop that restores r4 and r5; r8 is never written.
        case0 = (('label', 'load'), ('ldr', 5, 'control'), ('h', 0x46A8), ('h', 0x4642), ('label', 'call'),
                 ('bl', CPUSET), ('h', 0x4640), ('h', 0x2500), ('h', 0x2000))
        with self.assertRaisesRegex(ValueError, 'live at a return'):
            verify(build(case0))
        # Overwriting r8 too (mov r8, r4) ends every copy before the return.
        verify(build(case0 + (('h', 0x46A0),)))

    def test_a_cpufastset_fill_word_binds(self):
        case0 = (('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', CPUFASTSET))
        verify(build(case0, value=0x01000100))

    def test_a_word_reaching_both_routines_binds_when_whole_for_each(self):
        # 0x01000100 is a fill of 0x100 words for either routine.
        case0 = (('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('label', 'call'), ('bl', CPUSET),
                 ('h', 0x1C2A), ('label', 'call2'), ('bl', CPUFASTSET), ('h', 0x2500))
        verify(build(case0, value=0x01000100, uses=(('load', 'call'), ('load', 'call2'))))

    def test_a_copy_left_in_r2_may_reach_the_first_callee_and_the_return(self):
        # r2 still holds the word after the call. Unread, it may reach the first call after it, of a callee
        # declared with at most two argument words, and the function's own return (pop {r0}; bx r0 here),
        # which reads r0 only; it is live there whether or not that callee wrote it.
        for name, tail, passes in (('the return', (), ()), ('the first callee, then the return', NEXT, (('next', 2),)),
                                   ('overwritten after the first callee', NEXT + (('h', 0x2200),), (('next', 2),))):
            with self.subTest(name):
                verify(build(DIRECT + tail, passes=passes))
        for arguments in (0, 1):
            with self.subTest(arguments=arguments):
                verify(build(DIRECT + NEXT, passes=(('next', arguments),)),
                       prototypes=dict(PROTOTYPES) | {OTHER: arguments})
        # pop {r4, r5, pc} is a return too.
        self.assertEqual(walked(build(DIRECT + (('h', 0xBD30),))), [[[32, 34]], []])
        # Written before a call, r2 is that call's own argument, which need not be declared at all.
        verify(build(DIRECT + (('h', 0x2203),) + NEXT), prototypes=dict(PROTOTYPES) | {OTHER: 3})


class RefusalTests(unittest.TestCase):
    def refused(self, fixture, message, **options):
        with self.assertRaisesRegex(ValueError, message):
            verify(fixture, **options)

    def test_a_stored_word_is_refused(self):
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('h', 0x600A), ('label', 'call'),
                            ('bl', CPUSET))), 'only u16 literal values.*by str')

    def test_arithmetic_before_the_call_is_refused(self):
        for name, half in (('adds r2, r5, #1', 0x1C6A), ('lsls r2, r5, #0', 0x002A)):
            with self.subTest(name):
                self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', half), ('label', 'call'),
                                    ('bl', CPUSET))), 'only u16 literal values.*not as a register copy')
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('h', 0x3201), ('label', 'call'),
                            ('bl', CPUSET))), 'not as a register copy')

    def test_the_word_in_r0_or_r1_is_refused(self):
        for register in (0, 1, 3):
            with self.subTest(register=register):
                self.refused(build((('label', 'load'), ('ldr', register, 'control'), ('label', 'call'),
                                    ('bl', CPUSET))), 'another argument')
        # In r2 and r1 at once.
        self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('h', 0x1C29),
                            ('label', 'call'), ('bl', CPUSET))), 'another argument')

    def test_a_wrapper_with_an_extra_instruction_is_refused(self):
        # swi 0x0B; nop; bx lr, indexed as one six-byte row.
        self.refused(build(DIRECT), 'not the indexed CpuSet or CpuFastSet wrapper',
                     wrappers=dict(WRAPPERS) | {CPUSET: bytes.fromhex('0bdfc0467047')})

    def test_an_unknown_swi_is_refused(self):
        self.refused(build(DIRECT), 'not the indexed CpuSet', wrappers=dict(WRAPPERS) | {
            CPUSET: bytes.fromhex('0ddf7047')})
        # A real wrapper of another routine (ArcTan2, SWI 0x0A) takes no control word.
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', ARCTAN2))),
                     'not the indexed CpuSet')
        # An ordinary function.
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', OTHER))),
                     'not the indexed CpuSet')

    def test_reserved_bits_are_refused(self):
        for value in (0x04200080, 0x08000080, 0x02000080):
            with self.subTest(value=hex(value)):
                self.refused(build(DIRECT, value=value), 'reserved bit')
        # Bit 26 is CpuSet's alone.
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', CPUFASTSET)),
                           value=0x04000080), 'reserved bit')

    def test_a_zero_count_is_refused(self):
        self.refused(build(DIRECT, value=0x04000000), 'count is zero')
        self.refused(build((('label', 'load'), ('ldr', 2, 'control'), ('label', 'call'), ('bl', CPUFASTSET)),
                           value=0x01000004), 'multiple of eight')

    def test_the_word_reaching_an_address_use_on_another_path_is_refused(self):
        # Case 1 loads the same word and reads memory through it.
        self.refused(build(DIRECT, case1=(('ldr', 3, 'control'), ('h', 0x6818))),
                     'only u16 literal values.*by ldr')
        # One load, a conditional branch around the call.
        self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', 0x2C00), ('bhi', 'skip'),
                            ('h', 0x1C2A), ('label', 'call'), ('bl', CPUSET), ('label', 'skip'))),
                     'conditional branch')

    def test_flags_set_by_a_copy_are_a_use(self):
        # adds r3, r5, #0 sets the flags from the word; r5 and r3 are then overwritten, and bhi reads them.
        case0 = SAVED[:5] + (('h', 0x1C2B), ('h', 0x4645), ('h', 0x680B), ('bhi', 'skip'), ('label', 'skip'))
        self.refused(build(case0), 'flags set from the control word are read')

    def test_a_copy_a_call_leaves_in_r2_is_a_use(self):
        # The call is not taken to write r2: any instruction that reads it after the call refuses, a register
        # copy included, and so does one after the first callee returns (it may return r2 unwritten).
        for name, tail in (('str r2, [r1]', (('h', 0x600A),)), ('adds r0, r2, #1', (('h', 0x1C50),)),
                           ('adds r4, r2, #0', (('h', 0x1C14), ('h', 0x600C))), ('adds r2, r2, #0', (('h', 0x1C12),)),
                           ('push {r2}', (('h', 0xB404), ('h', 0xBC04))), ('cmp r2, #0', (('h', 0x2A00),))):
            with self.subTest(name):
                self.refused(build(DIRECT + tail), f'left in r2 is read at 0x[0-9A-F]+ by {re.escape(name)}')
        with self.subTest('after the first callee'):
            self.refused(build(DIRECT + NEXT + (('h', 0x600A),), passes=(('next', 2),)),
                         r'left in r2 is read at 0x[0-9A-F]+ by str r2, \[r1\]')

    def test_a_copy_a_call_leaves_in_r2_is_live_at_a_conditional_branch(self):
        # A one-path walk cannot follow both successors, so a left r2 live at a conditional branch refuses,
        # before the first callee and after it.
        branch = (('h', 0x2000), ('bhi', 'skip'), ('label', 'skip'))
        self.refused(build(DIRECT + branch), 'live at a conditional branch')
        self.refused(build(DIRECT + NEXT + branch, passes=(('next', 2),)), 'live at a conditional branch')
        # Written first, it is not.
        verify(build(DIRECT + (('h', 0x2200),) + branch))

    def test_a_copy_a_call_leaves_in_r2_reaches_one_call_only(self):
        # The first callee may return with r2 unwritten, so a second call would receive the word.
        self.refused(build(DIRECT + NEXT + (('bl', OTHER),), passes=(('next', 2),)), 'reaches a second call')
        self.refused(build(SAVED + (('bl', OTHER),), **SAVED_USES), 'reaches a second call')
        # Written in between, r2 is the second call's own argument.
        verify(build(DIRECT + NEXT + (('h', 0x2200), ('bl', OTHER)), passes=(('next', 2),)))

    def test_a_copy_a_call_leaves_in_r2_is_live_at_a_pc_write_other_than_a_return(self):
        # mov pc, r0 is no return form; the walk refuses it with the word left in r2.
        with self.assertRaisesRegex(ValueError, 'live at a return or PC write'):
            walked(build(DIRECT + (('h', 0x4687),)))
        with self.assertRaisesRegex(ValueError, 'live at a return or PC write'):
            walked(build(DIRECT + NEXT + (('h', 0x4687),), passes=(('next', 2),)))

    def test_flags_a_call_leaves_reach_no_other_call_and_no_return(self):
        # adds r2, r5, #0 sets the flags from the word, and the wrapper call leaves them; mov r5, r8 ends
        # the copy in r5 without writing them.
        tainted = SAVED[:5] + (('h', 0x4645),)
        self.refused(build(tainted + (('label', 'next'), ('bl', OTHER))), 'flags set from the control word are live '
                     'at the call')
        self.refused(build(tainted), 'live at a return')
        # Written by movs, they are not.
        verify(build(tainted + (('h', 0x2004), ('label', 'next'), ('bl', OTHER)), passes=(('next', 2),)))

    def test_flags_a_call_leaves_are_a_use(self):
        # adds r2, r5, #0 sets the flags from the word; the call is not taken to write them, and r5 is
        # overwritten before bhi reads them.
        case0 = SAVED[:5] + (('ldr', 5, 'object'), ('bhi', 'skip'), ('label', 'skip'))
        self.refused(build(case0), 'flags set from the control word are read')

    def test_a_load_that_reaches_no_wrapper_is_refused(self):
        self.refused(build(DIRECT, case1=(('ldr', 3, 'control'), ('h', 0x2300))), 'reaches no CpuSet')

    def test_a_copy_live_at_the_return_is_refused(self):
        # r6 keeps the word past the call, and the epilogue restores only r4 and r5.
        self.refused(build((('label', 'load'), ('ldr', 6, 'control'), ('h', 0x1C32), ('label', 'call'),
                            ('bl', CPUSET))), 'live at a return')
        # Only what a call left in r2 may be live at the return: a fresh copy there refuses (movs r0, #0 ends
        # the flags' taint, mov r2, r5 copies the word into r2 after the call, mov r5, r8 ends r5).
        tail = (('h', 0x2000), ('h', 0x462A), ('h', 0x4645))
        with self.assertRaisesRegex(ValueError, 'live at a return'):
            walked(build(SAVED[:5] + tail + (('h', 0xBD30),)))
        # The same with r2 written again before the return is admitted.
        self.assertEqual(walked(build(SAVED[:5] + tail + (('h', 0x2200), ('h', 0xBD30)))), [[[32, 36]], []])

    def test_a_copy_in_r0_r1_or_r3_at_the_return_is_refused(self):
        # A return reads r0 (r0-r1 for a 64-bit result), so the word there would be the function's result;
        # only what a call left in r2 may be live at a return. movs r0, #0 ends the flags' taint, adds rN, r5, #0
        # copies the word after the call, and movs r5, #0 ends r5 and the flags that copy set.
        for register in (0, 1, 3):
            tail = (('h', 0x2000), ('h', 0x1C28 | register), ('h', 0x2500))
            with self.subTest(register=register):
                with self.assertRaisesRegex(ValueError, 'live at a return'):
                    walked(build(SAVED[:5] + tail + (('h', 0xBD30),)))
                if register:
                    # The fixture's own return, pop {r4, r5}; pop {r0}; bx r0, overwrites r0 first.
                    self.refused(build(SAVED[:5] + tail), 'only u16 literal values.*live at a return')
        # Without the copy, only the left r2 is live there: admitted.
        self.assertEqual(walked(build(SAVED[:5] + (('h', 0x2000), ('h', 0x2500), ('h', 0xBD30)))), [[[32, 36]], []])
        verify(build(SAVED[:5] + (('h', 0x2000), ('h', 0x2500))))

    def test_a_bx_that_is_no_return_is_left_to_the_switch_verifier(self):
        # The walk takes every bx rN for the function's return; the switch verifier's return provenance
        # refuses one that is not (lr was written by the call; r3 holds no return address).
        for name, half in (('bx lr', 0x4770), ('bx r3', 0x4718)):
            with self.subTest(name):
                self.assertEqual(walked(build(DIRECT + (('h', half),))), [[[32, 34]], []])
                with self.assertRaisesRegex(ValueError, 'non-leaf indirect control flow'):
                    verify(build(DIRECT + (('h', half),)))

    def test_a_transfer_that_reads_what_a_call_left_in_r2_is_refused(self):
        # The walk alone refuses each of them, before the switch verifier's own PC-write rules do.
        for name, half in (('bx r2', 0x4710), ('mov pc, r2', 0x4697), ('add pc, r2', 0x4497)):
            with self.subTest(name):
                with self.assertRaisesRegex(ValueError, f'left in r2 is read at 0x[0-9A-F]+ by {name}$'):
                    walked(build(DIRECT + (('h', half),)))
                with self.assertRaises(ValueError):
                    verify(build(DIRECT + (('h', half),)))
        # The same instruction with nothing left in r2: the walk ends at the call.
        self.assertEqual(walked(build(DIRECT + (('h', 0x2200), ('h', 0x4710)))), [[[32, 34]], []])

    def test_the_next_callee_must_be_declared_with_at_most_two_argument_words(self):
        fixture = build(DIRECT + NEXT, passes=(('next', 2),))
        verify(fixture)
        for name, prototypes, message in (
                ('three', {OTHER: 3}, r'does not declare func_08001000 with at most 2 argument words \(3 declared\)'),
                ('unknown', {OTHER: None}, r'does not declare func_08001000 with at most 2 argument words\)$'),
                ('undeclared', {}, 'does not declare func_08001000')):
            with self.subTest(name):
                self.refused(fixture, message, prototypes=prototypes)
        with self.subTest('no source'), self.assertRaisesRegex(ValueError, 'does not declare'):
            match.verify_switches(bytes(fixture[0]), BASE, rom_image(fixture[0]), mapping(fixture[0]), fixture[2],
                                  data_mapping=json.dumps({'g_object': f'0x{OBJECT:08X}'}).encode())
        # The wrapper itself takes three: a copy left in r2 is not passed to it again.
        self.refused(build(DIRECT + (('label', 'next'), ('bl', CPUSET))), 'does not declare func_0814186C')

    def test_the_kit_counts_a_bios_wrapper_or_call_thunk_whatever_its_prototype(self):
        # The larger of the prototype's count and the kit's own decides. The kit counts r0-r3 for a BIOS SWI
        # wrapper and a call thunk, so a source that declares one with two argument words is still refused.
        kit = (r'the kit counts 4 argument words for func_{:08X}, a BIOS SWI wrapper or call thunk, whatever the '
               r'source declares \(2 declared\)')
        for name, target in (('CpuFastSet', CPUFASTSET), ('CpuSet', CPUSET), ('ArcTan2', ARCTAN2)):
            with self.subTest(name):
                self.refused(build(DIRECT + (('label', 'next'), ('bl', target))), kit.format(target),
                             prototypes=dict(PROTOTYPES) | {target: 2})
        with self.subTest('a table address holding other bytes'):
            self.refused(build(DIRECT + (('label', 'next'), ('bl', CPUFASTSET))), kit.format(CPUFASTSET),
                         prototypes=dict(PROTOTYPES) | {CPUFASTSET: 2},
                         wrappers=dict(WRAPPERS) | {CPUFASTSET: bytes.fromhex('00207047')})
        # Rows outside the wrapper table: an SWI wrapper (ObjAffineSet's swi 0x0F; bx lr reads r2 and r3) and
        # call thunks (bx r3 and bx r2, each with mov r8, r8).
        fixture = build(DIRECT + NEXT, passes=(('next', 2),))
        for name, row in (('swi 0x0F; bx lr', '0fdf7047'), ('bx r3', '1847c046'), ('bx r2', '1047c046')):
            with self.subTest(name), self.assertRaisesRegex(ValueError, kit.format(OTHER)):
                walked(fixture, rows=dict(WRAPPERS) | {OTHER: bytes.fromhex(row)})
        # An ordinary callee keeps its prototype's count; bx lr at its entry is a return, not a thunk.
        for row in ('7047', '00207047', None):
            rows = dict(WRAPPERS) if row is None else dict(WRAPPERS) | {OTHER: bytes.fromhex(row)}
            with self.subTest(row=row):
                self.assertEqual(walked(fixture, rows=rows), [[[32, 34]], [[40, 2]]])

        def unindexed(target):
            raise ValueError('not indexed')
        # Every address of the table counts, indexed or not.
        for target in control_words.summaries.WRAPPERS:
            self.assertEqual(control_words.known_arguments(target, unindexed), 4)
        self.assertIsNone(control_words.known_arguments(OTHER, unindexed))
        self.assertIsNone(control_words.known_arguments(OTHER, lambda target: b''))

    def test_a_copy_into_r12_is_refused(self):
        # mov ip, r5 copies the word into r12, which a call veneer may change; mov ip, r4 then overwrites it.
        self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', 0x46AC), ('h', 0x46A4),
                            ('h', 0x1C2A), ('label', 'call'), ('bl', CPUSET))), 'by mov ip, r5, not as a register copy')

    def test_flags_read_by_adcs_or_sbcs_are_a_use(self):
        for name, half in (('adcs r0, r0', 0x4140), ('sbcs r0, r0', 0x4180)):
            with self.subTest(name):
                self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('h', half),
                                    ('label', 'call'), ('bl', CPUSET))), 'flags set from the control word are read')

    def test_flags_set_again_before_a_second_call_are_its_own(self):
        # adds r2, r5, #0 sets the flags before each call; after the second, r5 is overwritten and bhi reads
        # the flags the second copy set, which that call left in place.
        self.refused(build((('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('label', 'call'),
                            ('bl', CPUSET), ('h', 0x1C2A), ('label', 'call2'), ('bl', CPUSET), ('ldr', 5, 'object'),
                            ('bhi', 'skip'), ('label', 'skip')), uses=(('load', 'call'), ('load', 'call2'))),
                     'flags set from the control word are read')

    def test_a_word_reaching_both_routines_is_whole_for_each(self):
        # 0x04000080 sets bit 26, CpuSet's 32-bit flag, which is reserved for CpuFastSet.
        case0 = (('label', 'load'), ('ldr', 5, 'control'), ('h', 0x1C2A), ('label', 'call'), ('bl', CPUSET),
                 ('h', 0x1C2A), ('label', 'call2'), ('bl', CPUFASTSET), ('h', 0x2500))
        self.refused(build(case0, uses=(('load', 'call'), ('load', 'call2'))), 'reserved bit')

    def test_a_copy_live_past_the_verified_code_is_refused(self):
        # The decoded code ends right after the call while r5 still holds the word.
        with self.assertRaisesRegex(ValueError, 'live past the verified straight-line code'):
            walked(build(SAVED[:5] + (('label', 'end'),)), end='end')

    def test_an_unindexed_wrapper_target_is_no_wrapper(self):
        def span(target):
            raise ValueError('no complete unique index row')
        self.assertFalse(control_words.wrapper(CPUSET, span))
        self.assertTrue(control_words.wrapper(CPUSET, WRAPPERS.get))


class ManifestTests(unittest.TestCase):
    def test_the_marker_and_records_are_exact(self):
        body, labels, manifest = build(SAVED, **SAVED_USES)
        verify((body, labels, manifest))
        [[offset, value, used, passed]] = manifest['control_words']
        for name, bad, message in (
                ('marker', dict(manifest, control_word_policy='other'), 'canonical policy marker'),
                ('no marker', {k: v for k, v in manifest.items() if k != 'control_word_policy'},
                 'invalid switch manifest'),
                ('neither', {k: v for k, v in manifest.items() if k not in ('control_word_policy', 'control_words')},
                 'nonempty scalar manifest|coverage'),
                ('as u16', dict({k: v for k, v in manifest.items() if k not in ('control_word_policy', 'control_words')},
                                scalars=[[labels['control'], CONTROL]]), 'exact nonoverlapping values'),
                ('empty', dict(manifest, control_words=[]), 'finite nonempty'),
                ('one call', dict(manifest, control_words=[[offset, value, used[:1], passed]]), 'coverage'),
                ('value', dict(manifest, control_words=[[offset, value + 1, used, passed]]), 'exact aligned'),
                ('object', dict(manifest, control_words=[[labels['object'], OBJECT, used, passed]]), 'coverage'),
                ('twice', dict(manifest, control_words=manifest['control_words'] * 2), 'unique ordered'),
                ('three fields', dict(manifest, control_words=[[offset, value, used]]), 'unique ordered'),
                ('no next call', dict(manifest, control_words=[[offset, value, used, []]]), 'coverage'),
                ('arguments', dict(manifest, control_words=[[offset, value, used, [[passed[0][0], 1]]]]),
                 'coverage'),
                ('three arguments', dict(manifest, control_words=[[offset, value, used, [[passed[0][0], 3]]]]),
                 'unique ordered'),
                ('next call twice', dict(manifest, control_words=[[offset, value, used, passed * 2]]),
                 'unique ordered'),
                ('a call on the word', dict(manifest, calls=[*manifest['calls'], [offset, f'func_{OTHER:08X}']]),
                 'overlapping switch manifest bindings')):
            with self.subTest(name), self.assertRaisesRegex(ValueError, message):
                verify((body, labels, manifest), bad)

    def test_u16_and_wide_words_keep_their_own_records(self):
        body, labels, manifest = build(DIRECT, case1=(('ldr', 4, 'u16'), ('ldr', 3, 'wide')), words=True)
        verify((body, labels, manifest))
        # Neither may be recorded as a control word, nor the control word as either.
        for name, bad in (
                ('u16 as control', dict(manifest, scalars=[], control_words=[
                    *manifest['control_words'], [labels['u16'], 0x1234, [[labels['load'], labels['call']]], []]])),
                ('control as wide', dict(manifest, control_words=[], wide_scalars=[
                    [labels['control'], CONTROL], *manifest['wide_scalars']]))):
            with self.subTest(name), self.assertRaises(ValueError):
                verify((body, labels, manifest), bad)
        # Without the control word, the existing policies refuse the function exactly as before.
        plain = {k: v for k, v in manifest.items() if k not in ('control_word_policy', 'control_words')}
        with self.assertRaisesRegex(ValueError, 'coverage'):
            verify((body, labels, manifest), plain)


SOURCE = """extern unsigned char data_02000100[];
extern unsigned short data_02000200[];
extern void func_0814186C(const void *source, void *destination, unsigned control);
extern unsigned char func_08000400(void);

void func_08000000(void *unused, unsigned char *state)
{
    switch (*state) {
    case 0:
        func_0814186C(data_02000100, data_02000200, 0x04000080);
        *state = 3;
        break;
    case 1:
        data_02000100[0] = 0;
        *state = 5;
        break;
    case 2:
        if (func_08000400() != 9)
            break;
        *state = 4;
        break;
    case 3:
        *state = 1;
        break;
    case 4:
        *state = 2;
        break;
    }
}
"""
COPY = "func_0814186C(data_02000100, data_02000200, 0x04000080);"
# Two copies with one control word, as in 0807478C.
TWICE = SOURCE.replace(COPY, COPY + "\n        func_0814186C(data_02000100 + 0x200, data_02000200 + 0x100, 0x04000080);")
# A call right after the copy, which r2 reaches still holding the word, as func_0808A604's in 080775A8:
# func_08000400 takes no argument, func_08000500 two.
NEXT_NONE = SOURCE.replace(COPY, COPY + "\n        func_08000400();")
NEXT_TWO = SOURCE.replace("extern unsigned char func_08000400(void);",
                          "extern unsigned char func_08000400(void);\n"
                          "extern void func_08000500(unsigned char index, unsigned char command);").replace(
    COPY, COPY + "\n        func_08000500(4, 1);")
# The CpuFastSet wrapper right after the copy, declared (wrongly) with two arguments: r2 reaches it still
# holding the word.
MISDECLARED = SOURCE.replace("extern unsigned char func_08000400(void);",
                             "extern unsigned char func_08000400(void);\n"
                             "extern void func_08141868(const void *source, void *destination);").replace(
    COPY, COPY + "\n        func_08141868(data_02000100, data_02000200);")
# No control word: the u16 word 0x1234 in its place.
PLAIN = SOURCE.replace("0x04000080", "0x1234")
OBJECTS = json.dumps({'data_02000100': '0x02000100', 'data_02000200': '0x02000200'}).encode()
ENTRIES = [(BASE + 0x400, 2), (BASE + 0x500, 2), (CPUSET, 4)]
ROM_WORDS = [(CPUSET, (0xDF0B, 0x4770))]


class ReportTests(unittest.TestCase):
    """Compiled sources: the report states the premise and each word, and replay requires both lines."""

    def issue(self, source, entries=ENTRIES, rom_words=ROM_WORDS):
        return thunk_tests.issue(self, source, OBJECTS, entries, evidence.SWITCH_U16_SCALAR_SELECTOR, link={},
                                 rom_words=rom_words)

    def test_a_source_that_declares_cpufastset_with_two_arguments_is_refused(self):
        # The prototype declares two argument words, but the kit counts r0-r3 for the CpuFastSet wrapper, and
        # the larger count decides: match.py refuses the function.
        with self.assertRaises(SystemExit) as caught:
            self.issue(MISDECLARED, entries=ENTRIES + [(CPUFASTSET, 4)],
                       rom_words=ROM_WORDS + [(CPUFASTSET, (0xDF0C, 0x4770))])
        self.assertRegex(str(caught.exception.code),
                         r'reaches the call at 0x0800[0-9A-F]{4}, and the kit counts 4 argument words for '
                         r'func_08141868, a BIOS SWI wrapper or call thunk, whatever the source declares '
                         r'\(2 declared\)')
        self.assertIn('compile failed', str(caught.exception.code))

    def test_issued_reports_state_each_word_and_replay(self):
        for name, source, calls, passed in (('one call', SOURCE, 1, None), ('two calls', TWICE, 2, None),
                                            ('a next call of no argument', NEXT_NONE, 1, (0x08000400, 0)),
                                            ('a next call of two arguments', NEXT_TWO, 1, (0x08000500, 2))):
            with self.subTest(name):
                root, report = self.issue(source)
                lines = report.splitlines()
                prefix = '* switch manifest: `'
                manifest = json.loads(next(line for line in lines if line.startswith(prefix))[len(prefix):-1])
                self.assertEqual(manifest['control_word_policy'], POLICY)
                [[_, value, uses, passes]] = manifest['control_words']
                self.assertEqual((value, len(uses)), (CONTROL, calls))
                self.assertEqual([arguments for _, arguments in passes], [] if passed is None else [passed[1]])
                premise = [line for line in lines if line.startswith(PREMISE)]
                words = [line for line in lines if line.startswith(WORD)]
                self.assertEqual(len(premise), 1, report)
                self.assertEqual(len(words), 1, report)
                self.assertIn('0x04000080 at 0x080', words[0])
                self.assertIn('CpuSet copy of 0x80 32-bit units, r2 of func_0814186C at ', words[0])
                if passed is None:
                    self.assertEqual(words[0].rsplit(' at ', 1)[1].count('0x'), calls)
                    self.assertNotIn('r2 left', words[0])
                else:
                    target, arguments = passed
                    self.assertRegex(words[0], f'; r2 left for func_{target:08X} at 0x080000[0-9A-F]{{2}}, declared '
                                               f'with {arguments} argument words$')
                self.assertTrue(evidence.report_matches(report, root, BASE))
                # The switch replay itself requires both lines, as the manifest derives them.
                self.assertTrue(evidence.switch_report_matches(lines, root, BASE, data_profile=True))
                for dropped in (premise[0], words[0]):
                    self.assertFalse(evidence.switch_report_matches([line for line in lines if line != dropped],
                                                                    root, BASE, data_profile=True))
                edits = [report.replace(premise[0] + '\n', ''), report.replace(words[0] + '\n', ''),
                         report.replace(words[0], words[0].replace('0x80 32-bit', '0x81 32-bit')),
                         report.replace(words[0] + '\n', words[0] + '\n' + words[0] + '\n')]
                if passed is not None:
                    # Replay reads the prototype from the bound source's translation unit, and only from it.
                    digest = evidence.source_fingerprint(root, BASE)
                    self.assertIn(f'func_{passed[0]:08X}(', match.addressed_translation_unit(root, BASE, digest))
                    with self.assertRaisesRegex(ValueError, 'snapshot differs'):
                        match.addressed_translation_unit(root, BASE, '0' * 64)
                    # The recorded argument words, in the manifest or on the line, are what the source declares.
                    line = next(line for line in lines if line.startswith(prefix))
                    other = 1 if passed[1] != 1 else 0
                    forged = evidence.switch_manifest(dict(manifest, control_words=[
                        [*manifest['control_words'][0][:3], [[passes[0][0], other]]]]))
                    edits += [report.replace(line, prefix + forged + '`'),
                              report.replace(words[0], words[0].replace(f'with {passed[1]} argument',
                                                                        f'with {other} argument'))]
                for edited in edits:
                    self.assertFalse(evidence.report_matches(edited, root, BASE))

    def test_a_report_without_a_control_word_carries_no_control_line(self):
        root, report = self.issue(PLAIN)
        lines = report.splitlines()
        self.assertFalse([line for line in lines if line.startswith(control_words.REPORT_PREFIX)], report)
        self.assertTrue(evidence.switch_report_matches(lines, root, BASE, data_profile=True))
        at = next(index for index, line in enumerate(lines) if line.startswith('* switch manifest: `')) + 1
        for injected in (f'{PREMISE}{control_words.PREMISE}',
                         f'{WORD}0x04000080 at 0x08000100, loaded at 0x08000020: CpuSet copy of 0x80 32-bit units'):
            with self.subTest(injected[:30]):
                forged = lines[:at] + [injected] + lines[at:]
                self.assertFalse(evidence.switch_report_matches(forged, root, BASE, data_profile=True))
                self.assertFalse(evidence.report_matches('\n'.join(forged) + '\n', root, BASE))


class LineTests(unittest.TestCase):
    """report_lines() decodes the routine, mode, unit and count of each word from the manifest."""

    def test_each_routine_mode_and_width_is_decoded(self):
        manifest = {'control_word_policy': POLICY,
                    'calls': [[0x20, f'func_{CPUSET:08X}'], [0x30, f'func_{CPUFASTSET:08X}'], [0x40, f'func_{OTHER:08X}']],
                    'control_words': [[0x80, 0x05000200, [[0x1C, 0x20]], []],
                                      [0x84, 0x00010100, [[0x1E, 0x20]], [[0x40, 1]]],
                                      [0x88, 0x01000100, [[0x2C, 0x30], [0x2E, 0x20]], []]]}
        self.assertEqual(control_words.report_lines(BASE, manifest), [
            f'{PREMISE}{control_words.PREMISE}',
            f'{WORD}0x05000200 at 0x08000080, loaded at 0x0800001C: CpuSet fill of 0x200 32-bit units, r2 of '
            'func_0814186C at 0x08000020',
            f'{WORD}0x00010100 at 0x08000084, loaded at 0x0800001E: CpuSet copy of 0x10100 16-bit units, r2 of '
            'func_0814186C at 0x08000020; r2 left for func_08001000 at 0x08000040, declared with 1 argument word',
            f'{WORD}0x01000100 at 0x08000088, loaded at 0x0800002C, 0x0800002E: CpuFastSet fill of 0x100 32-bit '
            'units, r2 of func_08141868 at 0x08000030; CpuSet fill of 0x100 16-bit units, r2 of func_0814186C at '
            '0x08000020'])
        self.assertEqual(control_words.report_lines(BASE, {'calls': []}), [])


class DeclarationTests(unittest.TestCase):
    """declarations() reads a callee's argument words from the file-scope prototypes, as the volatile
    checker does, and knows none it cannot read."""

    def declared(self, text, target=0x08000500):
        return control_words.declarations(lambda: text)(target)

    def test_prototypes(self):
        for text, expected in (
                ('extern void func_08000500(unsigned char index, unsigned char command);', 2),
                ('void func_08000500(void);', 0),
                ('extern int func_08000500(int a, unsigned *b, void *c);', 3),
                ('typedef unsigned char u8;\nextern void func_08000500(u8 index);', 1),
                ('extern void func_08000500();', None),
                ('extern void func_08000500(int index, ...);', None),
                ('extern void func_08000400(int a);', None),
                ('extern void func_08000500(int a);\nextern void func_08000500(int a, int b);', None),
                ('extern void func_08000500(struct pair value);', None),
                ('extern void func_08000500(int a) { /* unterminated', None)):
            with self.subTest(text):
                self.assertEqual(self.declared(text), expected)

    def test_the_text_is_read_once_and_only_when_asked(self):
        reads = []

        def text():
            reads.append(1)
            return 'void func_08000500(int a, int b);'
        declared = control_words.declarations(text)
        self.assertEqual(reads, [])
        self.assertEqual((declared(0x08000500), declared(0x08000400)), (2, None))
        self.assertEqual(reads, [1])

    def test_an_unreadable_text_declares_nothing(self):
        for error in (RuntimeError('cpp failed'), OSError('missing'), ValueError('snapshot differs')):
            with self.subTest(error=error):
                def text():
                    raise error
                self.assertIsNone(control_words.declarations(text)(0x08000500))


if __name__ == '__main__':
    unittest.main()
