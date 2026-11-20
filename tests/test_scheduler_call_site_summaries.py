"""Per-site scheduler descriptor summaries in the ordinary named-data owner walk."""
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'tools'))
import match
import conditional_local_buffer_profile as local
import named_data_buffer_profile as named
import owner_admission_profile as owner
import scheduler_call_site_profile as profile
from test_scheduler_predicates import half, bl, fixture, A, B, R0, LOCAL, SAVED

S, POOL, DIRECT = profile.SCHEDULER, profile.POOL, profile.DIRECT
CALLBACK, OTHER_CALLBACK = 0x08001601, 0x08001701
MANAGER = 0x0200F430
SELECTOR = profile.SELECTOR


class Owner:
    """A small Thumb owner with labels, patched branches and a trailing literal pool."""

    def __init__(self, base=A):
        self.base, self.data, self.labels, self.calls = base, bytearray(), {}, {}
        self.branches, self.loads = [], []

    def here(self):
        return self.base + len(self.data)

    def label(self, name):
        self.labels[name] = self.here()

    def emit(self, *words):
        self.data += half(*words)

    def call(self, target, name=None):
        if name:
            self.label(name)
        self.calls[self.here()] = target
        self.data += bl(self.here(), target)

    def load(self, register, value):
        # ldr rN,[pc,#imm]: the offset is patched once the pool is placed.
        self.loads.append((self.here(), register, value))
        self.emit(0x4800 | register << 8)

    def branch(self, word, destination):
        self.branches.append((self.here(), word, destination))
        self.emit(word)

    def build(self):
        for site, word, destination in self.branches:
            offset = (self.labels[destination] - site - 4) // 2
            word |= offset & (0x7FF if word & 0xF800 == 0xE000 else 0xFF)
            struct.pack_into('<H', self.data, site - self.base, word)
        if len(self.data) % 4:
            self.emit(0)
        pool = {}
        for site, register, value in self.loads:
            if value not in pool:
                pool[value] = self.here()
                self.data += struct.pack('<I', value)
            displacement = pool[value] - ((site + 4) & ~3)
            struct.pack_into('<H', self.data, site - self.base, 0x4800 | register << 8 | displacement // 4)
        self.literals = {value: address - self.base for value, address in pool.items()}
        return bytes(self.data), dict(self.calls)


def scheduler_call(p, target=S, *, name=None, descriptor=0xAA00, callback=CALLBACK):
    # R0 callback literal, R1 size 8, R2 = descriptor, R3 parent 0.
    p.load(0, callback)
    p.emit(0x2108, descriptor, 0x2300)
    p.call(target, name)


def epilogue(p, frame, popped=0xBC10):
    p.emit(0xB000 | frame, popped, 0xBC02, 0x4708)


def two_sites(*, second=POOL, before=(), frame=7):
    p = Owner()
    p.emit(0xB510, 0xB080 | frame, *before)       # push {r4,lr}; sub sp,#4*frame
    scheduler_call(p, name='first')
    scheduler_call(p, second, name='second', callback=OTHER_CALLBACK)
    epilogue(p, frame)
    return p


def looped(*, alias=(), payload=False, frame=7):
    p = Owner()
    p.emit(0xB530, 0xB080 | frame, *alias, 0x2400)   # push {r4,r5,lr}; sub sp; [alias]; movs r4,#0
    if payload:
        p.emit(0xA807, 0x9001)                      # add r0,sp,#28; str r0,[sp,#4]
    p.label('header')
    scheduler_call(p, name='site')
    p.emit(0x3401, 0x2C03)                          # adds r4,#1; cmp r4,#3
    p.branch(0xDB00, 'header')                      # blt header
    epilogue(p, frame, 0xBC30)
    return p


def direct(*, descriptor=0xAB01, parent=(0x2200, 0x9200), frame=8, manager=None):
    # manager R0 = *data (ldr r0,=MANAGER; ldr r0,[r0]), callback R1, size R2,
    # descriptor R3, parent at [sp].
    p = Owner()
    p.emit(0xB500, 0xB080 | frame)
    if manager is None:
        p.load(0, MANAGER)
        p.emit(0x6800)
    else:
        manager(p)
    p.load(1, CALLBACK)
    p.emit(*parent, 0x2228, descriptor)
    p.call(DIRECT, 'site')
    p.emit(0xB000 | frame, 0xBC02, 0x4708)
    return p


def payload(*, store=0x9001, value=0xA807, frame=9, extra=()):
    # Descriptor at SP, payload words above it; store sets a descriptor word to the payload.
    p = Owner()
    p.emit(0xB500, 0xB080 | frame, value, store, *extra)
    scheduler_call(p, name='site')
    p.emit(0xB000 | frame, 0xBC02, 0x4708)
    return p


BODIES = {S: bytes(60), POOL: bytes(44), DIRECT: bytes(206)}


def bound(owner_program, *, policy=SELECTOR, callee=half(0x4770), pins=None):
    data, calls = owner_program.build()
    bodies = {A: data, B: callee, **BODIES}
    p = fixture(bodies, policy=policy)
    span = p.span
    runtimes = set(match.function_thunk.ALIASES.values())
    p.span = lambda a: half(0x4710) if a in runtimes else span(a)
    pins = pins or {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in BODIES.items()}
    with mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]):
        p.bind_root(data, A, calls)
    return p, data, calls


def verified(owner_program, **kw):
    p, data, calls = bound(owner_program, **kw)
    match.verify_leaf_instructions(data, A, True, calls, buffer_proof=p)
    return p


def observation(p, name, program):
    return p.observations[program.labels[name]]


class CallSiteSummaryTests(unittest.TestCase):
    def test_two_sites_through_two_entries_are_each_summarised(self):
        program = two_sites()
        p = verified(program)
        report = p.contract_manifest()
        self.assertEqual(report['schema'], profile.SCHEMA)
        self.assertEqual([o['site'] for o in report['observations']],
                         [program.labels['first'], program.labels['second']])
        self.assertEqual([o['scheduler_entry'] for o in report['observations']],
                         ['scheduler', 'pool-manager-wrapper'])
        for o in report['observations']:
            self.assertEqual((o['descriptor_offset'], o['descriptor_bytes'], o['looped']), (-36, 28, False))
            self.assertEqual(o['aliases'], [(R0+2, -36)])
        self.assertEqual(sorted(p.dependencies), sorted([S, DIRECT, POOL]))
        self.assertEqual(p.dependency_budget, profile.DEPENDENCY_BUDGET)
        sites = report['call_sites']['sites']
        self.assertEqual([r['callback_literal_offsets'] for r in sites],
                         [[program.literals[CALLBACK]], [program.literals[OTHER_CALLBACK]]])
        self.assertFalse(report['caller_shape_bounds'])

    def test_existing_one_call_selectors_still_refuse_two_sites(self):
        for policy in (local.SCHEDULER, local.SCHEDULER_PAYLOAD, local.SCHEDULER_ENTRY):
            with self.subTest(policy=policy), self.assertRaises(ValueError):
                bound(two_sites(), policy=policy)

    def test_looped_site_with_descriptor_alone_or_r4_r7_copy(self):
        for alias in ((), (0xAD00,)):                  # add r5,sp,#0: a copy of the descriptor
            program = looped(alias=alias)
            p = verified(program)
            o = observation(p, 'site', program)
            self.assertTrue(o['looped'])
            self.assertEqual(p.contract_manifest()['call_sites']['looped_sites'], [program.labels['site']])

    def test_looped_site_refuses_other_alias_and_pointer_words(self):
        with self.assertRaisesRegex(ValueError, 'looped scheduler calls exclude every local alias'):
            verified(looped(alias=(0xAD01,), frame=8))   # add r5,sp,#4: another local word
        with self.assertRaisesRegex(ValueError, 'looped scheduler calls exclude pointer-bearing'):
            verified(looped(payload=True, frame=9))

    def test_unlooped_site_records_other_preserved_aliases(self):
        program = Owner()
        program.emit(0xB530, 0xB088, 0xAD07)           # add r5,sp,#28: a separate local word
        scheduler_call(program, name='site')
        epilogue(program, 8, 0xBC30)
        o = observation(verified(program), 'site', program)
        self.assertEqual(o['aliases'], [(R0+2, -44), (R0+5, -16)])

    def test_direct_entry_records_outgoing_word(self):
        program = direct()
        p = verified(program)
        o = observation(p, 'site', program)
        self.assertEqual((o['scheduler_entry'], o['descriptor_offset'], o['outgoing_argument_word']),
                         ('direct-entry', -32, -36))
        self.assertEqual(sorted(p.dependencies), [DIRECT])
        self.assertEqual(p.contract_manifest()['call_sites']['sites'][0]['callback_register'], 1)

    def test_direct_manager_chains_are_recorded(self):
        program = direct()
        record, = verified(program).contract_manifest()['call_sites']['sites']
        chain, = record['manager_chains']
        self.assertEqual((chain['literal_offset'], chain['dereference_count'], chain['field_offset'],
                          chain['pointer_load_site']), (program.literals[MANAGER], 1, 0, None))

        # The shape of 08025688: ldr r2,=data; adds r3,r2,#0; a join; ldr r0,[r3]; ldr r0,[r0,#0x20].
        def two_loads(p):
            p.load(2, MANAGER)
            p.emit(0x1C13, 0x2900)                      # adds r3,r2,#0; cmp r1,#0
            p.branch(0xD000, 'join')                    # beq join
            p.emit(0x2100)                              # movs r1,#0
            p.label('join')
            p.emit(0x6818, 0x6A00)                      # ldr r0,[r3]; ldr r0,[r0,#0x20]
        program = direct(manager=two_loads)
        record, = verified(program).contract_manifest()['call_sites']['sites']
        chain, = record['manager_chains']
        self.assertEqual((chain['literal_offset'], chain['dereference_count'], chain['field_offset']),
                         (program.literals[MANAGER], 2, 0x20))
        self.assertEqual(chain['dereference_site'] - chain['pointer_load_site'], 2)

    def test_direct_manager_without_a_named_load_chain_refused(self):
        variants = {
            'incoming R0 (a parameter)': lambda p: None,
            'a word of the frame': lambda p: p.emit(0x9807),                          # ldr r0,[sp,#28]
            'a constant': lambda p: p.emit(0x2000),                                   # movs r0,#0
            'the literal itself': lambda p: p.load(0, MANAGER),
            'a nonzero first offset': lambda p: (p.load(0, MANAGER), p.emit(0x6840)),  # ldr r0,[r0,#4]
            'a nonzero first of two offsets': lambda p: (p.load(0, MANAGER), p.emit(0x6840, 0x6A00)),
            'three loads': lambda p: (p.load(0, MANAGER), p.emit(0x6800, 0x6800, 0x6800)),
            'a call result': lambda p: (p.call(B), p.emit(0x6800)),
            'a literal clobbered by a call': lambda p: (p.load(0, MANAGER), p.call(B), p.emit(0x6800)),
            'a base from another load form': lambda p: (p.load(0, MANAGER), p.emit(0x7800)),  # ldrb r0,[r0]
        }
        for name, manager in variants.items():
            with self.subTest(manager=name), self.assertRaisesRegex(ValueError, 'direct scheduler manager'):
                bound(direct(manager=manager))

    def test_direct_manager_pointer_origin_is_searched_from_its_own_load(self):
        # ldr r2,[sp,#20]; ldr r3,[r2]; ldr r2,=data; ldr r0,[r3,#0x20]: the first load's base
        # is a frame word; the literal loaded into R2 after it is not its origin.
        def manager(p):
            p.emit(0x9A05, 0x6813)
            p.load(2, MANAGER)
            p.emit(0x6A18)
        with self.assertRaisesRegex(ValueError, 'direct scheduler manager'):
            bound(direct(manager=manager))

    def test_direct_manager_literal_requires_a_typed_zero_addend_data_binding(self):
        program = direct()
        report = verified(program).contract_manifest()
        manager, callback = program.literals[MANAGER], program.literals[CALLBACK]
        functions = [[callback, 'func']]
        profile.check_bindings(report, dict(functions=functions, data=[[manager, 'data_0200F430', 0]]))
        for rows in ([], [[manager, 'data_0200F430', 4]], [[manager + 4, 'data_0200F430', 0]],
                     [[manager, 'data_0200F430', 0], [manager, 'data_0200F434', 0]]):
            with self.subTest(rows=rows), self.assertRaisesRegex(ValueError, 'zero-addend named data'):
                profile.check_bindings(report, dict(functions=functions, data=rows))
        record, = report['call_sites']['sites']
        for chains in ([], None):
            forged = dict(record, manager_chains=chains) if chains is not None else \
                {k: v for k, v in record.items() if k != 'manager_chains'}
            with self.subTest(chains=chains), self.assertRaisesRegex(ValueError, 'manager chains'):
                profile.check_bindings(dict(report, call_sites=dict(report['call_sites'], sites=[forged])),
                                       dict(functions=functions, data=[[manager, 'data_0200F430', 0]]))
        pool = verified(two_sites()).contract_manifest()
        self.assertNotIn('manager_chains', pool['call_sites']['sites'][0])

    def test_direct_descriptor_overlapping_outgoing_word_refused(self):
        with self.assertRaisesRegex(ValueError, 'overlaps the outgoing argument word'):
            verified(direct(descriptor=0xAB00))

    def test_direct_parent_word_holding_local_pointer_refused(self):
        # add r2,sp,#0; str r2,[sp]: the parent is a pointer into the caller frame.
        with self.assertRaisesRegex(ValueError, 'parent word holds a local pointer'):
            verified(direct(parent=(0xAA00, 0x9200)))

    def test_descriptor_into_saved_word_or_unaligned_refused(self):
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            verified(two_sites(frame=6))
        program = Owner()
        program.emit(0xB510, 0xB088)
        program.load(0, CALLBACK)
        program.emit(0x2108, 0xAA00, 0x3202, 0x2300)    # add r2,sp,#0; adds r2,#2
        program.call(S, 'site')
        epilogue(program, 8)
        with self.assertRaisesRegex(ValueError, 'word-aligned'):
            verified(program)

    def test_second_caller_clobbered_alias_refused(self):
        for extra in (0xA900, 0x4694, 0x4696):            # add r1,sp,#0; mov r12,r2; mov lr,r2
            program = Owner()
            program.emit(0xB510, 0xB087)
            program.load(0, CALLBACK)
            program.emit(0x2108, 0xAA00, 0x2300)
            if extra == 0xA900:
                program.data[-6:-4] = half(extra)          # replace movs r1,#8 by the alias
            else:
                program.emit(extra)
            program.call(S, 'site')
            epilogue(program, 7)
            with self.subTest(extra=hex(extra)), \
                    self.assertRaisesRegex(ValueError, 'only the descriptor register'):
                verified(program)

    def test_site_without_a_local_descriptor_is_observed_and_refused(self):
        # movs r2,#0: no local alias reaches the call, so only the site hook sees it.
        program = Owner()
        program.emit(0xB510, 0xB087)
        scheduler_call(program, name='site', descriptor=0x2200)
        epilogue(program, 7)
        with self.assertRaisesRegex(ValueError, 'only the descriptor register'):
            verified(program)

    def test_payload_words_at_four_and_eight_record_extent(self):
        for store, field in ((0x9001, 4), (0x9002, 8)):
            program = payload(store=store)
            o = observation(verified(program), 'site', program)
            self.assertEqual(o['payload_words'], [dict(descriptor_field=field, offset=-12, extent_bytes=8)])
            self.assertEqual(o['other_pointer_words'], [])

    def test_payload_extent_stops_at_the_first_saved_word(self):
        # Payload at SP+32 in a 9-word frame: one local word, then the saved LR.
        program = payload(value=0xA808)
        o = observation(verified(program), 'site', program)
        self.assertEqual(o['payload_words'], [dict(descriptor_field=4, offset=-8, extent_bytes=4)])

    def test_payload_below_the_descriptor_stops_at_it(self):
        # Descriptor at SP+8, payload at SP: the extent ends at the descriptor, not at the saved LR.
        program = Owner()
        program.emit(0xB500, 0xB089, 0xA800, 0x9003)       # add r0,sp,#0; str r0,[sp,#12]
        scheduler_call(program, name='site', descriptor=0xAA02)
        program.emit(0xB009, 0xBC02, 0x4708)
        o = observation(verified(program), 'site', program)
        self.assertEqual(o['payload_words'], [dict(descriptor_field=4, offset=-40, extent_bytes=8)])

    def test_payload_addressing_the_descriptor_or_holding_a_pointer_refused(self):
        # add r0,sp,#8; str r0,[sp,#4]: descriptor+4 addresses descriptor+8.
        with self.assertRaisesRegex(ValueError, 'payload word addresses the descriptor'):
            verified(payload(value=0xA802))
        # str r0,[sp,#32] as well: a pointer word inside the payload extent.
        with self.assertRaisesRegex(ValueError, 'payload extent contains a pointer-bearing word'):
            verified(payload(extra=(0x9008,)))

    def test_unaligned_payload_sharing_a_pointer_word_refused(self):
        # Descriptor at SP; descriptor+4 -> SP+33 (add r0,sp,#32; adds r0,#1), and SP+32 holds a
        # pointer (add r1,sp,#0; str r1,[sp,#32]): the extent covers three bytes of that word.
        program = Owner()
        program.emit(0xB500, 0xB08A, 0xA808, 0x3001, 0x9001, 0xA900, 0x9108)
        scheduler_call(program, name='site')
        program.emit(0xB00A, 0xBC02, 0x4708)
        with self.assertRaisesRegex(ValueError, 'payload extent contains a pointer-bearing word'):
            verified(program)

    def test_payload_extent_over_the_direct_outgoing_word_refused(self):
        # Direct entry, descriptor at SP+8, descriptor+4 -> SP, SP+1 or SP+3: the extent would
        # cover the outgoing parent word, which the callee may overwrite.
        for adjust in ((), (0x3401,), (0x3403,)):                 # adds r4,#1; adds r4,#3
            program = Owner()
            program.emit(0xB510, 0xB089)
            program.load(0, MANAGER)
            program.emit(0x6800, 0xAC00, *adjust, 0x9403)       # add r4,sp,#0; str r4,[sp,#12]
            program.load(1, CALLBACK)
            program.emit(0x2200, 0x9200, 0x2228, 0xAB02)        # parent 0 at [sp]; add r3,sp,#8
            program.call(DIRECT, 'site')
            program.emit(0xB009, 0xBC10, 0xBC02, 0x4708)
            with self.subTest(adjust=[hex(word) for word in adjust]), \
                    self.assertRaisesRegex(ValueError, 'includes the direct entry outgoing argument word'):
                verified(program)

    def test_other_descriptor_pointer_word_refused(self):
        for store in (0x9000, 0x9003, 0x9006):            # descriptor+0, +12, +24
            with self.subTest(store=hex(store)), \
                    self.assertRaisesRegex(ValueError, r'only at descriptor\+4 and descriptor\+8'):
                verified(payload(store=store))

    def test_pointer_word_outside_the_descriptor_is_recorded(self):
        program = payload(store=0x9007)                    # str r0,[sp,#28]: outside the descriptor
        o = observation(verified(program), 'site', program)
        self.assertEqual((o['payload_words'], o['other_pointer_words']), ([], [(-12, -12)]))

    def test_payload_pointing_at_saved_word_refused(self):
        p, _, calls = bound(payload())
        site = next(iter(calls))
        stack = [LOCAL]*9 + [SAVED]
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            profile.check_call(p, S, {R0+2: -40}, stack, {-36: -4}, site=site)

    def test_callback_register_must_be_a_literal_on_every_path(self):
        program = Owner()
        program.emit(0xB510, 0xB087, 0x1C20)               # adds r0,r4,#0
        program.emit(0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        with self.assertRaisesRegex(ValueError, 'not a function literal'):
            bound(program)
        # A literal on one arm only: the other arm carries the incoming R0.
        program = Owner()
        program.emit(0xB510, 0xB087, 0x2900)
        program.branch(0xD000, 'skip')
        program.load(0, CALLBACK)
        program.label('skip')
        program.emit(0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        with self.assertRaisesRegex(ValueError, 'not a function literal'):
            bound(program)
        # A call between the literal load and the site clobbers R0.
        program = Owner()
        program.emit(0xB510, 0xB087)
        program.load(0, CALLBACK)
        program.call(B)
        program.emit(0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        with self.assertRaisesRegex(ValueError, 'not a function literal'):
            bound(program)

    def test_callback_literal_followed_through_register_copies(self):
        # ldr r1,=cb; adds r0,r1,#0: the shape of 0812638C and 0812640C.
        program = Owner()
        program.emit(0xB510, 0xB087)
        program.load(1, CALLBACK)
        program.emit(0x1C08, 0x2108, 0xAA00, 0x2300)        # adds r0,r1,#0
        program.call(S, 'site')
        epilogue(program, 7)
        record, = verified(program).contract_manifest()['call_sites']['sites']
        self.assertEqual(record['callback_literal_offsets'], [program.literals[CALLBACK]])
        # A preserved register carries the literal across an ordinary call, then two copies.
        program = Owner()
        program.emit(0xB510, 0xB087)
        program.load(4, CALLBACK)
        program.call(B)
        program.emit(0x46A0, 0x4640, 0x2108, 0xAA00, 0x2300)  # mov r8,r4; mov r0,r8
        program.call(S, 'site')
        epilogue(program, 7)
        record, = verified(program).contract_manifest()['call_sites']['sites']
        self.assertEqual(record['callback_literal_offsets'], [program.literals[CALLBACK]])
        # The same through R1, which the call clobbers, is refused; so is a copy of SP.
        for load, copy in ((1, 0x1C08), (None, 0x4668)):    # adds r0,r1,#0; mov r0,sp
            program = Owner()
            program.emit(0xB510, 0xB087)
            if load is not None:
                program.load(load, CALLBACK)
            program.call(B)
            program.emit(copy, 0x2108, 0xAA00, 0x2300)
            program.call(S, 'site')
            epilogue(program, 7)
            with self.subTest(copy=hex(copy)), self.assertRaisesRegex(ValueError, 'not a function literal'):
                bound(program)

    def test_callback_arithmetic_and_memory_loads_are_not_copies(self):
        # adds r0,r1,#2; lsls r0,r1,#1; add r0,r8 (after mov r8,r1); ldr r0,[r1,#0]: none is an exact copy.
        for tail in ((0x1C88,), (0x0048,), (0x4688, 0x2000, 0x4440), (0x6808,)):
            program = Owner()
            program.emit(0xB510, 0xB087)
            program.load(1, CALLBACK)
            program.emit(*tail, 0x2108, 0xAA00, 0x2300)
            program.call(S, 'site')
            epilogue(program, 7)
            with self.subTest(tail=[hex(word) for word in tail]), \
                    self.assertRaisesRegex(ValueError, 'not a function literal'):
                bound(program)

    def test_callback_literal_in_r12_or_lr_does_not_survive_a_call(self):
        # ldr r3,=cb; mov r12,r3 (or mov lr,r3); bl B; mov r0,r12 (or mov r0,lr).
        for save, restore in ((0x469C, 0x4660), (0x469E, 0x4670)):
            program = Owner()
            program.emit(0xB510, 0xB087)
            program.load(3, CALLBACK)
            program.emit(save)
            program.call(B)
            program.emit(restore, 0x2108, 0xAA00, 0x2300)
            program.call(S, 'site')
            epilogue(program, 7)
            with self.subTest(restore=hex(restore)), \
                    self.assertRaisesRegex(ValueError, 'not a function literal'):
                bound(program)

    def test_callback_search_refuses_an_interrupt(self):
        # ldr r0,=cb; svc #0x0b; ...: a BIOS call clobbers R0-R3 although no register operand says so.
        program = Owner()
        program.emit(0xB510, 0xB087)
        program.load(0, CALLBACK)
        program.emit(0xDF0B, 0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        data, calls = program.build()
        ins, edges = {}, {}
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        for item in decoder.disasm(data[:program.labels['site'] - A + 4], A):
            ins[item.address] = item
            edges[item.address] = [item.address + item.size]
        edges[program.labels['site']] = []
        with self.assertRaisesRegex(ValueError, 'interrupt'):
            profile.callback_literals(data, A, ins, edges, calls, program.labels['site'], R0)

    def test_every_literal_of_a_site_needs_a_typed_function_binding(self):
        program = Owner()
        program.emit(0xB510, 0xB087, 0x2900)
        program.branch(0xD001, 'other')
        program.load(0, CALLBACK)
        program.branch(0xE000, 'join')
        program.label('other')
        program.load(0, OTHER_CALLBACK)
        program.label('join')
        program.emit(0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        report = verified(program).contract_manifest()
        offsets = sorted(program.literals.values())
        profile.check_bindings(report, dict(functions=[[o, 'func'] for o in offsets]))
        for bound_offset in offsets:
            with self.subTest(bound=bound_offset), self.assertRaisesRegex(ValueError, 'typed function literal'):
                profile.check_bindings(report, dict(functions=[[bound_offset, 'func']]))

    def test_direct_outgoing_word_must_be_a_local_word(self):
        # push {lr}; sub sp,#32; push {r4}: the word at SP is a saved slot, not an outgoing local.
        p = Owner()
        p.emit(0xB500, 0xB088, 0xB410)
        p.load(0, MANAGER)
        p.emit(0x6800)
        p.load(1, CALLBACK)
        p.emit(0x2228, 0xAB01)
        p.call(DIRECT, 'site')
        p.emit(0xBC10, 0xB008, 0xBC02, 0x4708)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            verified(p)

    def test_looped_site_refuses_a_high_register_copy_of_the_descriptor(self):
        # add r5,sp,#0; mov r8,r5: R8 holds the descriptor address at the looped call.
        with self.assertRaisesRegex(ValueError, 'looped scheduler calls exclude every local alias'):
            verified(looped(alias=(0xAD00, 0x46A8)))

    def test_pool_site_alone_pins_the_direct_entry_body(self):
        program = Owner()
        program.emit(0xB510, 0xB087)
        scheduler_call(program, POOL, name='site')
        epilogue(program, 7)
        p = verified(program)
        self.assertEqual(sorted(p.dependencies), [DIRECT, POOL])
        self.assertEqual(p.contract_manifest()['call_sites']['dependencies'], [DIRECT, POOL])

    def test_callback_literals_on_both_arms_are_all_recorded(self):
        program = Owner()
        program.emit(0xB510, 0xB087, 0x2900)
        program.branch(0xD001, 'other')                     # beq other
        program.load(0, CALLBACK)
        program.branch(0xE000, 'join')                      # b join
        program.label('other')
        program.load(0, OTHER_CALLBACK)
        program.label('join')
        program.emit(0x2108, 0xAA00, 0x2300)
        program.call(S, 'site')
        epilogue(program, 7)
        p = verified(program)
        record, = p.contract_manifest()['call_sites']['sites']
        self.assertEqual(record['callback_literal_offsets'],
                         sorted(program.literals.values()))

    def test_callback_literals_require_typed_function_bindings(self):
        program = two_sites()
        report = verified(program).contract_manifest()
        offsets = sorted(program.literals.values())
        profile.check_bindings(report, dict(functions=[[o, 'func'] for o in offsets]))
        for rows in ([], [[offsets[0], 'func']], [[o + 4, 'func'] for o in offsets]):
            with self.subTest(rows=rows), self.assertRaisesRegex(ValueError, 'typed function literal'):
                profile.check_bindings(report, dict(functions=rows))

    def test_ordinary_calls_keep_the_buffer_rules(self):
        # add r0,sp,#0; bl B: B stores through the alias and is inspected.
        program = Owner()
        program.emit(0xB510, 0xB087, 0xA800)
        program.call(B, 'ordinary')
        scheduler_call(program, name='site')
        epilogue(program, 7)
        p = verified(program, callee=half(0x2100, 0x6001, 0x4770))   # movs r1,#0; str r1,[r0]; bx lr
        self.assertIn(B, p.dependencies)
        self.assertNotIn(program.labels['ordinary'], p.observations)
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08001200'):
            verified(program, callee=half(0x4900, 0x6008, 0x4770, 0, 0, 0x0200))  # ldr r1,=global; str r0,[r1]

    def test_scheduler_reached_inside_an_inspected_callee_is_not_summarised(self):
        program = Owner()
        program.emit(0xB510, 0xB087, 0xA800)
        program.call(B, 'ordinary')
        scheduler_call(program, name='site')
        epilogue(program, 7)
        callee = Owner(B)
        callee.emit(0xB500, 0x1C02)                         # push {lr}; adds r2,r0,#0
        callee.load(0, CALLBACK)
        callee.emit(0x2108, 0x2300)
        callee.call(S)
        callee.emit(0xBC01, 0x4700)
        body, _ = callee.build()
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x08001200: buffer callee 0x08005B6C'):
            verified(program, callee=body)

    def test_bind_refuses_no_entry_and_runtime_thunk_calls(self):
        program = two_sites()
        data, calls = program.build()
        with self.assertRaisesRegex(ValueError, 'pinned scheduler entry'):
            profile.bind(data, A, {}, {}, {site: B for site in calls})
        thunk = match.function_thunk.ALIASES['_call_via_r3']
        with self.assertRaisesRegex(ValueError, 'runtime thunks'):
            profile.bind(data, A, {}, {}, {**calls, A + 2: thunk})

    def test_entry_body_identity_differs_refused(self):
        pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in BODIES.items()}
        pins[POOL] = (44, '0'*64)
        with self.assertRaisesRegex(ValueError, 'dependency identity differs'):
            bound(two_sites(), pins=pins)

    def test_changed_state_unknown_site_and_unobserved_site_refused(self):
        program = two_sites()
        p, _, calls = bound(program)
        with self.assertRaisesRegex(ValueError, 'every scheduler call site must be observed'):
            p.contract_manifest()
        site, stack = program.labels['first'], [LOCAL]*7 + [SAVED]*2
        p.check_call(S, {R0+2: -36}, stack, {}, site=site)
        p.check_call(S, {R0+2: -36}, stack, {}, site=site)
        with self.assertRaisesRegex(ValueError, 'differs across incoming paths'):
            p.check_call(S, {R0+2: -36, R0+4: -32}, stack, {}, site=site)
        with self.assertRaises(ValueError):
            p.check_call(S, {R0+2: -36}, stack, {}, site=site+2)
        with self.assertRaises(ValueError):
            p.check_call(DIRECT, {R0+3: -36}, stack, {}, site=site)

    def test_manifest_states_the_per_site_premises(self):
        report = verified(two_sites()).contract_manifest()
        text = ' '.join(report['assumptions'])
        for flag in ('actual_callback_effects_proved', 'nonescape_proved', 'termination_proved',
                     'manager_memory_access_proved', 'caller_shape_bounds'):
            self.assertIs(report[flag], False)
        for phrase in ('ambient original R9', 'separate from all caller stack words', 'data_020159CC',
                       'ldr r6,[sp,#0x38]', 'extent_bytes', 'Every scheduler invocation, at any site',
                       'no direct-entry outgoing argument word'):
            self.assertIn(phrase, text)
        manager, = [line for line in report['assumptions'] if line.startswith('At a direct func_08005954 site')]
        for phrase in ('R0 is, on each actual path, the value of a recorded manager chain',
                       'typed named literal addresses a readable aligned word',
                       'for a one-load chain the word read is the manager',
                       'plus the recorded field offset addresses another readable aligned word without address wraparound',
                       'and the word read there is the manager',
                       'The storage words are separate from every caller stack word',
                       'no equality of values across paths follows',
                       'The manager is a valid scheduler manager separate from every caller stack word',
                       'may overwrite that word',
                       'No other caller private or saved word is read through SP'):
            self.assertIn(phrase, manager)

    def test_pinned_entries_and_registration(self):
        for target, entry in profile.ENTRIES.items():
            for body in entry['dependencies']:
                self.assertIn(body, local.DEPENDENCIES)
        self.assertEqual(local.SCHEDULER_CALL_SITES, SELECTOR)
        self.assertIn(SELECTOR, named.LOCAL_CALL_SELECTORS)
        self.assertEqual(owner.selector_for_report('* verification: `'+profile.SCHEMA+'`'), SELECTOR)
        run = subprocess.run([sys.executable, '-B', str(Path(match.__file__)), '--owner-runtime-profile',
                              SELECTOR, '--help'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stderr)


def admitted(owner_program, *, selector=SELECTOR, bodies=None, as_data=()):
    """owner.verify over a synthetic ROM, with the bindings an original build gives: every call
    named and every callback literal a function word. A literal value in `as_data` is bound to a
    zero-addend named data symbol at the same address instead."""
    data, calls = owner_program.build()
    base = owner_program.base
    image = fixture({base: data, CALLBACK - 1: half(0x4770), OTHER_CALLBACK - 1: half(0x4770),
                     **BODIES, **(bodies or {})})
    literals = sorted(owner_program.literals.items(), key=lambda item: item[1])
    bindings = dict(calls=sorted([site - base, f'func_{target:08X}'] for site, target in calls.items()),
                    data=[[offset, f'data_{value:08X}', 0] for value, offset in literals if value in as_data],
                    functions=[[offset, f'func_{value - 1:08X}'] for value, offset in literals
                               if value in (CALLBACK, OTHER_CALLBACK) and value not in as_data], switches=[])
    objects = json.dumps({f'data_{value:08X}': f'0x{value:08X}' for value in as_data}).encode()
    proof = local.ConditionalLocalBufferProof
    span, runtimes = proof.span, set(match.function_thunk.ALIASES.values())
    pins = {a: (len(b), hashlib.sha256(b).hexdigest()) for a, b in BODIES.items()}
    with mock.patch.dict(local.DEPENDENCIES, pins), \
            mock.patch.object(local.thunk, 'dependencies', return_value=[]), \
            mock.patch.object(proof, 'span', lambda p, a: half(0x4710) if a in runtimes else span(p, a)):
        return owner.verify(data, base, image.rom, image.mapping, image.index, objects,
                            bindings=bindings, selector=selector)


def scene_fill_owner(address):
    """A scene palette-fill owner: the fill word at its SP offset, the descriptor above it, and
    the CpuSet call and the scheduler site on separate arms."""
    size, site, destination, offset = local.scene_fill.OWNERS[address]
    frame, word = (offset + 32) // 4, offset // 4
    p = Owner(address)
    p.emit(0xB500, 0xB080 | frame, 0x2800)          # push {lr}; sub sp; cmp r0,#0
    p.branch(0xD000, 'scheduler')                   # beq scheduler
    p.emit(*[0] * ((site - 14 - p.here()) // 2))    # movs r0,r0 up to the fixed fill sequence
    p.emit(0xA900 | word if offset else 0x4669)     # add r1,sp,#offset or mov r1,sp
    p.load(2, local.scene_fill.WHITE)
    p.emit(0x1C10, 0x8008)                          # adds r0,r2,#0; strh r0,[r1]
    p.load(1, destination)
    p.load(2, local.scene_fill.CONTROL)
    p.emit(0xA800 | word if offset else 0x4668)     # add r0,sp,#offset or mov r0,sp
    p.call(local.scene_fill.bios.ADDRESS)
    p.branch(0xE000, 'exit')                        # b exit
    p.label('scheduler')
    p.emit(*[0] * ((address + size - 36 - p.here()) // 2))  # the owner's size is fixed
    scheduler_call(p, descriptor=0xAA00 | (word + 1))  # add r2,sp,#offset+4
    p.label('exit')
    p.emit(0xB000 | frame, 0xBC02, 0x4708)          # add sp; pop {r1}; bx r1
    return p


def fixed_owner(variable, address):
    """A fixed owner of the USA ROM from the game tree `variable` names: the owner.verify
    arguments before the data symbols, the data symbols, and the bindings of its saved report."""
    root = Path(os.environ[variable]).resolve()
    rom = Path(match.rom_path(str(root))).read_bytes()
    lines = (root / f'docs/match/{address:08X}.md').read_text().splitlines()
    saved = {key: next(line.split('`')[1] for line in lines if line.startswith(f'* {key}:'))
             for key in ('ROM bytes', 'owner runtime evidence')}
    start = address - match.ROM_BASE
    return ((rom[start:start + len(saved['ROM bytes']) // 2], address, rom, match.mapping_snapshot(root),
             owner.index_snapshot(root)), json.loads(match.data_snapshot(root)),
            json.loads(saved['owner runtime evidence'])['manifest']['bindings'])


REFUSAL = 'scheduler callback register requires a typed function literal'


class OwnerAdmissionBindingTests(unittest.TestCase):
    """check_bindings as owner.verify applies it, not called directly: one test for each selector
    in CALL_SITE_POLICIES but v2, which test_scheduler_call_site_forwarding covers."""

    def test_call_site_v1_selector_refuses_a_callback_bound_as_data(self):
        manifest, _ = admitted(two_sites())
        self.assertEqual(manifest['profile'], profile.SCHEMA)
        self.assertEqual([name for _, name in manifest['bindings']['functions']],
                         ['func_08001600', 'func_08001700'])
        for callback in (CALLBACK, OTHER_CALLBACK):
            with self.subTest(callback=hex(callback)), self.assertRaisesRegex(ValueError, REFUSAL):
                admitted(two_sites(), as_data=(callback,))

    def test_scene_fill_selector_refuses_a_callback_bound_as_data(self):
        scene = local.scene_fill
        found = dict(selector=scene.SELECTOR, bodies={scene.bios.ADDRESS: scene.bios.WRAPPER})
        for address, (_, _, destination, _) in scene.OWNERS.items():
            with self.subTest(owner=hex(address)):
                manifest, _ = admitted(scene_fill_owner(address), as_data=(destination,), **found)
                self.assertEqual(manifest['profile'], scene.SCHEMA)
                self.assertEqual([name for _, name in manifest['bindings']['functions']], ['func_08001600'])
                with self.assertRaisesRegex(ValueError, REFUSAL):
                    admitted(scene_fill_owner(address), as_data=(destination, CALLBACK), **found)

    def fixed_owner_refuses(self, module, variable, own_refusal):
        """Owner admission hands the admitted owner's sites and bindings to the call-site rule, as a
        spy on it records; a callback bound as data is refused by the selector's own exact-binding
        rule, which comes first, and would be refused by the call-site rule too. No rule is patched."""
        arguments, symbols, bindings = fixed_owner(variable, module.OWNER)
        verify = lambda bound, names=symbols: owner.verify(
            *arguments, json.dumps(names).encode(), bindings=bound, selector=module.SELECTOR)
        with mock.patch.object(profile, 'check_bindings', wraps=profile.check_bindings) as call_site_rule:
            manifest, _ = verify(bindings)
        self.assertEqual(manifest['profile'], module.SCHEMA)
        calls = manifest['proof']['buffers']['conditional_local_calls']
        call_site_rule.assert_called_once_with(calls, bindings)
        for offset in sorted({offset for site in calls['call_sites']['sites']
                              for offset in site['callback_literal_offsets']}):
            value = struct.unpack_from('<I', arguments[0], offset)[0]
            name = f'data_{value:08X}'
            bound = dict(bindings, functions=[row for row in bindings['functions'] if row[0] != offset],
                         data=sorted(bindings['data'] + [[offset, name, 0]]))
            with self.subTest(offset=offset):
                self.assertNotEqual(bound['functions'], bindings['functions'])
                with self.assertRaisesRegex(ValueError, own_refusal):
                    verify(bound, {**symbols, name: f'0x{value:08X}'})
                with self.assertRaisesRegex(ValueError, REFUSAL):
                    profile.check_bindings(calls, bound)

    @unittest.skipUnless(os.environ.get('FFTA_EFFECT_INITIALIZER_ROOT'), 'needs the indexed USA ROM and its reports')
    def test_effect_initializer_selector_refuses_a_callback_bound_as_data(self):
        self.fixed_owner_refuses(local.effect_init, 'FFTA_EFFECT_INITIALIZER_ROOT',
                                 'genuine initializer, child and resource bindings')

    @unittest.skipUnless(os.environ.get('FFTA_MENU_PALETTE_ROOT'), 'needs the indexed USA ROM and its reports')
    def test_menu_palette_selector_refuses_a_callback_bound_as_data(self):
        self.fixed_owner_refuses(local.menu_palette, 'FFTA_MENU_PALETTE_ROOT',
                                 'wrong call, object, addend or callback relocation')

    @unittest.skipUnless(os.environ.get('FFTA_EFFECT_REGISTRY_ROOT'), 'needs the indexed USA ROM and its reports')
    def test_effect_registry_selector_refuses_a_callback_bound_as_data(self):
        self.fixed_owner_refuses(local.effect_registry, 'FFTA_EFFECT_REGISTRY_ROOT',
                                 'exact callback, named tables and scheduler relocations')


if __name__ == '__main__':
    unittest.main()
