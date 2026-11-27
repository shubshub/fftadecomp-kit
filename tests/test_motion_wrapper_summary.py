"""The pinned motion-task wrappers summarised in the default stack buffer walk (kit #424).

Three layers:

* stand-in bodies (hand-written Thumb with the wrappers' shape, assembled at the pinned addresses, with
  ``PINS`` and ``ZERO_FILL_RETURN`` patched to them) drive the derivation and the site rules in
  process, including the hostile variants;
* the real pinned spans, read from ``FFTA_ROM`` into a synthetic ROM, with agbcc-compiled owners
  issued by match.py in a subprocess and replayed (skipped without the ROM or the compiler);
* the two decomp functions the rule was built for, 08100EF0 and 08103510, issued from an
  ``FFTA_ROOT`` checkout that carries their sources (skipped otherwise).

No ROM-derived body or disassembly is checked in.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import data_buffer_profile as data_buffer
import match_evidence as evidence
import motion_wrapper_summary_profile as motion

BASE = match.ROM_BASE
R0, R1, R2, R3 = (match.ARM_REG_R0 + n for n in range(4))
OWNER, COPY = 0x08010000, 0x08011000
ROM_END = 0x08142254

# Stand-ins at the pinned addresses.  The wrapper keeps R0, R1, R2 and its first stack word in a
# 16-byte block at its SP and points a 28-byte descriptor at it; the scheduler body allocates, fills
# through _call_via_r2, stores the callback, copies the descriptor, zeroes its phase and calls the
# callback through _call_via_r3; phase 0 of the callback reads three halfwords through each position
# and keeps R0 and the stack word in the allocation.
WRAPPER = """
    push {r4, r7, lr}
    mov r7, r8
    push {r7}
    sub sp, #44
    movs r4, #0
    mov r8, r4
    movs r7, #0
    str r0, [sp]
    str r1, [sp, #4]
    str r2, [sp, #8]
    ldr r0, [sp, #60]
    str r0, [sp, #12]
@WRAPPER_EXTRA@
    add r2, sp, #16
    mov r0, sp
    str r0, [r2, #4]
    ldr r0, 1f
    movs r1, #24
    ldr r3, [sp, #64]
    bl scheduler
@WRAPPER_AFTER@
    add sp, #44
    pop {r3}
    mov r8, r3
    pop {r4, r7}
    pop {r1}
    bx r1
    .align 2
1:  .word @CALLBACK@ + 1
"""
SCHEDULER = """
    push {lr}
    bl body
    movs r1, #1
    strh r1, [r0, #0x16]
    pop {r1}
    bx r1
"""
BODY = """
    push {r4, r5, r6, lr}
    sub sp, #28
    adds r4, r0, #0
    adds r5, r2, #0
    adds r0, r1, #0
    movs r6, #0
@BEFORE_ALLOCATOR@
    bl allocator
@AFTER_ALLOCATOR@
    adds r6, r0, #0
    movs r1, #8
    ldr r2, 2f
    bl via_r2
fill_return:
    str r4, [r6]
    mov r1, sp
    ldm r5!, {r0, r2, r3}
    stm r1!, {r0, r2, r3}
    ldm r5!, {r0, r2, r3}
    stm r1!, {r0, r2, r3}
    ldr r0, [r5]
    str r0, [r1]
@PHASE@
    adds r0, r6, #0
    mov r1, sp
    adds r2, r6, #4
    ldr r3, [r6]
    bl via_r3
@SECOND_CALL@
    adds r0, r6, #0
    add sp, #28
    pop {r4, r5, r6}
    pop {r1}
    bx r1
    .align 2
2:  .word 0x03005E79
"""
ZERO_PHASE = """
    movs r0, #0
    mov r1, sp
    strh r0, [r1]
"""
CALLBACK = """
    push {r4, lr}
    ldrh r0, [r1]
    cmp r0, #0
    bne 3f
    ldr r4, [r1, #4]
    ldr r3, [r4, #4]
    ldrh r0, [r3]
    strh r0, [r2]
    ldrh r0, [r3, #2]
    strh r0, [r2, #2]
    ldrh r0, [r3, #4]
    strh r0, [r2, #4]
    ldr r3, [r4, #8]
    ldrh r0, [r3]
    strh r0, [r2, #6]
    ldrh r0, [r3, #2]
    strh r0, [r2, #8]
    ldrh r0, [r3, #4]
    strh r0, [r2, #10]
    ldr r0, [r4]
    str r0, [r2, #12]
    ldr r0, [r4, #12]
    str r0, [r2, #16]
@CALLBACK_EXTRA@
3:  pop {r4}
    pop {r0}
    bx r0
"""
# The owner: two 6-byte positions at sp+8 and sp+16, two stack words, and R1/R2 pointing at them.
OWNER_BODY = """
    push {r4, r7, lr}
    mov r7, r8
    push {r7}
    sub sp, #24
    movs r0, #1
    str r0, [sp, #8]
    str r0, [sp, #12]
    str r0, [sp, #16]
    str r0, [sp, #20]
    movs r0, #0
    str r0, [sp]
    str r0, [sp, #4]
@OWNER_SETUP@
@R1@
    add r2, sp, #16
@R3@
    bl @TARGET@
@OWNER_AFTER@
    add sp, #24
    pop {r3}
    mov r8, r3
    pop {r4, r7}
    pop {r1}
    bx r1
"""
NAMES = {0x080D6238: 'wrapper_a', 0x080D6284: 'wrapper', motion.SCHEDULER: 'scheduler',
         motion.SCHEDULER_BODY: 'body', 0x080D5128: 'callback_a', 0x080D5594: 'callback',
         motion.CALL_VIA_R2: 'via_r2', motion.CALL_VIA_R3: 'via_r3'}


def tools_present():
    return all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


def stand_ins(work, owner_setup='', owner_after='', target='wrapper', r1='    add r1, sp, #8', r3='    movs r3, #0',
              wrapper_extra='', callback_extra='', phase=ZERO_PHASE, second_call='', before_allocator='',
              after_allocator='', wrapper_after=''):
    """Assemble the stand-ins; returns (rom, mapping entries, symbols, pins)."""
    owner = (OWNER_BODY.replace('@OWNER_SETUP@', owner_setup).replace('@OWNER_AFTER@', owner_after)
             .replace('@TARGET@', target).replace('@R1@', r1).replace('@R3@', r3))
    wrapper = WRAPPER.replace('@WRAPPER_EXTRA@', wrapper_extra).replace('@WRAPPER_AFTER@', wrapper_after)
    callback = CALLBACK.replace('@CALLBACK_EXTRA@', callback_extra)
    body = (BODY.replace('@PHASE@', phase).replace('@SECOND_CALL@', second_call)
            .replace('@BEFORE_ALLOCATOR@', before_allocator).replace('@AFTER_ALLOCATOR@', after_allocator))
    parts = [(0x5954, 'body', body), (0x5B6C, 'scheduler', SCHEDULER), (0x7138, 'allocator', 'movs r0, #0\nbx lr'),
             (0x10000, 'owner', owner), (0x11000, 'copy', wrapper.replace('@CALLBACK@', 'callback')),
             # An ordinary callee that keeps R1 in its own frame, 200 bytes down: a released word.
             (0x12000, 'deep', 'push {lr}\nsub sp, #200\nstr r1, [sp]\nadd sp, #200\npop {r0}\nbx r0'),
             (0xD5128, 'callback_a', callback), (0xD5594, 'callback', callback),
             (0xD6238, 'wrapper_a', wrapper.replace('@CALLBACK@', 'callback_a')),
             (0xD6284, 'wrapper', wrapper.replace('@CALLBACK@', 'callback')),
             (0x14224C, 'via_r2', 'bx r2'), (0x142250, 'via_r3', 'bx r3')]
    # The runtime's call-via thunks are `bx rN` then `mov r8, r8`; the pinned span is the `bx` alone.
    tails = {'via_r2': 'nop', 'via_r3': 'nop'}
    names = [name for _, name, _ in parts]
    text = ('.syntax unified\n.arch armv4t\n.thumb\n.text\n.global ' +
            ', '.join(f'{name}, {name}_end' for name in names) + '\n' +
            ''.join(f'.org 0x{offset:x}\n.thumb_func\n{name}:\n{code}\n{name}_end:\n{tails.get(name, "")}\n'
                    for offset, name, code in parts) +
            '.global fill_return\n')
    (work / 'standin.s').write_text(text)
    for command in (
            [match.DEFAULT_AS, '-mthumb-interwork', str(work / 'standin.s'), '-o', str(work / 'standin.o')],
            [match.DEFAULT_LD, '-Ttext=0x08000000', '-e', 'owner', str(work / 'standin.o'),
             '-o', str(work / 'standin.elf')],
            [match.DEFAULT_OBJCOPY, '-O', 'binary', '--only-section=.text', str(work / 'standin.elf'),
             str(work / 'standin.bin')]):
        subprocess.run(command, check=True, capture_output=True)
    rom = (work / 'standin.bin').read_bytes()
    image = match.elf_image((work / 'standin.elf').read_bytes())
    symbols = {symbol['name']: symbol['value'] & ~1 for symbol in image['symbols']}
    entries = [{'rom': f'0x{symbols[name]:08X}', 'end': f'0x{symbols[name + "_end"]:08X}', 'mode': 'thumb'}
               for name in names]
    pins = {}
    for address, name in NAMES.items():
        assert symbols[name] == address, (name, hex(symbols[name]))
        size = symbols[name + '_end'] - address
        pins[address] = (size, hashlib.sha256(rom[address - BASE:address - BASE + size]).hexdigest())
    return rom, entries, symbols, pins


def index_text(entries):
    return ''.join(f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} {int(e['end'], 16) - int(e['rom'], 16)} 0 return\n"
                   for e in entries).encode()


@unittest.skipUnless(tools_present(), 'ARM binutils required')
class StandInTests(unittest.TestCase):
    """The derivation and the site rules on stand-in bodies."""

    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='motion_wrapper_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.work = Path(directory.name)

    def build(self, **variant):
        rom, entries, symbols, pins = stand_ins(self.work, **variant)
        for patcher in (patch.dict(motion.PINS, pins), patch.object(motion, 'ZERO_FILL_RETURN', symbols['fill_return'])):
            patcher.start()
            self.addCleanup(patcher.stop)
        self.rom, self.entries, self.symbols = rom, entries, symbols
        return rom

    def derive(self, wrapper=0x080D6284, released=(), **variant):
        rom = self.build(**variant)
        return motion.Derivation(rom, wrapper, released).run()

    def walk(self, **variant):
        """The owner through the default stack-argument proof, as match.py builds it."""
        rom = self.build(**variant)
        mapping = json.dumps(self.entries).encode()
        index = index_text(self.entries)
        proof = match.BufferCallProof(
            rom, mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True, copy_helper_index=index,
            switch_callee_index=index, dead_registers=True, call_via_targets=True, forward_slots=True)
        end = self.symbols['owner_end']
        match.verify_leaf_instructions(rom[OWNER - BASE:end - BASE], OWNER, True,
                                       buffer_proof=proof, call_resolver=proof.target)
        return proof

    # ---- the derivation ---------------------------------------------------------------------
    def test_derivation_finds_the_block_reads_kept_words_and_returns(self):
        facts = self.derive()
        record = motion.facts_record(0x080D6284, facts, ())
        self.assertEqual(dict(record['reads'])['R1'], [[0, 2], [2, 2], [4, 2]])
        self.assertEqual(dict(record['reads'])['R2'], [[0, 2], [2, 2], [4, 2]])
        self.assertEqual(record['written'], [])
        self.assertEqual(record['stored'], ['R0', 'W0', 'W1'])
        self.assertEqual(record['argument_words'], 2)
        self.assertEqual((record['descriptor'], record['block']), (-44, 'entry-SP-60'))
        self.assertEqual(dict(record['frame_stores']), {'R1': [['0x080D6284', -56, 4]], 'R2': [['0x080D6284', -52, 4]]})
        results = dict(record['results'])
        self.assertEqual((results[0], results[3]), ('allocation+0', 'S8'))
        released = dict(record['released'])
        self.assertEqual((released[-56], released[-52], released[-12], released[-16]), ('R1', 'R2', 'S4', 'S8'))
        self.assertEqual(record['callback'], 0x080D5594)
        self.assertEqual(sorted(kind for _, kind in record['opaque']), ['allocator', 'zero fill 0x03005E79'])
        self.assertEqual(record['opaque_live'], ['S10', 'S11', 'S9'])

    def test_a_word_below_sp_at_an_opaque_call_is_kept_only_for_tracking(self):
        # A released word below the allocator's frame may be overwritten there: still tracked, never used.
        facts = self.derive(released=(-204,))
        self.assertEqual({motion.describe(value) for value in facts.released[-204]}, {'maybe(released entry-SP-204)'})
        # A constant left below SP before the allocator call is gone after it.
        below = '    sub sp, #8\n    movs r0, #1\n    str r0, [sp]\n    add sp, #8'
        again = '    sub sp, #8\n    ldr r1, [sp]\n    add sp, #8\n    cmp r1, #1\n    beq 5f\n5:'
        self.derive(before_allocator=below, after_allocator=again.replace('ldr r1, [sp]', 'movs r1, #1'))
        with self.assertRaisesRegex(ValueError, 'uninitialised or released frame word'):
            self.derive(before_allocator=below, after_allocator=again)

    def test_a_halfword_of_an_entry_value_is_never_an_address(self):
        with self.assertRaisesRegex(ValueError, 'load through an unsupported base'):
            self.derive(callback_extra='    ldr r0, [r4, #4]\n    mov r3, sp\n    subs r3, #8\n    strh r0, [r3]\n'
                                       '    ldrh r0, [r3]\n    ldrh r0, [r0]')

    # ---- a walked-frame address is tracked or refused, never dropped (review F1) ------------------
    def test_a_callback_that_keeps_the_block_address_refuses(self):
        with self.assertRaisesRegex(ValueError, 'stores a walked-frame address outside the frames'):
            self.derive(callback_extra='    str r4, [r2, #20]')

    def test_a_callback_that_keeps_its_message_address_refuses(self):
        with self.assertRaisesRegex(ValueError, 'stores a walked-frame address outside the frames'):
            self.derive(callback_extra='    str r1, [r2, #20]')

    def test_a_halfword_of_a_frame_address_kept_in_the_allocation_refuses(self):
        with self.assertRaisesRegex(ValueError, 'stores a walked-frame address outside the frames'):
            self.derive(callback_extra='    strh r4, [r2, #20]')

    def test_a_halfword_of_a_frame_address_read_back_refuses(self):
        with self.assertRaisesRegex(ValueError, 'a halfword or byte of a walked-frame address is read'):
            self.derive(callback_extra='    mov r0, sp\n    mov r3, sp\n    subs r3, #8\n    strh r0, [r3]\n'
                                       '    ldrh r0, [r3]')
        # Read through a wider store it is opaque (copied only), and using it refuses.
        with self.assertRaisesRegex(ValueError, 'uninitialised or released frame word'):
            self.derive(callback_extra='    mov r0, sp\n    mov r3, sp\n    subs r3, #8\n    str r0, [r3]\n'
                                       '    ldrh r0, [r3]\n    adds r0, #1')

    def test_a_frame_address_returned_in_r2_or_r12_refuses(self):
        for register, code in (('R2', '    add r2, sp, #16'), ('R12', '    add r1, sp, #16\n    mov ip, r1')):
            with self.subTest(register=register):
                with self.assertRaisesRegex(ValueError, f'{register} returns a walked-frame address'):
                    self.derive(wrapper_after=code)
                # The owner that would store through it is refused at the call.
                self.refused(f'{register} returns a walked-frame address', wrapper_after=code,
                             owner_after='    ldr r0, [r2, #4]')

    def test_frame_addresses_passed_to_the_opaque_calls_are_listed(self):
        # The descriptor (entry-SP-44) is still in R2 and R5 at the allocator call: the premise covers it.
        record = motion.facts_record(0x080D6284, self.derive(), ())
        self.assertTrue({(2, -44), (5, -44)} <= {(register, offset) for _, register, offset in record['opaque_frames']})
        proof = self.walk()
        self.assertIn('frame addresses passed: ', proof.motion_summaries.lines()[1])

    # The review's hostile fixtures F1-F7 (each was admitted before the walked-frame requires, F7 apart).
    GLOBAL_STORE = '    movs r3, #3\n    lsls r3, r3, #24\n    str r0, [r3]\n'

    def test_review_f1_block_address_kept_in_the_allocation(self):
        with self.assertRaisesRegex(ValueError, 'stores a walked-frame address outside the frames'):
            self.derive(callback_extra='    str r4, [r2, #20]\n')
        self.refused('stores a walked-frame address outside the frames', callback_extra='    str r4, [r2, #20]\n')

    def test_review_f2_message_or_callback_frame_address_kept(self):
        for code in ('    str r1, [r2, #20]\n', '    mov r0, sp\n    str r0, [r2, #20]\n'):
            with self.subTest(code=code):
                self.refused('stores a walked-frame address outside the frames', callback_extra=code)

    def test_review_f3_block_address_returned_and_the_owner_leaks_its_local(self):
        self.refused('R2 returns a walked-frame address', callback_extra='    adds r2, r4, #0\n',
                     owner_after='    ldr r0, [r2, #4]\n' + self.GLOBAL_STORE)

    def test_review_f3b_block_address_returned_in_r12(self):
        self.refused('R12 returns a walked-frame address', callback_extra='    mov r12, r4\n',
                     owner_after='    mov r2, r12\n    ldr r0, [r2, #4]\n' + self.GLOBAL_STORE)

    def test_review_f4_block_address_through_an_untracked_pointer(self):
        self.refused('stores a walked-frame address outside the frames',
                     callback_extra='    movs r3, #3\n    lsls r3, r3, #24\n    ldr r3, [r3]\n    str r4, [r3]\n')

    def test_review_f5_halfword_of_a_frame_address_used_as_a_number(self):
        self.refused('a halfword or byte of a walked-frame address is read',
                     callback_extra='    sub sp, #8\n    mov r3, sp\n    strh r4, [r3]\n    ldrh r0, [r3]\n'
                                    '    add sp, #8\n    str r0, [r2, #20]\n')

    def test_review_f6_owner_position_handed_to_the_allocator(self):
        self.refused('R1 is written through, kept or used as a number',
                     before_allocator='    ldr r3, [r5, #4]\n    ldr r3, [r3, #4]\n')

    def test_review_f7_descriptor_handed_to_the_allocator_is_admitted_under_the_premise(self):
        # As the real bodies do: a frame address in R3 at the allocator, listed and covered by the premise.
        proof = self.walk(before_allocator='    adds r3, r5, #0\n')
        facts = proof.motion_summaries.lines()[1]
        self.assertIn(':r3=entry-SP-44', facts)
        self.assertIn('keep none of their argument values', proof.motion_summaries.lines()[-1])

    def test_an_unrestored_callee_saved_register_refuses(self):
        with self.assertRaisesRegex(ValueError, 'R5 is not restored at the return'):
            self.derive(wrapper_extra='    movs r5, #0')

    def test_a_halfword_store_keeps_only_the_low_bits(self):
        # 0x10000 stored as the phase halfword is phase 0.
        facts = self.derive(phase='    movs r0, #1\n    lsls r0, r0, #16\n    mov r1, sp\n    strh r0, [r1]')
        self.assertEqual(len(facts.callback), 1)

    def test_a_shift_by_register_shifts_the_destination(self):
        # r0 = 1 << 3 = 8 takes the branch over the unpinned call; 3 << 0 (the operands swapped) would not.
        self.derive(callback_extra='    movs r0, #1\n    movs r3, #3\n    lsls r0, r3\n    cmp r0, #8\n    beq 4f\n'
                                   '    bl copy\n4:')

    def test_a_frame_address_in_unknown_arithmetic_refuses(self):
        with self.assertRaisesRegex(ValueError, 'frame, allocation or return address in arithmetic'):
            self.derive(callback_extra='    ldrh r0, [r3]\n    add r0, sp')

    def test_each_wrapper_reaches_only_its_own_callback(self):
        self.assertEqual(motion.facts_record(0x080D6238, self.derive(0x080D6238), ())['callback'], 0x080D5128)

    def test_a_write_to_the_caller_frame_refuses(self):
        with self.assertRaisesRegex(ValueError, 'writes the caller frame'):
            self.derive(wrapper_extra='    str r0, [sp, #60]')

    def test_a_nonzero_phase_refuses(self):
        with self.assertRaisesRegex(ValueError, 'nonzero phase'):
            self.derive(phase='    movs r0, #1\n    mov r1, sp\n    strh r0, [r1]')

    def test_an_unzeroed_phase_refuses(self):
        with self.assertRaisesRegex(ValueError, 'nonzero phase'):
            self.derive(phase='')

    def test_a_second_callback_call_refuses(self):
        with self.assertRaisesRegex(ValueError, 'second callback call'):
            self.derive(second_call='    adds r0, r6, #0\n    mov r1, sp\n    adds r2, r6, #4\n    ldr r3, [r6]\n'
                                    '    bl via_r3')

    def test_a_path_without_the_callback_refuses(self):
        # A null check on the allocation that skips the callback call on one path.
        with self.assertRaisesRegex(ValueError, 'returns without exactly one callback call'):
            self.derive(phase=ZERO_PHASE + '    cmp r6, #0\n    beq 6f', second_call='6:')

    def test_an_uninitialised_word_used_as_an_address_refuses(self):
        with self.assertRaisesRegex(ValueError, 'uninitialised or released frame word'):
            self.derive(callback_extra='    ldr r0, [r1, #8]\n    ldr r0, [r0]')

    def test_a_released_word_is_only_copied(self):
        # The caller's released word at entry-SP-36 is descriptor word +8, which the wrapper never writes:
        # the scheduler copies it and both words still hold it at the return; using it as an address refuses.
        facts = self.derive(released=(-36,))
        holding = sorted(offset for offset, values in facts.released.items()
                         if any(motion.describe(value) == 'released entry-SP-36' for value in values))
        self.assertEqual(holding, [-100, -36])          # the descriptor word and the scheduler's copy of it
        with self.assertRaisesRegex(ValueError, 'uninitialised or released frame word'):
            self.derive(released=(-36,), callback_extra='    ldr r0, [r1, #8]\n    ldr r0, [r0]')

    def test_an_unpinned_call_refuses(self):
        with self.assertRaisesRegex(ValueError, 'call to unpinned 0x08011000'):
            self.derive(callback_extra='    bl copy')

    def test_unsupported_encodings_refuse(self):
        with self.assertRaisesRegex(ValueError, 'unsupported instruction'):
            self.derive(callback_extra='    ldrsh r0, [r3, r0]')

    # ---- the site rules ---------------------------------------------------------------------
    def test_owner_positions_are_read_through_and_the_block_words_released(self):
        proof = self.walk()
        (record,) = proof.motion_summaries.observations.values()
        frame = record['frame_bytes']
        self.assertEqual(frame, 40)
        self.assertEqual(record['owner'], [['R1', 8 - frame], ['R2', 16 - frame]])
        base = match.FORWARD_STALE_BASE
        self.assertEqual(record['returned'], [[base - 56, 8 - frame], [base - 52, 16 - frame]])
        lines = proof.motion_summaries.lines()
        self.assertTrue(lines[0].startswith(f'* buffer motion wrapper: `{motion.NAME}`: '))
        self.assertIn('R1 read at +0:2 +2:2 +4:2', lines[1])
        self.assertIn('local addresses R1=sp+8 R2=sp+16; returns released entry-SP-56=sp+8 '
                      'released entry-SP-52=sp+16', lines[2])
        self.assertEqual(lines[3], f'* buffer motion wrapper premise: {motion.PREMISE}')
        replayed = proof.loop_replay_lines()
        start = replayed.index(lines[0])
        self.assertEqual(replayed[start:start + 4], lines)

    def test_the_fingerprint_binds_the_evidence_only_when_used(self):
        used = self.walk()
        digest = used.fingerprint()
        record = next(iter(used.motion_summaries.observations.values()))
        record['facts_sha256'] = '0' * 64
        self.assertNotEqual(used.fingerprint(), digest)

    def test_a_callee_saved_position_is_restored_and_released(self):
        proof = self.walk(owner_setup='    add r4, sp, #8', owner_after='    ldrh r0, [r4]')
        (record,) = proof.motion_summaries.observations.values()
        self.assertIn(['S4', 8 - 40], record['owner'])
        self.assertIn([match.FORWARD_STALE_BASE - 12, 8 - 40], record['returned'])

    def test_an_r8_position_returns_in_r3(self):
        proof = self.walk(owner_setup='    add r4, sp, #8\n    mov r8, r4\n    movs r4, #0')
        (record,) = proof.motion_summaries.observations.values()
        self.assertIn(['S8', 8 - 40], record['owner'])
        self.assertIn([R3, 8 - 40], record['returned'])
        self.assertIn([match.FORWARD_STALE_BASE - 16, 8 - 40], record['returned'])

    def refused(self, pattern, **variant):
        with self.assertRaisesRegex(ValueError, pattern):
            self.walk(**variant)

    def test_a_wrapper_that_stores_r1_outside_its_block_is_refused(self):
        self.refused('R1 is stored outside the wrapper\'s parameter block', wrapper_extra='    str r1, [sp, #24]')

    def test_a_callback_that_writes_through_a_position_is_refused(self):
        self.refused('R2 is written through, kept or used as a number', callback_extra='    strh r0, [r3]')

    def test_a_callback_that_keeps_a_position_is_refused(self):
        self.refused('R1 is written through, kept or used as a number',
                     callback_extra='    ldr r0, [r4, #4]\n    str r0, [r2, #20]')

    def test_a_callback_that_uses_a_position_as_a_number_is_refused(self):
        self.refused('R1 is written through, kept or used as a number',
                     callback_extra='    ldr r0, [r4, #4]\n    cmp r0, #0\n    beq 3f')

    def test_a_local_address_in_r0_or_r3_is_refused(self):
        for label, variant in (('R0', dict(owner_setup='    add r0, sp, #8')), ('R3', dict(r3='    add r3, sp, #8'))):
            with self.subTest(register=label):
                self.refused('only in R1 and R2', **variant)

    def test_a_read_outside_the_allocated_locals_is_refused(self):
        # R1 at the last local word: +4 reaches the owner's saved R8 word.
        self.refused('outside allocated local words', r1='    add r1, sp, #20')

    def test_a_callee_saved_position_read_through_is_refused(self):
        self.refused('S5 is read through', owner_setup='    add r5, sp, #8', wrapper_extra='    ldrh r0, [r5]')

    def test_a_deep_released_word_stays_tracked_across_the_opaque_calls(self):
        proof = self.walk(owner_setup='    add r1, sp, #8\n    bl deep')
        (record,) = proof.motion_summaries.observations.values()
        self.assertEqual(record['released_in'], [[-204, 8 - 40]])
        self.assertIn([match.FORWARD_STALE_BASE - 204, 8 - 40], record['returned'])
        facts = proof.motion_summaries.lines()[1]
        self.assertIn('entry-SP-204=maybe(released entry-SP-204)', facts)
        self.assertIn('caller released words at entry-SP-204', facts)

    def test_a_local_address_live_in_r9_at_an_opaque_call_is_refused(self):
        self.refused('S9 is in a callee-saved register at an opaque call',
                     owner_setup='    add r4, sp, #8\n    mov r9, r4\n    movs r4, #0')

    def test_an_argument_word_outside_the_allocated_locals_is_refused(self):
        # W6 is the owner's saved R8 word.
        self.refused('outside allocated local words', wrapper_extra='    ldr r0, [sp, #84]\n    str r0, [sp, #12]')

    def test_an_owner_address_in_a_kept_word_is_refused(self):
        self.refused('pointer-bearing local word is an argument word',
                     owner_setup='    add r4, sp, #8\n    str r4, [sp]\n    movs r4, #0')

    def test_a_read_over_a_pointer_bearing_word_is_refused(self):
        self.refused('a read through R1 overlaps a pointer-bearing word',
                     owner_setup='    add r4, sp, #16\n    str r4, [sp, #12]\n    movs r4, #0')

    def test_a_same_shape_callee_at_another_address_is_walked_as_before(self):
        with self.assertRaises(ValueError) as caught:
            self.walk(target='copy')
        self.assertNotIn('motion', str(caught.exception))

    def test_changed_bytes_at_a_pinned_address_are_refused(self):
        rom = bytearray(self.build())
        rom[0x080D6284 - BASE + 8] ^= 1          # a store offset inside the wrapper
        mapping = json.dumps(self.entries).encode()
        proof = match.BufferCallProof(bytes(rom), mapping, stack_arguments=True, copy_helper_index=b'',
                                      forward_slots=True)
        with self.assertRaisesRegex(ValueError, 'differs from the pinned motion-task body'):
            match.verify_leaf_instructions(bytes(rom[OWNER - BASE:self.symbols['owner_end'] - BASE]), OWNER, True,
                                           buffer_proof=proof, call_resolver=proof.target)

    def test_the_disabled_policy_walks_the_wrapper_as_before(self):
        with patch.object(motion.POLICY, 'enabled', False), self.assertRaises(ValueError) as caught:
            self.walk()
        self.assertNotIn('motion', str(caught.exception))

    def test_an_aborted_pass_leaves_no_observation(self):
        proof = self.walk()
        saved = proof._snapshot_ledgers()
        proof.motion_summaries.observations['x'] = {}
        proof._restore_ledgers(saved)
        self.assertNotIn('x', proof.motion_summaries.observations)


# ---- the real pinned bodies -------------------------------------------------------------------
NATIVE_C = """typedef struct { short x, y, z; } Point;
extern short gMotionOrigin;
extern int func_080D6238(void *unit, Point *from, Point *to, int a, int b, int c, int d, int e, int f, void *parent);
extern int func_080D6284(void *unit, Point *from, Point *to, int a, int b, int c, int d, int e, void *parent);
int func_08010000(void *unit, int x)
{
    Point from, to;

    from.x = x + gMotionOrigin;
    from.y = x + 1;
    from.z = x + 2;
    to.x = 0;
    to.y = 1;
    to.z = 2;
    func_080D6238(unit, &from, &to, 3, 4, 5, 6, 7, 8, 0);
    return func_080D6284(unit, &to, &from, 3, 4, 5, 6, 7, 0);
}
"""


# The allocator and the functions it calls (function-index spans), which the callee-saved watch walks
# when the owner keeps a local address in R4-R11 across a wrapper call.
ALLOCATOR_CHAIN = ((0x08006C88, 0x08006D36), (0x08006D38, 0x08006D9E), (0x08006DA0, 0x08006E26),
                   (0x08006E28, 0x08006EBE), (0x08006EC0, 0x08006FCA), (0x08007138, 0x0800716E))


def approved_rom():
    selected = os.environ.get('FFTA_ROM')
    return Path(selected) if selected and Path(selected).is_file() else None


def compiler_present():
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and tools_present()


def replay_in_subprocess(root, address, report_text, rom):
    """report_matches in a fresh interpreter (match imported as a module, as status.py does)."""
    path = Path(root) / 'replayed.md'
    path.write_text(report_text)
    code = ('import sys; sys.path.insert(0, sys.argv[1]); import match_evidence as e; '
            'print(e.report_matches(open(sys.argv[2]).read(), sys.argv[3], int(sys.argv[4], 16)))')
    result = subprocess.run([sys.executable, '-c', code, str(ROOT / 'tools'), str(path), str(root), f'0x{address:08X}'],
                            capture_output=True, text=True, timeout=900,
                            env=dict(os.environ, FFTA_ROM=str(rom), PYTHONDONTWRITEBYTECODE='1'))
    return result.stdout.strip().splitlines()[-1:] == ['True']


@unittest.skipUnless(approved_rom() and compiler_present(), 'FFTA_ROM, agbcc and ARM binutils required')
class RealBodyNativeTests(unittest.TestCase):
    """An agbcc-compiled owner calling both real wrappers, issued by match.py and replayed."""

    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='motion_wrapper_native_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.build()

    def build(self):
        root, real = self.root, approved_rom().read_bytes()
        for name in ('src', 'include', 'config', 'symbols'):
            (root / name).mkdir(parents=True, exist_ok=True)
        rom = bytearray(ROM_END - BASE)
        entries = []
        for address, (size, _) in sorted(motion.PINS.items()):
            # The call-via thunks are followed by their `mov r8, r8`, which the thunk check reads.
            copied = size + (2 if address in (motion.CALL_VIA_R2, motion.CALL_VIA_R3) else 0)
            rom[address - BASE:address - BASE + copied] = real[address - BASE:address - BASE + copied]
            entries.append({'rom': f'0x{address:08X}', 'end': f'0x{address + size:08X}', 'mode': 'thumb'})
        for address, end in ALLOCATOR_CHAIN:
            rom[address - BASE:end - BASE] = real[address - BASE:end - BASE]
            entries.append({'rom': f'0x{address:08X}', 'end': f'0x{end:08X}', 'mode': 'thumb'})
        entries.sort(key=lambda entry: entry['rom'])
        (root / f'src/{OWNER:08X}.c').write_text(NATIVE_C)
        objects = b'{"gMotionOrigin": "0x02001000"}\n'
        (root / 'config/data_symbols.json').write_bytes(objects)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, root, OWNER, f'src/{OWNER:08X}.c')
            symbol, _ = match.function_record(original, f'func_{OWNER:08X}', OWNER, True)
            entries.insert(0, {'rom': f'0x{OWNER:08X}', 'end': f'0x{OWNER + symbol["size"]:08X}', 'mode': 'thumb'})
            mapping = json.dumps(entries).encode()
            body, _, _ = match.link_calls(runner, workspace, args, original, OWNER, mapping, len(rom),
                                          bytes(rom), objects, {})
        rom[OWNER - BASE:OWNER - BASE + len(body)] = body
        (root / 'config/functions.json').write_bytes(mapping)
        (root / 'symbols/functions.txt').write_bytes(index_text(entries))
        (root / 'baserom.bin').write_bytes(bytes(rom))

    def issue(self, disabled=False):
        report = self.root / f'docs/match/{OWNER:08X}.md'
        if report.exists():
            report.unlink()
        command = [sys.executable, str(ROOT / 'tools/match.py'), '--root', str(self.root), f'0x{OWNER:08X}']
        if disabled:
            command = [sys.executable, '-c',
                       'import runpy, sys; sys.path.insert(0, sys.argv[1]); import motion_wrapper_summary_profile as m; '
                       'm.POLICY.enabled = False; sys.argv = sys.argv[2:]; runpy.run_path(sys.argv[0], run_name="__main__")',
                       str(ROOT / 'tools'), *command[1:]]
        result = subprocess.run(command, capture_output=True, text=True, timeout=900,
                                env=dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin'), PYTHONDONTWRITEBYTECODE='1'))
        return result.returncode, result.stdout + result.stderr, report.read_text() if report.exists() else None

    def test_both_wrappers_are_summarised_and_the_report_replays(self):
        code, output, report = self.issue()
        self.assertEqual(code, 0, output[-3000:])
        lines = report.splitlines()
        # The owner reads a named datum, so its report is checked by the data-buffer route.
        self.assertIn(f'* verification: `{data_buffer.SCHEMA}`', lines)
        sites = [line for line in lines if line.startswith('* buffer motion wrapper site: ')]
        self.assertEqual(sorted(line.split()[5] for line in sites), ['0x080D6238', '0x080D6284'])
        facts = [line for line in lines if line.startswith('* buffer motion wrapper facts: ')]
        self.assertEqual(len(facts), 2)
        for line in facts:
            self.assertIn('R1 read at +0:2 +2:2 +4:2; R2 read at +0:2 +2:2 +4:2', line)
            self.assertIn('written through W', line)
        # The second call is derived with the first call's released block words given as frame words.
        self.assertIn('caller released words at', ' '.join(facts))
        self.assertIn(f'* buffer motion wrapper premise: {motion.PREMISE}', lines)
        rom = self.root / 'baserom.bin'
        self.assertTrue(replay_in_subprocess(self.root, OWNER, report, rom))
        for label, forged in {
                'facts': report.replace('R1 read at +0:2 +2:2 +4:2', 'R1 read at +0:2 +2:2', 1),
                'premise': '\n'.join(line for line in lines if not line.startswith('* buffer motion wrapper premise')),
                'site': report.replace(sites[0], sites[0].replace('local addresses R', 'local addresses R1=sp+0 R', 1)),
        }.items():
            with self.subTest(forgery=label):
                self.assertNotEqual(forged, report)
                with patch.dict(os.environ, FFTA_ROM=str(rom)):
                    self.assertFalse(evidence.report_matches(forged, self.root, OWNER))

    def test_without_the_summary_the_owner_is_refused_as_before(self):
        code, output, report = self.issue(disabled=True)
        self.assertNotEqual(code, 0)
        self.assertIsNone(report)

    def test_a_changed_wrapper_byte_is_refused(self):
        rom = bytearray((self.root / 'baserom.bin').read_bytes())
        rom[0x080D6284 - BASE + 0x16] ^= 4         # a store offset inside the wrapper
        (self.root / 'baserom.bin').write_bytes(bytes(rom))
        code, output, report = self.issue()
        self.assertNotEqual(code, 0)
        self.assertIn('differs from the pinned motion-task body', output)


# ---- the two decomp functions -----------------------------------------------------------------
DECOMP = {0x08100EF0: 2, 0x08103510: 1}        # address: motion-wrapper sites


def decomp_root():
    return Path(os.environ.get('FFTA_ROOT', ROOT.parent / 'fftadecomp')).resolve()


@unittest.skipUnless(approved_rom() and compiler_present(), 'FFTA_ROM, agbcc and ARM binutils required')
class DecompFunctionTests(unittest.TestCase):
    """08100EF0 and 08103510 issued from an FFTA_ROOT checkout that carries their sources."""

    def run_one(self, address):
        game = decomp_root()
        sources = [path for path in evidence.source_paths(game, address) if path.name == f'{address:08X}.c']
        if not sources:
            self.skipTest(f'FFTA_ROOT has no source for {address:08X}')
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix=f'motion_wrapper_{address:08X}_', dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for path in (*evidence.source_paths(game, address), *(game / 'config').glob('*.json'),
                     game / 'symbols/functions.txt'):
            target = root / path.relative_to(game)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
        rom = approved_rom().resolve()
        result = subprocess.run([sys.executable, str(ROOT / 'tools/match.py'), '--root', str(root), f'0x{address:08X}'],
                                capture_output=True, text=True, timeout=1800,
                                env=dict(os.environ, FFTA_ROM=str(rom), PYTHONDONTWRITEBYTECODE='1'))
        self.assertEqual(result.returncode, 0, (result.stdout + result.stderr)[-3000:])
        report = (root / f'docs/match/{address:08X}.md').read_text()
        sites = [line for line in report.splitlines() if line.startswith('* buffer motion wrapper site: ')]
        self.assertEqual(len(sites), DECOMP[address])
        self.assertTrue(replay_in_subprocess(root, address, report, rom))

    def test_08100EF0(self):
        self.run_one(0x08100EF0)

    def test_08103510(self):
        self.run_one(0x08103510)
