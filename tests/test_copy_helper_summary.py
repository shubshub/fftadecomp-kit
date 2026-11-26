"""The pinned copy helper func_081443FC summarised in the default stack buffer walk (kit #240)."""
import ast
import hashlib
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import match
import match_evidence as evidence
import copy_helper_summary_profile as summary
import rom_table_copy_profile as rtc
import data_buffer_profile as data_buffer
# The module, not its test classes: importing a TestCase class would run it here again.
import test_data_buffer_calls as data_calls

R0, R1, R2, R3, R12, LR = (match.ARM_REG_R0, match.ARM_REG_R0 + 1, match.ARM_REG_R0 + 2,
                           match.ARM_REG_R0 + 3, match.ARM_REG_R12, match.ARM_REG_LR)
HELPER = summary.HELPER
OWNER, MID, LOCAL, LEAK, READ, FAKE = 0x08010000, 0x08011000, 0x08011800, 0x08012000, 0x08012800, 0x08013000
INDEXED = 0x08013800
RET3 = 0x08013800                      # an ordinary callee returning R1 + 4 in R3 (patched in per test)
ROM_SIZE = 0x150000
# The canonical 98-byte copy helper (49 halfwords), as in test_local_shadow_halfword_matrix.
HELPER_WORDS = (0xb530, 0x1c05, 0x1c2c, 0x1c0b, 0x2a0f, 0xd919, 0x1c18, 0x4328, 0x2103, 0x4008,
                0x2800, 0xd113, 0x1c29, 0xcb01, 0xc101, 0xcb01, 0xc101, 0xcb01, 0xc101, 0xcb01,
                0xc101, 0x3a10, 0x2a0f, 0xd8f4, 0x2a03, 0xd904, 0xcb01, 0xc101, 0x3a04, 0x2a03,
                0xd8fa, 0x1c0c, 0x3a01, 0x2001, 0x4240, 0x4282, 0xd007, 0x1c01, 0x7818, 0x7020,
                0x3301, 0x3401, 0x3a01, 0x428a, 0xd1f8, 0x1c28, 0xbc30, 0xbc02, 0x4708)
BODY = struct.pack('<49H', *HELPER_WORDS)
# The caller's local frame: push {r4, lr}; sub sp, #frame.  Entry SP is offset 0.
TAIL = (0x7840,)                       # ldrb r0, [r0, #1]: reads the copy, kills R0


def bl(site, target):
    value = target - site - 4
    return struct.pack('<HH', 0xf000 | ((value >> 12) & 0x7ff), 0xf800 | ((value >> 1) & 0x7ff))


def assemble(address, tokens):
    raw = bytearray()
    for token in tokens:
        raw += bl(address + len(raw), token) if token >= 0x08000000 else struct.pack('<H', token)
    return bytes(raw)


def owner(setup=(0x4668, 0x2100), count=4, frame=8, tail=TAIL, target=HELPER):
    """push {r4,lr}; sub sp,#frame; <setup>; movs r2,#count; bl target; <tail>; epilogue."""
    count_setup = () if count is None else (0x2200 | count,)
    return [0xb510, 0xb080 | frame // 4, *setup, *count_setup, target, *tail,
            0xb000 | frame // 4, 0xbc10, 0xbc02, 0x4708]


CALLEES = {
    # push {lr}; movs r1,#0; movs r2,#4; bl HELPER; pop {r0}; bx r0 -- forwards the caller's R0
    MID: [0xb500, 0x2100, 0x2204, HELPER, 0xbc01, 0x4700],
    # push {lr}; sub sp,#8; mov r0,sp; movs r1,#0; movs r2,#4; bl HELPER; add sp,#8; pop {r0}; bx r0
    LOCAL: [0xb500, 0xb082, 0x4668, 0x2100, 0x2204, HELPER, 0xb002, 0xbc01, 0x4700],
    LEAK: [0x6008, 0x4770],             # str r0, [r1]; bx lr: stores the pointer
    READ: [0x7800, 0x4770],             # ldrb r0, [r0]; bx lr: a bounded read
    # movs r1, #0; ldrb r0, [r0, r1]; bx lr: a bounded read through a register index, which only the
    # version-2 proof admits
    INDEXED: [0x2100, 0x5c40, 0x4770],
}


CONCRETE_SP = 0x03007F00


def concrete_copy(body, count, destination, source, data):
    """Concrete ARMv4T Thumb execution of the helper's encodings; returns state and accesses."""
    mask = 0xFFFFFFFF
    regs = [(0x2468ACE0 + 0x1111 * i) & mask for i in range(16)]
    regs[0], regs[1], regs[2], regs[13], regs[14] = destination, source, count, CONCRETE_SP, 0x08012345
    initial = regs[:]
    memory = {source + i: value for i, value in enumerate(data)}
    reads, writes, trace = [], [], []
    n = z = c = v = False

    def load(address, size):
        reads.append((address, size))
        return int.from_bytes(bytes(memory[address + i] for i in range(size)), 'little')

    def store(address, value, size):
        writes.append((address, size))
        for i in range(size):
            memory[address + i] = value >> (8 * i) & 255

    def subtract(a, b):
        r = (a - b) & mask
        return r, bool(r >> 31), r == 0, a >= b, bool((a ^ b) & (a ^ r) & 0x80000000)

    pc = 0
    for _ in range(8192):
        trace.append(pc)
        w = struct.unpack_from('<H', body, pc)[0]
        following = pc + 2
        rd, rm = w & 7, w >> 3 & 7
        if w == 0xB530:                                       # push {r4, r5, lr}
            regs[13] -= 12
            for i, register in enumerate((4, 5, 14)):
                store(regs[13] + 4 * i, regs[register], 4)
        elif w == 0xBC30:                                     # pop {r4, r5}
            regs[4], regs[5] = load(regs[13], 4), load(regs[13] + 4, 4)
            regs[13] += 8
        elif w == 0xBC02:                                     # pop {r1}
            regs[1] = load(regs[13], 4)
            regs[13] += 4
        elif w == 0x4708:                                     # bx r1
            return regs, initial, memory, reads, writes, trace
        elif w & 0xFFC0 == 0x1C00:                            # adds rd, rn, #0
            regs[rd] = regs[rm]
            n, z, c, v = bool(regs[rd] >> 31), regs[rd] == 0, False, False
        elif w & 0xF800 == 0x2000:                            # movs rd, #imm8
            regs[w >> 8 & 7] = w & 255
            n, z = False, w & 255 == 0
        elif w & 0xF800 == 0x2800:                            # cmp rn, #imm8
            _, n, z, c, v = subtract(regs[w >> 8 & 7], w & 255)
        elif w & 0xF800 == 0x3000:                            # adds rd, #imm8
            a, b = regs[w >> 8 & 7], w & 255
            r = (a + b) & mask
            regs[w >> 8 & 7], n, z, c, v = r, bool(r >> 31), r == 0, a + b > mask, bool(~(a ^ b) & (a ^ r) & 0x80000000)
        elif w & 0xF800 == 0x3800:                            # subs rd, #imm8
            regs[w >> 8 & 7], n, z, c, v = subtract(regs[w >> 8 & 7], w & 255)
        elif w & 0xFFC0 in (0x4000, 0x4300):                  # ands / orrs rd, rm
            regs[rd] = regs[rd] & regs[rm] if w & 0xFFC0 == 0x4000 else regs[rd] | regs[rm]
            n, z = bool(regs[rd] >> 31), regs[rd] == 0
        elif w & 0xFFC0 == 0x4240:                            # negs rd, rm
            regs[rd], n, z, c, v = subtract(0, regs[rm])
        elif w & 0xFFC0 == 0x4280:                            # cmp rn, rm
            _, n, z, c, v = subtract(regs[rd], regs[rm])
        elif w & 0xF000 == 0xC000:                            # ldmia / stmia rb!, {list}
            base, registers = w >> 8 & 7, [i for i in range(8) if w >> i & 1]
            address = regs[base] & ~3                         # ARMv4T LDM/STM ignore address bits 1:0
            for i, register in enumerate(registers):
                if w & 0x800:
                    regs[register] = load(address + 4 * i, 4)
                else:
                    store(address + 4 * i, regs[register], 4)
            regs[base] = (regs[base] + 4 * len(registers)) & mask
        elif w & 0xF800 == 0x7800:                            # ldrb rd, [rn, #imm5]
            regs[rd] = load(regs[rm] + (w >> 6 & 31), 1)
        elif w & 0xF800 == 0x7000:                            # strb rd, [rn, #imm5]
            store(regs[rm] + (w >> 6 & 31), regs[rd] & 255, 1)
        elif w & 0xF000 == 0xD000:                            # b<cond>
            take = {0: z, 1: not z, 8: c and not z, 9: not c or z}[w >> 8 & 15]
            if take:
                following = pc + 4 + 2 * ((w & 255) - 256 if w & 128 else w & 255)
        else:
            raise AssertionError(f'concrete executor has no rule for {w:04X}')
        pc = following
    raise AssertionError('concrete executor did not return')


def environment(code, *, body=BODY, helper_instrs=49):
    data = assemble(OWNER, code)
    rom = bytearray(ROM_SIZE)
    spans = [(OWNER, data, None), (HELPER, body, helper_instrs), (FAKE, body, 49)]
    spans += [(address, assemble(address, tokens), None) for address, tokens in CALLEES.items()]
    for address, raw, _ in spans:
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
    rows = [dict(rom=f'0x{a:08X}', end=f'0x{a + len(raw):08X}', mode='thumb',
                 **({} if n is None else {'instrs': n})) for a, raw, n in sorted(spans)]
    index = ''.join(f'{a:08X} {a + len(raw):08X} {len(raw)} {n or len(raw) // 2} return\n'
                    for a, raw, n in sorted(spans)).encode()
    return dict(data=data, rom=bytes(rom), mapping=json.dumps(rows).encode(), index=index)


def prove(code, *, index=True, stack_arguments=True, **options):
    env = environment(code, **options)
    proof = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=stack_arguments, loop_replay=True,
                                  copy_helper_index=env['index'] if index else None)
    match.verify_leaf_instructions(env['data'], OWNER, True, buffer_proof=proof,
                                   call_resolver=proof.target, incoming_narrow_reads=True)
    return proof, env


def observations(proof):
    return proof.copy_summaries.evidence()['observations']


class InterpreterTests(unittest.TestCase):
    def test_fixture_is_the_pinned_helper(self):
        self.assertEqual(hashlib.sha256(BODY).hexdigest(), rtc.COPY_SHA256)

    def test_every_count_and_alignment_copies_exactly(self):
        for count in (*range(0, 40), 63, 64, 65, 127, 255, 256):
            for destination in range(4):
                for source in range(4):
                    run = summary.run(BODY, HELPER, count, destination, source)
                    written = sorted({offset for region, start, width in run['writes']
                                      if region == 'destination' for offset in range(start, start + width)})
                    self.assertEqual(written, list(range(count)))
                    self.assertTrue(all(region in ('source', 'stack') for region, _, _ in run['reads']))
                    self.assertEqual({(region, start) for region, start, width in run['writes']
                                      if region == 'stack'}, {('stack', -12), ('stack', -8), ('stack', -4)})

    def test_word_path_runs_only_when_both_are_aligned(self):
        aligned = summary.run(BODY, HELPER, 64, 0, 0)
        unaligned = summary.run(BODY, HELPER, 64, 1, 0)
        self.assertIn(['source', 0, 4], aligned['reads'])
        self.assertTrue(all(width == 1 for region, _, width in unaligned['reads'] if region == 'source'))
        self.assertLess(aligned['steps'], unaligned['steps'])
        # Counts up to 15 always take the byte loop: the trace is the same for every alignment.
        self.assertEqual(len({tuple(summary.run(BODY, HELPER, 15, d, s)['trace'])
                              for d in range(4) for s in range(4)}), 1)

    def test_contract_digest_is_stable_and_count_specific(self):
        self.assertEqual(summary.contract(BODY, 4), summary.contract(BODY, 4))
        self.assertNotEqual(summary.contract(BODY, 4)['execution_sha256'],
                            summary.contract(BODY, 5)['execution_sha256'])
        self.assertEqual(summary.contract(BODY, 4)['cases'], 16)

    def mutated(self, offset, word):
        raw = bytearray(BODY)
        struct.pack_into('<H', raw, offset, word)
        return bytes(raw)

    def test_mutated_bodies_are_refused(self):
        cases = {
            'return registers differ': (90, 0x1c20, 4),          # adds r0, r4, #0: R0 = dst + n
            'leaves the source and destination ranges': (2, 0x1c0d, 4),   # adds r5, r1, #0: writes the source
            'leaves the source and destination ranges ': (76, 0x7858, 4),  # ldrb r0, [r3, #1]
            'leaves the source and destination ranges  ': (78, 0x7060, 4),  # strb r0, [r4, #1]
            'unmodelled encoding': (14, 0x4068, 16),             # eors r0, r5
            'returns other than to its entry LR': (92, 0xbc10, 4),  # pop {r4}: R5's save becomes the return
            'compares an opaque value': (86, 0x4288, 4),         # cmp r0, r1: a data byte steers the loop
            'stores a pointer': (78, 0x7024, 4),                 # strb r4, [r4]
            'non-source value to the destination': (78, 0x7022, 4),  # strb r2, [r4]
            'computes with an opaque value': (6, 0x1c1b, 4),     # adds r3, r3, #0: reads the entry R3
            'masks more than the known low pointer bits': (16, 0x2107, 16),  # movs r1, #7
            'step budget': (88, 0xe7fe, 4),                      # b . : never returns
            'unaligned in this case': (10, 0xe005, 16),          # b to the word loop: skips the test
            'leaves its own save words': (0, 0xb5f0, 4),         # push {r4-r7, lr}
            'does not restore SP, LR, R4-R11 and R12': (92, 0xbc50, 4),  # pop {r4, r6}
            'does not copy each source byte': (62, 0x1c2c, 65),  # adds r4, r5, #0: the tail restarts at dst
        }
        for message, (offset, word, count) in cases.items():
            with self.subTest(message=message):
                body = self.mutated(offset, word)
                with self.assertRaisesRegex(ValueError, message.strip()):
                    for destination in range(4):
                        for source in range(4):
                            summary.run(body, HELPER, count, destination, source)

    def test_more_mutated_bodies_are_refused(self):
        # (offset, word) edits; count; expected refusal.  Branch offsets are from the edited halfword.
        cases = [
            ([(76, 0x7810)], 4, 'accesses memory through a non-pointer'),       # ldrb r0, [r2]
            ([(6, 0x1e4b)], 4, 'leaves the source and destination ranges'),     # subs r3, r1, #1: reads src-1
            ([(14, 0x4330)], 16, 'computes with an opaque value'),              # orrs r0, r6
            ([(8, 0x1c2c)], 4, 'branch reads an unknown flag'),                 # adds r4, r5, #0 before bls
            ([(20, 0x2d00)], 16, 'compares an opaque value or a pointer'),      # cmp r5, #0
            ([(68, 0x4268)], 4, 'negates an opaque value or a pointer'),        # negs r0, r5
            ([(26, 0xcb08)], 16, 'block transfer list is ambiguous'),           # ldm r3!, {r3}
            ([(94, 0xbd02)], 4, 'pops the program counter'),                    # pop {r1, pc}
            ([(94, 0x4770)], 0, 'does not restore SP, LR, R4-R11 and R12'),     # bx lr with the LR still saved
            # Count 0 skips the byte loop, so its words can hold a different ending:
            # b to offset 74; <one instruction>; bx lr.
            ([(96, 0xe7f3), (74, 0x2105), (76, 0x4770)], 0, 'R1 = LR'),         # movs r1, #5
            ([(96, 0xe7f3), (74, 0x2205), (76, 0x4770)], 0, 'R2 = -1'),         # movs r2, #5
            ([(96, 0xe7f3), (74, 0x2305), (76, 0x4770)], 0, 'R3 = src'),        # movs r3, #5
        ]
        for edits, count, message in cases:
            with self.subTest(message=message):
                raw = bytearray(BODY)
                for offset, word in edits:
                    struct.pack_into('<H', raw, offset, word)
                with self.assertRaisesRegex(ValueError, message.replace('+', '\\+')):
                    for destination in range(4):
                        for source in range(4):
                            summary.run(bytes(raw), HELPER, count, destination, source)

    def test_hand_written_bodies(self):
        words = lambda *halfwords: struct.pack(f'<{len(halfwords)}H', *halfwords)
        # Copies two bytes crosswise with every register right: only the content check refuses.
        swap = words(0xb530, 0x1c05, 0x1c2c, 0x1c0b, 0x7858, 0x7020, 0x7818, 0x7060, 0x3302,
                     0x2101, 0x424a, 0x1c28, 0xbc30, 0xbc02, 0x4708)
        with self.assertRaisesRegex(ValueError, 'does not copy each source byte to its destination offset'):
            summary.run(swap, HELPER, 2, 0, 0)
        # Ends exactly as the helper does but writes nothing: push {lr}; adds r3, r1, #1; R2 = -1; pop {r1}; bx r1.
        skips = words(0xb500, 0x1c4b, 0x2201, 0x4252, 0xbc02, 0x4708)
        with self.assertRaisesRegex(ValueError, 'does not copy each source byte to its destination offset'):
            summary.run(skips, HELPER, 1, 0, 0)
        # Saves and restores the entry R3 (push {r3, r4, lr}) and otherwise copies one byte correctly.
        saves = words(0xb518, 0x780b, 0x7003, 0x1c4b, 0x2201, 0x4252, 0xbc12, 0xbc02, 0x4708)
        with self.assertRaisesRegex(ValueError, 'reads the entry R3 or R12'):
            summary.run(saves, HELPER, 1, 0, 0)
        # The same routine without the R3 save is admitted (push {r4, lr}).
        plain = words(0xb510, 0x780b, 0x7003, 0x1c4b, 0x2201, 0x4252, 0xbc10, 0xbc02, 0x4708)
        self.assertEqual(summary.run(plain, HELPER, 1, 0, 0)['writes'], [['stack', -8, 4], ['stack', -4, 4], ['destination', 0, 1]])

    def test_cross_check_against_the_kit_concrete_executor(self):
        # The kit's independent concrete decoder for the same helper (byte path, counts 2..10).
        from test_compiler_small_local_copy_prerequisite import raw_run as concrete_run
        for count in (2, 4, 8, 10):
            for values in (bytes(range(count)), bytes([0xA5]) * count,
                           bytes((i * 37 + 19) & 255 for i in range(count))):
                for destination, source in ((0x03007001, 0x02001001), (0x03007000, 0x02001000),
                                            (0x03007002, 0x02001003)):
                    with self.subTest(count=count, values=values, destination=destination):
                        regs, initial, memory, reads, writes, trace, _ = concrete_run(
                            BODY, values, destination, source)
                        mine = summary.run(BODY, HELPER, count, destination & 3, source & 3)
                        concrete_writes = sorted({a - destination for a, _ in writes if destination <= a < destination + count})
                        my_writes = sorted({o for region, start, width in mine['writes']
                                            if region == 'destination' for o in range(start, start + width)})
                        self.assertEqual(my_writes, concrete_writes)
                        self.assertEqual(my_writes, list(range(count)))
                        concrete_reads = sorted({a - source for a, _, _ in reads if source <= a < source + count})
                        my_reads = sorted({o for region, start, width in mine['reads']
                                           if region == 'source' for o in range(start, start + width)})
                        self.assertEqual(my_reads, concrete_reads)
                        # Final register state agrees on the facts the summary relies on.
                        self.assertEqual((regs[1], regs[2], regs[3] - source), (initial[14], 0xFFFFFFFF, count))
                        self.assertEqual([regs[i] for i in (0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13)],
                                         [initial[i] for i in (0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13)])

    def test_word_and_byte_paths_against_an_independent_concrete_executor(self):
        # raw_run above decodes only the byte path. concrete_copy decodes the helper's encodings
        # on concrete values, word path included, from the ARMv4T Thumb definitions.
        for count in (*range(0, 41), 63, 64, 65, 127, 128, 255, 256):
            for d in range(4):
                for s in range(4):
                    with self.subTest(count=count, d=d, s=s):
                        destination, source = 0x02001000 + d, 0x02009000 + s
                        data = bytes((i * 73 + 11) & 255 for i in range(count))
                        regs, initial, memory, reads, writes, trace = concrete_copy(
                            BODY, count, destination, source, data)
                        mine = summary.run(BODY, HELPER, count, d, s)
                        base = dict(destination=destination, source=source, stack=CONCRETE_SP)
                        self.assertEqual(trace, mine['trace'])
                        self.assertEqual(reads, [(base[r] + o, w) for r, o, w in mine['reads']])
                        self.assertEqual(writes, [(base[r] + o, w) for r, o, w in mine['writes']])
                        self.assertEqual(bytes(memory[destination + i] for i in range(count)), data)
                        self.assertEqual(regs[:4], [destination, initial[14], 0xFFFFFFFF, source + count])
                        self.assertEqual(regs[4:15], initial[4:15])

    def test_every_helper_instruction_is_modelled(self):
        # No byte of the pinned helper falls through to the "unmodelled encoding" branch.
        summary.run(BODY, HELPER, 64, 0, 0)   # the word path
        summary.run(BODY, HELPER, 4, 0, 0)     # the byte path
        import armv4t
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        for item in decoder.disasm(BODY, HELPER):
            self.assertTrue(armv4t.instruction(item), f'{item.mnemonic} {item.op_str}')

    def test_execution_digest_covers_every_case(self):
        cases = [summary.run(BODY, HELPER, 20, d, s) for d in range(4) for s in range(4)]
        self.assertEqual(summary.contract(BODY, 20)['execution_sha256'],
                         hashlib.sha256(json.dumps(cases, separators=(',', ':')).encode()).hexdigest())
        self.assertEqual(summary.contract(BODY, 20)['steps'], [min(c['steps'] for c in cases),
                                                                max(c['steps'] for c in cases)])

    def test_entry_scratch_reads_are_refused(self):
        # push {r3}/pop {r3} reads the entry R3 without computing with it.
        body = BODY[:0] + struct.pack('<H', 0xb538) + BODY[2:92] + struct.pack('<H', 0xbc38) + BODY[94:]
        with self.assertRaisesRegex(ValueError, 'leaves its own save words|reads the entry R3'):
            summary.run(body, HELPER, 4, 0, 0)

    def test_inputs_are_bounded(self):
        for count in (-1, summary.MAX_COUNT + 1):
            with self.subTest(count=count), self.assertRaisesRegex(ValueError, 'exact bounded inputs'):
                summary.run(BODY, HELPER, count, 0, 0)
        with self.assertRaisesRegex(ValueError, 'exact bounded inputs'):
            summary.run(BODY, HELPER, 4, 4, 0)


class WalkTests(unittest.TestCase):
    def test_local_destination_is_summarised(self):
        proof, _ = prove(owner())
        record, = observations(proof)
        self.assertEqual((record['count'], record['destination'], record['source'], record['frame_bytes']),
                         (4, -16, None, 16))
        self.assertEqual(record['returned'], [[0, -16]])
        self.assertEqual(record['dropped'], [])
        self.assertEqual(proof.dependencies[HELPER], BODY)
        self.assertEqual(proof.loop_replay_lines(), [
            f'* buffer copy summary: `{summary.POLICY}` 0x081443FC at 0x{OWNER + 10:08X}: count 4, '
            'destination sp+0, source external; returns r0=sp+0; drops none; pointer words 0; '
            f'contract 16 cases {summary.contract(BODY, 4)["execution_sha256"][:16]}'])
        self.assertEqual(proof.copy_summaries.evidence()['helper']['written_registers'],
                         ['r0', 'r1', 'r2', 'r3', 'r4', 'r5'])

    def test_an_aborted_joined_pass_leaves_no_observation(self):
        # A joined pass that ends in a loop replay may summarise calls the replay does not
        # make; like the base ledgers, its contracts and observations never enter the evidence.
        proof, _ = prove(owner())
        before = proof.copy_summaries.evidence()

        def aborted_then_empty(proof, address, *args, replay, **kwargs):
            if not replay:
                proof.copy_summaries.contracts[5] = {'aborted': True}
                proof.copy_summaries.observations['aborted'] = {'aborted': True}
                raise match._LoopReplayRequired()
            return proof.word_result({}, {})

        with patch.object(match.BufferCallProof, '_check_arguments', aborted_then_empty):
            proof.check_arguments(READ, {}, [], {}, frozenset())
        self.assertEqual(proof.copy_summaries.evidence(), before)

        def cleared_then_empty(proof, address, *args, replay, **kwargs):
            if not replay:
                proof.copy_summaries.contracts.clear()
                proof.copy_summaries.observations.clear()
                raise match._LoopReplayRequired()
            return proof.word_result({}, {})

        with patch.object(match.BufferCallProof, '_check_arguments', cleared_then_empty):
            proof.check_arguments(READ, {}, [], {}, frozenset())
        self.assertEqual(proof.copy_summaries.evidence(), before)

    def test_without_the_summary_the_walk_still_refuses(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: unsupported buffer pointer use or escape'):
            prove(owner(), index=False)
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: unsupported buffer pointer use or escape'):
            prove(owner((0x2000, 0x4669), tail=(0x2300,)), index=False)

    def test_local_source_returns_r3_one_past_it(self):
        # movs r0,#0; mov r1,sp: the helper leaves R3 = src+n = sp+4, a live frame pointer, and
        # R1 = its entry LR (a code address). R3 is handed back as an alias; R1 is dropped.
        proof, _ = prove(owner((0x2000, 0x4669), tail=(0x2300,)))     # movs r3,#0
        record, = observations(proof)
        self.assertEqual((record['destination'], record['source'], record['returned'], record['dropped']),
                         (None, -16, [[3, -12]], [[1, -16]]))
        self.assertIn('returns r3=sp+4; drops r1=sp+0', proof.loop_replay_lines()[0])
        # R3 stays tracked, so its later uses are checked as after an ordinary walked callee
        # that returns src+4 in R3: str r0,[r3,#8] overwrites the saved LR and a frame pointer
        # left in R3 reaches the return. Both refuse; dropping R3 admitted both.
        for tail in ((0x6098, 0x2300), (0x6018,)):                   # str r0,[r3,#8]; movs r3,#0 / str r0,[r3]
            with self.subTest(tail=tail):
                with self.assertRaises(ValueError):
                    prove(owner((0x2000, 0x4669), tail=tail))
                with patch.dict(CALLEES, {RET3: [0x1d0b, 0x4770]}), \
                        self.assertRaises(ValueError):                # adds r3, r1, #4; bx lr
                    prove(owner((0x2000, 0x4669), tail=tail, target=RET3))
        # R1 is not a frame pointer after the call.
        prove(owner((0x2000, 0x4669), tail=(0x6008, 0x2300)))        # str r0, [r1]; movs r3,#0

    def test_twelve_is_kept_and_three_is_dropped(self):
        # mov ip, r0 before the call; after it, mov r0, ip and pass R0 to a callee that stores it.
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{LEAK:08X}: unsupported buffer pointer use'):
            prove(owner((0x4668, 0x4684, 0x2100), tail=(0x4660, LEAK, 0x2000)))
        proof, _ = prove(owner((0x4668, 0x4684, 0x2100)))
        self.assertEqual(observations(proof)[0]['returned'], [[0, -16], [12, -16]])
        # mov r3, sp: an R3 alias at the call is dropped; afterwards R3 reaches the leak freely.
        proof, _ = prove(owner((0x4668, 0x466b, 0x2100), tail=(0x1c18, 0x2100, LEAK)))
        self.assertEqual(observations(proof)[0]['dropped'], [[3, -16]])
        self.assertEqual(observations(proof)[0]['returned'], [[0, -16]])

    def test_counts_above_fifteen(self):
        proof, _ = prove(owner(count=64, frame=64))
        self.assertEqual(proof.copy_summaries.evidence()['contracts'][0]['count'], 64)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            prove(owner(count=65, frame=64))
        proof, _ = prove(owner(count=255, frame=256))
        self.assertEqual(observations(proof)[0]['count'], 255)

    def test_count_must_be_an_exact_bounded_constant(self):
        for setup, count in (((0x4668, 0x2100), 0), ((0x4668, 0x2100, 0x1c22), None)):
            with self.subTest(count=count), self.assertRaisesRegex(
                    ValueError, 'buffer callee 0x081443FC: copy summary count must be an exact constant from 1 to 256'):
                prove(owner(setup, count=count))
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        for count in (summary.MAX_COUNT, summary.MAX_COUNT + 1):
            with self.subTest(count=count):
                call = lambda: proof.check_call(HELPER, {R0: -16}, stack, constants={R2: count}, site=OWNER + 8)
                if count > summary.MAX_COUNT:
                    with self.assertRaisesRegex(ValueError, 'exact constant from 1 to 256'):
                        call()
                else:
                    with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
                        call()

    def test_destination_must_fit_the_allocated_local_words(self):
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: buffer access is unaligned or outside allocated local words'):
            prove(owner(count=9))
        prove(owner(count=8))
        with self.assertRaisesRegex(ValueError, 'outside allocated local words'):
            prove(owner((0x4668, 0x3004, 0x2100), count=5))            # adds r0, #4: sp+4..sp+9

    def test_destination_may_not_hold_a_pointer_or_return_word(self):
        # add r1, sp, #4; str r1, [sp, #0]: the word at sp+0 holds a pointer.
        pointer = (0xa901, 0x9100, 0x4668, 0x2100)
        with self.assertRaisesRegex(ValueError, 'copy destination overlaps a pointer-bearing or return-carrying word'):
            prove(owner(pointer, count=8, frame=12, tail=(0x7840, 0x2100)))
        with self.assertRaisesRegex(ValueError, 'copy destination overlaps a pointer-bearing or return-carrying word'):
            prove(owner(pointer, count=1, frame=12, tail=(0x7840, 0x2100)))
        prove(owner((0xa901, 0x9100, 0xa801, 0x2100), count=8, frame=12, tail=(0x7840, 0x2100)))
        # mov r1, lr; str r1, [sp, #0]: the word at sp+0 carries the return address.
        with self.assertRaisesRegex(ValueError, 'copy destination overlaps a pointer-bearing or return-carrying word'):
            prove(owner((0x4671, 0x9100, 0x4668, 0x2100), count=4))

    def test_source_may_not_hold_a_pointer(self):
        # add r0, sp, #4; str r0, [sp, #0]; movs r0, #0; mov r1, sp: copies the pointer word.
        with self.assertRaisesRegex(ValueError, 'copy source overlaps a pointer-bearing word'):
            prove(owner((0xa801, 0x9000, 0x2000, 0x4669), count=4, frame=12, tail=(0x2300,)))
        # The same source four bytes higher does not include it.
        prove(owner((0xa801, 0x9000, 0x2000, 0xa901), count=4, frame=12, tail=(0x2300,)))

    def test_local_spans_must_be_disjoint(self):
        # mov r0, sp; add r1, sp, #4
        with self.assertRaisesRegex(ValueError, 'copy source and destination overlap'):
            prove(owner((0x4668, 0xa901), count=8, frame=16, tail=(0x7840, 0x2300)))
        proof, _ = prove(owner((0x4668, 0xa901), count=4, frame=16, tail=(0x7840, 0x2300)))
        self.assertEqual((observations(proof)[0]['returned'], observations(proof)[0]['dropped']),
                         ([[0, -24], [3, -16]], [[1, -20]]))

    def test_pointer_in_r2_or_lr_is_refused(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        for register in (R2, LR):
            with self.subTest(register=register), self.assertRaisesRegex(
                    ValueError, 'copy summary refuses a local pointer in R2 or LR'):
                proof.check_call(HELPER, {R0: -16, register: -12}, stack, constants={R2: 4}, site=OWNER + 8)

    def test_word_contexts_and_missing_sites_are_refused(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        with self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
            proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4}, site=OWNER + 8,
                             words={-12: ('constant', 1)})
        with self.assertRaisesRegex(ValueError, 'requires an actual direct call site'):
            proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4})
        for flag in ('word_provenance', 'callee_frames', 'single_word_stores', 'forwarded_stack_arguments'):
            with self.subTest(flag=flag), patch.object(proof, flag, True), \
                    self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
                proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4}, site=OWNER + 8)
        with patch.object(proof, 'exact_alias_state_budget', 8), self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
            proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4}, site=OWNER + 8)
        for attribute, value in (('runtime_summaries', object()), ('discarded_exit_scratch', {}),
                                 ('bios_fill_proof', SimpleNamespace(calls={}))):
            with self.subTest(attribute=attribute), patch.object(proof, attribute, value), \
                    self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
                proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4}, site=OWNER + 8)
        with patch.object(proof, 'stack_arguments', False), self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
            proof.copy_summaries.call(proof, {R0: -16}, stack, {}, frozenset(), constants={R2: 4},
                                      site=OWNER + 8, words={})
        other = match.BufferCallProof(proof.rom, proof.copy_summaries.mapping, stack_arguments=True,
                                      copy_helper_index=proof.copy_summaries.index)
        with self.assertRaisesRegex(ValueError, 'excludes word-provenance'):
            proof.copy_summaries.call(other, {R0: -16}, stack, {}, frozenset(), constants={R2: 4},
                                      site=OWNER + 8, words={})

    def test_only_the_plain_stack_argument_proof_takes_summaries(self):
        # The plain and the function-literal stack-argument proofs take them; any other
        # subclass, or a proof without stack arguments, refuses.
        env = environment(owner())

        class Other(match.BufferCallProof):
            pass
        for build in (lambda: match.BufferCallProof(env['rom'], env['mapping'], copy_helper_index=env['index']),
                      lambda: Other(env['rom'], env['mapping'], stack_arguments=True,
                                    copy_helper_index=env['index'])):
            with self.assertRaisesRegex(ValueError, 'copy summaries require the plain or function-literal '
                                                    'stack-argument buffer proof'):
                build()
        self.assertIsNotNone(match.FunctionBufferCallProof(env['rom'], env['mapping'], stack_arguments=True,
                                                           copy_helper_index=env['index']).copy_summaries)

    def test_identical_helper_elsewhere_is_walked(self):
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{FAKE:08X}: unsupported buffer pointer use or escape'):
            prove(owner(target=FAKE))

    def test_helper_identity_is_required(self):
        raw = bytearray(BODY)
        raw[40] ^= 1                                                   # an unexecuted word-path byte
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: .*(differs|helper)'):
            prove(owner(), body=bytes(raw))
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: .*instruction counts'):
            prove(owner(), helper_instrs=48)

    def test_mapped_span_must_be_the_pinned_body(self):
        proof, env = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        with patch.object(proof, 'span', lambda address: BODY[:-2] + b'\0\0'), \
                self.assertRaisesRegex(ValueError, 'mapped helper span differs'):
            proof.check_call(HELPER, {R0: -16}, stack, constants={R2: 4}, site=OWNER + 8)

    def test_callee_frames(self):
        # A caller pointer forwarded by a callee to the helper is walked, as before.
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{MID:08X}: buffer callee 0x081443FC: '
                                    'unsupported buffer pointer use or escape'):
            prove([0xb510, 0xb082, 0x4668, MID, 0xb002, 0xbc10, 0xbc02, 0x4708])
        # A callee copying into its own frame is summarised by that callee's own frame walk.
        proof, _ = prove([0xb510, 0xb082, 0x4668, LOCAL, 0xb002, 0xbc10, 0xbc02, 0x4708])
        record, = observations(proof)
        self.assertEqual((record['site'], record['destination'], record['frame_bytes']), (LOCAL + 10, -12, 12))

    def test_pointer_words_and_stack_arguments_are_kept(self):
        # add r1, sp, #4; str r1, [sp, #0]; the copy goes to sp+4..sp+8 and leaves the pointer word.
        proof, _ = prove(owner((0xa901, 0x9100, 0xa801, 0x2100), count=8, frame=12, tail=(0x7840, 0x2100)))
        record, = observations(proof)
        self.assertEqual((record['destination'], record['protected'], record['incoming']), (-16, [-20], [[0, -16]]))
        self.assertIn('pointer words 1', proof.loop_replay_lines()[0])

    def test_argument_pointers_are_validated(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        for register in (R3, R12):
            with self.subTest(register=register), self.assertRaisesRegex(
                    ValueError, 'buffer callee 0x081443FC: buffer access is unaligned or outside allocated local words'):
                proof.check_call(HELPER, {R0: -16, register: -4}, stack, constants={R2: 4}, site=OWNER + 8)

    def test_count_must_be_an_int(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        for count in (True, 4.0, '4'):
            with self.subTest(count=count), self.assertRaisesRegex(ValueError, 'exact constant from 1 to 256'):
                proof.check_call(HELPER, {R0: -16}, stack, constants={R2: count}, site=OWNER + 8)

    def test_each_count_has_its_own_contract(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 4 + [(False, True, False)] * 2
        proof.check_call(HELPER, {R0: -24}, stack, constants={R2: 16}, site=OWNER + 8)
        self.assertEqual([record['count'] for record in proof.copy_summaries.evidence()['contracts']], [4, 16])
        self.assertEqual(len(proof.loop_replay_lines()), 2)

    def test_every_distinct_visit_is_recorded(self):
        proof, _ = prove(owner())
        stack = [(False, False, True)] * 2 + [(False, True, False)] * 2
        proof.check_call(HELPER, {R0: -16, R3: -12}, stack, constants={R2: 4}, site=OWNER + 8)
        self.assertEqual(len(observations(proof)), 2)
        self.assertEqual(len(proof.loop_replay_lines()), 2)


class EvidenceTests(unittest.TestCase):
    def test_fingerprint_binds_only_actual_summaries(self):
        code = [0xb510, 0xb082, 0x2000, 0x2100, 0x2204, HELPER, 0xb002, 0xbc10, 0xbc02, 0x4708]
        env = environment(code)
        plain = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True)
        with_index = match.BufferCallProof(env['rom'], env['mapping'], stack_arguments=True, loop_replay=True,
                                           copy_helper_index=env['index'])
        for proof in (plain, with_index):
            proof.dependencies[HELPER] = BODY
        self.assertEqual(plain.fingerprint(), with_index.fingerprint())
        self.assertEqual(with_index.loop_replay_lines(), [])
        summarised, _ = prove(owner())
        before = summarised.fingerprint()
        record = observations(summarised)[0]
        key, = summarised.copy_summaries.observations
        for field, value in (('count', 5), ('destination', -12), ('returned', []), ('dropped', [[3, -16]]),
                             ('protected', [-12]), ('dropped', [[1, -16]]), ('site', OWNER + 12)):
            with self.subTest(field=field):
                summarised.copy_summaries.observations[key] = dict(record, **{field: value})
                self.assertNotEqual(summarised.fingerprint(), before)
        summarised.copy_summaries.observations[key] = record
        self.assertEqual(summarised.fingerprint(), before)
        summarised.copy_summaries.contracts[4] = dict(summarised.copy_summaries.contracts[4], execution_sha256='0' * 64)
        self.assertNotEqual(summarised.fingerprint(), before)


class ReplayTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix='copy_helper_summary_', dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        variables = patch.dict(os.environ, {'FFTA_ROM': str(self.root / 'baserom.bin')})
        variables.start()
        self.addCleanup(variables.stop)

    def report(self, code, *, write_index=True, stack_arguments=True):
        proof, env = prove(code, index=stack_arguments, stack_arguments=stack_arguments)
        (self.root / 'baserom.bin').write_bytes(env['rom'])
        (self.root / 'symbols').mkdir(exist_ok=True)
        if write_index:
            (self.root / 'symbols/functions.txt').write_bytes(env['index'])
        lines = [f"* compiled : `{env['data'].hex()}`",
                 f'* buffer calls: {evidence.STACK_BUFFER_SUMMARY if stack_arguments else evidence.BUFFER_SUMMARY}',
                 f'* buffer proof SHA-256: `{proof.fingerprint()}`',
                 *proof.loop_replay_lines(),
                 f"**MATCH - byte identical** - {len(env['data'])}/{len(env['data'])} bytes"]
        return lines, env

    def accepted(self, lines, env):
        return evidence.buffer_report_matches(lines, self.root, OWNER, env['mapping'], stack_arguments=True)

    def test_report_replays_and_tampers_fail(self):
        lines, env = self.report(owner())
        self.assertTrue(self.accepted(lines, env))
        summary_line = next(index for index, line in enumerate(lines) if line.startswith('* buffer copy summary:'))
        tampers = {
            'count': lines[summary_line].replace('count 4', 'count 5'),
            'destination': lines[summary_line].replace('destination sp+0', 'destination sp+4'),
            'returns': lines[summary_line].replace('returns r0=sp+0', 'returns none'),
            'contract': lines[summary_line].replace('contract 16 cases', 'contract 15 cases'),
            'indented': '  ' + lines[summary_line],
        }
        self.assertIn('drops none', lines[summary_line])
        for name, line in tampers.items():
            with self.subTest(name=name):
                self.assertFalse(self.accepted(lines[:summary_line] + [line] + lines[summary_line + 1:], env))
        with self.subTest(name='removed'):
            self.assertFalse(self.accepted(lines[:summary_line] + lines[summary_line + 1:], env))
        with self.subTest(name='duplicated'):
            self.assertFalse(self.accepted(lines[:summary_line + 1] + lines[summary_line:], env))
        with self.subTest(name='fingerprint'):
            stale = [line if not line.startswith('* buffer proof SHA-256') else
                     '* buffer proof SHA-256: `' + '0' * 64 + '`' for line in lines]
            self.assertFalse(self.accepted(stale, env))
        with self.subTest(name='version 1'):
            self.assertFalse(evidence.buffer_report_matches(
                [line.replace(evidence.STACK_BUFFER_SUMMARY, evidence.BUFFER_SUMMARY) for line in lines],
                self.root, OWNER, env['mapping'], stack_arguments=False))

    def test_reports_without_a_summary_replay_unchanged(self):
        # mov r0, sp; bl READ: an ordinary bounded callee, which the version-1 proof admits; bl INDEXED
        # needs version 2.  match.py tries version 1 first, so each body has the one report it writes.
        code = [0xb510, 0xb082, 0x4668, READ, 0xb002, 0xbc10, 0xbc02, 0x4708]
        indexed = [0xb510, 0xb082, 0x4668, INDEXED, 0xb002, 0xbc10, 0xbc02, 0x4708]
        for body, stack_arguments in ((code, False), (indexed, True)):
            with self.subTest(stack_arguments=stack_arguments):
                lines, env = self.report(body, stack_arguments=stack_arguments)
                self.assertFalse(any(line.startswith('* buffer copy summary') for line in lines))
                self.assertTrue(evidence.buffer_report_matches(lines, self.root, OWNER, env['mapping'],
                                                               stack_arguments=stack_arguments))
        with self.subTest(version_2_of_a_version_1_body=True):
            lines, env = self.report(code, stack_arguments=True)
            self.assertFalse(evidence.buffer_report_matches(lines, self.root, OWNER, env['mapping'],
                                                            stack_arguments=True))
        # Without a function index nothing is summarised, so such a report still replays.
        lines, env = self.report(indexed, write_index=False)
        (self.root / 'symbols/functions.txt').unlink(missing_ok=True)
        self.assertTrue(self.accepted(lines, env))

    def test_replay_needs_the_index(self):
        lines, env = self.report(owner(), write_index=False)
        self.assertFalse(self.accepted(lines, env))

    def test_replay_refuses_a_changed_helper(self):
        lines, env = self.report(owner())
        rom = bytearray(env['rom'])
        rom[HELPER - match.ROM_BASE + 40] ^= 1
        (self.root / 'baserom.bin').write_bytes(bytes(rom))
        self.assertFalse(self.accepted(lines, env))


# A #236 typed-data caller that copies a typed object into its own local with the helper.
DATA_COPY = """typedef unsigned short u16;
typedef unsigned int u32;
extern u16 data_02000000[];
extern void func_081443FC(void *destination, const void *source, u32 size);
void func_08000200(void)
{
    u16 buffer[4];

    func_081443FC(buffer, data_02000000, 8);
    data_02000000[4] = buffer[0];
    data_02000000[5] = buffer[3];
}
"""


def build_data_copy(root):
    """A complete tree: the caller compiled at data_calls.A, the pinned helper at HELPER."""
    import argparse
    root = Path(root)
    for name in ('src', 'include', 'config', 'symbols', 'build'):
        (root / name).mkdir(parents=True, exist_ok=True)
    rom = bytearray(ROM_SIZE)
    rom[HELPER - match.ROM_BASE:HELPER - match.ROM_BASE + len(BODY)] = BODY
    helper = {'rom': f'0x{HELPER:08X}', 'end': f'0x{HELPER + len(BODY):08X}', 'mode': 'thumb', 'instrs': 49}
    (root / 'src/08000200.c').write_text(DATA_COPY)
    (root / 'include/types.h').write_text('/* fixture */\n')
    objects = json.dumps(data_calls.OBJECTS).encode()
    (root / 'config/data_symbols.json').write_bytes(objects)
    args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
    runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
    with runner.workspace() as workspace:
        _, _, original = match.compile_object(runner, workspace, args, root, data_calls.A, 'src/08000200.c')
        symbol, _ = match.function_record(original, 'func_08000200', data_calls.A, True)
        caller = {'rom': f'0x{data_calls.A:08X}', 'end': f'0x{data_calls.A + symbol["size"]:08X}', 'mode': 'thumb'}
        mapping = json.dumps([caller, helper]).encode()
        body, _, _ = match.link_calls(runner, workspace, args, original, data_calls.A, mapping, len(rom),
                                      bytes(rom), objects, {})
    rom[data_calls.A - match.ROM_BASE:data_calls.A - match.ROM_BASE + len(body)] = body
    (root / 'config/functions.json').write_bytes(mapping)
    (root / 'symbols/functions.txt').write_text(
        f'{data_calls.A:08X} {data_calls.A + len(body):08X} {len(body)} 0 return\n'
        f'{HELPER:08X} {HELPER + len(BODY):08X} {len(BODY)} 49 return\n')
    (root / 'baserom.bin').write_bytes(bytes(rom))
    return root


@unittest.skipUnless(data_calls.tools_present(), 'fixed compiler and ARM tools required')
class DataBufferCompositionTests(unittest.TestCase):
    """A typed-data caller reaches the copy summary through data_buffer_profile's proof."""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get('FFTA_TEST_SCRATCH', ROOT / 'build'))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix='copy_summary_data_', dir=scratch)
        cls.root = build_data_copy(Path(cls.temporary.name) / 'copy')
        cls.code, cls.output, cls.report = data_calls.run(cls.root)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / 'baserom.bin')):
            return evidence.report_matches(report, self.root, data_calls.A)

    def manifest(self):
        line = next(line for line in self.report.splitlines() if line.startswith(data_buffer.MANIFEST_FIELD))
        return json.loads(line[len(data_buffer.MANIFEST_FIELD) + 1:-1])

    def test_the_data_buffer_report_carries_and_replays_the_copy_summary(self):
        self.assertEqual(self.code, 0, self.output)
        self.assertIn('verdict MATCH - byte identical', self.output)
        self.assertEqual(data_calls.verification(self.report), data_buffer.SCHEMA)
        self.assertEqual([row[1:] for row in self.manifest()['data']], [['data_02000000', 0]])
        line, = [line for line in self.report.splitlines() if line.startswith('* buffer copy summary:')]
        self.assertRegex(line, r'^\* buffer copy summary: `pinned-copy-helper-summary-v1` 0x081443FC at '
                               r'0x080002[0-9A-F]{2}: count 8, destination sp\+0, source external; '
                               r'returns r0=sp\+0; drops none; pointer words 0; contract 16 cases [0-9a-f]{16}$')
        self.assertTrue(self.replays(self.report))

    def test_tampered_removed_or_duplicated_lines_fail(self):
        lines = self.report.splitlines()
        at = next(i for i, line in enumerate(lines) if line.startswith('* buffer copy summary:'))
        for name, edited in (('count', lines[:at] + [lines[at].replace('count 8', 'count 4')] + lines[at + 1:]),
                             ('contract', lines[:at] + [lines[at][:-16] + '0' * 16] + lines[at + 1:]),
                             ('removed', lines[:at] + lines[at + 1:]),
                             ('duplicated', lines[:at + 1] + lines[at:])):
            with self.subTest(name=name):
                self.assertFalse(self.replays('\n'.join(edited) + '\n'))

    def test_a_replay_without_an_index_proves_without_summaries(self):
        # No function index: the replay still proves, with no summary, and so refuses this report.
        index = self.root / 'symbols/functions.txt'
        saved, seen, real = index.read_bytes(), [], data_buffer.prove

        def recording(*arguments, **options):
            seen.append(options.get('index'))
            return real(*arguments, **options)

        index.unlink()
        try:
            with patch.object(data_buffer, 'prove', recording):
                self.assertFalse(self.replays(self.report))
        finally:
            index.write_bytes(saved)
        self.assertEqual(seen, [None])

    def test_without_the_index_the_data_proof_refuses_at_the_helper(self):
        rom = (self.root / 'baserom.bin').read_bytes()
        mapping = (self.root / 'config/functions.json').read_bytes()
        objects = (self.root / 'config/data_symbols.json').read_bytes()
        code = bytes.fromhex(next(line for line in self.report.splitlines()
                                  if line.startswith('* compiled : '))[len('* compiled : `'):-1])
        manifest = self.manifest()
        calls = {data_calls.A + offset: int(name[5:], 16) for offset, name in manifest['calls']}
        symbols = match.parse_data_symbols(objects)
        literals = {offset: (name, symbols[name] + delta) for offset, name, delta in manifest['data']}
        index = (self.root / 'symbols/functions.txt').read_bytes()
        _, proof, schema, _ = data_buffer.prove(code, data_calls.A, rom, mapping, objects, calls, literals,
                                                index=index)
        self.assertEqual(schema, data_buffer.SCHEMA)
        self.assertEqual([record['count'] for record in proof.copy_summaries.evidence()['observations']], [8])
        with self.assertRaisesRegex(ValueError, 'buffer callee 0x081443FC: unsupported buffer pointer use or escape'):
            data_buffer.prove(code, data_calls.A, rom, mapping, objects, calls, literals)


class WiringTests(unittest.TestCase):
    def test_only_reviewed_construction_sites_pass_the_index(self):
        found = set()
        for path in sorted((ROOT / 'tools').glob('*.py')):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call) and any(keyword.arg == 'copy_helper_index' or
                                                              keyword.arg is None for keyword in node.keywords) and \
                                getattr(node.func, 'id', getattr(node.func, 'attr', None)) in (
                                    'BufferCallProof', 'FunctionBufferCallProof'):
                            for keyword in node.keywords:
                                if keyword.arg == 'copy_helper_index':
                                    # The index must be a real expression, never a literal None.
                                    self.assertFalse(isinstance(keyword.value, ast.Constant), ast.dump(keyword))
                                    found.add((path.name, function.name))
        self.assertEqual(found, {('match.py', 'main'), ('match_evidence.py', 'buffer_report_matches'),
                                 ('function_thunk_profile.py', 'verify_source'),
                                 ('data_buffer_profile.py', 'prove')})

    def test_the_data_proof_receives_the_index_from_both_producers(self):
        # match.main and the data-buffer replay pass an index expression to data_buffer.prove.
        found = set()
        for name in ('match.py', 'data_buffer_profile.py'):
            for function in ast.walk(ast.parse((ROOT / 'tools' / name).read_text())):
                if isinstance(function, ast.FunctionDef):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call) and any(
                                keyword.arg == 'index' and not isinstance(keyword.value, ast.Constant)
                                for keyword in node.keywords):
                            callee = node.func.attr if isinstance(node.func, ast.Attribute) else node.func.id
                            found.add((name, function.name, callee))
        self.assertEqual(found, {('match.py', 'main', 'prove'),
                                 ('data_buffer_profile.py', 'verify_source', 'prove')})

    def test_data_buffer_reports_accept_the_summary_line(self):
        self.assertIn('* buffer copy summary', data_buffer.FIELDS)

    def test_other_reports_refuse_the_summary_line(self):
        # A report check without buffer evidence refuses every line that starts with evidence.BUFFER_LINES, and
        # one with it compares every such line with the recomputed proof
        # (test_closed_report_replay.BufferLineTests replays each check).  The copy summary line is such a line.
        tree = ast.parse((ROOT / 'tools' / 'copy_helper_summary_profile.py').read_text())
        written = [node.value for node in ast.walk(tree) if isinstance(node, ast.Constant) and
                   isinstance(node.value, str) and node.value.startswith('* ')]
        self.assertEqual(written, ['* buffer copy summary: `'])
        self.assertTrue(written[0].startswith(evidence.BUFFER_LINES))

    def test_copy_summaries_are_never_assigned_outside_the_constructor(self):
        for path in sorted((ROOT / 'tools').glob('*.py')):
            tree = ast.parse(path.read_text())
            for node in ast.walk(tree):
                if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                    for target in targets:
                        if isinstance(target, ast.Attribute) and target.attr == 'copy_summaries':
                            self.assertEqual(path.name, 'match.py', ast.dump(target))


if __name__ == '__main__':
    unittest.main()
