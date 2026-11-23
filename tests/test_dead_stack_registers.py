"""Dead stack-address registers on the default stack-argument buffer proofs (no ROM, compiler or game C)."""
import ast
import json
from pathlib import Path
import struct
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.dont_write_bytecode = True
import match
import dead_register

OWNER, P, C, G, X, Y = 0x08010000, 0x08011000, 0x08012000, 0x08013000, 0x08014000, 0x08016000
R0, R1, R2, R3 = (match.ARM_REG_R0 + n for n in range(4))
ROM_SIZE = 0x20000
ESCAPE = 'local stack pointer escapes through a return register'

# Thumb halfwords used below.
PUSH_LR, PUSH_R4_LR, POP_R4 = 0xb500, 0xb510, 0xbc10
SUB8, ADD8 = 0xb082, 0xb002
POP_R0, BX_R0, POP_R1, BX_R1, BX_LR, BX_R3 = 0xbc01, 0x4700, 0xbc02, 0x4708, 0x4770, 0x4718
MOV_R0_SP, MOV_R2_SP = 0x4668, 0x466a
MOVS_R0_0, MOVS_R0_1, MOVS_R2_0, MOVS_R3_0 = 0x2000, 0x2001, 0x2200, 0x2300
CMP_R0_0, BEQ_SKIP1 = 0x2800, 0xd000
BEQ_BACK2 = 0xd0fd                                  # beq to the instruction before it
MOV_LR_PC, BX_R2, BX_PC, NOP = 0x46fe, 0x4710, 0x4778, 0x46c0
ARM_BX_LR = (0xff1e, 0xe12f)                        # bx lr (ARM), as two halfwords
READ_R3 = 0x1c19                                    # adds r1, r3, #0
VIA_R3 = match.RUNTIME_HELPERS['_call_via_r3']      # bx r3; nop


def bl(site, target):
    value = target - site - 4
    return struct.pack('<HH', 0xf000 | ((value >> 12) & 0x7ff), 0xf800 | ((value >> 1) & 0x7ff))


def assemble(address, tokens):
    raw = bytearray()
    for token in tokens:
        raw += bl(address + len(raw), token) if token >= 0x08000000 else struct.pack('<H', token)
    return bytes(raw)


def calls_of(address, tokens):
    calls, offset = {}, 0
    for token in tokens:
        if token >= 0x08000000:
            calls[address + offset] = token
            offset += 4
        else:
            offset += 2
    return calls


# P(r0): adds r3, r0, #0; bx lr - returns the caller's stack address in R0 and R3, as 080032F8 does.
P_RETURNS_R3 = [0x1c03, BX_LR]
# P(r0): adds r2, r0, #0; bx lr - returns it in R0 and R2, as 0801E68C does.
P_RETURNS_R2 = [0x1c02, BX_LR]
# X: bx r3, a _call_via_r3 thunk.
THUNK = [BX_R3]
# Y: bx lr.
LEAF = [BX_LR]
# C(r0, r1): push {lr}; sub sp,#8; adds r3,r1,#0; mov r0,sp; bl Y; mov r2,sp; bl X; add sp,#8;
# pop {r0}; bx r0 - overwrites R3 first, passes its own frame to a leaf (inspected and recorded)
# and then to a thunk, as 080D3E9C passes its descriptor to the scheduler: inspecting it refuses
# at the thunk.
C_KILLS_R3 = [PUSH_LR, SUB8, 0x1c0b, MOV_R0_SP, Y, MOV_R2_SP, X, ADD8, POP_R0, BX_R0]
# C(r0): push {lr}; sub sp,#8; add r2,sp,#4; ldrb r1,[r0]; strb r1,[r2]; add sp,#8; pop {r1}; bx r1 -
# reads the caller's buffer and returns with its own expired sp+4 in R2, as 0801CC7C does.
C_LEAVES_R2 = [PUSH_LR, SUB8, 0xaa01, 0x7801, 0x7011, ADD8, POP_R1, BX_R1]
# G: movs r2, #0; bx lr - overwrites R2 at its entry, as 0801CC18 does.
G_KILLS_R2 = [MOVS_R2_0, BX_LR]


def owner_shape1(c_code=C_KILLS_R3, p_code=P_RETURNS_R3, between=(MOVS_R0_1,), prologue=None, epilogue=None):
    """push {lr}; sub sp,#8; mov r0,sp; bl P; <between>; bl C; add sp,#8; pop {r0}; bx r0"""
    prologue = [PUSH_LR, SUB8] if prologue is None else prologue
    epilogue = [ADD8, POP_R0, BX_R0] if epilogue is None else epilogue
    owner = prologue + [MOV_R0_SP, P, *between, C] + epilogue
    return {OWNER: owner, P: p_code, C: c_code, X: THUNK, Y: LEAF}


def owner_shape2(after=(MOVS_R2_0, MOVS_R0_0, G), c_code=C_LEAVES_R2, g_code=G_KILLS_R2, extra=None):
    """push {lr}; sub sp,#8; mov r0,sp; bl C; <after>; add sp,#8; pop {r0}; bx r0"""
    bodies = {OWNER: [PUSH_LR, SUB8, MOV_R0_SP, C, *after, ADD8, POP_R0, BX_R0],
              C: c_code, G: g_code, X: THUNK}
    bodies.update(extra or {})
    return bodies


def build(bodies):
    images = {address: assemble(address, tokens) for address, tokens in sorted(bodies.items())}
    rom = bytearray(max([ROM_SIZE] + [address - match.ROM_BASE + len(raw) for address, raw in images.items()]))
    rows = []
    for address, raw in images.items():
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
        rows.append(dict(rom=f'0x{address:08X}', end=f'0x{address + len(raw):08X}', mode='thumb', instrs=0))
    return bytes(rom), json.dumps(rows).encode()


def walk(bodies, *, dead=True, kind=None):
    """The default walk of OWNER; dead=False is the proof as it was before the rules."""
    rom, mapping = build(bodies)
    kind = kind or match.BufferCallProof
    options = dict(stack_arguments=True, loop_replay=True)
    if kind is match.BufferCallProof:
        options['bios_wrappers'] = True
    if dead:
        options['dead_registers'] = True
    proof = kind(rom, mapping, **options)
    data = assemble(OWNER, bodies[OWNER])
    match.verify_leaf_instructions(data, OWNER, True, calls_of(OWNER, bodies[OWNER]), buffer_proof=proof)
    return proof


class SharedWalkTests(unittest.TestCase):
    """dead_register.prove, the one walk behind every dead-register check."""
    MESSAGES = dict(end='end', cycle='cycle', budget='budget')

    @staticmethod
    def graph(nodes):
        def step(node, live):
            written, successors, read = nodes[node]
            if live & read:
                raise ValueError('read')
            return written, successors
        return step

    def test_kill_on_every_path(self):
        nodes = {0: (set(), (1, 2), set()), 1: ({R2}, (3,), set()), 2: ({R2}, (3,), set()), 3: (set(), (), {R2})}
        result = dead_register.prove(0, {R2}, self.graph(nodes), **self.MESSAGES)
        self.assertEqual(result.kills, {(1, R2), (2, R2)})
        self.assertEqual(result.states, 3)
        self.assertEqual(result.visited, [0, 2, 1])

    def test_read_on_one_path_or_end_with_a_live_value_refuses(self):
        read = {0: (set(), (1, 2), set()), 1: ({R2}, (), set()), 2: (set(), (), {R2})}
        with self.assertRaisesRegex(ValueError, 'read'):
            dead_register.prove(0, {R2}, self.graph(read), **self.MESSAGES)
        ends = {0: (set(), (1, 2), set()), 1: ({R2}, (), set()), 2: (set(), (), set())}
        with self.assertRaisesRegex(ValueError, 'end'):
            dead_register.prove(0, {R2}, self.graph(ends), **self.MESSAGES)

    def test_a_cycle_that_can_avoid_the_kill_refuses(self):
        # Least fixpoint: a read-free cycle around the kill is still a path without it.
        loop = {0: (set(), (1, 2), set()), 1: (set(), (0,), set()), 2: ({R2, R3}, (), set())}
        with self.assertRaisesRegex(ValueError, 'cycle'):
            dead_register.prove(0, {R2, R3}, self.graph(loop), **self.MESSAGES)
        # A loop whose every pass kills is proved.
        killing = {0: (set(), (1,), set()), 1: ({R2}, (0,), set())}
        self.assertEqual(dead_register.prove(0, {R2}, self.graph(killing), **self.MESSAGES).states, 2)
        partial = {0: (set(), (1, 2), set()), 1: ({R2}, (0,), set()), 2: (set(), (3,), set()), 3: (set(), (), {R2})}
        with self.assertRaisesRegex(ValueError, 'read'):
            dead_register.prove(0, {R2}, self.graph(partial), **self.MESSAGES)

    def test_state_budget(self):
        chain = {n: (set(), (n + 1,), set()) for n in range(10)}
        chain[10] = ({R2}, (), set())
        self.assertEqual(dead_register.prove(0, {R2}, self.graph(chain), limit=11, **self.MESSAGES).states, 11)
        with self.assertRaisesRegex(ValueError, 'budget'):
            dead_register.prove(0, {R2}, self.graph(chain), limit=9, **self.MESSAGES)


class DeadCallArgumentTests(unittest.TestCase):
    """A callee inspected only for stack addresses it overwrites unread is an alias-free call."""

    def test_stale_r3_into_a_killing_callee_is_not_inspected(self):
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: buffer callee 0x{X:08X}: '
                                                'non-leaf indirect control flow'):
            walk(owner_shape1(), dead=False)
        for kind in (match.BufferCallProof, match.FunctionBufferCallProof):
            with self.subTest(kind=kind.__name__):
                proof = walk(owner_shape1(), kind=kind)
                # The refused inspection leaves no record: only P was inspected.
                self.assertEqual(set(proof.dependencies), {P})
                evidence = proof.dead_registers.evidence()
                self.assertEqual(len(evidence['calls']), 1)
                row = evidence['calls'][0]
                self.assertEqual((row['site'], row['callee'], row['registers']), (OWNER + 12, C, [[3, -12]]))
                self.assertEqual(row['entry']['kills'], [[C + 4, 3]])
                self.assertEqual(row['entry']['body_sha256'], dead_register.sha(assemble(C, C_KILLS_R3)))
                self.assertEqual(set(evidence), {'schema', 'calls'})
                line, = [line for line in proof.loop_replay_lines() if line.startswith('* buffer dead register:')]
                self.assertIn(f'call 0x{OWNER + 12:08X} to 0x{C:08X} passes r3=-12', line)
                self.assertIn(f'r3@0x{C + 4:08X}', line)

    def test_callee_that_observes_or_keeps_the_value_refuses(self):
        tail = [MOV_R2_SP, X, ADD8, POP_R0, BX_R0]
        for name, c_code in (
                ('read first', [PUSH_LR, SUB8, 0x1c19, 0x1c0b] + tail),              # adds r1,r3,#0
                ('pushed', [0xb508, SUB8, 0x1c0b] + tail),                           # push {r3, lr}
                ('copied, then killed', [PUSH_LR, SUB8, 0x1c1a, MOVS_R3_0] + tail),  # adds r2,r3,#0
                ('killed on one path', [PUSH_LR, SUB8, CMP_R0_0, BEQ_SKIP1, MOVS_R3_0] + tail),
                ('call first', [PUSH_LR, SUB8, X, 0x1c0b] + tail),
                ('never killed', [PUSH_LR, SUB8] + tail)):
            with self.subTest(name), self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: '):
                walk(owner_shape1(c_code))

    def test_thunk_callee_refuses(self):
        bodies = owner_shape1()
        bodies[OWNER] = [PUSH_LR, SUB8, MOV_R0_SP, P, MOVS_R0_1, X, ADD8, POP_R0, BX_R0]
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{X:08X}: non-leaf indirect control flow'):
            walk(bodies)

    def test_second_live_argument_the_callee_reads_refuses(self):
        # P: adds r2,r0,#0; adds r3,r0,#0; bx lr. C kills R3 only and reaches its call with R2 live.
        c_code = [PUSH_LR, SUB8, 0x1c0b, X, ADD8, POP_R0, BX_R0]
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: '):
            walk(owner_shape1(c_code, p_code=[0x1c02, 0x1c03, BX_LR]))

    def test_callee_saved_copy_stays_tracked_across_the_alias_free_call(self):
        # push {r4,lr}; sub sp,#8; mov r0,sp; adds r4,r0,#0; bl P; movs r0,#1; bl C; <after>; ...; pop {r4}
        # The call is alias-free for its arguments; R4 stays an alias and a later store through it is
        # checked.  R4 holds the stack address across the call, so the callee-saved walk follows C
        # (kit #350): a bare `bx r3` it reaches with that value live refuses, while a call through
        # the real _call_via_r3 to an unknown address is premised.
        def bodies(after, c_code=C_KILLS_R3):
            values = owner_shape1(c_code)
            values[OWNER] = [PUSH_R4_LR, SUB8, MOV_R0_SP, 0x1c04, P, MOVS_R0_1, C, *after,
                             ADD8, POP_R4, POP_R0, BX_R0]
            values[VIA_R3] = [BX_R3, NOP]
            return values
        with self.assertRaisesRegex(ValueError, f'callee 0x{X:08X}: an indirect branch at 0x{X:08X} '
                                                f'while watched values are live'):
            walk(bodies(()))
        via_r3 = [PUSH_LR, SUB8, 0x1c0b, MOV_R0_SP, Y, MOV_R2_SP, VIA_R3, ADD8, POP_R0, BX_R0]
        self.assertEqual(len(walk(bodies((), via_r3)).dead_registers.evidence()['calls']), 1)
        with self.assertRaisesRegex(ValueError, 'outside allocated local words|stack-alias'):
            walk(bodies((0x7520,), via_r3))                                 # strb r0,[r4,#20]

    def test_pointer_bearing_frame_word_keeps_the_inspection(self):
        # add r1,sp,#4; str r1,[sp]: the callee may read the word through its incoming stack.
        bodies = owner_shape1()
        bodies[OWNER] = [PUSH_LR, SUB8, 0xa901, 0x9100, 0x2100, MOV_R0_SP, P, MOVS_R0_1, C, ADD8, POP_R0, BX_R0]
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: '):
            walk(bodies)

    def test_address_also_in_r12_keeps_the_inspection(self):
        # mov r0,sp; mov ip,r0; bl P; movs r0,#1; bl C - C overwrites R12 too (mov ip,r1), but
        # only R0-R3 are dropped.
        bodies = owner_shape1([PUSH_LR, SUB8, 0x468c] + C_KILLS_R3[2:])
        bodies[OWNER] = [PUSH_LR, SUB8, MOV_R0_SP, 0x4684, P, MOVS_R0_1, C, ADD8, POP_R0, BX_R0]
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: '):
            walk(bodies)


def same_refusal(case, bodies):
    """The whole default walk refuses exactly as it does without the policy."""
    with case.assertRaises(ValueError) as before:
        walk(bodies, dead=False)
    with case.assertRaises(ValueError) as after:
        walk(bodies)
    case.assertEqual(str(after.exception), str(before.exception))


class DeadCallRefusalTests(unittest.TestCase):
    """Calls the rule must leave refused, with the walk's own message."""

    def test_indirect_call_before_the_kill(self):
        same_refusal(self, owner_shape1([PUSH_LR, SUB8, MOV_LR_PC, BX_R2] + C_KILLS_R3[2:]))

    def test_high_register_copy_before_the_kill(self):
        same_refusal(self, owner_shape1([PUSH_LR, SUB8, 0x469b] + C_KILLS_R3[2:]))      # mov r11,r3

    def test_every_argument_register_is_proved(self):
        # P leaves the owner's frame in R2 and R3 (R0 is overwritten); C kills R2 first but reads R3.
        c_code = [PUSH_LR, SUB8, MOVS_R2_0, READ_R3, MOV_R2_SP, X, ADD8, POP_R0, BX_R0]
        same_refusal(self, owner_shape1(c_code, p_code=[0x1c02, 0x1c03, BX_LR]))

    def test_interworking_callee(self):
        same_refusal(self, owner_shape1([BX_PC, NOP, *ARM_BX_LR]))

    def test_cycle_that_can_avoid_the_kill(self):
        # cmp r0,#0; beq back to the compare; adds r3,r1,#0: read-free, but a path never kills R3.
        same_refusal(self, owner_shape1([PUSH_LR, SUB8, CMP_R0_0, BEQ_BACK2] + C_KILLS_R3[2:]))


class DeadEntryProofTests(unittest.TestCase):
    """DeadStackRegisters.entry, the callee-entry proof behind the call rule."""

    def entry(self, code, registers=(R3,), extra=None, end=None):
        rom, mapping = build({OWNER: [BX_LR], C: code, **(extra or {})})
        if end is not None:
            rows = json.loads(mapping)
            for row in rows:
                if int(row['rom'], 16) == C:
                    row['end'] = f'0x{end:08X}'
            mapping = json.dumps(rows).encode()
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True,
                                      dead_registers=True)
        return proof.dead_registers.entry(C, frozenset(registers))

    def test_overwritten_at_the_entry(self):
        self.assertEqual(self.entry([PUSH_LR, MOVS_R3_0, POP_R0, BX_R0])['kills'], [[C + 2, 3]])
        self.assertEqual(self.entry([0xbc08, BX_LR])['kills'], [[C, 3]])                    # pop {r3}

    def test_observation_or_transfer_before_the_kill_refuses(self):
        for name, code in {
                'indirect call mov lr,pc; bx r2': [PUSH_LR, MOV_LR_PC, BX_R2, MOVS_R3_0, BX_LR],
                'loop exit reads it': [PUSH_LR, CMP_R0_0, 0xd001, MOVS_R3_0, 0xe7fb, READ_R3, BX_LR],
                'read-free cycle that can avoid the kill': [CMP_R0_0, BEQ_BACK2, MOVS_R3_0, BX_LR],
                'push {r3}': [0xb408, MOVS_R3_0, 0xbc08, BX_LR],
                'stmia r0!,{r3}': [0xc008, MOVS_R3_0, BX_LR],
                'str r3,[sp]': [SUB8, 0x9300, MOVS_R3_0, ADD8, BX_LR],
                'mov r8,r3, then killed': [0x4698, MOVS_R3_0, BX_LR],
                'mov r12,r3, then killed': [0x469c, MOVS_R3_0, BX_LR],
                'killed on one path, the join reads': [CMP_R0_0, BEQ_SKIP1, MOVS_R3_0, READ_R3, BX_LR],
                'the fallthrough reads, the target kills': [CMP_R0_0, 0xd100, READ_R3, MOVS_R3_0, BX_LR],
                'ldr r3,[r3]': [0x681b, BX_LR],
                'add pc,r3': [0x449f, MOVS_R3_0, BX_LR],
                'mov pc,lr': [0x46f7, MOVS_R3_0, BX_LR],
                'interworking veneer bx pc': [BX_PC, NOP, *ARM_BX_LR],
                'swi before the kill': [0xdf0b, MOVS_R3_0, BX_LR],
                'Thumb-2 str.w r3,[sp]': [0xf8cd, 0x3000, MOVS_R3_0, BX_LR],
                'BLX pair (ARMv5)': [0xf000, 0xe800, MOVS_R3_0, BX_LR],
                'UNPREDICTABLE low-low hi mov r3,r0': [0x4603, BX_LR],
                'branch out of the span': [0xe400, MOVS_R3_0, BX_LR],
                'BL to a killing callee first': [PUSH_LR, G, MOVS_R3_0, POP_R0, BX_R0]}.items():
            with self.subTest(name), self.assertRaises(ValueError):
                self.entry(code, extra={G: [MOVS_R3_0, BX_LR]})

    def test_span_shorter_than_the_kill_refuses(self):
        with self.assertRaisesRegex(ValueError, 'leaves its function'):
            self.entry([NOP, NOP, MOVS_R3_0, BX_LR], end=C + 4)

    def test_proofs_are_cached_per_register_set(self):
        rom, mapping = build({OWNER: [BX_LR], C: [MOVS_R2_0, READ_R3, BX_LR]})
        dead = match.BufferCallProof(rom, mapping, stack_arguments=True, dead_registers=True).dead_registers
        dead.entry(C, frozenset({R2}))
        with self.assertRaisesRegex(ValueError, 'read before'):
            dead.entry(C, frozenset({R2, R3}))


class ReturnsStayRefusedTests(unittest.TestCase):
    """A stack address left in a register at a return keeps the walk's refusal."""

    def test_inspected_callee_returns_its_own_frame_in_r2(self):
        with self.assertRaisesRegex(ValueError, f'buffer callee 0x{C:08X}: {ESCAPE}'):
            walk(owner_shape2())
        same_refusal(self, owner_shape2())

    def test_root_returns_a_frame_address_in_r2_or_r3(self):
        for name, bodies in (
                ('own frame r2', {OWNER: [PUSH_LR, SUB8, MOV_R0_SP, P, MOVS_R0_0, ADD8, POP_R1, BX_R1],
                                  P: P_RETURNS_R2}),
                ('own frame r3', {OWNER: [PUSH_LR, SUB8, MOV_R0_SP, P, MOVS_R0_0, ADD8, POP_R1, BX_R1],
                                  P: P_RETURNS_R3}),
                ('entry sp in r2', {OWNER: [PUSH_LR, SUB8, 0xaa03, MOVS_R0_0, ADD8, POP_R1, BX_R1]}),
                ('caller frame in r2', {OWNER: [PUSH_LR, SUB8, 0xaa04, MOVS_R0_0, ADD8, POP_R1, BX_R1]})):
            with self.subTest(name):
                if name.startswith('own frame'):
                    with self.assertRaisesRegex(ValueError, ESCAPE):
                        walk(bodies)
                same_refusal(self, bodies)


class DeadRegisterEvidenceTests(unittest.TestCase):
    def test_evidence_is_bound_and_absent_evidence_keeps_the_fingerprint(self):
        proof = walk(owner_shape1())
        bound = proof.fingerprint()
        key = next(iter(proof.dead_registers.calls))
        proof.dead_registers.calls[key]['entry'] = dict(proof.dead_registers.calls[key]['entry'],
                                                        kills=[[C + 6, 3]])
        self.assertNotEqual(proof.fingerprint(), bound)
        # An owner no rule applies to: the same fingerprint and lines with and without the policy.
        clean = {OWNER: [PUSH_LR, SUB8, MOV_R0_SP, P, MOVS_R0_0, MOVS_R3_0, ADD8, POP_R0, BX_R0],
                 P: P_RETURNS_R3}
        with_policy, without = walk(clean), walk(clean, dead=False)
        self.assertFalse(with_policy.dead_registers.observed())
        self.assertEqual(with_policy.fingerprint(), without.fingerprint())
        self.assertEqual(with_policy.loop_replay_lines(), without.loop_replay_lines())

    def test_only_the_default_stack_argument_proofs_take_the_policy(self):
        rom, mapping = build(owner_shape1())

        class Subclass(match.BufferCallProof):
            pass
        for name, build_proof in (
                ('no stack arguments', lambda: match.BufferCallProof(rom, mapping, dead_registers=True)),
                ('not exactly True', lambda: match.BufferCallProof(rom, mapping, stack_arguments=True,
                                                                   dead_registers=1)),
                ('subclass', lambda: Subclass(rom, mapping, stack_arguments=True, dead_registers=True))):
            with self.subTest(name), self.assertRaisesRegex(ValueError, 'dead stack registers require'):
                build_proof()
        self.assertIsNone(match.BufferCallProof(rom, mapping, stack_arguments=True).dead_registers)
        self.assertIsNone(Subclass(rom, mapping, stack_arguments=True).dead_registers)

    def test_only_reviewed_construction_sites_set_the_policy(self):
        classes = ('BufferCallProof', 'FunctionBufferCallProof')
        found, unpacked = set(), []
        for path in sorted((ROOT / 'tools').glob('*.py')):
            for function in ast.walk(ast.parse(path.read_text())):
                if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                for node in ast.walk(function):
                    if not isinstance(node, ast.Call):
                        continue
                    callee = getattr(node.func, 'attr', getattr(node.func, 'id', None))
                    for keyword in node.keywords:
                        if keyword.arg == 'dead_registers':
                            found.add((path.name, function.name, ast.unparse(keyword.value)))
                        elif keyword.arg is None and callee in classes:
                            unpacked.append((path.name, function.name))
        self.assertEqual(unpacked, [])
        self.assertEqual(found, {
            ('match.py', 'verify_function_buffers', 'True'), ('match.py', 'main', 'True'),
            ('data_buffer_profile.py', 'prove', 'True'),
            ('match_evidence.py', 'buffer_report_matches', 'stack_arguments is True')})

if __name__ == '__main__':
    unittest.main()
