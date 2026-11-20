"""Counted stack cursor in the phase-two panel clear, verified under the normal owner walk."""

from capstone import CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP
from capstone.arm import ARM_REG_R2, ARM_REG_R3, ARM_REG_R4, ARM_REG_R6, ARM_REG_SP

OWNER, END = 0x080447B4, 0x08044D90
SETUP, HEAD, STORE, LATCH = 0x08044B50, 0x08044B58, 0x08044B64, 0x08044B6A
# MOVS r3,#0; ADD r6,sp,#64; MOVS r2,#0; MOV r4,sp.
SETUP_WORDS = (0x2300, 0xAE10, 0x2200, 0x466C)


class MenuCursor:
    store = STORE

    def __init__(self, instructions, edges):
        import match
        span = range(SETUP, LATCH + 2, 2)
        if any(pc not in instructions or instructions[pc].size != 2 for pc in span):
            raise ValueError('incomplete native local cursor instructions')
        words = {pc: int.from_bytes(instructions[pc].bytes, 'little') for pc in span}
        if tuple(words[pc] for pc in range(SETUP, HEAD, 2)) != SETUP_WORDS or \
                words[STORE] != 0xc404 or words[STORE+2] != 0x3301 or \
                words[LATCH-2] & 0xff00 != 0x2b00 or words[LATCH] != 0xddf5:
            raise ValueError('expected the initialized word cursor and signed count guard')
        for pc in range(SETUP, LATCH, 2):
            item = instructions[pc]
            if set(edges[pc]) != {pc+2} or any(group in item.groups for group in
                    (CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP)):
                raise ValueError('local cursor setup and body must be straight-line')
            if HEAD <= pc < STORE:
                reads, writes = map(set, item.regs_access())
                if writes & {ARM_REG_R2, ARM_REG_R3, ARM_REG_R4, ARM_REG_R6, ARM_REG_SP} or \
                        reads & {ARM_REG_R4, ARM_REG_R6, ARM_REG_SP}:
                    raise ValueError('panel updates modify or expose local cursor state')
        for pc in range(SETUP+2, LATCH+2, 2):
            expected = {pc-2, LATCH} if pc == HEAD else {pc-2}
            if {pred for pred, targets in edges.items() if pc in targets} != expected:
                raise ValueError('edge bypasses the local cursor setup or iteration')
        if set(edges[LATCH]) != {HEAD, LATCH+2}:
            raise ValueError('local cursor latch has unexpected successors')
        # Compute the concrete itinerary using the same Thumb transfer and CMP
        # predicate as the existing bounded-callee replay. Other values may be
        # unknown: only the condition is used here. All native effects still
        # run through the normal verifier separately for each visited state.
        known, flags = {}, None
        for pc in range(SETUP, HEAD, 2):
            values, flags = match.loop_replay_transfer(instructions[pc], known, flags)
            known = dict(values)
        self.decisions = []
        for iteration in range(16):
            for pc in range(HEAD, LATCH, 2):
                values, flags = match.loop_replay_transfer(instructions[pc], known, flags)
                known = dict(values)
            if flags is None:
                raise ValueError('local cursor latch has no concrete CMP')
            again = match.loop_replay_condition(instructions[LATCH].cc, flags)
            self.decisions.append(again)
            if not again:
                break
        else:
            raise ValueError('local word cursor crosses the adjacent SP+64 output')
        self.stores = set()

    def check_store(self, iteration, aliases, stack, constants, pointer_slots, return_registers):
        import match
        bottom = -4*len(stack)
        offset = bottom + 4*iteration
        if aliases.get(ARM_REG_R4) != offset or aliases.get(ARM_REG_R6) != bottom+64 or \
                constants.get(ARM_REG_R2) != 0 or ARM_REG_R2 in aliases or ARM_REG_R2 in return_registers or \
                offset in pointer_slots:
            raise ValueError('local cursor lacks its exact zero, word offset or adjacent output')
        match.BufferCallProof.access(offset, 4, stack)
        match.BufferCallProof.access(bottom + 64, 1, stack)
        if stack[iteration][0]:
            raise ValueError('local cursor overlaps a return-carrying word')
        self.stores.add(iteration)

    def state_key(self, pc, successor, iteration):
        if pc == LATCH:
            taken = self.decisions[iteration]
            if successor != (HEAD if taken else LATCH+2):
                return None
            if taken:
                iteration += 1
        return (successor, iteration) if HEAD <= successor <= LATCH else successor

    def evidence(self):
        if self.stores != set(range(len(self.decisions))):
            raise ValueError('missing a reached local cursor store')
        return dict(store=STORE, stride=4, offsets=[4*i for i in sorted(self.stores)],
                    taken=self.decisions, adjacent_output=64)
