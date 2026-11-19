"""Frame words: the stack-index analysis, extended past what registers alone can prove.

The stack-index analysis (``stack_index_precondition_profile``) refuses a variable stack address
left in an argument register at a call, because the callee could read it.  agbcc leaves one
there across callees that never read that register (0x080E4EB0 keeps `&x[i+3]` in R3 across the
BIOS division wrapper 0x08141870).

This module extends the stack-index analysis.  It is used only where the plain analysis
refuses: every report the plain analysis admits keeps its evidence, and a function both
refuse keeps the plain refusal.  Its obligations, each enforced by a refusal:

F1. A callee's stack reach (the bytes above its entry SP it, or anything it calls, may read or
    write), the registers of R0-R3 and R12 it may read before writing them, and those it writes
    on every path to a return are proved by walking its mapped ROM bytes (``CalleeReach``).  The
    only BIOS calls the walk admits are those in ``Policy.swis``, under the printed GBATEK
    premise.
F2. A variable stack address in R0-R3 at a call is no escape when the walk proves the callee
    never reads that register.  After the call it is poison unless the callee writes it on
    every path to a return.

``POLICY`` is the one switch, and disabling it restores the plain analysis exactly.
"""
import functools

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
from capstone.arm import (ARM_INS_BL, ARM_OP_IMM, ARM_REG_CPSR, ARM_REG_LR, ARM_REG_PC,
                          ARM_REG_R0, ARM_REG_SP)

import armv4t
import stack_index_precondition_profile as sip

SCHEMA = "stack-index-frame-words-v1"
MAX_CALLEES = 64
MAX_CALLEE_INSTRUCTIONS = 8192
SWI_PREMISE = ("GBATEK premise, not proved from ROM bytes: BIOS SWI 6 (Div) takes R0 and R1 and "
               "returns in R0, R1 and R3; the SWI handler saves SPSR, R11, R12 and R14 on the "
               "supervisor stack, then switches into System mode so that all further stack "
               "operations use the user stack, the caller's, below its SP; it reads and writes "
               "no word at or above the caller's SP")


class Policy:
    """The one switch: ``enabled`` False restores the plain analysis."""

    def __init__(self, enabled, swis):
        self.enabled = enabled
        self.swis = frozenset(swis)


POLICY = Policy(True, (6,))


# ---- callee stack reach ---------------------------------------------------------------
DECODER = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
DECODER.detail = True
REGISTER = {ARM_REG_R0 + n: n for n in range(13)}
REGISTER.update({ARM_REG_SP: 13, ARM_REG_LR: 14, ARM_REG_PC: 15, ARM_REG_CPSR: 16})
ARGUMENTS = frozenset(range(4))
PASSED = ARGUMENTS | {12}       # what a caller may hand a callee in a register: R0-R3 and IP
CLOBBERED = frozenset({0, 1, 2, 3, 12, 14})
# GBATEK Div: (reads, writes).  The SWI handler also stores R2 below SP and restores it, so R2
# counts as read: a stack address in R2 at the call is a stored copy, never a dead register.
SWI_ARGUMENTS = {6: (frozenset({0, 1, 2}), frozenset({0, 1, 3}))}


class CalleeReach:
    """What a callee, and anything it calls, may touch of its caller: ``(reach, reads, swis, writes)``.

    ``reach`` is the number of bytes above the callee's entry SP it may read or write,
    ``reads`` the registers of R0-R3 and R12 it may read before writing them, and ``writes``
    those it writes on every path to a return.  The walk follows
    the callee's control flow in its mapped bytes with an exact SP depth.  Every reached
    instruction is an ARMv4T encoding (``armv4t``), or SWI.  SP is used only by
    push, pop, `add/sub sp,#imm` and `ldr/str Rd,[sp,#imm]`; any other SP or PC use (an address
    of a local, a jump table, an indirect branch) refuses.  A return is `bx lr` while LR is
    untouched at depth 0, `pop {pc}` of the word the entry push saved LR in, or `bx Rm` once
    Rm was popped from that word, at depth 0.  A nested call that may write the saved LR word
    unsaves it, so a later return through it refuses; ``stores`` keeps, for every callee walked,
    the bytes above its entry SP it may write.
    """

    def __init__(self, span, swis):
        self.span, self.swis = span, swis
        self.memo, self.stores, self.instructions = {}, {}, 0

    def __call__(self, address, active=frozenset()):
        if address in self.memo:
            found = self.memo[address]
            if isinstance(found, sip.Refusal):
                raise found
            return found
        try:
            found = self.walk(address, active)
        except sip.Refusal as refusal:
            self.memo[address] = refusal
            raise
        self.memo[address] = found
        return found

    def walk(self, address, active):
        if address in active:
            sip.refuse(f"callee 0x{address:08X} is recursive")
        if len(self.memo) >= MAX_CALLEES:
            sip.refuse("callee stack reach budget exhausted")
        if self.span is None:
            sip.refuse("callee bytes are not available")
        try:
            data = bytes(self.span(address))
        except ValueError as error:
            sip.refuse(f"callee 0x{address:08X} has no mapped span ({error})")
        end = address + len(data)
        name = f"callee 0x{address:08X}"

        def half(site):
            if not address <= site <= end - 2:
                sip.refuse(f"{name} leaves its mapped span")
            return int.from_bytes(data[site - address:site - address + 2], "little")

        # depth (words), return register, LR untouched, entry-SP offset of the saved LR word,
        # argument registers written on every path
        states = {address: (0, None, True, None, frozenset())}
        pending, reach, stores, reads, swis, exits = [address], 0, 0, set(), set(), []
        while pending:
            site = pending.pop()
            self.instructions += 1
            if self.instructions > MAX_CALLEE_INSTRUCTIONS:
                sip.refuse("callee stack reach budget exhausted")
            depth, ret, intact, saved, defined = states[site]
            popped = surely = None
            raw = half(site)
            size = 4 if raw & 0xF800 == 0xF000 else 2
            instruction = next(DECODER.disasm(data[site - address:site - address + size], site, count=1), None)
            if instruction is None or instruction.size != size:
                sip.refuse(f"{name} reaches an undecodable instruction")
            if raw & 0xFF00 != 0xDF00 and not armv4t.instruction(instruction):
                sip.refuse(f"{name} reaches an instruction that is not ARMv4T Thumb")
            read, written = (set(REGISTER.get(register, -1) for register in registers)
                             for registers in instruction.regs_access())
            successors = [site + size]
            if raw & 0xFE00 == 0xB400:                              # push
                if raw & 0x100:
                    if saved is not None:
                        sip.refuse(f"{name} saves LR twice")
                    saved = -4 * depth - 4
                depth += bin(raw & 0x1FF).count("1")
            elif raw & 0xFE00 == 0xBC00:                            # pop
                registers = [n for n in range(8) if raw & (1 << n)] + ([15] if raw & 0x100 else [])
                if len(registers) > depth:
                    sip.refuse(f"{name} pops past its entry SP")
                for position, register in enumerate(registers):
                    word = -4 * depth + 4 * position
                    if register == 15:
                        if word != saved or depth != len(registers):
                            sip.refuse(f"{name} pops PC from a word other than its saved LR")
                        successors = []
                        exits.append(None)
                    elif word == saved:
                        popped, saved = register, None
                depth -= len(registers)
                if saved is not None and saved < -4 * depth:
                    saved = None
            elif raw & 0xFF00 == 0xB000:                            # add/sub sp,#imm
                words = raw & 0x7F
                if raw & 0x80:
                    depth += words
                elif words > depth:
                    sip.refuse(f"{name} releases past its entry SP")
                else:
                    depth -= words
                    if saved is not None and saved < -4 * depth:
                        saved = None
            elif raw & 0xF000 == 0x9000:                            # ldr/str Rd,[sp,#imm]
                offset = 4 * (raw & 0xFF) - 4 * depth
                reach = max(reach, offset + 4)
                if not raw & 0x800:
                    stores = max(stores, offset + 4)
                    if offset == saved:
                        saved = None
            elif raw & 0xF800 in (0x4800, 0xA000):                  # literal load, adr
                pass
            elif raw & 0xFF00 == 0x4700:                            # bx / blx
                register = (raw >> 3) & 15
                if raw & 0x87 or depth or not (register == 14 and intact or
                                               register == ret is not None):
                    sip.refuse(f"{name} leaves through an unproved indirect branch")
                successors = []
                exits.append(None)
            elif raw & 0xF800 == 0xF000:                            # bl
                if instruction.id != ARM_INS_BL or instruction.operands[0].type != ARM_OP_IMM:
                    sip.refuse(f"{name} has an unsupported long branch")
                target = instruction.operands[0].imm
                if address <= target < end:
                    sip.refuse(f"{name} branches and links inside itself")
                inner, inner_reads, inner_swis, inner_writes = self(target, active | {address})
                reach = max(reach, inner - 4 * depth)
                stores = max(stores, self.stores[target] - 4 * depth)
                if saved is not None and saved < self.stores[target] - 4 * depth:
                    saved = None            # the inner callee may overwrite the saved LR word
                read |= inner_reads
                swis |= inner_swis
                # It may clobber all of these, but surely writes only what every return writes.
                written, surely = set(CLOBBERED), inner_writes
            elif raw & 0xFF00 == 0xDF00:                            # swi
                if raw & 0xFF not in self.swis:
                    sip.refuse(f"{name} calls BIOS SWI {raw & 0xFF}, outside the policy")
                swis.add(raw & 0xFF)
                read, written = SWI_ARGUMENTS[raw & 0xFF]
            elif raw & 0xF000 == 0xD000 and (raw >> 8) & 15 < 14:   # conditional branch
                displacement = raw & 0xFF
                successors.append(site + 4 + 2 * (displacement - 256 if displacement & 0x80 else displacement))
            elif raw & 0xF800 == 0xE000:                            # b
                displacement = raw & 0x7FF
                successors = [site + 4 + 2 * (displacement - 2048 if displacement & 0x400 else displacement)]
            elif {13, 15, -1} & (read | written):
                sip.refuse(f"{name} uses SP or PC outside push, pop and fixed slots")
            reads |= (read & PASSED) - defined
            defined = defined | ((written if surely is None else surely) & PASSED)
            if exits and exits[-1] is None:
                exits[-1] = defined
            if ret in written:
                ret = None
            if popped is not None:
                ret = popped
            if 14 in written:
                intact = False
            for successor in successors:
                if not address <= successor < end or successor % 2:
                    sip.refuse(f"{name} branches outside its mapped span")
                state = (depth, ret, intact, saved, defined)
                previous = states.get(successor)
                if previous is not None:
                    if previous[0] != depth:
                        sip.refuse(f"{name} joins different stack depths")
                    # A join keeps only what both paths prove.
                    state = (depth, ret if previous[1] == ret else None, previous[2] and intact,
                             saved if previous[3] == saved else None, previous[4] & defined)
                if state != previous:
                    states[successor] = state
                    pending.append(successor)
        # Argument registers written on every path to a return: what the call surely replaces.
        writes = frozenset.intersection(*exits) if exits else frozenset()
        self.stores[address] = stores
        return reach, frozenset(reads), frozenset(swis), writes


# ---- the analysis ---------------------------------------------------------------------
class FrameWordsAnalysis(sip.Analysis):
    def __init__(self, *args, reach=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.reach = reach
        self.calls, self.swis = {}, set()

    # ---- calls (F2) ---------------------------------------------------------------
    def callee(self, state, site, target):
        """F2: argument registers a callee never reads."""
        carried = [register for register in range(4) if sip.is_ranged(state.regs[register])]
        if not carried:
            return []
        try:
            reach, reads, swis, writes = self.reach(target)
        except sip.Refusal:
            reach, reads, swis, writes = None, PASSED, frozenset(), frozenset()
        dead = [register for register in carried if register not in reads]
        for register in dead:
            # Never read by the callee: not an escape.  Hidden from the call's own checks here;
            # ``step`` gives it back as POISON unless the callee surely overwrites it.
            state.regs[register], state.exprs[register] = sip.TOP, None
        if self.check and reach is not None:
            self.calls[site] = (target, reach, sorted(reads), dead)
            self.swis |= swis
        return [register for register in dead if register not in writes]

    # ---- transfer -----------------------------------------------------------------
    def step(self, state, site):
        raw = self.halfword(site)
        if raw & 0xF800 == 0xF000:
            second = self.halfword(site + 2)
            offset = ((raw & 0x7FF) << 12) | ((second & 0x7FF) << 1)
            target = site + 4 + (offset - 0x800000 if offset & 0x400000 else offset)
            state = state.copy()
            surviving = self.callee(state, site, target) if not self.address <= target < self.end else []
            outgoing = super().step(state, site)
            for _, after in outgoing:
                for register in surviving:
                    # The callee may leave it untouched: still a stack address, now unusable.
                    after.regs[register], after.exprs[register] = sip.POISON, None
            return outgoing
        return super().step(state, site)

    def frame_words_evidence(self):
        return {"schema": SCHEMA,
                "calls": [[site, target, reach, reads, dead]
                          for site, (target, reach, reads, dead) in sorted(self.calls.items())],
                "swis": sorted(self.swis), "premise": SWI_PREMISE if self.swis else None,
                "premise_proved": False}


def prove(prove_words, data, address, verified_sites, derivations, accesses, copies, *,
          selector, forwarding, callee_span):
    """The plain analysis where it may be used; frame words where it refuses."""
    arguments = (data, address, verified_sites, derivations, accesses, copies)
    try:
        return prove_words(*arguments, selector=selector, forwarding=forwarding)
    except sip.Refusal as refusal:
        if not POLICY.enabled:
            raise
        first = refusal
    analysis_type = functools.partial(FrameWordsAnalysis, reach=CalleeReach(callee_span, POLICY.swis))
    try:
        return prove_words(*arguments, selector=selector, forwarding=forwarding,
                           analysis_type=analysis_type)
    except sip.Refusal:
        raise first


def lines(found):
    """The report lines for a frame-words admission; the replayed report repeats them."""
    reach = max([row[2] for row in found["calls"]], default=0)
    dead = ", ".join(f"R{register} at 0x{row[0]:08X}" for row in found["calls"] for register in row[4])
    line = (f"* stack index frame words: {len(found['calls'])} calls with ROM-walked callee stack "
            f"reach (at most {reach} bytes above the callee's entry SP); stack addresses left in "
            f"argument registers the callee never reads: {dead or 'none'}")
    if found["premise"] is not None:
        line += f"; {found['premise']}"
    return [line]
