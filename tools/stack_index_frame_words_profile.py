"""Frame words: stack-index owners whose locals hold spilled stack addresses and counters.

The stack-index analysis (``stack_index_precondition_profile``) tracks every value derived
from SP in registers, but a value written to a local word used to leave its domain: a ranged
stack address stored to the frame refused ("escapes to memory"), an exact one was the core's
``pointer_slots`` business, and the core refuses every frame holding such a word under a
variable-index policy, because a variable store could overwrite it unseen.  agbcc at -O2 spills
both kinds under register pressure (0x080E4EB0 keeps `&x[i]`, `&y[i]` and the bases of four
s16[6] arrays in local words, and its u8 loop counter at sp+0x48).

This module is the stack-index analysis extended word by word.  It is used only where the
plain analysis cannot be: when the core deferred an exact stack-address spill to it, or when
the plain analysis refuses.  Every report the plain analysis admits keeps its evidence, and a
function both refuse keeps the plain refusal.  Its obligations, each enforced by a refusal:

F1. A callee's stack reach (the bytes above its entry SP it, or anything it calls, may read or
    write), the registers of R0-R3 and R12 it may read before writing them, those it writes on
    every path to a return, and the registers of R4-R11 it may return changed are proved by
    walking its mapped ROM bytes (``CalleeReach``).  The only BIOS calls the walk admits are
    those in ``Policy.swis``, under the printed GBATEK premise.
F2. A variable stack address in R0-R3 at a call is no escape when the walk proves the callee
    never reads that register.  After the call it is poison unless the callee writes it on
    every path to a return.
F3. A stack address (exact, ranged, or a join that may be either) is stored only as a whole,
    aligned, allocated local word at a fixed offset (`str Rd,[sp,#k]`, or through an exact
    alias at a constant offset).  The word becomes *pointer-bearing* and holds that value.
    An exact address is accepted only at a `str Rd,[sp,#k]` the core deferred
    (``Policy.defer_spill``); the core then keeps no pointer slot for it.  A word that is
    pointer-bearing on one path of a join only is "maybe pointer-bearing" (F4 and F5 treat it
    as one).
F4. A whole-word reload of a pointer-bearing word yields the stored address as a value this
    analysis owns (ranged, even when it is one exact offset), so every later use is checked
    here: no escape to calls, memory, comparisons or returns, and every access through it
    stays inside allocated local words.  A partial read or store of a pointer-bearing word,
    and a block transfer over one, refuse.
F5. Every variable access (a deferred site, or one through an address this analysis owns),
    proved in range or admitted under a recorded premise, must not overlap a word that may be
    pointer-bearing at that point.  So the pointer-bearing words in a variable store's value
    hull lie outside the range it may write, and keep their values.
F6. At a call while a word is pointer-bearing, a pointer-bearing word inside the callee's reach
    (F1), or any when the walk refuses, refuses the owner.  So does a callee that may read a
    register holding a stack address (R0-R3 or R12): it may write any local word through it,
    and the core bounds those writes against its own slots only, which hold none of these words.
    A call this analysis does not walk, other than a proved ROM table copy, is trusted, as the
    core trusts every callee it does not walk, to return no address into the caller's frame;
    the report lists those calls.
F7. Releasing SP over a pointer-bearing word (`add sp`) forbids any later call or SP move
    down, so no released stack address is read back while the owner runs.  A pop that reads a
    word which may be pointer-bearing refuses, as the core refuses one over its own pointer
    slots: the register, PC included, would hold a stack address no check here could see.
F8. A *possible* stack address is a register the core may hold as an exact stack alias that
    this analysis cannot pin to one value: a stack alias the core keeps from a call's result
    (``Policy.note_returned``, every alternative included) or a join of an exact alias with a
    scalar or with another exact alias.  It is ``("O", offsets)``, one of those entry-SP
    offsets or no stack address at all, or ``OPAQUE`` when the offsets are not known (then
    every local word is a candidate).  An access through one may reach each candidate word,
    and a pointer-bearing candidate refuses.
F9. A load through an address this analysis owns is initialised when the same address value
    (one identity per defining instruction) was stored through at the same displacement with
    at least the same width on every path since; byte-level initialisation still covers the
    rest.  Joins keep an identity or a fact only when both paths hold it, so none reaches its
    own defining instruction again.
F10. A whole scalar word stored at a fixed offset keeps its value range but not its derivation;
    a register loaded from it, or stored to it, mirrors it until either is written, and a
    compare-and-branch refinement of the register refines the word.  Every write that may reach
    a word ends its mirrors, whether the word is tracked or not, and forgets the scalar words it
    may overwrite: a variable store those its value hull overlaps, a store through a possible
    stack address its candidates, a callee those inside its reach, or all of them when it may
    read a register holding a stack address.  A call walks the callee while a word is mirrored
    too: a mirror held in R4-R11 survives the call only when the walk proves the callee returns
    that register restored (F1), and the walk drops it otherwise.  The walk sees the callee's
    stores through SP and stack addresses handed over in R0-R3 or R12, nothing else: that a
    callee writes no local word through an address held in R4-R11 is the ABI premise every
    call rests on.  Joins keep a scalar word only when both paths track it.
F11. A premise is never stated on an index with no variable in it: it is the same on every run,
    so the premise would be always true or always false (a reloaded constant word makes such
    an index common).

The core reaches this module through ``Policy.defer_spill`` and ``Policy.note_returned``;
``POLICY`` is the one switch, and disabling it restores the plain analysis and the core's
refusal exactly.
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
MAX_POSSIBLE = 16           # candidate offsets of one possible stack address before OPAQUE
SWI_PREMISE = ("GBATEK premise, not proved from ROM bytes: BIOS SWI 6 (Div) takes R0 and R1 and "
               "returns in R0, R1 and R3; the SWI handler saves SPSR, R11, R12 and R14 on the "
               "supervisor stack, then switches into System mode so that all further stack "
               "operations use the user stack, the caller's, below its SP; it reads and writes "
               "no word at or above the caller's SP")


class Policy:
    """The one switch: ``enabled`` False restores the plain analysis and the core refusal."""

    def __init__(self, enabled, swis):
        self.enabled = enabled
        self.swis = frozenset(swis)

    def defers(self, instruction):
        raw = int.from_bytes(bytes(instruction.bytes[:2]), "little")
        return self.enabled and instruction.size == 2 and raw & 0xF800 == 0x9000


POLICY = Policy(True, (6,))


def is_pointer(value):
    return value[0] in ("A", "P", "O")


ZERO = ("c", 0)


def owned(value):
    """A reloaded stack address, as a value only this analysis may let be used.

    An exact address becomes an index-zero base: its own offset, index expression 0."""
    if value[0] != "A":
        return sip.POISON
    if not value[4]:
        return sip.norm("A", value[1], value[1], 32, True, value[1], ZERO)
    return sip.norm("A", value[1], value[2], value[3], True, value[5], value[6])


def drop_zero(expr):
    """`0 + e` -> `e`, so a premise through a reloaded base reads like one through a register."""
    if expr is not None and expr[0] == "bin" and expr[1] == "add" and expr[2] == ZERO:
        return expr[3]
    return expr


def variable(expr):
    """Whether a derivation reads anything that is not a constant (an entry register, a call
    result or a load)."""
    return expr[0] in ("entry", "ret", "ld") or any(variable(part) for part in expr[1:]
                                                    if type(part) is tuple)


def possible(offsets):
    """A possible stack address (F8): one of ``offsets`` (entry-SP relative) or none at all."""
    offsets = frozenset(offsets)
    return ("O", offsets) if offsets and len(offsets) <= MAX_POSSIBLE else sip.OPAQUE


def possible_join(left, right):
    """The join of two values the plain domain makes OPAQUE, keeping their exact offsets."""
    found = (candidates(left), candidates(right))
    return sip.OPAQUE if None in found else possible(found[0] | found[1])


def candidates(value):
    """The exact stack offsets ``value`` may hold; None when any local word may be one."""
    if value[0] == "S":
        return frozenset()
    if value[0] == "A" and not value[4]:
        return frozenset((value[1],))
    if value[0] == "O" and len(value) > 1:
        return value[1]
    return None


# ---- callee stack reach ---------------------------------------------------------------
DECODER = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
DECODER.detail = True
REGISTER = {ARM_REG_R0 + n: n for n in range(13)}
REGISTER.update({ARM_REG_SP: 13, ARM_REG_LR: 14, ARM_REG_PC: 15, ARM_REG_CPSR: 16})
ARGUMENTS = frozenset(range(4))
PASSED = ARGUMENTS | {12}       # what a caller may hand a callee in a register: R0-R3 and IP
CLOBBERED = frozenset({0, 1, 2, 3, 12, 14})
CALLEE_SAVED = frozenset(range(4, 12))
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
    the bytes above its entry SP it may write.  ``clobbers`` keeps the registers of R4-R11 that
    may differ from their entry values at a return: a register written is restored only by a pop
    from the word its entry value was pushed to, while no store of the callee or of anything it
    calls may have reached that word since.
    """

    def __init__(self, span, swis):
        self.span, self.swis = span, swis
        self.memo, self.stores, self.instructions = {}, {}, 0
        self.clobbers = {}

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
        # argument registers written on every path, R4-R11 holding their entry values, and the
        # (entry-SP offset, register) of every word holding one of those entry values
        states = {address: (0, None, True, None, frozenset(), CALLEE_SAVED, frozenset())}
        pending, reach, stores, reads, swis, exits = [address], 0, 0, set(), set(), []
        clobbers = set()
        while pending:
            site = pending.pop()
            self.instructions += 1
            if self.instructions > MAX_CALLEE_INSTRUCTIONS:
                sip.refuse("callee stack reach budget exhausted")
            depth, ret, intact, saved, defined, fresh, kept = states[site]
            popped = surely = None
            restored = set()
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
                # Ascending registers at ascending addresses, from the new SP up.
                kept |= {(-4 * depth - 4 * bin(raw & 0x1FF).count("1") + 4 * position, register)
                         for position, register in enumerate(n for n in range(8) if raw & (1 << n))
                         if register in fresh}
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
                    if (word, register) in kept:
                        restored.add(register)
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
                    kept = frozenset(pair for pair in kept if pair[0] != offset)
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
                kept = frozenset(pair for pair in kept if pair[0] >= self.stores[target] - 4 * depth)
                fresh -= self.clobbers[target]
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
            fresh = (fresh - written) | restored
            kept = frozenset(pair for pair in kept if pair[0] >= -4 * depth)    # released words
            if exits and exits[-1] is None:
                exits[-1] = defined
                clobbers |= CALLEE_SAVED - fresh
            if ret in written:
                ret = None
            if popped is not None:
                ret = popped
            if 14 in written:
                intact = False
            for successor in successors:
                if not address <= successor < end or successor % 2:
                    sip.refuse(f"{name} branches outside its mapped span")
                state = (depth, ret, intact, saved, defined, fresh, kept)
                previous = states.get(successor)
                if previous is not None:
                    if previous[0] != depth:
                        sip.refuse(f"{name} joins different stack depths")
                    # A join keeps only what both paths prove.
                    state = (depth, ret if previous[1] == ret else None, previous[2] and intact,
                             saved if previous[3] == saved else None, previous[4] & defined,
                             previous[5] & fresh, previous[6] & kept)
                if state != previous:
                    states[successor] = state
                    pending.append(successor)
        # Argument registers written on every path to a return: what the call surely replaces.
        writes = frozenset.intersection(*exits) if exits else frozenset()
        self.stores[address] = stores
        self.clobbers[address] = frozenset(clobbers)
        return reach, frozenset(reads), frozenset(swis), writes


# ---- the analysis ---------------------------------------------------------------------
class WordState(sip.State):
    __slots__ = ("words", "mirrors", "ids", "facts", "released")

    def __init__(self, kinds, init, regs, exprs, flags, words=(), mirrors=(), ids=(None,) * 16,
                 facts=frozenset(), released=False):
        super().__init__(kinds, init, regs, exprs, flags)
        self.words, self.mirrors, self.ids = words, mirrors, ids
        self.facts, self.released = facts, released

    def key(self):
        return super().key() + (self.words, self.mirrors, tuple(self.ids), self.facts, self.released)

    def __eq__(self, other):
        return type(other) is WordState and self.key() == other.key()

    def copy(self):
        return WordState(self.kinds, self.init, list(self.regs), list(self.exprs), self.flags,
                         self.words, self.mirrors, list(self.ids), self.facts, self.released)

    def freeze(self):
        super().freeze()
        self.ids = tuple(self.ids)
        return self


def word_entry(state, offset):
    return next(((value, ident) for word, value, ident in state.words if word == offset), None)


class FrameWordsAnalysis(sip.Analysis):
    def __init__(self, *args, spills=frozenset(), reach=None, returned=None, **kwargs):
        super().__init__(*args, **kwargs)
        self.spills, self.reach = spills, reach
        self.returned = returned or {}
        self.initialised = False
        self.pointer_words, self.spilled, self.identity_loads = set(), set(), set()
        self.calls, self.swis, self.call_sites = {}, set(), set()

    # ---- words --------------------------------------------------------------------
    def put(self, state, offset, value, ident):
        state.words = tuple(sorted([entry for entry in state.words if entry[0] != offset] +
                                   [(offset, value, ident)]))

    def forget(self, state, low, high, *, scalars_only=False):
        """Drop the tracked words overlapping [low, high) (only the scalar ones if asked) and the
        mirror of every word there, tracked or not: whatever [low, high) now holds, no register
        is known to equal it."""
        gone = {word for word, value, _ in state.words if word < high and low < word + 4 and
                not (scalars_only and is_pointer(value))}
        if gone:
            state.words = tuple(entry for entry in state.words if entry[0] not in gone)
        state.mirrors = tuple(pair for pair in state.mirrors if not (pair[1] < high and low < pair[1] + 4))

    def pointer_overlap(self, state, low, high):
        return next((word for word, value, _ in state.words
                     if is_pointer(value) and word < high and low < word + 4), None)

    def spans(self, state, value, displacement, width):
        """The byte ranges an access through a possible stack address may reach (F8)."""
        offsets = candidates(value)
        if offsets is None or displacement is None:
            return [(-4 * sip.depth(state), 0)]
        return [(offset + displacement, offset + displacement + width) for offset in sorted(offsets)]

    def through_possible(self, state, spans, load, stored):
        """F8: an access that may reach any of ``spans`` (``stored``: the values a store writes)."""
        for low, high in spans:
            word = self.pointer_overlap(state, low, high)
            if word is not None:
                self.fail(f"{'load' if load else 'store'} through a possible stack address may "
                          f"reach the pointer-bearing local word at entry-SP{word:+d}")
        if not load:
            if any(is_pointer(value) for value in stored):
                self.fail("stack address stored through a possible stack address")
            for low, high in spans:
                self.forget(state, low, high)

    def write(self, state, register, value, expr=None):
        super().write(state, register, value, expr)
        state.ids[register] = None
        state.mirrors = tuple(pair for pair in state.mirrors if pair[0] != register)

    def premise(self, state, site, width, load, c, texpr, tlo, tmod, disp):
        texpr = drop_zero(texpr)
        if c is not None and texpr is not None and not variable(texpr):
            # The same index on every run: a premise on it is always true or always false, and
            # neither is a premise to review (a reloaded constant word makes this common).
            return f"index is the constant {sip.render(texpr)} (no premise can be stated)"
        return super().premise(state, site, width, load, c, texpr, tlo, tmod, disp)

    def frame_check(self, state, lo, hi, width, *, load):
        problem = super().frame_check(state, lo, hi, width, load=load and not self.initialised)
        if problem is None:
            word = self.pointer_overlap(state, lo, hi + width)
            if word is not None:
                problem = f"index range overlaps a pointer-bearing local word at entry-SP{word:+d}"
        return problem

    # ---- accesses -----------------------------------------------------------------
    def fixed(self, state, site, offset, width, load, register):
        """A fixed-offset access to the frame (F3, F4, F10)."""
        word = offset - offset % 4
        entry = word_entry(state, word)
        floor = -4 * sip.depth(state)
        whole = width == 4 and offset % 4 == 0 and floor <= offset < 0 and \
            state.kinds[(-offset - 1) // 4] == "L"
        if load:
            self.origins.add(offset)
            if entry is not None and is_pointer(entry[0]):
                if not whole:
                    self.fail("partial read of a pointer-bearing local word")
                self.write(state, register, owned(entry[0]) if whole else sip.POISON)
                state.ids[register] = entry[1] if whole else None
                return
            result = sip.TOP
            if whole and entry is not None:
                result = entry[0]
            elif width == 1:
                result = ("S", 0, 255, 0)
            elif width == 2:
                result = ("S", 0, 0xFFFF, 0)
            self.write(state, register, result)
            if whole:
                state.mirrors = state.mirrors + ((register, word),)
            return
        value = self.read(state, register)
        if is_pointer(value):
            if not whole:
                self.fail("stack address stored outside a whole allocated local word")
            elif not sip.is_ranged(value) and value[0] == "A" and site not in self.spills:
                self.fail("exact stack address stored to a local word the core did not defer")
            self.forget(state, word, word + 4)
            if whole:
                self.put(state, word, value, state.ids[register])
                if self.check:
                    self.pointer_words.add(word)
                    if site in self.spills:
                        self.spilled.add(site)
        else:
            if entry is not None and is_pointer(entry[0]) and not whole:
                self.fail("partial store over a pointer-bearing local word")
            self.forget(state, offset, offset + width)
            if whole:
                self.put(state, word, value, None)
                state.mirrors = tuple(pair for pair in state.mirrors if pair[0] != register) + \
                    ((register, word),)
        self.mark(state, offset, width)

    def access(self, state, site, base_register, displacement, index_register, width, load,
               value_register, signed=False):
        base = self.read(state, base_register)
        index = None if index_register is None else self.read(state, index_register)
        constant = index is None or index[0] == "S" and index[1] == index[2]
        deferred = site in self.accesses
        if base[0] == "A" and not base[4] and constant and not deferred:
            offset = base[1] + displacement + (0 if index is None else index[1])
            return self.fixed(state, site, offset, width, load, value_register)
        if base[0] == "O":
            at = displacement + (0 if index is None else index[1]) if constant else None
            self.through_possible(state, self.spans(state, base, at, width), load,
                                  () if load else (self.read(state, value_register),))
        ident = state.ids[base_register]
        disp = displacement + (0 if index is None else index[1]) if constant else None
        self.initialised = load and ident is not None and disp is not None and any(
            held == ident and at == disp and size >= width for held, at, size in state.facts)
        try:
            super().access(state, site, base_register, displacement, index_register, width, load,
                           value_register, signed)
            if self.initialised and self.check:
                self.identity_loads.add(site)
        finally:
            self.initialised = False
        if (deferred or sip.is_ranged(base)) and base[0] == "A" and (index is None or index[0] == "S"):
            hull = base if index is None else sip.add_values(base, index)
            if not load:
                # The access is proved or premised clear of pointer-bearing words (F5); only the
                # hull, which may be far wider under a premise, reaches them.
                self.forget(state, hull[1] + displacement, hull[2] + displacement + width,
                            scalars_only=True)
                if ident is not None and disp is not None:
                    state.facts = state.facts | {(ident, disp, width)}

    def copy_site(self, state, site):
        destination, count = self.copies[site]
        if self.pointer_overlap(state, destination, destination + count) is not None:
            self.fail("ROM copy destination overlaps a pointer-bearing local word")
        self.forget(state, destination, destination + count)
        return super().copy_site(state, site)

    # ---- identities (F9) ----------------------------------------------------------
    def identify(self, state, site, register):
        # No holder or fact of this identity reaches its own instruction: the state there joins
        # the path that first reaches it, which has none, so a new value needs no clean-up.
        if sip.is_ranged(state.regs[register]) and state.regs[register][0] == "A":
            state.ids[register] = site

    def derive(self, state, site, destination, left, right):
        super().derive(state, site, destination, left, right)
        self.identify(state, site, destination)

    def immediate(self, state, destination, source, amount):
        ident = state.ids[source]
        value = self.read(state, source)
        super().immediate(state, destination, source, amount)
        if value[0] == "O" and len(value) > 1:
            # The core moves its exact alias by the immediate: so do the candidates (F8).
            state.regs[destination] = possible(offset + amount for offset in value[1])
        if amount == 0:
            state.ids[destination] = ident
        else:
            self.identify(state, self.current, destination)

    # ---- calls (F2, F6, F10) -----------------------------------------------------
    def callee(self, state, site, target):
        """F2, F6 and F10: words a callee may reach, and argument registers it never reads."""
        if self.check and site not in self.copies:
            self.call_sites.add(site)       # a ROM table copy's helper is authenticated, not trusted
        carried = [register for register in range(4) if sip.is_ranged(state.regs[register])]
        # A mirror held in R4-R11 may survive the call, so the words it mirrors need the walk too.
        if not state.words and not state.mirrors and not state.released and not carried:
            return []
        if state.released:
            self.fail("call after a pointer-bearing local word was released")
        try:
            reach, reads, swis, writes = self.reach(target)
        except sip.Refusal as refusal:
            reach, reads, swis, writes, reason = None, PASSED, frozenset(), frozenset(), str(refusal)
        floor = -4 * sip.depth(state)
        # A callee handed a stack address may write any local word through it: the core bounds
        # those writes against its own slots only, which hold none of these words.
        receives = [register for register in sorted(reads) if state.regs[register][0] in ("A", "O")]
        if receives and any(is_pointer(value) for _, value, _ in state.words):
            self.fail(f"callee 0x{target:08X} receives a stack address in R{receives[0]} while a "
                      f"local word holds one")
        for word, value, _ in state.words:
            if is_pointer(value) and (reach is None or word < floor + reach):
                self.fail(f"callee 0x{target:08X} may reach the pointer-bearing local word at "
                          f"entry-SP{word:+d}" + ("" if reach is not None else f" ({reason})"))
        self.forget(state, floor, 0 if reach is None or receives else floor + reach)
        # A mirror of a register the callee may return changed ends here (F10): the word keeps its
        # range, but a later compare of the register says nothing about it.  A refused walk proves
        # nothing, so every register of R4-R11 counts as changed.
        changed = CALLEE_SAVED if reach is None else self.reach.clobbers[target]
        state.mirrors = tuple(pair for pair in state.mirrors if pair[0] not in changed)
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
        self.current = site
        if raw & 0xF000 == 0x9000:
            state = state.copy()
            offset = -4 * sip.depth(state) + 4 * (raw & 255)
            self.fixed(state, site, offset, 4, bool(raw & 0x800), (raw >> 8) & 7)
            return [(site + 2, state)]
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
                for register, offsets in self.returned.get(site, {}).items():
                    # A stack alias the core keeps from the call, on some return paths (F8).
                    if register is None:
                        self.fail(f"call at 0x{site:08X} returns a stack alias outside R0-R12")
                    elif register not in surviving:
                        held = candidates(after.regs[register])
                        if held is None or not offsets <= held:
                            after.regs[register] = sip.OPAQUE if held is None else possible(held | offsets)
                            after.exprs[register] = None
                for register in CLOBBERED:
                    after.ids[register] = None
                after.mirrors = tuple(pair for pair in after.mirrors if pair[0] not in CLOBBERED)
            return outgoing
        moved = None
        if raw & 0xF000 == 0xC000:
            base = (raw >> 8) & 7
            pointer, count = state.regs[base], bin(raw & 0xFF).count("1")
            if pointer[0] == "A" and not pointer[4]:
                low, high = pointer[1], pointer[1] + 4 * count
                if self.pointer_overlap(state, low, high) is not None:
                    self.fail("block transfer over a pointer-bearing local word")
                if not raw & 0x800:
                    state = state.copy()
                    self.forget(state, low, high)
            elif pointer[0] == "O":
                state = state.copy()
                self.through_possible(state, self.spans(state, pointer, 0, 4 * count), bool(raw & 0x800),
                                      [state.regs[n] for n in range(8) if raw & (1 << n)])
                if len(pointer) > 1 and not (raw & 0x800 and raw & (1 << base)):
                    # Written back past the words, as the core moves its exact alias.
                    moved = (base, possible(offset + 4 * count for offset in pointer[1]))
        if raw & 0xFE00 == 0xBC00:
            floor = -4 * sip.depth(state)
            word = self.pointer_overlap(state, floor, floor + 4 * bin(raw & 0x1FF).count("1"))
            if word is not None:
                # The core pops into TOP: the register would hold a stack address unseen (F7).
                self.fail(f"pop of the pointer-bearing local word at entry-SP{word:+d}")
        if state.released and sip.moves_sp_down(raw):
            self.fail("the owner moves SP down after releasing a pointer-bearing local word")
        before = sip.depth(state)
        source = None
        if raw & 0xFF00 == 0x4600:
            source = (raw >> 3) & 15
        elif raw & 0xFFC0 == 0x0000:
            source = (raw >> 3) & 7
        ident = state.ids[source] if source is not None and source < 13 else None
        outgoing = super().step(state, site)
        for _, after in outgoing:
            if after is None:
                continue
            if moved is not None:
                after.regs[moved[0]] = moved[1]
            if source is not None:
                after.ids[(raw & 7) | ((raw >> 4) & 8) if raw & 0xFF00 == 0x4600 else raw & 7] = ident
            if sip.depth(after) < before:
                floor = -4 * sip.depth(after)
                if any(is_pointer(value) for word, value, _ in after.words if word < floor):
                    after.released = True
                self.forget(after, -4 * before, floor)
                after.facts = frozenset()
        if raw & 0xF000 == 0xD000 and state.flags is not None:
            register = state.flags[0]
            for _, after in outgoing:
                if after is not None and after.regs[register][0] == "S":
                    for held, word in after.mirrors:
                        entry = word_entry(after, word)
                        # A mirror holds only while neither side is written, so the word holds
                        # the register's value; never let a refinement rewrite a pointer entry.
                        if held == register and (entry is None or entry[0][0] == "S"):
                            self.put(after, word, after.regs[register], None)
        return outgoing

    # ---- driver -------------------------------------------------------------------
    def join_states(self, old, new, site, visits):
        if old is None:
            return new
        joined = super().join_states(old, new, site, visits)
        left = {word: (value, ident) for word, value, ident in old.words}
        right = {word: (value, ident) for word, value, ident in new.words}
        words = []
        for word in sorted(set(left) | set(right)):
            a, b = left.get(word), right.get(word)
            if a is not None and b is not None:
                if a[0][0] == "S" and b[0][0] == "S":
                    value = sip.widen(a[0], sip.join_values(a[0], b[0]), self.thresholds, visits)
                elif is_pointer(a[0]) and is_pointer(b[0]):
                    value = sip.widen(a[0], sip.join_values(a[0], b[0]), self.thresholds, visits)
                else:
                    value = sip.POISON
                words.append((word, value, a[1] if a[1] == b[1] else None))
            elif is_pointer((a or b)[0]):
                words.append((word, sip.POISON, None))
        # A join the plain domain makes OPAQUE keeps the exact offsets it may hold (F8).
        regs = tuple(possible_join(a, b) if value == sip.OPAQUE else value
                     for value, a, b in zip(joined.regs, old.regs, new.regs))
        return WordState(joined.kinds, joined.init, regs, joined.exprs, joined.flags,
                         tuple(words), tuple(sorted(set(old.mirrors) & set(new.mirrors))),
                         tuple(x if x == y else None for x, y in zip(old.ids, new.ids)),
                         old.facts & new.facts, old.released or new.released)

    def run(self):
        exprs = tuple(("entry", n) if n < 4 else None for n in range(16))
        entry = WordState((), frozenset(), tuple([sip.TOP] * 16), exprs, None)
        states, visits, pending, updates = {self.address: entry}, {}, [self.address], 0
        while pending:
            site = pending.pop()
            for successor, outgoing in self.step(states[site], site):
                if successor is sip.EXIT or outgoing is None:
                    continue
                outgoing.freeze()
                visits[successor] = visits.get(successor, 0) + 1
                merged = self.join_states(states.get(successor), outgoing, successor, visits[successor])
                if merged != states.get(successor):
                    updates += 1
                    if updates > sip.MAX_UPDATES:
                        sip.refuse("value-range proof budget exhausted")
                    states[successor] = merged
                    pending.append(successor)
        self.check = True
        for site in sorted(states):
            self.step(states[site], site)
        unproved = {site for site in self.spills if site in states} - self.spilled
        if unproved:
            sip.refuse(f"deferred stack-address spill at 0x{min(unproved):08X} is not a tracked local word")
        return states

    def frame_words_evidence(self):
        return {"schema": SCHEMA, "pointer_words": sorted(self.pointer_words),
                "spills": sorted(self.spilled), "identity_loads": sorted(self.identity_loads),
                "calls": [[site, target, reach, reads, dead]
                          for site, (target, reach, reads, dead) in sorted(self.calls.items())],
                "unwalked": sorted(self.call_sites - set(self.calls)),
                "swis": sorted(self.swis), "premise": SWI_PREMISE if self.swis else None,
                "premise_proved": False}


def prove(prove_words, data, address, verified_sites, derivations, accesses, copies, *,
          selector, forwarding, spills, callee_span, returned):
    """The plain analysis where it may be used; frame words where it refuses or must not."""
    arguments = (data, address, verified_sites, derivations, accesses, copies)
    first = None
    if not spills:
        try:
            return prove_words(*arguments, selector=selector, forwarding=forwarding)
        except sip.Refusal as refusal:
            if not POLICY.enabled:
                raise
            first = refusal
    analysis_type = functools.partial(FrameWordsAnalysis, spills=spills, returned=returned,
                                      reach=CalleeReach(callee_span, POLICY.swis))
    try:
        return prove_words(*arguments, selector=selector, forwarding=forwarding,
                           analysis_type=analysis_type)
    except sip.Refusal:
        if first is not None:
            raise first
        raise


def lines(found):
    """The report lines for a frame-words admission; the replayed report repeats them."""
    words = ", ".join(f"entry_SP{word:+#x}" for word in found["pointer_words"]) or "none"
    spills = ", ".join(f"0x{site:08X}" for site in found["spills"]) or "none"
    reach = max([row[2] for row in found["calls"]], default=0)
    dead = ", ".join(f"R{register} at 0x{row[0]:08X}" for row in found["calls"] for register in row[4])
    line = (f"* stack index frame words: pointer-bearing local words {words}; deferred exact "
            f"spills {spills}; {len(found['identity_loads'])} identity-initialised loads; "
            f"{len(found['calls'])} calls with ROM-walked callee stack reach (at most {reach} "
            f"bytes above the callee's entry SP), none reaching a pointer-bearing word; stack "
            f"addresses left in argument registers the callee never reads: {dead or 'none'}")
    if found["unwalked"]:
        sites = ", ".join(f"0x{site:08X}" for site in found["unwalked"])
        line += (f"; calls this analysis did not walk ({sites}): their results are trusted, as the "
                 f"core trusts every callee it does not walk, to hold no address into this frame")
    if found["premise"] is not None:
        line += f"; {found['premise']}"
    return [line]
