"""Callees that use R4-R11 while the caller keeps a stack address there (kit #350).

The buffer walks hand a callee only the caller's aliases in R0-R3, R12 and LR, and the
stack-index analysis carries R4-R11 across a call unchanged.  "Callee-saved" obliges a
callee to restore those registers, not to leave their values unused, so a callee that
reads one can store through the caller's frame, hand the address back, or branch on it.
``Checker.call`` proves, for a call made while registers in R4-R11 hold an owner stack
address (exact or ranged), that no bit depending on those values reaches a use anywhere
in what the call executes, and that the callee returns them unchanged.

The walk is interprocedural and follows one frame model:

* SP is an exact byte offset from the SP at the checked call.  Every value derived from SP
  is a frame address, never an unknown scalar:
  * exact (``("F", offset)``), one of a few exact ones, or one of a proved range
    (``("FR", lo, hi, step)``: an index whose unsigned range a mask, a narrow load, a compare
    or a loop bound proves);
  * a stack array base plus or minus an unknown index: somewhere in the frame it was taken
    from (``("FW", lo, hi)``, the span of one function's frame, or of several);
  * after any other arithmetic, rebuilt from stored bytes, or read from a stale word: of
    unknown provenance (``FV``).  An access through one refuses.
  A result that cannot be a frame address (below ``RAM_BASE``, or an arithmetic shift
  right by 7 or more) is bits of one (``FS``): tracked, so that shifting it back into the
  high bits makes it ``FV`` again, but no address; a difference of two frame addresses is
  one too.  A narrow store over a word holding an address leaves its other bytes marked
  (``("FB", mask)``).  Storing an address outside the walked frames is premised per site
  (``ESCAPE_PREMISE``).
* The memory below SP keeps the words a walked callee leaves there, so a later one reads
  them.  A word below the checked call's SP that the walk has not written is ``STALE``:
  whatever earlier code left there, perhaps any frame address.  After code that is not
  walked in context (a summarised, unresolved or skipped callee, or a SWI) every word
  below SP is stale again.
* Code that is not walked, given frame addresses (in R0-R3, R12 or its stack-argument
  words), may write any word of their frames that no push wrote, and any object it finds
  addressed there, with a plain value or any of those addresses, and may hand one back in
  R0-R3 or R12 (``released``), the exact addresses it was given among them.  What it might
  copy or build from a stale word, part of an address or an address of unknown provenance is
  premised per site (``STALE_PREMISE``).
* An access at an unknown frame offset is taken to stay inside its stack array
  (``INDEX_PREMISE``): it reaches only live words of the frame the address was taken from
  that no push wrote.  A load returns any of them, and a store may change any of them.  Each
  site where an excluded word matters is recorded.  An index whose unsigned range is proved
  needs no premise: every word it may reach is checked.
* A nested callee runs in the caller's context: the same frame, registers and flags, with
  LR a return token, so its stack arguments and anything it reads above its entry SP are
  the caller's tracked words.  Its returns continue the caller.  A callee reached while a
  register or the flags depend on a watched value is always walked.  One reached while
  only frame words do is skipped with its summary (``isolation``) when that shows the call
  cannot matter.  The summary is probed once with symbolic inputs and lists every access
  through them, what it returns, and the unresolved calls, SWIs, indexed accesses into its
  own frame and stale reaches it makes, as templates stated against the caller's values
  where it is used.  A callee whose unresolved call's function pointer is known at the
  call site is walked instead.
* A data-processing instruction passes the dependence on bit by bit:
  * AND, ORR and BIC with a known constant fix the bits the constant decides;
  * a shift by a known amount moves the dependent bits, ASR filling from a dependent sign;
  * sums, differences and NEG carry them upwards; MVN keeps them;
  * a product, a rotate, or a shift by an unknown amount depends on every dependent bit.
* The condition flags are tracked per flag.  N and Z follow the result.  C is the shifter's
  carry-out, which an unknown shift amount may leave as it was.  Arithmetic and CMP/CMN set
  all four from the operands, TST only N and Z.  A skipped or unresolved call and a SWI
  leave the flags as they were.  A compare of known constants decides the branch on it.
* A use is a dependent bit reaching any of these, and each refuses:
  * a load or store address or index, or the bits a store writes outside the walked frames;
  * a comparison, a conditional branch on dependent flags, or a carry into ADC or SBC;
  * a SWI argument in R0-R3, or a branch target;
  * an unresolved callee in R0-R3 or R12.
* At the checked callee's return each watched register must hold its own value again, and
  no other callee-saved register may hold a dependent value or a frame address.  A
  dependent value left in R0-R3 or R12 is handed back, and so is a frame address, as
  ``DEAD``.  The caller's code after the call (``continuation``) is then walked the same
  way, and it must not use either (a ``DEAD`` address may be compared).  agbcc's high-register epilogue
  `pop {r3, ...}; mov r8, r3` leaves such a copy in R3.
* Anything the walk cannot model refuses:
  * control that leaves an indexed span, or code that is not ARMv4T Thumb;
  * a computed branch that is not a recognised word switch;
  * an SP write other than a known constant adjustment;
  * an access through a frame address of unknown provenance;
  * recursion deeper than ``MAX_DEPTH`` that no summary covers.
  A call is taken not to return only if its callee provably never does.

A call through a ``_call_via_rN`` thunk, or to any other aligned Thumb halfword that is exactly
``bx r3`` (MPlayMain's tail at 0x08144D84), is walked at its destination when rN is known:
from a literal, a word read from ROM at a known address, or another thunk.  Values are
tracked through walked code and summarised callees that preserve them, never across other
calls.  When the destination is unknown or outside ROM, nothing in R0-R3 or R12 may depend
on a watched value or address a word that does.  The call is then admitted under
``PREMISE``, and the registers and frame words it relies on are recorded for one report
line per site (``premise_lines``).  A SWI made while anything depends on a watched value
is admitted under ``BIOS_PREMISE`` the same way.
"""

import struct
import weakref

from capstone import CS_ARCH_ARM, CS_GRP_INT, CS_GRP_JUMP, CS_MODE_THUMB, Cs
from capstone import arm as _arm
from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG

import armv4t
import match
import rom_mirror

PREMISE = ("unproved premise: code reached through an unresolved function pointer, or outside ROM, "
           "uses the values those registers hold on entry only to save and restore them, neither reads "
           "nor writes those frame words, and returns no address into the caller's frame except within "
           "the objects it is given")
BIOS_PREMISE = ("unproved premise: the BIOS uses the values those registers hold on entry only to save and "
                "restore them, neither reads nor writes those frame words, and returns no address into the "
                "caller's frame except within the objects it is given")
# The SWIs the decomp's reports reach, with the GBATEK-documented writes of each routine.  At one of
# these, what the routine stores into the objects it is given is premised as documented (stated at
# every site given frame addresses); any other SWI may store any address it is handed.
BIOS_WRITES = {
    0x06: ("Div", "none"), 0x08: ("Sqrt", "none"), 0x0A: ("ArcTan2", "none"),
    0x0B: ("CpuSet", "copies"), 0x0C: ("CpuFastSet", "copies"),
    0x0E: ("BgAffineSet", "computes"), 0x0F: ("ObjAffineSet", "computes"),
}
BIOS_WRITES_CLAUSE = {
    "none": "stores nothing to memory",
    "copies": "stores into the objects it is given only data it copies from them",
    "computes": "stores into the objects it is given only numbers it computes",
}


# Indexed accesses whose INDEX premise holds only because the game never reaches some state (a
# game-state invariant, not analysis precision), with the invariant, checked on the decomp side.
GAME_STATE_INVARIANTS = {
    0x0809AC22: "the battle has at most 13 registered units (a design limit the scene and script data keep; "
                "not enforced by code)",
}


def bios_premise(number):
    """The premise of a SWI line: ``BIOS_PREMISE``, with what an enumerated routine stores."""
    if number not in BIOS_WRITES:
        return BIOS_PREMISE
    return BIOS_PREMISE.replace(", and returns", f", {BIOS_WRITES_CLAUSE[BIOS_WRITES[number][1]]}, and returns")
R12_PREMISE = "does not branch to the address R12 holds"
INDEX_PREMISE = ("unproved premise: an access through a variable index or pointer into a stack array stays "
                 "inside that array, so it reaches no saved register, return address, word below SP or "
                 "word of another function's frame")
STALE_PREMISE = ("unproved premise: those words hold no frame address that earlier code left there, and "
                 "code that is not walked neither copies nor builds an address from part of a frame address "
                 "or from an address of unknown provenance")
ESCAPE_PREMISE = ("unproved premise: code that loads that address back while its frame is live uses it only "
                  "inside the object it addresses, so it reaches no saved register, return address or word that "
                  "depends on an owner stack address")
READ_PREMISE = ("unproved premise: the bytes read there are plain data, no part of a frame address (the "
                "buffer was filled before)")
REBUILT_PREMISE = "unproved premise: that store missed them, so they hold the whole address used here"
BITS_PREMISE = "unproved premise: no code rebuilds an address from those bits"
UNSET_PREMISE = "unproved premise: it reads no frame address that earlier code left there"
ARGS_PREMISE = ("unproved premise: the callee's stack arguments cover these words, and its caller does not "
                "read them after the call")
DANGLING_FACT = "the address dangles: the escape premise covers only loads while the frame is live"
PREMISE_PREFIX = "* callee-saved premise:"   # not "* buffer": owner reports refuse those lines
FACT_PREFIX = "* callee-saved fact:"
LINE_PREFIX = "* callee-saved "              # the report lines ``premise_lines`` binds, both kinds
CALLEE_SAVED = frozenset(range(4, 12))
DEAD = 13                  # a frame address a walked callee returned in R0-R3 or R12
WATCHABLE = frozenset(range(0, 14))      # token values: the watched registers at the checked call, DEAD
RET = -1                   # the checked callee's entry LR
UNK = -2                   # a value with no tracked provenance
EMPTY = frozenset({UNK})   # tuples: ("P", r, mask) some bits of r; ("L", a) local return point;
FV = ("FV",)               # ("R", d) return to call depth d; ("F", o) frame address sp0+o
MAX_UPDATES = 200000
MAX_HELD_WORDS = 1000000   # frame words, over all the states one walk keeps: its memory bound
PROBE_BUDGET = 400000      # walk steps one check spends probing summaries before it walks instead
MAX_POINTS = 4             # exact offsets a joined value keeps before it widens
MAX_ROUNDS = 8             # recursion: rounds of a summary's fixpoint
MAX_DELTAS = 16            # recursion: exact offsets per summary input before they widen
MAX_DEPTH = 32
INF = 1 << 40              # frame spans: no bound
FS = ("FS",)               # bits of a frame address of unknown source; ("FS", t): bits of the frame
                           # address t (a byte or halfword of it, say): no address, but part of one
KBITS = -300               # constants[KBITS - n]: (zero, one), the bits of register n's value that
                           # are the same for every frame address, where the value derives from them
WIDE = -500                # constants[WIDE - n]: register n's range grew past what its paths give
                           # (widened to a threshold) and no comparison has bounded it since: an
                           # unknown index, not a proved one
PATHS = -600               # constants[PATHS - n]: (loop head, range or None) at a loop head: the
                           # join of the ranges of the paths that reached it, none widened (None
                           # once one was); see ``walk``
ORIGIN = -400              # constants[ORIGIN - n]: the frame addresses (and probed inputs) register
                           # n's address of unknown provenance was computed from: a finite tag that
                           # names the source of bits taken from it
FRAME_BITS = (0xFCFF8000, 0x03000000)   # a frame address lies in IWRAM 0x03000000-0x03007FFF
RAM_BASE = 0x02000000      # every frame address is at or above this
SFV = ("FV", "stale")      # what earlier code may have left in a word the walk has not written:
                           # FV, except where a word load reads nothing else (see ``unset``)
STALE = frozenset({SFV, -2})   # an unwritten word below the checked call's SP: whatever earlier
                                   # code left there, possibly any frame address
# Probing: ("E", mask) marks the bytes (mask over bytes 0-3) of a word of the probed callee's own
# frame that a path may not have written, so that they may still hold what its caller's walk had
# there, a watched value included: a word not written at all is ``EARLY``.  The summary does not
# know that, so a read of marked bytes is walked in context, or recorded as an "early" access
# checked where the summary is used; a store that may miss the word keeps its mark.
EARLY = STALE | frozenset({("E", 0xF)})
_ENGINE = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
_ENGINE.detail = True
_REGISTERS = None
ROOT, CONT, PROBE, KNOWN = "root", "continuation", "probe", "known"


class WatchRefusal(ValueError):
    pass


class _NotIsolated(Exception):
    pass


def refuse(target, message):
    raise WatchRefusal(f"callee 0x{target:08X}: {message}")


def register(operand):
    """R0-R15 as 0-15 for a capstone operand or register id; None for any other register."""
    global _REGISTERS
    if _REGISTERS is None:
        from capstone import arm
        _REGISTERS = {getattr(arm, f"ARM_REG_R{n}"): n for n in range(13)}
        _REGISTERS.update({arm.ARM_REG_SP: 13, arm.ARM_REG_LR: 14, arm.ARM_REG_PC: 15})
    return _REGISTERS.get(operand.reg if hasattr(operand, "reg") else operand)


FULL = 0xFFFFFFFF
STORED = {"str": FULL, "strh": 0xFFFF, "strb": 0xFF}    # the bits of the value a store writes
WIDTH = {"ldr": 4, "str": 4, "ldrh": 2, "strh": 2, "ldrsh": 2, "ldrb": 1, "strb": 1, "ldrsb": 1}
FLAGS = 16                         # regs[FLAGS]: the condition flags a watched value may have set
ALL_FLAGS = frozenset("NZCV")
CONDITION_FLAGS = {_arm.ARM_CC_EQ: "Z", _arm.ARM_CC_NE: "Z", _arm.ARM_CC_HS: "C", _arm.ARM_CC_LO: "C",
                   _arm.ARM_CC_MI: "N", _arm.ARM_CC_PL: "N", _arm.ARM_CC_VS: "V", _arm.ARM_CC_VC: "V",
                   _arm.ARM_CC_HI: "CZ", _arm.ARM_CC_LS: "CZ", _arm.ARM_CC_GE: "NV", _arm.ARM_CC_LT: "NV",
                   _arm.ARM_CC_GT: "NZV", _arm.ARM_CC_LE: "NZV"}
ALU = {"ands": "and", "orrs": "orr", "eors": "eor", "bics": "bic", "mvns": "mvn", "lsls": "lsl",
       "lsrs": "lsr", "asrs": "asr", "rors": "ror", "adds": "add", "subs": "sub", "adcs": "adc",
       "sbcs": "sbc", "negs": "neg", "rsbs": "neg", "muls": "mul", "add": "add"}


KNOWN_FLAGS = -1           # constants[KNOWN_FLAGS]: NZCV (N=8, Z=4, C=2, V=1) after a compare of constants
COMPARED = -3              # constants[COMPARED]: (register, range of what it was compared with,
                           # whether that range is a proved one)
SAVED = 1 << 42            # constants[SAVED + o]: (constant, range, signed range) of the register
                           # a push or word store wrote to frame word o, while nothing else wrote it
RANGES = -100              # constants[RANGES - n]: the unsigned range of plain-number register n
SIGNED = -200              # constants[SIGNED - n]: its signed range (lo, hi), where one is known
MAX_RANGE = 256            # a frame address plus a proved index spans at most this many bytes
PRESERVE_FLAGS = frozenset({"push", "pop", "ldm", "stm", "b", "bl", "bx", "mov", "add", "sub", "adr", "nop"})


CONDITION_CODES = {_arm.ARM_CC_EQ: 0, _arm.ARM_CC_NE: 1, _arm.ARM_CC_HS: 2, _arm.ARM_CC_LO: 3, _arm.ARM_CC_MI: 4,
                   _arm.ARM_CC_PL: 5, _arm.ARM_CC_VS: 6, _arm.ARM_CC_VC: 7, _arm.ARM_CC_HI: 8, _arm.ARM_CC_LS: 9,
                   _arm.ARM_CC_GE: 10, _arm.ARM_CC_LT: 11, _arm.ARM_CC_GT: 12, _arm.ARM_CC_LE: 13}


def condition(cc, flags):
    """Whether condition ``cc`` holds for NZCV ``flags``."""
    n, z, c, v = (bool(flags & bit) for bit in (8, 4, 2, 1))
    return {_arm.ARM_CC_EQ: z, _arm.ARM_CC_NE: not z, _arm.ARM_CC_HS: c, _arm.ARM_CC_LO: not c,
            _arm.ARM_CC_MI: n, _arm.ARM_CC_PL: not n, _arm.ARM_CC_VS: v, _arm.ARM_CC_VC: not v,
            _arm.ARM_CC_HI: c and not z, _arm.ARM_CC_LS: not c or z, _arm.ARM_CC_GE: n == v,
            _arm.ARM_CC_LT: n != v, _arm.ARM_CC_GT: not z and n == v, _arm.ARM_CC_LE: z or n != v}[cc]


def compared(mnemonic, a, b):
    """NZCV after ``cmp a, b`` or ``cmn a, b`` of known 32-bit values."""
    if mnemonic == "cmp":
        result, carry = (a - b) & FULL, a >= b
        overflow = (a ^ b) & (a ^ result)
    else:
        total = a + b
        result, carry = total & FULL, total > FULL
        overflow = ~(a ^ b) & (a ^ result)
    return (result >> 31) << 3 | (result == 0) << 2 | carry << 1 | (overflow >> 31 & 1)


def collapsed(templates):
    """Premised sites of a summary, one per site: a site reached at several SPs (recursion, or
    call paths of different depth) keeps the highest, its shallowest execution, and its kind
    gains "+".  The frame words it relies on are named from that SP, and its line claims every
    word of the stack between each execution's SP and the summarised callee's entry too
    (``recursion_text``).  A union over the SPs would not converge: each recursion level names
    the frames of the levels above it a frame further from its own SP, one more each round."""
    groups = {}
    for template in templates:
        # An indexed access's excluded words, and the values and frame words an unresolved
        # call or SWI is given, are grouped by site alone: at several SPs it keeps those of its
        # shallowest call (deeper levels repeat them further from that SP).
        cut = 4 if template[0].startswith(("index", "swi")) else 5 if template[0].startswith("call") else -1
        groups.setdefault((template[0].rstrip("+"),) + template[1:cut], []).append(template)
    out = set()
    for head, members in groups.items():
        if len(members) == 1:
            out.add(members[0])
            continue
        at = max(member[-1] for member in members)
        if not head[0].startswith(("index", "call", "swi")):
            out.add((head[0] + "+",) + head[1:] + (at,))
            continue
        held = {}
        for member in members:
            for off, value in member[-2]:
                # Frame words, named from the SP, only from the shallowest call; the registers a
                # call or SWI is given, from every depth (a deeper level may hold another one).
                if member[-1] == at or not head[0].startswith("index") and isinstance(off, int):
                    held[off] = held.get(off, frozenset()) | value
        recursive = len({member[-1] for member in members}) > 1 or any(member[0].endswith("+") for member in members)
        out.add((head[0] + ("+" if recursive else ""),) + head[1:] +
                (tuple(sorted(held.items(), key=lambda item: repr(item[0]))), at))
    return frozenset(out)


def template_site(template):
    """The (function, site) of a premised site's template or record."""
    return tuple(template[1:3])


RELEASED = ("FW", -INF, 0)   # anywhere in a probed callee's own frame, released at its return


def covers(wide, value):
    """Whether every token of ``value`` is in ``wide``, an input at an exact offset being
    covered by the same input at an unknown one, and an address of the callee's own frame by
    ``RELEASED``."""
    return all(token in wide or type(token) is tuple and token[0] == "A" and ("AV", token[1]) in wide or
               RELEASED in wide and is_frame(token) and not is_vague(token) or
               released_frames(frozenset({token})) <= wide for token in value)


def released_frames(value):
    """A recursive summary's value with every address of the callee's own frames made
    ``RELEASED``, and every return address of its nested calls ``RET``: each recursion level
    has its own, and the summary must reach a fixpoint."""
    if not any(is_frame(token) and not is_vague(token) or type(token) is tuple and token[0] in ("R", "FL", "FX", "FU")
               or is_fs(token) and len(token) > 1 for token in value):
        return value
    return frozenset(RELEASED if is_frame(token) and not is_vague(token) else
                     RET if type(token) is tuple and token[0] == "R" else
                     token[:4] + (0,) if type(token) is tuple and token[0] in ("FL", "FX", "FU") else
                     bits_of(RELEASED) if is_fs(token) and len(token) > 1 else token
                     for token in value)


def released_template(template):
    """A premised site of a recursive summary with its values' frame addresses ``RELEASED``."""
    if template[0].startswith(("call", "swi", "index")):
        values = tuple((key, released_frames(value)) for key, value in template[-2])
        return template[:-2] + (tuple(sorted(values, key=repr)),) + template[-1:]
    return template


def widened(accesses):
    """Accesses with an input reached at more than MAX_DELTAS offsets made vague, so a
    recursion that walks a pointer reaches a fixpoint."""
    counts = {}
    for kind, key, delta, width in accesses:
        if kind != "compared":
            counts[key] = counts.get(key, 0) + 1
    return frozenset((kind, key, None if counts.get(key, 0) > MAX_DELTAS and key != "sp" else delta, width)
                     for kind, key, delta, width in accesses)


def frame_spans(ctx, bottomless):
    """The frame-offset span [lo, hi) of each function on the walked call chain, owner first:
    a function's frame lies between its entry SP and the SP at the call it is making (the
    deepest one has no lower bound)."""
    tops = [0] + [level[2] for level in ctx]
    spans = [] if bottomless else [(0, INF)]
    for depth, top in enumerate(tops):
        spans.append((tops[depth + 1] if depth + 1 < len(tops) else -INF,
                      INF if bottomless and depth == 0 else top))
    return tuple(spans)


def frame_of(spans, offset):
    for lo, hi in spans or ():
        if lo <= offset < hi:
            return lo, hi
    return -INF, INF


def extent(token, spans):
    """The frame span [lo, hi) an address token lies in."""
    if token[0] == "FW":
        return token[1], token[2]
    if is_vague(token) or spans is None:
        return -INF, INF
    low = frame_of(spans, token[1])
    high = frame_of(spans, token[2] if token[0] == "FR" else token[1])
    return min(low[0], high[0]), max(low[1], high[1])


def somewhere(lo, hi):
    """A stack array address somewhere in the frame span [lo, hi) (perhaps every frame)."""
    return ("FW", lo, hi)


def bounded(value, spans=None):
    """A joined value with more than MAX_POINTS exact or ranged frame addresses, or offsets of
    one input, made vague (somewhere in their frames), so a loop that walks a pointer reaches
    a fixpoint."""
    exact = [token for token in value if type(token) is tuple and token[0] in ("F", "FR")]
    keys = {}
    for token in value:
        if type(token) is tuple and token[0] == "A":
            keys.setdefault(token[1], []).append(token)
    if len(exact) <= MAX_POINTS and all(len(tokens) <= MAX_POINTS for tokens in keys.values()):
        return value
    out = set(value)
    if len(exact) > MAX_POINTS:
        out.difference_update(exact)
        found = [extent(token, spans) for token in exact]
        out.add(somewhere(min(lo for lo, _ in found), max(hi for _, hi in found)))
    for key, tokens in keys.items():
        if len(tokens) > MAX_POINTS:
            out.difference_update(tokens)
            out.add(("AV", key))
    return frozenset(out)


def joined_value(a, b):
    """Two paths' values joined.  An exact or ranged frame address that only one side holds,
    and that the other side's somewhere-in-the-frame address (``FW``) covers, is dropped: a
    pointer walk widened on one path takes the exact steps of the other with it (accesses
    through them stay premised).  Exact addresses held together with ``FW`` on one side (code
    that is not walked hands back both) stay exact."""
    out = set(a | b)
    for side, other in ((a, b), (b, a)):
        covers = [token for token in other if type(token) is tuple and token[0] == "FW"]
        for token in side:
            if covers and type(token) is tuple and token[0] in ("F", "FR") and token not in other and \
                    any(lo <= min(offsets(token)) and max(offsets(token)) < hi for _, lo, hi in covers):
                out.discard(token)
    return normal(frozenset(out))


def numeric(value):
    """Whether a value is a number whose range the walk may keep: no frame address, and no
    probed input but one proved below RAM_BASE (bits of it)."""
    return all(type(token) is tuple and token[0] == "AF" and token[2] for token in pointers(value))


def is_vague(token):
    """An address of unknown provenance: FV, or SFV (what earlier code may have left)."""
    return type(token) is tuple and token[0] == "FV"


def vague_in(value):
    return any(is_vague(token) for token in value)


def is_partial(token):
    return type(token) is tuple and token[0] == "P"


def is_frame(token):
    """("F", o) exact; ("FR", lo, hi, m) one of lo, lo + 2**m, ..., hi (a proved index range);
    ("FW", lo, hi) somewhere in the frame span [lo, hi); FV anywhere in the walked frames."""
    return type(token) is tuple and token[0] in ("F", "FR", "FW", "FV")


def offsets(token):
    """The frame offsets an exact or ranged frame token may be."""
    if token[0] == "F":
        return [token[1]]
    return list(range(token[1], token[2] + 1, 1 << token[3] if token[3] < 32 else 1))


def frames(value):
    return frozenset(token for token in value if is_frame(token))


def is_argument(token):
    """("A", key, delta): an input of a probed callee plus ``delta`` (key R0-R12, or ("s", off)
    for the stack word at entry SP + off); ("AV", key): that input plus an unknown offset;
    ("AF", key, small): other arithmetic on it (at the call site: ``FS`` if ``small``, else an
    address of unknown provenance, where the input is a frame address)."""
    return type(token) is tuple and token[0] in ("A", "AV", "AF")


def pointers(value):
    """The tokens of a value that are, or may be, addresses the walk tracks."""
    return frozenset(token for token in value if is_frame(token) or is_argument(token))


def moved(token, amount):
    """A pointer token plus a known ``amount``."""
    if token[0] == "F":
        return ("F", token[1] + amount)
    if token[0] == "FR":
        return ("FR", token[1] + amount, token[2] + amount, token[3])
    if token[0] == "A":
        return ("A", token[1], token[2] + amount)
    return token


def is_fs(token):
    """Bits of a frame address (``FS``, or ("FS", source))."""
    return type(token) is tuple and token[0] == "FS"


def bits(value):
    """The tokens of a value that are bits of a frame address: ``FS``, or ("FL", ...) bits read
    from words that may hold plain data instead."""
    return frozenset(token for token in value if type(token) is tuple and token[0] in ("FS", "FL"))


def bits_of(token):
    """Bits of the frame address ``token``: ("FS", token), or ``FS`` where it has no known source."""
    if is_fs(token):
        return token
    return ("FS", token) if is_frame(token) and not is_vague(token) else FS


def known_constant(c):
    """Known bits (zero, one) of a constant."""
    c &= FULL
    return FULL ^ c, c


def known_frame(value):
    """Known bits of a value that holds only frame addresses: the IWRAM page, and for exact
    addresses the word offset (the SP at the checked call is word aligned); None otherwise."""
    if not value or any(not (type(token) is tuple and token[0] in ("F", "FR", "FW")) for token in value):
        return None
    zero, one = FRAME_BITS
    lows = {token[1] & 3 if token[0] == "F" else None for token in value}
    if len(lows) == 1 and None not in lows:
        low, = lows
        zero, one = zero | (3 & ~low), one | low
    return zero, one


def known_add(a, b, carry_zero=True, carry_one=False):
    """Known bits of a + b + carry (as LLVM's KnownBits::computeForAddCarry)."""
    sum_zero = ((FULL ^ a[0]) + (FULL ^ b[0]) + (0 if carry_zero else 1)) & FULL
    sum_one = (a[1] + b[1] + (1 if carry_one else 0)) & FULL
    carry_known = (FULL ^ (sum_zero ^ a[0] ^ b[0])) | ((sum_one ^ a[1] ^ b[1]) & FULL)
    known = (a[0] | a[1]) & (b[0] | b[1]) & carry_known & FULL
    return (FULL ^ sum_zero) & known, sum_one & known


def known_op(name, a, b, amount):
    """Known bits of a Thumb data-processing result, from its operands' (``amount``: a constant
    shift amount, or None)."""
    def shifted(k, left, n, fill_zero, fill_one):
        if left:
            return ((k[0] << n) | ((1 << n) - 1)) & FULL, (k[1] << n) & FULL
        high = FULL ^ (FULL >> n)
        return (k[0] >> n) | (high if fill_zero else 0), (k[1] >> n) | (high if fill_one else 0)
    if name == "and":
        return a[0] | b[0], a[1] & b[1]
    if name == "orr":
        return a[0] & b[0], a[1] | b[1]
    if name == "bic":
        return a[0] | b[1], a[1] & b[0]
    if name == "eor":
        known = (a[0] | a[1]) & (b[0] | b[1])
        value = (a[1] ^ b[1]) & known
        return known & ~value & FULL, value
    if name == "mvn":
        return a[1], a[0]
    if name == "neg":
        return known_add(known_constant(0), (a[1], a[0]), False, True)
    if name == "add":
        return known_add(a, b)
    if name == "sub":
        return known_add(a, (b[1], b[0]), False, True)
    if name in ("lsl", "lsr", "asr") and amount is not None:
        n = amount & 0xFF
        if n == 0:
            return a
        if n >= 32:
            if name != "asr":
                return FULL, 0
            n = 31
        sign_zero, sign_one = bool(a[0] >> 31 & 1), bool(a[1] >> 31 & 1)
        return shifted(a, name == "lsl", n, name == "lsr" or name == "asr" and sign_zero,
                       name == "asr" and sign_one)
    if (a[0] | a[1]) == FULL and (b[0] | b[1]) == FULL and name == "mul":
        return known_constant(a[1] * b[1])
    return 0, 0


def lifted(value):
    """("FX", ...) tokens: an address rebuilt from bits read where plain data may have been
    (``READ_PREMISE`` makes it plain, stated where it is used as an address); ("FU", ...): a
    word read where only what earlier code left may be (``UNSET_PREMISE``, the same)."""
    return frozenset(token for token in value if type(token) is tuple and token[0] in ("FX", "FU"))


def unknown_of(value, small):
    """Arithmetic other than adding an index on ``value``: bits of a frame address (``FS``) where
    the result is proved below RAM_BASE (``small``), else an address of unknown provenance; an
    input of a probed callee becomes ("AF", key, small)."""
    out = set()
    for token in value:
        if is_argument(token):
            out.add(("AF", token[1], small))
        elif is_frame(token) or is_fs(token):
            out.add(bits_of(token) if small else FV)
        elif type(token) is tuple and token[0] == "FL":
            out.add(token if small else ("FX",) + token[1:])
        elif type(token) is tuple and token[0] in ("FX", "FU"):
            out.add(token)
    return frozenset(out) | EMPTY


def rebased(token, amount):
    """A frame token of a frame whose offsets are ``amount`` lower here (a callee's own frame
    seen from its caller)."""
    if token[0] == "FW":
        return ("FW", token[1] + amount if token[1] > -INF else -INF, token[2] + amount if token[2] < INF else INF)
    return moved(token, amount)


def vague(token, spans=None):
    """A pointer token plus an unknown amount: under ``INDEX_PREMISE`` it stays in its frame."""
    if is_vague(token):
        return FV                       # an index does not give an address a provenance
    if is_frame(token):
        return somewhere(*extent(token, spans))
    return token if token[0] == "AF" else ("AV", token[1])


def fragment(value):
    """The bytes of a stack word (mask over bytes 0-3) that may hold part of a frame address:
    ("FB", mask) tokens are what a narrow store leaves of one."""
    mask = 0xF if frames(value) or bits(value) else 0
    for token in value:
        if type(token) is tuple and token[0] == "FB":
            mask |= token[1]
    return mask


def watched_tokens(value):
    return frozenset(token[1] if is_partial(token) else token for token in value
                     if token in WATCHABLE or is_partial(token))


def taints(value):
    """{watched register: mask of the bits of ``value`` that may depend on it}."""
    masks = {}
    for token in value:
        if is_partial(token):
            masks[token[1]] = masks.get(token[1], 0) | token[2]
        elif token in WATCHABLE:
            masks[token] = FULL
    return masks


def tainted(masks, rest=EMPTY):
    """The value whose bits depend on watched registers as ``masks`` says: the plain register
    token for a full mask, ("P", register, mask) for some bits; ``rest`` when no bit does."""
    tokens = frozenset(number if mask & FULL == FULL else ("P", number, mask & FULL)
                       for number, mask in masks.items() if mask & FULL)
    return tokens or rest


def normal(value):
    """One token per watched register, and one early mark, so joins of partial masks stay bounded."""
    partial = marks = 0
    for token in value:
        if type(token) is tuple:
            if token[0] == "P":
                partial = 1
            elif token[0] == "E":
                marks += 1
    if not partial and marks < 2:
        return value
    if marks > 1:
        value = frozenset(token for token in value if not is_early(token)) | marked(early(value))
    if not partial:
        return value
    return frozenset(token for token in value if not is_partial(token) and token not in WATCHABLE) | \
        tainted(taints(value), frozenset())


def is_early(token):
    return type(token) is tuple and token[0] == "E"


def early(value):
    """The bytes of a probed callee's frame word that may still hold what its caller had there."""
    mask = 0
    for token in value:
        if type(token) is tuple and token[0] == "E":
            mask |= token[1]
    return mask


def marked(mask):
    """The early mark of ``mask``'s bytes (nothing for none)."""
    return frozenset({("E", mask & 0xF)}) if mask & 0xF else frozenset()


def without_early(value):
    return frozenset(token for token in value if not is_early(token)) if early(value) else value


def settled(word, width):
    """Whether a frame word holds no more than what a summary assumed where it read the word as
    what earlier code may have left (``STALE``): no watched value, and for a whole word no address
    but one of unknown provenance; for bytes, only bytes that may be plain data (as for a load
    through an input)."""
    if taints(word):
        return False
    if width < 4:
        return not (live(word) or bits(word) or lifted(word)) or UNK in word
    return not (live(word - {SFV}) or lifted(word))


def lane_bytes(low, width):
    """The bytes of a word an access at byte ``low`` of ``width`` bytes covers, per word: [(0, mask)]
    or, straddling, [(0, mask), (4, mask)]."""
    if low + width <= 4:
        return [(0, ((1 << width) - 1) << low)]
    return [(0, (0xF << low) & 0xF), (4, (1 << (low + width - 4)) - 1)]


def merge(*maps):
    out = {}
    for masks in maps:
        for number, mask in masks.items():
            out[number] = out.get(number, 0) | mask
    return out


def upward(mask):
    """Bits a sum may change: every bit from the lowest dependent one up (carries)."""
    return FULL & ~((mask & -mask) - 1) if mask else 0


def live(value):
    """Whether a value depends on a watched value or is (part of) a frame address."""
    return bool(taints(value) or fragment(value) or any(is_argument(token) for token in value))


def span(rom, entries, target):
    """The callee's indexed bytes, as BufferCallProof.span requires them."""
    rows = [entry for entry in entries if isinstance(entry, dict) and isinstance(entry.get("rom"), str)
            and int(entry["rom"], 16) & ~1 == target & ~1]
    if target % 2 or len(rows) != 1 or rows[0].get("mode") != "thumb" or int(rows[0]["rom"], 16) != target:
        refuse(target, "watched registers reach a call target that is not unique aligned Thumb code")
    end = int(rows[0]["end"], 16)
    if end % 2 or not target < end <= match.ROM_BASE + len(rom):
        refuse(target, "watched registers reach a callee without a complete mapped span")
    for other in entries:
        if other is not rows[0] and int(other["rom"], 16) < end and int(other["end"], 16) > target:
            refuse(target, "watched registers reach a callee whose mapping overlaps another span")
    return rom[target - match.ROM_BASE:end - match.ROM_BASE], end


BX_R3 = 0x4718


def link_register(link):
    """The register a call-via ``link`` (``Checker.chain``) branches to."""
    return link if link < 16 else 3


def chain_registers(links):
    return {link_register(link) for link in links}


class Checker:
    """The callee-saved check of one verification, memoised per call shape."""

    def __init__(self, rom, entries):
        self.rom, self.entries = rom, entries
        self.results = {}          # (target, watched, arguments) -> (copies, exit flags)
        self.continued = set()     # continuations already proved
        self.premises = set()      # see premise_lines
        self.mended = set()        # (function, site) of word loads whose ("FX", ...) is REBUILT_PREMISE's
        self.isolated = {}         # target -> (reach, may return), see isolation
        self.isolation_log = []    # probed targets, in the order their probes ended
        self.probing = {}          # targets being probed -> the summary assumed for recursive calls
        self.assumed = set()       # targets whose assumed summary a recursive call used
        self.probes = {}           # (function, site) -> constants known there
        self.spans = {}
        # iwram_image_profile: (bytes, end) for a boot IWRAM image address the buffer proof's
        # call-via resolver answered, else None (set by checker_for).
        self.image_span = None
        # iwram_image_profile: an exact odd value in the boot IWRAM image as a call-via destination,
        # (value, site) -> the routine's address or None (set by attach_image).
        self.image_target = None
        self.limits = {}
        self.leaves = {}
        self.heads = {}
        # Where a walk may skip a callee with its summary: (callee, the functions on the walked
        # chain) -> bool; None everywhere.  The summary test walks recursion only with them.
        self.summarised = None
        self.probe_work = 0
        # A site stated at several depths ("+"): (function, site) -> the callees whose summaries,
        # applied in the walk, state it there (``collapsed``), and -> the recursive functions
        # whose summaries reach it at every depth; the frame each probed function sets up.
        self.recursion = {}
        self.recursive = {}
        self.frames = {}
        # Test-only: a list that collects (record, SP at its site, [(function, entry SP), ...] of
        # the walked chain) for every premise of a walk in context.  None (the default) records
        # nothing and changes nothing.
        self.trace = None
        self._now = None
        self._applying = None

    def state(self, record, at, applied=False):
        """Add a premise whose frame words are offsets from the SP ``at``: for the test trace
        (``trace``), recorded at that SP (and, ``applied``, inside the summarised callee being
        applied).  Without the trace, a plain add."""
        if self.trace is None:
            self.premises.add(record)
            return
        now = self._now
        self._now = (at, now[1] + ((self._applying,) if applied and self._applying else ()))
        try:
            self.premises.add(record)
        finally:
            self._now = now

    def span(self, target):
        if target not in self.spans:
            image = self.image_span(target) if self.image_span is not None else None
            self.spans[target] = image if image is not None else span(self.rom, self.entries, target)
        return self.spans[target]

    def loop_heads(self, function):
        """The targets of backward branches in ``function``'s span: where its loops start."""
        if function not in self.heads:
            self.heads[function] = frozenset(
                instruction.operands[0].imm for instruction in self.instructions(function)
                if instruction.mnemonic.startswith("b") and instruction.mnemonic not in ("bl", "blx", "bx") and
                instruction.operands and instruction.operands[0].type == ARM_OP_IMM and
                instruction.operands[0].imm <= instruction.address)
        return self.heads[function]

    def instructions(self, function):
        """The instructions of ``function``'s span, stepping over what does not decode (its
        literal pools)."""
        data, _ = self.span(function)
        offset = 0
        while offset + 2 <= len(data):
            instruction = next(_ENGINE.disasm(data[offset:offset + 4], function + offset, 1), None)
            if instruction is None:
                offset += 2
                continue
            yield instruction
            offset += instruction.size

    def leaf(self, target):
        """Whether ``target`` is straight-line code that calls nothing: no BL and no backward
        branch in its span."""
        if target not in self.leaves:
            self.leaves[target] = not any(
                instruction.mnemonic == "bl" or instruction.mnemonic.startswith("b") and
                instruction.operands and instruction.operands[0].type == ARM_OP_IMM and
                instruction.operands[0].imm <= instruction.address
                for instruction in self.instructions(target))
        return self.leaves[target]

    def thresholds(self, function):
        """Widening thresholds for ranges in ``function``: the constants it compares with and
        loads, one either side, and the byte, halfword and word limits."""
        if function not in self.limits:
            data, _ = self.span(function)
            found = {0, 0xFF, 0xFFFF, FULL}
            for item in _ENGINE.disasm(data, function):
                if item.mnemonic.split(".")[0] in ("cmp", "movs", "mov") and item.operands and \
                        item.operands[-1].type == ARM_OP_IMM:
                    value = item.operands[-1].imm & FULL
                    found.update(value + delta for delta in (-1, 0, 1) if 0 <= value + delta <= FULL)
            self.limits[function] = sorted(found)
        return self.limits[function]

    def chain_thresholds(self, root, ctx):
        functions = (root,) + tuple(level[0] for level in ctx)
        if functions not in self.limits:
            self.limits[functions] = sorted(set().union(*(self.thresholds(function) for function in functions)))
        return self.limits[functions]

    # ---- entry points -------------------------------------------------------------------
    def call(self, target, watched, constants=None, *, caller=None, site=None, known=None):
        """Check a call at ``site`` in ``caller`` made while ``watched`` (registers in R4-R11)
        hold owner stack addresses, and the caller's code after it.  ``constants`` (tests
        only) adds register values known at the call.  ``known``, when given, is the caller's
        register values at the call ({number: value}) and replaces ``known_at`` for this call
        only (call_via_target_profile passes its strict values).  Returns the copies
        {R0-R3/R12: watched register} the callee hands back."""
        watched = frozenset(watched)
        if not watched <= CALLEE_SAVED:
            raise ValueError("only R4-R11 are watched across a call")
        if known is not None:
            known = dict(known)
        else:
            known = dict(self.known_at(caller, site)) if caller is not None and site is not None else {}
        known.update(constants or {})
        if not watched:
            return {}
        destination = self.resolve(target, known, watched, site=site)
        if destination is None:
            if caller is None or site is None:
                refuse(target, "an indirect call through a call-via thunk while watched values are live")
            self.premises.add(("call", caller, site, self.chain(target, known), self.destination(target, known),
                               tuple(sorted(watched)), (), False))
            return {}
        key = (destination, watched, self.arguments(known))
        if key not in self.results:
            regs = [EMPTY] * 16 + [frozenset()]
            for number in watched:
                regs[number] = frozenset({number})
            regs[14] = frozenset({RET})
            self.results[key] = self.run(destination, destination, ROOT, regs, dict(key[2]), watched)
        copies, flags = self.results[key]
        if caller is not None and site is not None and (copies or flags):
            self.continuation(caller, site + 4, copies, flags)
        return dict(copies)

    def continuation(self, function, site, copies, flags=frozenset()):
        """Prove that ``function``, from ``site`` on, never uses the values a callee handed back:
        ``copies`` maps R0-R3/R12 to the watched register each holds (a set of registers is
        taken as copies of themselves); ``flags`` are the flags left depending on them."""
        if not isinstance(copies, dict):
            copies = {number: number for number in copies}
        key = (function, site, tuple(sorted(copies.items())), frozenset(flags))
        if key in self.continued or not (copies or flags):
            return
        regs = [EMPTY] * 16 + [frozenset(flags)]
        for number, source in copies.items():
            regs[number] = frozenset({source})
        self.run(function, site, CONT, regs, {})
        self.continued.add(key)

    def known_at(self, function, site):
        """Register values this check's own walk knows at ``site`` in ``function``, with no value
        carried across a call ({} if it cannot walk it)."""
        key = (function, site)
        if key not in self.probes:
            try:
                self.probes[key] = self.run(function, function, KNOWN, [EMPTY] * 16 + [frozenset()], {},
                                            until=site)
            except (WatchRefusal, _NotIsolated):
                self.probes[key] = {}
        return self.probes[key]

    def isolation(self, target):
        """The summary (accesses, returns, may return, premised sites) of a callee, or None.

        The callee is probed with symbolic inputs: R0-R12 hold ("A", n, 0), and a word it
        reads at or above its entry SP is ("A", ("s", off), 0).  ``accesses`` lists every
        memory access made through an input as (kind, key, delta, width), delta None for an
        unknown offset.  The kinds are "load", "store", ("store", tokens) for a store of an
        input address, ("escape", tokens) for an input stored to memory the walk does not
        track, and "argument" for a word read above the entry SP (key "sp").  ``returns``
        gives what each of R0-R12 holds at the return, in those terms or as the callee's own
        frame addresses, ``left`` the words it leaves below its entry SP on every return, and
        ``definite`` the input words (key, offset) a full-word store writes on every path, and the
        input bytes (key, offset, "byte") a narrow store does, and ``clobbers`` the highest offset
        below which code it does not walk, or a recursion's deeper levels, may write words that
        ``left`` does not list (None where nothing does).
        The premised sites are its unresolved calls and SWIs, with the
        addresses they receive and the SP there.  There is no summary when it, or something
        it calls, accesses its own frame at an unknown offset, reads a stack word it has not
        written, stores its own frame address outside its frame, or does not restore SP.
        Callees it cannot summarise are walked inside the probe.  Recursion assumes the
        summary being computed and iterates until the assumption covers the result."""
        if target in self.isolated:
            return self.isolated[target]
        if self.probe_work > PROBE_BUDGET:
            return None
        if target in self.probing:
            self.assumed.add(target)
            return self.probing[target]
        # Assumed at a recursive call: it states nothing of the words its deeper levels leave below
        # its entry SP, so any may change (it clobbers below 0).
        assumed = (frozenset(), tuple(frozenset({("A", n, 0)}) if 4 <= n <= 11 else EMPTY for n in range(13)),
                   True, frozenset(), (), (), 0)
        mark = len(self.isolation_log)
        for _ in range(MAX_ROUNDS):
            self.probing[target] = assumed
            self.assumed.discard(target)
            try:
                regs = [frozenset({("A", n, 0)}) for n in range(13)] + [EMPTY, frozenset({RET}), EMPTY, frozenset()]
                result = self.run(target, target, PROBE, regs, {})
            except (WatchRefusal, _NotIsolated):
                result = None
            if result is not None:
                result = result[:3] + (collapsed(result[3]),) + result[4:]
                if target in self.assumed:                    # it recursed: its sites at every depth
                    for template in result[3]:
                        if template[0].endswith("+"):
                            self.recursive.setdefault(template_site(template), set()).add(target)
            if result is None or target not in self.assumed:
                break
            if all(access in assumed[0] or access[:2] + (None,) + access[3:] in assumed[0]
                   for access in result[0]) and \
                    all(covers(b, a) for a, b in zip(result[1], assumed[1])) and \
                    collapsed(frozenset(map(released_template, result[3])) | assumed[3]) == assumed[3]:
                # The assumption covers the result.  The words its first level leaves (the deeper
                # levels' are stale there, as the assumption has them) are the run's.
                result = assumed[:4] + (result[4], (), 0)
                break
            assumed = (widened(result[0] | assumed[0]),
                       tuple(released_frames(bounded(a | b)) for a, b in zip(result[1], assumed[1])),
                       True, collapsed(frozenset(map(released_template, result[3])) | assumed[3]), (), (), 0)
            for done in self.isolation_log[mark:]:       # they may rest on the old assumption
                self.isolated.pop(done, None)
            del self.isolation_log[mark:]
        else:
            result = None
        del self.probing[target]
        if result is None:                                # anything probed meanwhile may have
            for done in self.isolation_log[mark:]:       # assumed this callee summarised
                self.isolated.pop(done, None)
            del self.isolation_log[mark:]
        self.isolated[target] = result
        self.isolation_log.append(target)
        return result

    @staticmethod
    def arguments(constants):
        return tuple(sorted((number, value) for number, value in constants.items() if number in (0, 1, 2, 3, 12)))

    def bare_thunk(self, target):
        """Whether ``target`` is an aligned Thumb halfword that is exactly ``bx r3`` and no
        ``_call_via_rN`` runtime helper.  A BL there is a call through R3 with LR set, as one to
        ``_call_via_r3`` is: only that halfword runs, so the span the function index puts it in
        does not matter (0x08144D84 is the tail of MPlayMain, a real call target)."""
        offset = target - match.ROM_BASE
        return target not in match.RUNTIME_HELPERS.values() and not target % 2 and \
            0 <= offset and offset + 2 <= len(self.rom) and \
            struct.unpack_from("<H", self.rom, offset)[0] == BX_R3

    def chain(self, thunk, constants):
        """The thunks a call to ``thunk`` goes through, as ``link`` values: the register number
        of a ``_call_via_rN``, or the address of a bare ``bx r3``."""
        links = []
        while len(links) < 16:
            if thunk in match.RUNTIME_HELPERS.values():
                links.append((thunk - match.RUNTIME_HELPERS["_call_via_r0"]) // 4)
            elif self.bare_thunk(thunk):
                links.append(thunk)
            else:
                break
            thunk = constants.get(link_register(links[-1]), 0) & ~1
        return tuple(links)

    def destination(self, thunk, constants):
        links = self.chain(thunk, constants)
        return constants.get(link_register(links[-1])) if links else None

    def resolve(self, target, constants, watched, *, site=None):
        """The callee proper: the target itself or a call-via thunk's known ROM destination
        (followed through further thunks), or a routine of the boot IWRAM image the destination
        lies in (``image_target``, for a call at ``site``), else None: rN unknown, or other code
        outside ROM.  ``watched`` holds the registers whose values must not become a branch
        target."""
        seen = set()
        while target not in seen:
            if target in match.RUNTIME_HELPERS.values():
                number = (target - match.RUNTIME_HELPERS["_call_via_r0"]) // 4
                if not match.thunk_is_call_via(self.rom, target, number):
                    break
            elif self.bare_thunk(target):
                number = 3
            else:
                break
            seen.add(target)
            if number in watched:
                refuse(target, f"the call-via thunk branches to the watched R{number}")
            destination = constants.get(number)
            if destination is not None:
                destination = rom_mirror.canonical(destination)   # a wait-state mirror is ROM code (#377)
            if destination is None or not match.ROM_BASE <= destination < match.ROM_BASE + len(self.rom):
                if destination is not None and site is not None and self.image_target is not None:
                    return self.image_target(destination, site)      # walked over the image bytes
                return None
            if not destination & 1:
                refuse(target, f"the call-via thunk branches to 0x{destination:08X}, which is not Thumb code")
            target = destination & ~1
        return target

    # ---- the walk -----------------------------------------------------------------------
    def run(self, root, start, mode, regs, constants, watched=frozenset(), until=None):
        """Walk ``root`` from ``start``.  ROOT returns (copies, exit flags) of the checked
        callee; CONT returns None; PROBE returns the callee's summary (see ``isolation``);
        KNOWN returns the constants known at ``until``."""
        if self.trace is None:
            return self.walk(root, start, mode, regs, constants, watched, until)
        now = self._now                       # a nested walk returns to the caller's position
        try:
            return self.walk(root, start, mode, regs, constants, watched, until)
        finally:
            self._now = now

    def walk(self, root, start, mode, regs, constants, watched=frozenset(), until=None):
        """``run`` itself, in two passes where a loop needs them.  A range widened at a loop head
        is an unknown index (WIDE) until something proves it.  Where every path into the head
        but the widened one arrives bounded (a comparison cut the back edge, or the body set the
        register), the first pass records the join of those paths, and the walk is repeated with
        the head's range that join, proved, as long as every path stays inside it.  The first
        pass's premises are dropped: they rest on ranges the second pass proves."""
        caps = {}
        saved = (set(self.premises), set(self.mended), {key: set(value) for key, value in self.recursion.items()},
                 None if self.trace is None else len(self.trace))
        result = self.one_walk(root, start, mode, regs, constants, watched, until, caps, None)
        if not caps:
            return result
        self.premises.clear()
        self.premises.update(saved[0])
        self.mended.clear()
        self.mended.update(saved[1])
        self.recursion.clear()
        self.recursion.update(saved[2])
        if saved[3] is not None:
            del self.trace[saved[3]:]
        return self.one_walk(root, start, mode, regs, constants, watched, until, None, caps)

    def one_walk(self, root, start, mode, regs, constants, watched, until, head_joins, head_ranges):
        """One pass of ``walk``: ``head_joins`` collects (context, loop head, register) -> the
        join of the bounded paths into a head that widening marked WIDE; ``head_ranges`` is the
        first pass's record, the range taken at each such head while every path stays inside it."""
        bottomless = mode == CONT          # the owner's frame above the continuation is untracked
        states, pending = {}, []
        exits = {"copies": {}, "flags": frozenset(), "returns": False, "accesses": set(),
                 "registers": [frozenset()] * 13, "premises": set(), "left": None, "definite": None,
                 "arguments read": set(), "arguments written": [], "clobbers": None}

        def owner(ctx, off):
            """Whether a frame offset lies at or above the entry SP of the walked function,
            in the frame of whoever made the checked call (or, probing, of the caller)."""
            return not bottomless and off >= 0

        def enqueue(ctx, site, state):
            nonlocal updates, held_words
            key = (ctx, site)
            previous = states.get(key)
            if previous is None:
                merged = state
            else:
                if previous[2] != state[2]:
                    refuse(function_of(ctx), f"the stack depth differs at the join 0x{site:08X}")
                memory = dict(previous[1])
                spans = frame_spans(ctx, bottomless)

                def unwritten(off):
                    """A word one path has not written: stale below the checked call's SP (probing,
                    in the probed callee's own frame: what its caller had there, ``EARLY``)."""
                    return (EARLY if mode == PROBE else STALE) if off < 0 and mode in (ROOT, CONT, PROBE) \
                        else EMPTY
                for off, value in state[1]:
                    memory[off] = value if memory.get(off) == value else \
                        bounded(joined_value(memory.get(off, unwritten(off)), value), spans)
                for off in dict(previous[1]).keys() - dict(state[1]).keys():
                    memory[off] = normal(memory[off] | unwritten(off))
                if mode == PROBE:
                    for off in dict(previous[1]).keys() ^ dict(state[1]).keys():
                        if off >= 0:                   # above the entry SP, unwritten on one path: an input
                            memory.pop(off, None)
                merged = (tuple(a if a == b else bounded(joined_value(a, b), spans) for a, b in zip(previous[0], state[0])),
                          tuple(sorted(memory.items())), state[2],
                          joined(dict(previous[3]), dict(state[3]), ctx,
                                 site if site in self.loop_heads(function_of(ctx)) else None, previous[0], state[0]),
                          tuple(sorted(set(previous[4]) & set(state[4]))),
                          tuple(sorted(set(previous[5]) | set(state[5]), key=repr)),
                          tuple(sorted(set(previous[6]) & set(state[6]), key=repr)))
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:
                    refuse(root, "the callee-saved check exceeded its budget")
                if mode == PROBE:
                    self.probe_work += 1
                    if self.probe_work > PROBE_BUDGET:
                        raise _NotIsolated          # summaries are an optimisation: walk instead
                held_words += len(merged[1]) - (len(states[key][1]) if key in states else 0)
                if held_words > MAX_HELD_WORDS:          # the memory one walk may keep
                    if mode == PROBE:
                        raise _NotIsolated
                    refuse(root, "the callee-saved check exceeded its budget")
                states[key] = merged
                pending.append(key)

        def function_of(ctx):
            return ctx[-1][0] if ctx else root

        def joined(old, new, ctx, head=None, old_regs=None, new_regs=None):
            """Constants known on both paths; a register's two values or ranges become the
            range covering both, widened where it grew to the thresholds of every function on
            the call chain (a callee walked in its caller's loop keeps the caller's bound).
            ``head``: the loop head joined at, or None (see ``walk`` for its two passes)."""
            import stack_index_precondition_profile as bounds
            out = {key: value for key, value in old.items() if new.get(key) == value and
                   (key > RANGES or KBITS - 16 <= key <= KBITS)}
            if old_regs is not None:
                # The frame addresses an address of unknown provenance was computed from: those
                # of either path, where each path that holds one knows them.
                for number in range(13):
                    sides = [(items.get(ORIGIN - number), value) for items, value in
                             ((old, old_regs[number]), (new, new_regs[number])) if vague_in(value)]
                    if sides and all(origin is not None for origin, _ in sides):
                        union = frozenset().union(*(origin for origin, _ in sides))
                        if len(union) <= MAX_POINTS:                  # else unknown: no source named
                            out[ORIGIN - number] = union
            for number in range(13):
                def known(items):
                    if number in items:
                        return bounds.const(items[number])
                    return items.get(RANGES - number)
                left, right = known(old), known(new)
                if head is not None and left is not None and right is not None:
                    # The paths into this head so far, none of them widened: the old state's
                    # record, or, joined here first, the old state itself unless it arrived
                    # widened (then nothing here proves it).
                    mark = old.get(PATHS - number)
                    before = mark[1] if mark is not None and mark[0] == head else \
                        None if WIDE - number in old else left
                    paths = None if before is None or WIDE - number in new else bounds.join_values(before, right)
                    out[PATHS - number] = (head, paths)
                    cap = (head_ranges or {}).get((ctx, head, number))
                    if cap is not None and paths is not None and bounds.join_values(paths, cap) == cap:
                        out.pop(number, None)                # the first pass's join, proved: kept
                        out.pop(RANGES - number, None)
                        if cap[1] == cap[2]:
                            out[number] = cap[1]
                        else:
                            out[RANGES - number] = cap
                        continue
                    if head_joins is not None and paths is not None and WIDE - number in old:
                        head_joins[(ctx, head, number)] = paths  # widened here, then bounded
                if left is None or right is None or left == right:
                    if left is not None and left == right and number not in out:
                        out[RANGES - number] = left
                        if WIDE - number in old or WIDE - number in new:
                            out[WIDE - number] = True
                    continue
                joined_hull = bounds.join_values(left, right)
                # Widened only where a loop starts: elsewhere every path's value comes from one
                # there, so the hull of the paths is the range.
                hull = bounds.widen(left, joined_hull, self.chain_thresholds(root, ctx), 0) if head is not None \
                    else joined_hull
                out.pop(number, None)
                if hull[1] == hull[2]:
                    out[number] = hull[1]
                elif hull != bounds.TOP:
                    out[RANGES - number] = hull
                    # Grown past both paths at a loop head (the target of a backward branch):
                    # a widened bound, which no comparison has proved.
                    if head is not None and hull != joined_hull or WIDE - number in old or WIDE - number in new:
                        out[WIDE - number] = True
            return tuple(sorted(out.items()))

        def decode(function, site):
            data, end = self.span(function)
            offset = site - function
            if not 0 <= offset <= len(data) - 2:
                refuse(function, f"control leaves the indexed span at 0x{site:08X}")
            found = next(_ENGINE.disasm(data[offset:offset + 4], site, 1), None)
            if found is None:
                refuse(function, f"undecodable instruction at 0x{site:08X}")
            if CS_GRP_INT not in found.groups and not armv4t.instruction(found):
                refuse(function, f"0x{site:08X} is not an ARMv4T Thumb instruction")
            return found

        def decodable(function, site):
            try:
                decode(function, site)
                return True
            except WatchRefusal:
                return False

        updates = held_words = 0
        enqueue((), start, (tuple(regs), (), 0, tuple(sorted(constants.items())), (), (), ()))
        while pending:
            ctx, site = pending.pop()
            state = states[(ctx, site)]
            function = function_of(ctx)
            data, end = self.span(function)
            entry_sp = ctx[-1][2] if ctx else 0
            spans = frame_spans(ctx, bottomless)
            regs, memory, sp, constants = list(state[0]), dict(state[1]), state[2], dict(state[3])
            if mode == PROBE and not ctx and sp < self.frames.get(root, 0):
                self.frames[root] = sp                     # its own frame, for a recursive line
            if self.trace is not None:
                self._now = (sp, ((root, 0),) + tuple((level[0], level[2]) for level in ctx))
            pushed = set(state[4])          # live words a push wrote: saved registers, return addresses
            # Frame addresses stored outside the frames that a global may still hold:
            # (function, site, target, address or None, highest frame offset); and, for forgetting
            # what is known of the words they reach, ("kept", function, site, None, INF, the addresses)
            # for each address stored to memory or handed to code that is not walked.  Whatever took
            # one may keep it after the global is cleared, so a "kept" entry stays while its frame is
            # live (it never dangles and no global's overwrite removes it).
            escaped = set(state[5])
            # Probing: the input words (key, offset) a full-word store has written on every path.
            definite = set(state[6])
            instruction = decode(function, site)
            mnemonic = instruction.mnemonic.split(".")[0]
            operands = instruction.operands
            # Flags known from a compare of constants survive only instructions that keep them,
            # so a conditional branch on them follows the one feasible edge.
            known_flags = constants.pop(KNOWN_FLAGS, None)
            compared_with = constants.pop(COMPARED, None)
            if mnemonic in WIDTH or mnemonic in PRESERVE_FLAGS or \
                    mnemonic.startswith("b") and CS_GRP_JUMP in instruction.groups:
                if known_flags is not None:
                    constants[KNOWN_FLAGS] = known_flags
                if compared_with is not None:
                    constants[COMPARED] = compared_with
            if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) and not \
                    (mnemonic.startswith("b") and CS_GRP_JUMP in instruction.groups):
                refuse(function, f"conditional instruction at 0x{site:08X}")
            successors = [(ctx, site + instruction.size)]

            def anything_live():
                return any(taints(value) for value in regs[:16]) or bool(regs[FLAGS]) or \
                    any(taints(value) for value in memory.values())

            def use(value, what, bits=FULL):
                used = [number for number, mask in taints(value).items() if mask & bits]
                if used == [DEAD]:
                    refuse(function, f"{what} at 0x{site:08X} uses a frame address a callee returned")
                if used:
                    refuse(function, f"{what} at 0x{site:08X} uses a watched callee-saved register's value")

            def value(operand):
                if operand.type == ARM_OP_IMM:
                    return EMPTY
                number = register(operand)
                if number == 15:
                    refuse(function, f"program-counter operand at 0x{site:08X}")
                return frozenset({("F", sp)}) if number == 13 else regs[number]

            def forget(number):
                """Drop every fact known about register ``number``'s value."""
                constants.pop(number, None)
                constants.pop(RANGES - number, None)
                constants.pop(SIGNED - number, None)
                constants.pop(KBITS - number, None)
                constants.pop(ORIGIN - number, None)
                constants.pop(WIDE - number, None)
                if constants.get(COMPARED, (None,))[0] == number:
                    del constants[COMPARED]

            def write(number, new=EMPTY, constant=None, span=None, signed=None):
                """Set a register; ``constant``, ``span`` (an unsigned range) or ``signed`` (a
                signed one) describe a plain number."""
                if number in (13, 15):
                    refuse(function, f"unmodelled SP or PC write at 0x{site:08X}")
                regs[number] = new
                constants.pop(number, None)
                constants.pop(RANGES - number, None)
                constants.pop(SIGNED - number, None)
                constants.pop(KBITS - number, None)
                constants.pop(ORIGIN - number, None)
                constants.pop(WIDE - number, None)
                if signed is not None and numeric(new) and not taints(new):
                    constants[SIGNED - number] = signed
                if constants.get(COMPARED, (None,))[0] == number:
                    del constants[COMPARED]
                if constant is not None:
                    constants[number] = constant & FULL
                elif span is not None and numeric(new) and not taints(new) and span[0] == "S":
                    if span[1] == span[2]:
                        constants[number] = span[1]
                    elif (span[1], span[2]) != (0, FULL):
                        constants[RANGES - number] = span

            def narrow(name):
                """The range a zero-extending narrow load gives."""
                import stack_index_precondition_profile as bounds
                return bounds.norm("S", 0, 0xFF if name == "ldrb" else 0xFFFF, 0) \
                    if name in ("ldrb", "ldrh") else None

            def range_of(number):
                """The unsigned range of a register that holds a plain number, else None."""
                import stack_index_precondition_profile as bounds
                if number is None or number > 12 or not numeric(regs[number]) or taints(regs[number]):
                    return None
                if number in constants:
                    return bounds.const(constants[number])
                return constants.get(RANGES - number, bounds.TOP)

            def set_flags(names, dirty):
                regs[FLAGS] = (regs[FLAGS] - frozenset(names)) | (frozenset(names) if dirty else frozenset())

            def where(base, offset):
                """None outside the walked frames; ("exact", frame offset); ("some", offsets, also
                outside) for one of several frame words, or perhaps an untracked address; ("frame",
                also outside, span, exact offsets) for anywhere in the walked frames, or one of the
                exact offsets; ("input", ((key, delta), ...), True) for an
                access through a probed callee's inputs."""
                plain(base | (offset if isinstance(offset, frozenset) else frozenset()))
                points = pointers(base) | (pointers(offset) if isinstance(offset, frozenset) else frozenset())
                if not points:
                    return None
                inputs = [token for token in points if is_argument(token)]
                if inputs and frames(points):
                    # A probed callee's input or one of its own frame addresses: both, the frame
                    # word only perhaps (a weak update).
                    own = where(frozenset(token for token in base if not is_argument(token)),
                                offset if isinstance(offset, int) else
                                frozenset(token for token in offset if not is_argument(token)))
                    given = where(frozenset(token for token in base if is_argument(token)) | EMPTY,
                                  offset if isinstance(offset, int) else
                                  frozenset(token for token in offset if not is_frame(token)))
                    if own is not None and own[0] == "exact":
                        own = ("range", (own[1],), False)
                    return ("mixed", given, own)
                if inputs:
                    vague_offset = not isinstance(offset, int)
                    # Other arithmetic on an input than adding an index (("AF", key)): an address of
                    # unknown provenance where the input is a frame address, which the caller knows.
                    return ("input", tuple(sorted({(("AF", token[1]), None) if token[0] == "AF" else
                                                   (token[1], None if token[0] != "A" or vague_offset
                                                    else token[2] + offset) for token in inputs}, key=repr)), True)
                if vague_in(points):
                    refuse(function, f"an access at 0x{site:08X} goes through a frame address of unknown "
                                     f"provenance (not a stack array base plus an index)")
                exact = sorted(token[1] for token in base if type(token) is tuple and token[0] == "F")
                ranged = [token for token in base if type(token) is tuple and token[0] == "FR"]
                if ranged and not vague_in(points) and isinstance(offset, int):
                    # A proved index range: every candidate word is checked exactly, none excluded.
                    found = sorted({point + offset for token in base if type(token) is tuple and
                                    token[0] in ("F", "FR") for point in offsets(token)})
                    if len(found) <= MAX_RANGE:
                        return ("range", tuple(found), len(base) > len(exact) + len(ranged))
                vague_points = [token for token in frames(points) if token[0] in ("FW", "FV", "FR")]
                if vague_points or not isinstance(offset, int):
                    # ("frame", also outside, span): somewhere in the frames the addresses were
                    # taken from; a base that may be a plain number keeps the access possibly
                    # outside the frames too.
                    found = [extent(moved(token, offset) if isinstance(offset, int) else token, spans)
                             for token in frames(points)]
                    if mode == PROBE and max(hi for _, hi in found) > 0:
                        raise _NotIsolated              # perhaps the caller's frame: walked there
                    # The exact addresses among them are accessed exactly, never premised.
                    exact = tuple(sorted({point + offset for token in base if type(token) is tuple and
                                          token[0] in ("F", "FR") for point in offsets(token)})) \
                        if isinstance(offset, int) else ()
                    return ("frame", len(pointers(base)) < len(base) and
                            not (isinstance(offset, frozenset) and pointers(offset)),
                            (min(lo for lo, _ in found), max(hi for _, hi in found)), exact)
                others = len(base) > len(exact)
                if len(exact) == 1 and not others:
                    return ("exact", exact[0] + offset)
                return ("some", tuple(point + offset for point in exact), others)

            def shifted(location, amount):
                if location is None:
                    return location
                if location[0] == "mixed":
                    return ("mixed", shifted(location[1], amount), shifted(location[2], amount))
                if location[0] == "frame":
                    return location[:3] + (tuple(point + amount for point in location[3]),)
                if location[0] == "input":
                    return ("input", tuple((key, None if delta is None else delta + amount)
                                           for key, delta in location[1]), True)
                if location[0] == "range":
                    return ("range", tuple(point + amount for point in location[1]), location[2])
                if location[0] == "exact":
                    return ("exact", location[1] + amount)
                return ("some", tuple(point + amount for point in location[1]), location[2])

            def address_of(location):
                """The address value a location stands for (an LDM/STM writeback)."""
                if location is None:
                    return EMPTY
                if location[0] == "mixed":
                    return normal(address_of(location[1]) | address_of(location[2]))
                if location[0] == "frame":
                    return frozenset({somewhere(*location[2])}) | frozenset(("F", point) for point in location[3]) | \
                        (EMPTY if location[1] else frozenset())
                if location[0] == "range":
                    return frozenset({("FR", location[1][0], location[1][-1], 0)}) | (EMPTY if location[2] else frozenset())
                if location[0] == "exact":
                    return frozenset({("F", location[1])})
                if location[0] == "input":
                    return frozenset(("AV", key) if delta is None else ("A", key, delta) for key, delta in location[1]) | EMPTY
                return frozenset(("F", point) for point in location[1]) | (EMPTY if location[2] else frozenset())

            def word_at(off):
                """A frame word: what the walk wrote there, or for a word below the checked call's
                SP that it has not written, what earlier code may have left (``STALE``)."""
                if off in memory:
                    return memory[off]
                return STALE if off < 0 and mode in (ROOT, CONT) else EMPTY

            def held_before(off):
                """What a frame word holds before a store that may miss it, or writes part of it:
                for one not yet written, what earlier code left (probing, in its own frame: what its
                caller had there, marked ``EARLY``)."""
                return EARLY if mode == PROBE and off not in memory and off < 0 else word_at(off)

            def unread(off, mask):
                """Probing: whether bytes ``mask`` of frame word ``off`` may hold what the probed
                callee's caller had there: not written on some path into here."""
                return off not in memory or bool(early(memory[off]) & mask)

            def forget_below_sp():
                """Code that is not walked here (an unresolved callee or the BIOS) leaves unknown
                words below SP, but a word that holds a watched value may still hold it, and keeps
                those bits: that code need not write it (an unresolved call's premise says it does
                not)."""
                if mode == PROBE:                     # words its summary cannot list
                    exits["clobbers"] = sp if exits["clobbers"] is None else max(exits["clobbers"], sp)
                for off in [off for off in memory if off < sp]:
                    kept = tainted(taints(memory[off]), frozenset())
                    if kept:
                        memory[off] = normal(STALE | kept)
                    else:
                        del memory[off]
                for key in [key for key in constants if key >= SAVED - INF and key - SAVED < sp]:
                    del constants[key]

            def touched(word):
                """A frame word written: the range its push recorded no longer holds."""
                constants.pop(SAVED + word, None)

            def escaped_addresses():
                """The frame addresses, in frames still live, that escaped to memory or to code that
                is not walked: code that has one may write inside its object (``ESCAPE_PREMISE``, and
                code not walked may keep what it is given), whether or not it is given it again."""
                return frozenset(token for entry in escaped if entry[0] == "kept" for token in entry[5]
                                 if not (token[0] in ("F", "FR") and max(offsets(token)) < sp))

            def forget_escaped():
                """Code that may write through an escaped frame address ran: a call this walk does
                not enter, a summarised callee, a SWI (walked code may hand the BIOS a pointer it
                loaded back), or a store through an address it does not know.
                The words of those frames no longer hold the value a store gave them.  A continuation
                walk does not see the escapes made before it starts, so there every word of the frames
                live at its start (at or above the SP it starts with) counts as well; a frame made
                after that escapes only where this walk sees it."""
                reached = [extent(token, spans) for token in escaped_addresses()] + ([(0, INF)] if mode == CONT else [])
                for key in [key for key in constants if key >= SAVED - INF and key - SAVED not in pushed and
                            any(lo - 3 <= key - SAVED < hi for lo, hi in reached)]:
                    del constants[key]

            def unknown_words():
                """KNOWN mode does not follow the frame addresses that code it does not walk is
                given, so after such code any frame word may hold something else: the value a
                push or store gave it is no longer known.  A pushed word too: hand-written code can
                hand its address on (``push {r1}; mov r0, sp``), and a callee may write the stack
                argument words at SP, where a push in mid-function puts it."""
                for key in [key for key in constants if key >= SAVED - INF]:
                    del constants[key]

            def indexed(kind, matters, span):
                """The words an access at an unknown frame offset may reach, under the premise that
                an access through a variable index into a stack array stays inside that array:
                live words (at or above SP) of the frame span ``span`` the address was taken from
                that no push wrote.  The premise is recorded where an excluded word holds what
                ``matters``."""
                def inside(off):
                    return off >= sp and off not in pushed and off + 4 > span[0] and off < span[1]
                reached = [off for off in memory if inside(off)]
                excluded = sorted(off - sp for off, word in memory.items() if not inside(off) and matters(word))
                low = max(sp, span[0] & ~3 if span[0] > -INF else sp)
                admissible = bool(reached) or span[1] > low and \
                    (span[1] - low + 3) // 4 > len([off for off in pushed if low <= off < span[1]])
                if excluded and not admissible:
                    # No word the access may reach is one the premise admits: it cannot hold.
                    if mode == PROBE:
                        raise _NotIsolated
                    refuse(function, f"an indexed stack {kind} at 0x{site:08X} can reach only saved registers, "
                                     f"return addresses or words below SP")
                if excluded and mode in (ROOT, CONT):
                    self.premises.add(("index", function, site, kind, tuple(excluded)))
                if mode == PROBE:
                    # Whether an excluded word matters depends on the caller's values: a template,
                    # instantiated where the summary is used.
                    held = tuple(sorted((off - sp, word) for off, word in memory.items()
                                        if not inside(off) and word - EMPTY))
                    if held:
                        exits["premises"].add(("index", function, site, kind, held, sp))
                return reached

            def inexact(offsets, width, kind, matters):
                """The candidates of an access through one of several frame addresses that the
                premise of ``indexed`` leaves: a candidate over a saved word or below SP is
                dropped, and recorded where such a word holds what ``matters``."""
                if len(offsets) < 2:
                    return offsets
                kept, excluded = [], set()
                for off in offsets:
                    words = [off & ~3] + ([(off & ~3) + 4] if (off & 3) + width > 4 else [])
                    barred = [word for word in words if not owner(ctx, word) and (word < sp or word in pushed)]
                    if not barred:
                        kept.append(off)
                    excluded.update(word for word in barred if matters(memory.get(word, EMPTY)))
                if excluded:
                    if mode == PROBE:
                        raise _NotIsolated                 # walked where the premise is recorded
                    if not kept:                           # the premise could not hold
                        refuse(function, f"an access at 0x{site:08X} through one of several frame addresses "
                                         f"can reach only saved registers, return addresses or words below SP")
                    if mode in (ROOT, CONT):
                        self.premises.add(("index", function, site, kind,
                                           tuple(sorted(word - sp for word in excluded))))
                return kept

            def maybe_bits(words):
                """The bits a narrow load reads from words that may hold part of a frame address:
                ("FL", function, site, words, sp) where every such word may hold plain data
                instead (an address rebuilt from them is then premised plain where it is used,
                ``READ_PREMISE``), else ``FS``."""
                if not words:
                    return frozenset({FS})
                if any(UNK not in word_at(off) or taints(word_at(off)) for off in words):
                    return sources(words)
                return frozenset({("FL", function, site, tuple(sorted(off - sp for off in words)), sp)})

            def sources(words):
                """Bits read from ``words``: of the frame addresses they hold, each with its source."""
                found = set()
                for off in words:
                    word = word_at(off)
                    found.update(bits_of(token) for token in frames(word) | frozenset(t for t in word if is_fs(t)))
                    if vague_in(word) or any(type(token) is tuple and token[0] == "FB" for token in word):
                        found.add(FS)
                return frozenset(found or {FS})

            def plain(value):
                """An address rebuilt from maybe bits, used as one here: premised plain at the
                loads that read them (``READ_PREMISE``); a word that a narrow store may have partly
                overwritten, used as an address here: premised whole at its load
                (``REBUILT_PREMISE``)."""
                for token in lifted(value):
                    record = ("unset" if token[0] == "FU" else "rebuilt" if token[1:3] in self.mended else "bytes",) + \
                        token[1:4]
                    if mode == PROBE:
                        exits["premises"].add(record + token[4:])
                    elif mode in (ROOT, CONT):
                        self.state(record, token[4])
                return value - lifted(value)

            def plain_bytes(value):
                """Maybe bits stored where the walk does not look: premised plain at the loads
                that read them (``READ_PREMISE``)."""
                for token in value:
                    if type(token) is tuple and token[0] == "FL":
                        record = ("bytes",) + token[1:4]
                        if mode == PROBE:
                            exits["premises"].add(record + token[4:])
                        elif mode in (ROOT, CONT):
                            self.state(record, token[4])

            def mended(words):
                """What a word load reads from words that a narrow store may have partly
                overwritten, besides their whole old addresses: where that store may have missed
                them (each still holds a whole frame address), ("FX", ...), which is premised
                whole where it is used as an address (``REBUILT_PREMISE``, stated at this load);
                else an address of unknown provenance."""
                if not words:
                    return frozenset()
                if any(not frames(frozenset(token for token in memory.get(off, EMPTY) if not
                                            (type(token) is tuple and token[0] == "FB" or is_vague(token))))
                       for off in words):
                    return frozenset({FV})
                self.mended.add((function, site))
                return frozenset({("FX", function, site, tuple(sorted(off - sp for off in words)), sp)})

            def indexed_input(kind, keys):
                """An access through a probed callee's input at an unknown offset: where the input
                is a stack array address its caller gives, INDEX_PREMISE is stated here, naming the
                words of the callee's frames (("index-in", function, site, (kind, key), words, SP))."""
                held = tuple(sorted(((off - sp, word) for off, word in memory.items() if word - EMPTY), key=repr))
                for key, delta in keys:
                    if delta is None:
                        exits["premises"].add(("index-in", function, site, (kind, key), held, sp))

            def overruns(lo, hi):
                """Whether frame offsets lo..hi reach a word a push wrote, a word below SP or the
                owner's frame: where a range only widening produced does, it is an unknown index."""
                return any(word in pushed or word < sp or owner(ctx, word) for word in range(lo & ~3, hi + 1, 4))

            def handed_on(value):
                """What code that is not walked finds in ``value``: what earlier code left in a word
                (SFV) is no address under STALE_PREMISE (the word is stated as stale), but a word
                read where only that may be (``FU``) is an address of unknown provenance there."""
                lazy = any(type(token) is tuple and token[0] == "FU" for token in value)
                return (value - {SFV}) | (frozenset({FV}) if lazy else frozenset())

            def stale(value):
                """``value`` with a word read where only what earlier code left may be (``FU``)
                as that is (SFV), for code that is not walked and for the caller."""
                return value | frozenset({SFV}) if any(type(token) is tuple and token[0] == "FU"
                                                       for token in value) else value

            def unset(value, words):
                """A word load of ``words`` where nothing but what earlier code left may be found
                besides what the walk wrote (SFV, no other address of unknown provenance): that
                part is ("FU", ...), premised plain where it is used as an address
                (``UNSET_PREMISE``, stated at this load)."""
                if mode == KNOWN or SFV not in value or FV in value:
                    return value
                return (value - {SFV}) | frozenset({("FU", function, site, tuple(sorted(off - sp for off in words)), sp)})

            def load(location, width, signed=False):
                if location[0] == "mixed":
                    return normal(frozenset().union(*(load(part, width, signed) if part is not None else EMPTY
                                                      for part in location[1:])))
                if location[0] == "input":
                    for key, delta in location[1]:
                        exits["accesses"].add(("load", key, delta, width))
                    indexed_input("load", location[1])
                    if width < 4:
                        # Bytes of an input word: where the caller's word may hold part of a frame
                        # address, premised plain at this load (``READ_PREMISE``).
                        exits["premises"].add(("bytes-in", function, site, tuple(sorted(location[1], key=repr)), sp))
                    return EMPTY
                if location[0] in ("some", "range"):
                    kept = inexact(location[1], width, "load", live) if location[0] == "some" else location[1]
                    found = frozenset().union(*(load(("exact", off), width, signed) for off in kept))
                    return normal(found | (EMPTY if location[2] or not kept else frozenset()))
                if location[0] == "frame":
                    words = indexed("load", lambda word: live(word), location[2])
                    found = frozenset().union(*(memory[off] for off in words)) if words else frozenset()
                    exact = frozenset().union(*(load(("exact", off), width, signed) for off in location[3]))
                    lo, hi = location[2]
                    unwritten = [off for off in range(max(sp, lo & ~3), min(0, hi), 4)
                                 if off not in memory and off not in pushed]
                    if mode in (ROOT, CONT, PROBE) and unwritten:
                        found |= STALE                   # an element it has not written
                    if mode == PROBE:
                        # Elements that may hold what its caller had there: checked where the
                        # summary is used, against what the caller's walk has in those words.
                        exits["accesses"].update(("early", "sp", off, width) for off in sorted(
                            set(unwritten) | {off for off in words if off < 0 and early(memory[off])}))
                    masks = {number: FULL for number in taints(found)}
                    if width == 4:          # a whole word: the addresses stored there, as stored
                        rebuilt = mended([off for off in words if fragment(memory[off]) and
                                          any(type(token) is tuple and token[0] == "FB" for token in memory[off])])
                        left = unset(frames(found), unwritten + [off for off in words if SFV in memory[off]])
                        return normal(tainted(masks, frozenset()) | left | bits(found) | lifted(found) |
                                      rebuilt | exact | EMPTY)
                    pieces = maybe_bits([off for off in words if fragment(memory[off])]) if fragment(found) \
                        else frozenset()
                    return normal(tainted(masks, frozenset()) | pieces | exact | EMPTY)
                off = location[1]
                if owner(ctx, off):
                    if mode == PROBE:                      # a stack argument: its caller checks it
                        exits["accesses"].add(("argument", "sp", off, width))
                        if width == 4 and not off & 3:
                            return frozenset({("A", ("s", off), 0)})
                    elif mode == ROOT and not ctx:         # the checked callee's stack argument
                        exits["arguments read"].update(range(off & ~3, off + width, 4))
                    return EMPTY                           # the caller's own frame: untracked
                base, low = off & ~3, off & 3
                if mode == PROBE and any(unread(base + step, mask) for step, mask in lane_bytes(low, width)):
                    # Bytes it has not written, on every path or on one: what earlier code left
                    # there, which the walk in its caller's context knows and a summary does not.
                    raise _NotIsolated
                if low + width > 4:                        # straddles two words
                    found = word_at(base) | word_at(base + 4)
                    masks = {number: FULL for number in taints(found)}
                    if fragment(found):                    # bytes of two words: no premise
                        return tainted(masks, frozenset()) | \
                            (sources([base, base + 4]) if width < 4 else frozenset({FV})) | EMPTY
                    return tainted(masks, frozenset()) | EMPTY
                word = word_at(base)
                if width == 4:
                    if any(type(token) is tuple and token[0] == "FB" for token in word):
                        whole = frozenset(token for token in word if not (type(token) is tuple and token[0] == "FB"))
                        return unset(whole, [base]) | mended([base]) | EMPTY
                    return unset(word, [base])
                lane = (1 << 8 * width) - 1
                masks = {number: (mask >> 8 * low) & lane for number, mask in taints(word).items()}
                if signed:
                    masks = {number: mask | (FULL ^ lane if mask >> (8 * width - 1) & 1 else 0)
                             for number, mask in masks.items()}
                # A byte or halfword of an address is bits of one (below RAM_BASE, sign extended or not):
                # maybe bits, where the word may hold plain data instead.
                pieces = maybe_bits([base]) if fragment(word) & ((1 << width) - 1) << low else frozenset()
                return tainted({n: m for n, m in masks.items() if m}, frozenset()) | pieces | EMPTY

            def store(location, width, stored, what="a store", surely=True):
                """``surely``: the address is that location and nothing else (a base that may be
                another value, or a store that may hit its own frame instead, writes no input word
                surely)."""
                if location is not None and location[0] == "mixed":
                    for part in location[1:]:
                        store(part, width, stored, what, surely=False)
                    return
                if location is not None and location[0] == "input":
                    if taints(stored):
                        raise _NotIsolated
                    # A stored address (or bits of one) is kept with the access: where it is a
                    # frame address, the call is walked.
                    kept = pointers(stored) | bits(stored) | lifted(stored)
                    kind = ("store", frozenset(kept)) if kept else "store"
                    for key, delta in location[1]:
                        exits["accesses"].add((kind, key, delta, width))
                    indexed_input("store", location[1])
                    if surely and len(location[1]) == 1 and location[1][0][1] is not None:
                        key, delta = location[1][0]
                        if width == 4 and not delta & 3:
                            definite.add((key, delta))
                        else:                    # bytes it surely writes: they keep no mark
                            definite.update((key, delta + byte, "byte") for byte in range(width))
                    return
                if location is not None and location[0] in ("some", "range"):
                    if location[2]:
                        store(None, width, stored, what)      # it may write outside the frames
                    kept = location[1] if location[0] == "range" else \
                        inexact(location[1], width, "store", lambda word: word - EMPTY)
                    for off in kept:
                        words = [off & ~3] + ([(off & ~3) + 4] if (off & 3) + width > 4 else [])
                        before = {word: held_before(word) for word in words}    # it may not be this one
                        store(("exact", off), width, stored, what)
                        for word in words:
                            if word in memory:
                                memory[word] = normal(memory[word] | before[word])
                    return
                if location is None:
                    use(stored, what, STORED.get(mnemonic, FULL))
                    if target()[1] is None:
                        if mode in (ROOT, CONT):
                            forget_escaped()
                        elif mode == KNOWN:
                            unknown_words()     # the replay follows no escape: any word may be written
                    plain(stored)
                    # Bits of a frame address that vary with it (FS, or the part of an address a
                    # narrow store writes) escape like the address: code that is not walked could
                    # rebuild it.  Bits read where plain data may have been are premised plain.
                    plain_bytes(stored)
                    pieces = frozenset(token for token in stored if type(token) is tuple and
                                       (is_fs(token) or token[0] == "AF" and token[2])) | \
                        (pointers(stored) if width < 4 else frozenset())
                    if pieces and mode == PROBE:
                        inputs = frozenset(token for token in pieces if is_argument(token))
                        if pieces - inputs:
                            raise _NotIsolated            # bits of its own frame: walked where used
                        # Where an input is a frame address, its bits escape: walked there.  Only
                        # which inputs matter, so the summary of a recursion reaches a fixpoint.
                        exits["accesses"].update((("escape", frozenset({("A", token[1], 0)})), None, 0, width)
                                                 for token in inputs)
                    elif pieces and mode in (ROOT, CONT):
                        sources = frozenset(token[1] if is_fs(token) and len(token) > 1 else
                                            FV if is_fs(token) else token for token in pieces)
                        addressed = escaping(sources, "bits of a ")
                        self.premises.add(("bits", function, site, target()[0], addressed, tuple(sorted(
                            off - sp for off, word in memory.items() if taints(word)))))
                    if pointers(stored) and width == 4:
                        if mode == PROBE and not frames(stored):
                            # An input stored to memory the walk does not track: where the
                            # input is an address of the frames, the call is walked.
                            exits["accesses"].add((("escape", frozenset(pointers(stored))), None, 0, width))
                            return
                        if mode == PROBE:
                            raise _NotIsolated
                        if mode in (ROOT, CONT):
                            # Code that loads it back is not walked: premised per site, and any
                            # word of the object may change through it.
                            addressed = escaping(stored)
                            text, address = target()
                            if address is not None:
                                escaped.difference_update([entry for entry in escaped if entry[3] == address])
                            self.premises.add(("escape", function, site, text, addressed, tuple(sorted(
                                off - sp for off, word in memory.items() if taints(word)))))
                            escaped.add((function, site, text, address, max(addressed, default=0) + sp))
                            escaped.add(("kept", function, site, None, INF, tuple(sorted(frames(stored), key=repr))))
                            released(frames(stored), arguments=False)
                    elif width == 4 and mode in (ROOT, CONT):
                        address = target()[1]       # a known global overwritten with no frame address
                        if address is not None:
                            escaped.difference_update([entry for entry in escaped if entry[3] == address])
                    return
                if location[0] == "frame" and location[3]:
                    # Somewhere in the frames, or exactly one of the exact candidates (each checked).
                    store(location[:3] + ((),), width, stored, what)
                    store(("range", location[3], False), width, stored, what)
                    return
                if location[0] == "frame" or owner(ctx, location[1]):
                    if mode == PROBE and location[0] != "frame":
                        raise _NotIsolated
                    if location[0] != "frame":
                        # Above the checked callee's entry SP: the owner's frame, which no callee
                        # writes (the core's walk refuses the same store), but for its own stack
                        # arguments: a plain value stored to a word the checked callee also reads
                        # there is premised (``ARGS_PREMISE``), checked when the walk ends.
                        if mode == ROOT and not ctx and not live(stored) and not lifted(stored):
                            exits["arguments written"].append(
                                (function, site, tuple(range(location[1] & ~3, location[1] + width, 4))))
                            return
                        refuse(function, f"{what} at 0x{site:08X} writes the owner's frame above the checked "
                                         f"callee's entry SP")
                    if location[0] == "frame" and location[1]:
                        store(None, width, stored, what)      # it may write outside the frames
                    if live(stored) and (location[0] != "frame" or bottomless):
                        refuse(function, f"{what} at 0x{site:08X} writes an owner stack address or a frame "
                                         f"address to an untracked stack word")
                    if location[0] == "frame":           # any local word may now hold the value
                        reached = indexed("store", lambda word: word - EMPTY, location[2])
                        if live(stored) or lifted(stored):  # unwritten locals too, up to the entry SP
                            reached = set(reached) | {off for off in range(max(sp, location[2][0]) & ~3,
                                                                           min(0, location[2][1]), 4)
                                                      if off not in pushed}
                        piece = (frozenset({("FB", 0xF)}) if fragment(stored) and width < 4 else frozenset())
                        value = tainted({n: FULL for n in taints(stored)}, frozenset()) | piece | \
                            (frames(stored) | bits(stored) | lifted(stored) if width == 4 else frozenset())
                        for off in reached:                 # perhaps not this word: it keeps what it held
                            memory[off] = normal(held_before(off) | value | EMPTY)
                            touched(off)
                    return
                off = location[1]
                base, low = off & ~3, off & 3
                touched(base)
                if low + width > 4:
                    touched(base + 4)
                if width == 4 and not low:
                    memory[base] = stored
                    return
                old = [base] if low + width <= 4 else [base, base + 4]
                for word, (_, covered) in zip(old, lane_bytes(low, width)):
                    previous = held_before(word)
                    # The bytes it does not write of what earlier code left stay that (SFV), and,
                    # probing, keep their mark.
                    left = previous & {SFV} | marked(early(previous) & ~covered)
                    if len(old) == 1:
                        lane = ((1 << 8 * width) - 1) << 8 * low
                        written = ((1 << width) - 1) << low
                        kept = {n: m & ~lane for n, m in taints(previous).items()}
                        new = {n: (m << 8 * low) & lane for n, m in taints(stored).items()}
                        pieces = fragment(previous - left) & ~written | (written if fragment(stored) else 0)
                        memory[word] = normal(tainted(merge(kept, new), frozenset()) |
                                              (frozenset({("FB", pieces)}) if pieces else frozenset()) | left | EMPTY)
                    else:
                        masks = {n: FULL for n in merge(taints(previous), taints(stored))}
                        pieces = 0xF if fragment(previous - left) or fragment(stored) else 0
                        memory[word] = normal(tainted(masks, frozenset()) |
                                              (frozenset({("FB", pieces)}) if pieces else frozenset()) | left | EMPTY)

            def escaping(stored, what=""):
                """The frame words a stored address may reach (offsets from SP).  An address that
                may reach a saved register, a return address, a word below SP, an untracked word
                of the owner's frame or a word that depends on an owner stack address may not
                escape: the escape premise could not hold."""
                reached = set()
                for token in frames(stored):
                    if is_vague(token):
                        refuse(function, f"{what or 'a '}frame address of unknown provenance escape"
                                         f"{'' if what else 's'} to memory at 0x{site:08X}")
                    if token[0] == "FW":
                        if token[1] < sp or token[2] >= INF or not bottomless and token[2] > 0:
                            words = None
                        else:
                            words = range(token[1] & ~3, token[2], 4)
                    else:
                        words = sorted({point & ~3 for point in offsets(token)})
                    if words is None or any(owner(ctx, word) or bottomless and word >= 0 or word < sp or
                                            word in pushed or taints(word_at(word)) for word in words):
                        refuse(function, f"a store at 0x{site:08X} lets {what or 'a '}frame address escape that may "
                                         f"reach a saved register, return address, word below SP, word of the "
                                         f"owner's frame or word that depends on an owner stack address")
                    reached.update(word - sp for word in words)
                return tuple(sorted(reached))

            def target():
                """What a store at this site writes outside the frames: (text, address or None)."""
                if mnemonic in WIDTH and operands[1].type == ARM_OP_MEM:
                    memory_operand = operands[1].mem
                    base = register(memory_operand.base)
                    if memory_operand.index:
                        index = register(memory_operand.index)
                        if base in constants and index in constants:
                            address = (constants[base] + constants[index]) & FULL
                            return f"0x{address:08X}", address
                        return f"the memory at R{base}+R{index}", None
                    if base in constants:
                        address = (constants[base] + memory_operand.disp) & FULL
                        return f"0x{address:08X}", address
                    return f"the memory at R{base}+0x{memory_operand.disp:X}", None
                if mnemonic == "stm":
                    return f"the block at R{register(operands[0])}", None
                return "memory", None

            def dangling(top):
                """Escapes into frames a return at this site releases (offsets below ``top``) that a
                global may still hold: stated as facts."""
                for entry in sorted(escaped, key=repr):
                    if entry[4] < top:
                        self.premises.add(("dangling", entry[0], entry[1], entry[2], function, site))
                        escaped.discard(entry)

            def transfer(destination):
                """Successors of a branch to ``destination``."""
                use(destination, "a branch target")
                destination = stale(destination)      # no premise makes a branch target plain
                if frames(destination):
                    refuse(function, f"a branch at 0x{site:08X} targets a frame address")
                if destination == frozenset({RET}) and not ctx:
                    if mode == ROOT:
                        at_return()
                    if mode == PROBE:
                        if sp != 0:
                            raise _NotIsolated
                        for number in range(13):
                            # Addresses, bits of them and lazily premised values: where the
                            # summary is used, as a walk there would have them.
                            returned = frozenset(pointers(regs[number]) | bits(regs[number]) | lifted(regs[number]))
                            if len(returned) < len(regs[number]):
                                returned |= EMPTY
                            exits["registers"][number] = exits["registers"][number] | returned
                        # The words it leaves below its entry SP, written on every return path.
                        words = {off: value for off, value in memory.items() if off < 0}
                        # A word left on some return paths only may hold whatever was there before.
                        exits["left"] = words if exits["left"] is None else \
                            {off: normal(exits["left"].get(off, EARLY) | words.get(off, EARLY))
                             for off in exits["left"].keys() | words.keys()}
                        exits["definite"] = set(definite) if exits["definite"] is None else exits["definite"] & definite
                    exits["returns"] = True
                    return []
                if len(destination) == 1 and type(next(iter(destination))) is tuple and \
                        next(iter(destination))[0] == "R":
                    depth = next(iter(destination))[1]
                    if depth != len(ctx):
                        refuse(function, f"a return at 0x{site:08X} does not match its call")
                    if sp != entry_sp:
                        refuse(function, f"a return at 0x{site:08X} does not restore SP")
                    regs[14] = EMPTY
                    if mode in (ROOT, CONT):
                        dangling(entry_sp)
                    return [(ctx[:-1], ctx[-1][1])]
                points = [token[1] for token in destination if type(token) is tuple and token[0] == "L"]
                if points and len(points) == len(destination):
                    return [(ctx, point) for point in sorted(points)]
                if mode == PROBE:
                    raise _NotIsolated
                if mode == CONT and not ctx:
                    dangling(INF)
                    # The owner's own return: a callee's dead frame address may be left behind (its
                    # frame is gone, and the owner's is about to be); a watched value may not.
                    if any(set(taints(value)) - {DEAD} for value in list(regs[:16]) + list(memory.values())):
                        refuse(function, f"an indirect branch at 0x{site:08X} while watched values are live")
                elif anything_live():
                    refuse(function, f"an indirect branch at 0x{site:08X} while watched values are live")
                return []

            def at_return():
                if sp != 0:
                    refuse(function, f"the return at 0x{site:08X} does not restore SP")
                dangling(0)
                for number in sorted(watched):
                    if regs[number] != frozenset({number}):
                        refuse(function, f"R{number} does not hold its value at the return 0x{site:08X}")
                for number in sorted(CALLEE_SAVED - watched):
                    if live(regs[number]):
                        refuse(function, f"R{number} holds an owner stack address or a frame address at "
                                         f"the return 0x{site:08X}")
                for number in (0, 1, 2, 3, 12):
                    # A frame address left here (agbcc leaves dead `add r2, sp, #8` pointers) is
                    # handed back as DEAD: the caller may not use it at all.
                    sources = watched_tokens(regs[number]) | (frozenset({DEAD}) if frames(regs[number]) or
                                                              any(is_fs(token) for token in regs[number]) or
                                                              stale(regs[number]) != regs[number]
                                                              else frozenset())
                    if len(sources) > 1:
                        refuse(function, f"R{number} may hold more than one watched value at the return 0x{site:08X}")
                    if sources:
                        source = next(iter(sources))
                        if exits["copies"].setdefault(number, source) != source:
                            refuse(function, f"R{number} holds different watched values at returns")
                exits["flags"] = exits["flags"] | regs[FLAGS]

            def passed():
                """The addresses R0-R12 hold at code that is not walked, for a summary, and the
                inputs its frame words hold (("w", offset from SP), where the summary is used: the
                words that depend on owner stack addresses there)."""
                return tuple((number, frozenset(pointers(regs[number]) | bits(regs[number]) | lifted(regs[number])))
                             for number in range(13) if pointers(regs[number]) or bits(regs[number]) or
                             lifted(regs[number])) + inputs_held(memory, sp)

            def inputs_held(words, at):
                return tuple(sorted((("w", off - at), frozenset(token for token in word if is_argument(token)))
                                    for off, word in words.items() if off >= sp and
                                    any(is_argument(token) for token in word)))

            def released(extra=frozenset(), arguments=True, where=None, base=None, surely=True, bios=False,
                         writes=None):
                """``released_to`` the code that is not walked; with ``arguments`` and R12 holding a
                frame address a walked callee returned (``DEAD``, ``scratch``), that address is one
                of its arguments too, and it may address any word of the walked frames.  At a SWI
                (``bios``) R12 is no argument: the BIOS dispatcher saves it and loads the routine's
                own address there before branching to it.  ``writes`` is what an enumerated BIOS
                routine stores into the objects it is given (``BIOS_WRITES``); else any address."""
                if arguments and not bios and scratch():
                    extra = extra | frozenset({somewhere(-INF, 0)})
                return released_to(extra, arguments, where, base, surely, bios, writes)

            def released_to(extra=frozenset(), arguments=True, where=None, base=None, surely=True, bios=False,
                            writes=None):
                """Code that is not walked, given frame addresses (``extra``, and with ``arguments``
                R0-R3, R12 and the words of the calling function's frame, where its stack
                arguments are), may write any word of the objects they address that no push
                wrote (under INDEX_PREMISE, words of the frames they were taken from), and any
                object it finds addressed there, with a plain value or any address it can reach,
                and may return such an address in R0-R3 or R12.  Returns what it may hand back:
                those addresses, exactly as given or anywhere in their objects (nothing when it was
                given none)."""
                words = [off for off in memory if off >= sp and off not in pushed]
                own = [off for off in words if off < entry_sp] if arguments else []
                given = handed_on(frozenset().union(extra, *(regs[number] for number in (0, 1, 2, 3, 12)[:4 if bios else 5]
                                                           if arguments),
                                                *(memory[off] for off in own)))
                if not (pointers(given) or fragment(given)):
                    return frozenset()
                writable, held = set(own), set(given)
                found = set().union(*(handed_on(memory[off]) for off in own))    # what those objects hold

                def objects(tokens):
                    """The frame spans the objects at those addresses lie in; an exact address
                    below SP (a returned callee's frame) is of an object below SP."""
                    return [(-INF, sp) if token[0] in ("F", "FR") and max(offsets(token)) < sp else
                            extent(token, spans) for token in frames(tokens)]
                while True:
                    reached = objects(frozenset(held))
                    grown = {off for off in words if any(lo - 3 <= off < hi for lo, hi in reached)} - writable
                    if not grown:
                        break
                    writable |= grown
                    for off in grown:
                        held |= handed_on(memory[off])
                        found |= handed_on(memory[off])
                held = frozenset(held)
                # Words it can reach that hold parts of frame addresses or an address of unknown
                # provenance, or nothing written yet (what earlier code left): an address built
                # from them is premised per site, not spread.
                partial = {off for off in writable if vague_in(memory[off]) or
                           any(type(token) is tuple and token[0] == "FB" for token in memory[off])}
                # Words of the calling function's frame, where its stack arguments are, that nothing
                # has written: what earlier code left (probing, what the caller's code left).
                fresh = {off for off in range(sp, entry_sp, 4)
                         if off not in memory and off not in pushed} if arguments else set()
                for lo, hi in objects(held):
                    fresh |= {off for off in range(max(sp, lo & ~3), min(0, hi), 4)
                              if off not in memory and off not in pushed}
                partial |= fresh
                if partial:
                    # Stated at each site of code not walked that is given those addresses (a
                    # summarised callee's), naming the words from the SP there.
                    for named, at in where or [((function, site), sp if base is None else base)]:
                        record = ("stale",) + named + (tuple(sorted(off - at for off in partial)),)
                        if mode == PROBE:
                            exits["premises"].add(record + (at,))     # stated where the summary is used
                        else:
                            self.state(record, at, where is not None)
                def reachable(tokens):
                    return frozenset(token for token in pointers(tokens) if token[0] in ("F", "FR", "A")) | \
                        frozenset(inside(token) for token in pointers(tokens) if not is_vague(token)) | bits(tokens)
                reach = reachable(held)
                # An enumerated BIOS routine stores into those objects only what GBATEK documents:
                # nothing, numbers it computes, or data it copies from them (an address copied stays
                # an address), never an address it was handed (stated per site).
                stored = reach if writes is None else reachable(frozenset(found)) if writes == "copies" else EMPTY
                for off in writable:         # it may write them, or not: they keep what they held
                    memory[off] = normal(memory[off] | EMPTY | stored)
                    touched(off)
                for off in fresh:            # under the premise, no address earlier code left
                    # A call inside a summary may not run on every path: what was there may stay.
                    # Probing, what its caller had there may stay too: the word stays marked.
                    memory[off] = normal((EARLY if mode == PROBE else EMPTY if surely else word_at(off)) |
                                         EMPTY | stored)
                    touched(off)
                return reach

            def inside(token):
                """Anywhere in the object at an exact or ranged frame address, as code that is not
                walked hands it back (``PREMISE``): no object spans a word a push wrote, so at
                most the run of other live words of its frame around it."""
                if token[0] not in ("F", "FR"):
                    return vague(token, spans)
                lo, hi = extent(token, spans)
                points = offsets(token)
                low, high = min(points) & ~3, (max(points) & ~3) + 4
                if hi >= INF or low < sp or any(word in pushed for word in range(low, high, 4)):
                    return vague(token, spans)
                while low - 4 >= max(lo, sp) and low - 4 not in pushed:
                    low -= 4
                while high < hi and high not in pushed:
                    high += 4
                return somewhere(low, high)

            def arguments_refused(what, registers, stacked):
                """Code that is not walked may receive frame addresses in R0-R3 or R12 (its buffer
                arguments), but no dependent value and no address of a word that holds one.  IP is
                scratch that thunks and veneers read (``_call_via_ip``), so no dependent value may
                be there either; a frame address a walked callee returned and left in IP is premised
                unread instead (``scratch``)."""
                for number in (0, 1, 2, 3, 12):
                    if taints(regs[number]) and not (number == 12 and scratch()):
                        refuse(function, f"{what} at 0x{site:08X} receives an owner stack address in R{number}")
                    pointed = [point - sp for token in regs[number] if is_frame(token) and token[0] in ("F", "FR")
                               for point in offsets(token)]
                    if set(pointed) & set(stacked):
                        refuse(function, f"{what} at 0x{site:08X} receives in R{number} the address of a frame "
                                         f"word that may hold an owner stack address")

            def scratch():
                """Whether IP holds, of anything that matters, only a frame address a walked callee
                returned (``DEAD``), at an unresolved call or SWI: an argument it is given (see
                ``released``), stated as no branch target (``R12_PREMISE``)."""
                return set(taints(regs[12])) == {DEAD}

            def call(target):
                """Successors of a BL to ``target`` outside the walked function."""
                registers = [n for n in range(13) if live(regs[n])]
                # A thunk may not branch to a dependent value or a frame address; a probed
                # callee's input is checked where its summary is used.
                destination = self.resolve(target, constants, frozenset(
                    n for n in range(13) if taints(regs[n]) or fragment(regs[n])), site=site) \
                    if mode != KNOWN else None
                stacked = sorted(off - sp for off, word in memory.items() if taints(word))
                # A frame address in the caller's frame may be a stack argument.
                framed = [off for off, word in memory.items() if sp <= off < entry_sp and off not in pushed
                          and live(word)]
                exposed = bool(registers or regs[FLAGS] or stacked or framed)
                after = (ctx, site + 4)

                def apply():
                    """Skip the call using the callee's summary: R0-R12 as it returns them, or
                    None when it must be walked here instead (no summary, an access that reaches
                    a dependent value, a frame address, a saved word or the caller's frame)."""
                    if self.summarised is not None and mode != PROBE and \
                            not self.summarised(destination, (root,) + tuple(level[0] for level in ctx)):
                        return None
                    summary = self.isolation(destination)
                    if summary is None:
                        return None
                    accesses, returned = summary[0], summary[1]

                    def word_value(off):
                        at = sp + off
                        if owner(ctx, at):
                            return frozenset({("A", ("s", at), 0)}) if mode == PROBE else EMPTY
                        return word_at(at)

                    def input_value(key):
                        if key == "sp":
                            return frozenset({("F", sp)})
                        if isinstance(key, tuple) and key[0] == "AF":
                            return unknown_of(input_value(key[1]), False)
                        return regs[key] if isinstance(key, int) else word_value(key[1])

                    def unusable(value):
                        return bool(taints(value)) or any(type(token) is tuple and token[0] == "FB"
                                                          for token in value)

                    def mapped(tokens):
                        """The callee's value ``tokens`` (inputs, its own frame addresses, plain
                        numbers) as a value here, or None if an input it uses is unusable."""
                        value = frozenset()
                        for token in tokens:
                            if is_frame(token):           # the callee's own, now released, frame
                                value |= frozenset({rebased(token, sp)})
                            elif is_fs(token):            # bits of its own frame's addresses
                                value |= frozenset({bits_of(rebased(token[1], sp)) if len(token) > 1 else FS})
                            elif type(token) is tuple and token[0] in ("FB", "L", "FL", "FX", "FU", "E"):
                                value |= frozenset({token})      # ("E", ...): resolved by ``skip``
                            elif token == RET:            # its return address, as a walk here has it
                                value |= frozenset({("R", len(ctx) + 1)})
                            elif type(token) is tuple and token[0] == "R":
                                value |= frozenset({("R", len(ctx) + 1 + token[1])})
                            elif not is_argument(token):
                                value |= EMPTY
                            else:
                                base = input_value(token[1])
                                if unusable(base):
                                    return None
                                found = pointers(base)
                                if token[0] == "AF":
                                    value |= unknown_of(base, token[2])
                                    continue
                                value |= frozenset(vague(point, spans) if token[0] == "AV" else moved(point, token[2])
                                                   for point in found) | bits(base) | lifted(base)
                                if len(found) < len(base):
                                    value |= EMPTY
                        return value

                    weak, indexes = {}, []
                    for kind, key, delta, width in sorted(accesses, key=repr):
                        if kind == "compared":            # an input that decides a branch
                            if key in constants:
                                return None               # known here: walked, on the paths it takes
                            if mode == PROBE:
                                exits["accesses"].update(("compared", token[1], 0, 0) for token in regs[key]
                                                         if type(token) is tuple and token[0] == "A" and
                                                         isinstance(token[1], int))
                            continue
                        if kind == "argument":            # a stack-argument word, read as an input
                            at = sp + delta
                            if owner(ctx, at):
                                if mode == PROBE:
                                    exits["accesses"].add(("argument", "sp", at, width))
                                continue
                            word = word_at(at & ~3)
                            if unusable(word) or (width < 4 or at & 3) and live(word) or \
                                    mode == PROBE and any(unread((at & ~3) + step, mask)
                                                          for step, mask in lane_bytes(at & 3, width)):
                                return None
                            continue
                        if kind == "early":
                            # Words of its own frame it read where a path had not written them, as
                            # what earlier code may leave there (``STALE``): it applies only where the
                            # walk here has no more than that in them.  Probing, a word this walk has
                            # not written either is its own caller's, and is checked where its summary
                            # is used.  A callee whose summary is being computed (a recursion) reads
                            # them anywhere below this SP, as its frames at any depth: there no word
                            # may hold a watched value (what else earlier code left in the stack below
                            # a recursion's first frame is read as the stale words below SP are).
                            ranged = isinstance(delta, tuple) or destination in self.probing
                            if ranged:
                                limit = sp if destination in self.probing else sp + delta[1]
                                if mode == PROBE:
                                    exits["accesses"].add(("early", "sp", ("below", limit), width))
                                words = sorted(off for off in memory if off < limit)
                            else:
                                words = [sp + delta]
                            for word in words:
                                if mode == PROBE and unread(word, 0xF):
                                    if not ranged:
                                        exits["accesses"].add(("early", "sp", word, width))
                                    continue
                                if (taints(word_at(word)) if ranged else not settled(word_at(word), width)):
                                    return None
                            continue
                        if isinstance(kind, tuple) and kind[0] == "escape":
                            value = mapped(kind[1])
                            if value is None or frames(value) or bits(value) or lifted(value) or \
                                    mode != PROBE and live(value):
                                return None
                            if mode == PROBE and pointers(value):
                                exits["accesses"].add((("escape", frozenset(pointers(value))), None, 0, width))
                            continue
                        base = input_value(key)
                        if unusable(base) or lifted(base):
                            return None                   # (a lazy address: premised where walked)
                        if delta is None or delta & FULL > RAM_BASE - 0x10000:
                            # Maybe bits (of a halfword at most) plus an index, or a constant that
                            # may take them past RAM_BASE: an address rebuilt from them, used, as
                            # the walk in context premises it at their loads.
                            plain_bytes(frozenset(token for token in base if type(token) is tuple and token[0] == "FL"))
                        stored_value = EMPTY
                        if isinstance(kind, tuple):       # a store of an address (or bits of one) it holds
                            value = mapped(kind[1])
                            if value is None or taints(value) or frames(value):
                                return None
                            if len(pointers(base)) < len(base) or not pointers(base):
                                # Perhaps outside the frames: bits of a frame address there are
                                # walked (an escape); maybe bits, or an address rebuilt from them,
                                # are premised plain at their loads, as a store walked here is.
                                if any(is_fs(token) for token in value):
                                    return None
                                plain_bytes(value)
                                plain(value)
                                if mode == PROBE:
                                    # An input of the probed caller stored there escapes, as its
                                    # own store there would: walked where it is a frame address
                                    # (or, by a narrow store or other arithmetic, bits of one).
                                    pieces = frozenset(token for token in value if type(token) is tuple and
                                                       token[0] == "AF" and token[2]) | \
                                        (pointers(value) if width < 4 else frozenset())
                                    exits["accesses"].update((("escape", frozenset({("A", token[1], 0)})), None, 0, width)
                                                             for token in pieces if is_argument(token))
                                    if pointers(value) and width == 4:
                                        exits["accesses"].add((("escape", frozenset(pointers(value))), None, 0, width))
                            kept = pointers(value) | bits(value) | lifted(value)
                            kind = ("store", frozenset(kept)) if kept else "store"
                            stored_value = bits(value) | lifted(value) | EMPTY
                        for token in pointers(base):
                            if is_argument(token):        # through the probed caller's own input
                                exits["accesses"].add((kind, ("AF", token[1]) if token[0] == "AF" else token[1],
                                                       None if token[0] != "A" or delta is None
                                                       else token[2] + delta, width))
                                continue
                            if token[0] != "F":
                                return None
                            if delta is None:
                                # At an unknown offset: under INDEX_PREMISE, inside the object at
                                # that address, which spans no word a push wrote.
                                span = inside(token)
                                if span[0] != "FW" or span[1] <= -INF or span[2] >= INF:
                                    return None
                                candidates = list(range(span[1], span[2], 4))
                                matters = live if kind == "load" else (lambda word: word - EMPTY)
                                outside = [(off, word) for off, word in memory.items()
                                           if not span[1] <= off < span[2] and matters(word)]
                                if outside:
                                    if mode == PROBE:
                                        indexes.append(("index", function, site, kind if kind == "load" else "store",
                                                        tuple(sorted((off - sp, word) for off, word in outside)), sp))
                                    else:
                                        indexes.append(("index", function, site, kind if kind == "load" else "store",
                                                        tuple(sorted(off - sp for off, _ in outside))))
                            else:
                                at = token[1] + delta
                                candidates = [at & ~3] + ([(at & ~3) + 4] if (at & 3) + width > 4 else [])
                            lanes = {} if delta is None else \
                                {(at & ~3) + step: mask for step, mask in lane_bytes(at & 3, width)}
                            for word in candidates:
                                if owner(ctx, word):
                                    if mode == PROBE and kind == "load":
                                        exits["accesses"].add(("load", "sp", word, 4))
                                    elif kind != "load":
                                        return None       # a store to the caller's frame
                                elif kind == "load":
                                    current = STALE if mode == PROBE and word not in memory else word_at(word)
                                    # The summary reads every input word as plain data: it applies
                                    # only where the word holds no frame address or part of one.
                                    addressy = live(current) or fragment(current) or bits(current) or \
                                        lifted(current)
                                    if taints(current) or addressy and (width >= 4 or UNK not in current):
                                        return None
                                    if mode == PROBE and unread(word, lanes.get(word, 0xF)):
                                        # What the probed caller's caller may have left there: checked
                                        # where that summary is used.
                                        exits["accesses"].add(("early", "sp", word, width))
                                    # Bytes of a word that may be uninitialised or hold part of
                                    # a frame address, or plain data (a text buffer filled by code
                                    # not walked): premised plain at the load (its "bytes-in").
                                elif word in pushed:
                                    return None           # a store over a saved register
                                else:
                                    weak[word] = weak.get(word, EMPTY) | stored_value
                                    # A narrow store leaves the rest of an address it overwrites
                                    # marked, as a store walked here does.
                                    written = 0xF if delta is None or width == 4 and not at & 3 else \
                                        ((1 << width) - 1) << (at & 3) & 0xF if word == at & ~3 else \
                                        ((1 << width) - 1) >> (4 - (at & 3)) & 0xF
                                    pieces = (fragment(word_at(word) - {SFV}) & ~written if width < 4 or at & 3 or
                                              delta is None else 0) | (written if fragment(stored_value) else 0)
                                    if pieces and not (width == 4 and delta is not None and not at & 3 and
                                                       not fragment(stored_value)):
                                        weak[word] = weak[word] | frozenset({("FB", pieces & 0xF)})
                    new = []
                    for number in range(13):
                        value = mapped(returned[number])
                        if value is None:
                            return None
                        new.append(normal(value) if value else EMPTY)
                    records, release = [], frozenset()    # checked first, applied only if all pass
                    calls_release = False                         # and not the BIOS alone
                    swi_writes = set()                            # documented writes of the SWIs that do
                    release_sites = set()                         # sites given frame addresses here
                    records.extend(indexes)
                    marks = []                                    # (first record, its SP) for a trace
                    for template in summary[3]:
                        at = sp + template[-1]               # the SP at that call, SWI or access
                        marks.append((len(records), at))
                        if template[0].startswith("bytes-in"):
                            # Bytes it reads through an input: of the words here that may hold
                            # part of a frame address, premised at that load; of an input of the
                            # outer callee, stated where that is used.
                            words, outer = set(), set()
                            for key, delta in template[3]:
                                base = input_value(key)
                                if unusable(base):
                                    return None
                                for point in pointers(base):
                                    if is_argument(point):
                                        # At an unknown offset in that input's object, so that a
                                        # recursion reaches a fixpoint.
                                        outer.add((("AF", point[1]) if point[0] == "AF" else point[1], None))
                                        continue
                                    if point[0] == "F" and delta is not None:
                                        candidates = [(point[1] + delta) & ~3]
                                    else:                 # anywhere in its object (INDEX_PREMISE)
                                        span = inside(point)
                                        if span[0] != "FW" or span[1] <= -INF or span[2] >= INF:
                                            return None
                                        candidates = range(span[1] & ~3, span[2], 4)
                                    for word in candidates:
                                        current = word_at(word)
                                        if fragment(current) or lifted(current):
                                            words.add(word)
                            suffix = "+" if template[0].endswith("+") else ""
                            if outer and mode == PROBE:
                                records.append(("bytes-in" + suffix,) + template[1:3] +
                                               (tuple(sorted(outer, key=repr)), at))
                            if words:
                                record = ("bytes" + suffix,) + template[1:3] + (tuple(sorted(word - at for word in words)),)
                                records.append(record + (at,) if mode == PROBE else record)
                            continue
                        if template[0].startswith(("stale", "rebuilt", "bytes", "unset")):
                            records.append(template[:-1] + (at,) if mode == PROBE else template[:-1])
                            continue
                        if template[0].startswith("index-in"):
                            kind_, key = template[3]
                            base = input_value(key)
                            if unusable(base) or lifted(base):
                                return None
                            words = []
                            for off, tokens in template[-2]:
                                value = mapped(tokens)
                                if value is None:
                                    return None
                                returning = any(token == RET or type(token) is tuple and token[0] in ("L", "R")
                                                for token in tokens)
                                words.append((off, value | (frozenset({RET}) if returning else frozenset())))
                            suffix = "+" if template[0].endswith("+") else ""
                            for token in pointers(base):
                                if is_argument(token):   # the outer callee's own input: stated where used
                                    records.append(("index-in" + suffix,) + template[1:3] + ((kind_, token[1]),) +
                                                   (tuple(sorted(words + [(off - at, word) for off, word in
                                                                          memory.items() if word - EMPTY],
                                                                 key=repr)), at))
                                    continue
                                if token[0] != "F":
                                    return None
                                span = inside(token)
                                if span[0] != "FW" or span[1] <= -INF or span[2] >= INF:
                                    return None
                                # The words here outside that array are excluded too.
                                outside = words + [(off - at, word) for off, word in memory.items()
                                                   if off >= sp and not span[1] <= off < span[2] and word - EMPTY]
                                if mode == PROBE:        # an array of the outer callee's own frame
                                    records.append(("index" + suffix,) + template[1:3] + (kind_,) +
                                                   (tuple(sorted(outside, key=repr)), at))
                                    continue
                                excluded = tuple(sorted({off for off, value in outside if
                                                         (live(value) if kind_ == "load" else value - EMPTY)}))
                                if excluded:
                                    records.append(("index" + suffix,) + template[1:3] + (kind_, excluded))
                            continue
                        if template[0].startswith("index"):
                            words = []
                            for off, tokens in template[-2]:
                                value = mapped(tokens)
                                if value is None:
                                    return None
                                returning = any(token == RET or type(token) is tuple and token[0] in ("L", "R")
                                                for token in tokens)
                                words.append((off, value | (frozenset({RET}) if returning else frozenset())))
                            # The words of the frames here lie outside the callee's: excluded too.
                            words += [(off - at, word) for off, word in memory.items() if off >= sp and word - EMPTY]
                            if mode == PROBE:
                                records.append(template[:-2] + (tuple(sorted(words, key=repr)), at))
                                continue
                            excluded = tuple(sorted(off for off, value in words if
                                                    (live(value) if template[3] == "load" else value - EMPTY)))
                            if excluded:
                                records.append(template[:4] + (excluded,))
                            continue
                        if template[0].startswith("call") and template[4] is None and any(
                                number in chain_registers(template[3]) and token[0] == "A" and isinstance(token[1], int)
                                and token[1] in constants for number, tokens in template[-2] for token in tokens):
                            return None      # its function pointer is known here: walked, and resolved
                        given, held_words = [], []           # its arguments, as values here
                        for number, tokens in template[-2]:
                            if isinstance(number, tuple):    # a word of the callee's frames
                                held_words.append((number, tokens))
                                continue
                            if number == 12 and template[0].startswith("swi"):
                                continue                     # the BIOS dispatcher saves R12: no argument
                            value = mapped(tokens)
                            if value is None:
                                return None
                            given.append((number, frozenset(pointers(value) | bits(value) | lifted(value))))
                        if any(number not in CALLEE_SAVED and pointers(value) for number, value in given):
                            release_sites.add((template[1:3], at))
                        if mode == PROBE:
                            # Its words that hold inputs, as inputs here, and this frame's words
                            # that hold the outer callee's inputs.
                            outer = {}
                            for key, tokens in held_words:
                                outer[key] = frozenset(token for token in tokens if not is_argument(token)) | \
                                    frozenset().union(*(frozenset(t for t in input_value(token[1]) if is_argument(t))
                                                        for token in tokens if is_argument(token)))
                            for key, tokens in inputs_held(memory, at):
                                outer[key] = outer.get(key, frozenset()) | tokens
                            records.append(template[:-2] + (tuple(given) + tuple(sorted(
                                (key, tokens) for key, tokens in outer.items() if tokens)), at))
                            release |= frozenset().union(*(value for number, value in given
                                                           if number not in CALLEE_SAVED and pointers(value)))
                            calls_release = calls_release or template[0].startswith("call")
                            if template[0].startswith("swi") and any(number not in CALLEE_SAVED and pointers(value)
                                                                     for number, value in given):
                                swi_writes.add(BIOS_WRITES.get(template[3], (None, None))[1])
                            continue
                        # The words that depend on owner stack addresses there: here, and those of
                        # its frames that hold inputs that do.
                        stacked = tuple(sorted({off - at for off, word in memory.items() if taints(word)} |
                                               {key[1] for key, tokens in held_words if any(
                                                   taints(input_value(token[1])) for token in tokens)}))
                        held = tuple(number for number, value in given if number in CALLEE_SAVED and live(value))
                        if template[0].startswith("call") and any(frames(value) for number, value in given
                                                         if number in chain_registers(template[3])):
                            return None                  # a thunk branching to a frame address
                        for number, value in given:
                            pointed = {point - at for token in value if token[0] in ("F", "FR")
                                       for point in offsets(token)}
                            if number not in CALLEE_SAVED and pointed & set(stacked):
                                return None              # walked here, where it refuses
                        # The callee's own frame words at the site, where the code's stack arguments
                        # are, are given to it too (``released_to``): the frame addresses they hold
                        # here are released with the registers'.
                        held_frames = frozenset()
                        for key, tokens in held_words:
                            value = mapped(tokens)
                            if value is None:
                                return None
                            held_frames |= frames(value)
                        release |= frozenset().union(held_frames, *(value for number, value in given
                                                                    if number not in CALLEE_SAVED and frames(value)))
                        given_frames = bool(held_frames) or any(number not in CALLEE_SAVED and frames(value)
                                                                for number, value in given)
                        calls_release = calls_release or template[0].startswith("call") and given_frames
                        documented = template[0].startswith("swi") and template[3] in BIOS_WRITES
                        if template[0].startswith("swi") and given_frames:
                            swi_writes.add(BIOS_WRITES.get(template[3], (None, None))[1])
                        if stacked or held or documented and given_frames:
                            records.append(template[:-2] + (held, stacked, False))
                    strong = set()                                # words it certainly overwrites
                    covered = {}                                  # words -> bytes it certainly writes
                    for item in summary[5]:
                        key, delta = item[:2]
                        base = input_value(key)
                        if len(base) == 1 and pointers(base) == base:
                            token, = base
                            if token[0] == "F" and not owner(ctx, (token[1] + delta) & ~3):
                                at = token[1] + delta
                                if len(item) == 2 and not at & 3:
                                    strong.add(at)
                                elif len(item) > 2:
                                    covered[at & ~3] = covered.get(at & ~3, 0) | 1 << (at & 3)
                            elif token[0] == "A" and mode == PROBE:
                                definite.add((token[1], token[2] + delta) + item[2:])
                    carried.clear()
                    for off, tokens in summary[4]:               # what it leaves below the SP here
                        value = mapped(tokens)
                        if value is None:
                            return None                          # walked here, where it is known
                        carried[sp + off] = normal(value)
                    for word, stored_value in weak.items():
                        # A word it may not write keeps what was there: probing, a word not yet
                        # written holds what earlier code left, as below the checked call's SP.
                        before = held_before(word)
                        if word in strong:
                            before = EMPTY
                        elif covered.get(word):           # probing: those bytes hold what it wrote
                            before = without_early(before) | marked(early(before) & ~covered[word])
                        memory[word] = normal(before | EMPTY | stored_value)
                        touched(word)
                    if release:
                        # Code it does not walk may also hand back what it finds through those
                        # addresses in the objects here, which the probe did not see: wherever the
                        # probe has it hand back an input (a value holding an input's address).
                        writes = None if calls_release or None in swi_writes or not swi_writes else \
                            "copies" if "copies" in swi_writes else "computes"
                        if self.trace is not None:
                            self._applying = (destination, sp)
                        extra = released(release, arguments=False, where=sorted(release_sites), surely=False,
                                         bios=not calls_release, writes=writes)
                        if extra:
                            def handed(tokens, value):
                                return bounded(normal(value | extra), spans) if any(
                                    is_argument(token) for token in tokens) else value
                            new = [value if returned[number] == frozenset({("A", number, 0)}) else
                                   handed(returned[number], value) for number, value in enumerate(new)]
                            for off, tokens in summary[4]:
                                if sp + off in carried:
                                    carried[sp + off] = handed(tokens, carried[sp + off])
                    if mode != PROBE and self.trace is not None:
                        here = ((root, 0),) + tuple((level[0], level[2]) for level in ctx)
                        bounds_ = [first for first, _ in marks] + [len(records)]
                        for index_, record in enumerate(records):
                            spot = [at for (first, at), last in zip(marks, bounds_[1:]) if first <= index_ < last]
                            # an index at the call itself is the caller's; the rest are the callee's
                            self.trace.append((record, spot[0], here + ((destination, sp),)) if spot else
                                              (record, sp, here))
                    if mode != PROBE:
                        for record in records:
                            if record[0].endswith("+"):
                                self.recursion.setdefault(template_site(record), set()).add(destination)
                    (exits["premises"] if mode == PROBE else self.premises).update(records)
                    return new

                carried = {}

                def skip(new):
                    """Continue after a call skipped with its summary."""
                    summary = self.isolation(destination)
                    returned = summary[1]
                    for number in range(13):
                        if returned[number] != frozenset({("A", number, 0)}):
                            forget(number)              # its value, range and compare are gone
                        regs[number] = new[number]
                    regs[14] = EMPTY
                    forget(14)
                    constants.pop(KNOWN_FLAGS, None)
                    constants.pop(COMPARED, None)
                    before = dict(memory)
                    # A word below SP that it does not surely write keeps what it held, frame
                    # addresses and watched values included; below where code it does not walk (or a
                    # recursion's deeper levels) may write words it does not list, the word may hold
                    # what that code left too (stale).  Probing, a word not yet written stays so
                    # (what its caller had there).
                    if summary[6] is not None:
                        reach = sp + summary[6]
                        if mode == PROBE:
                            exits["clobbers"] = reach if exits["clobbers"] is None else max(exits["clobbers"], reach)
                        for off in [off for off in memory if off < reach]:
                            memory[off] = normal(memory[off] | STALE)
                    for key in [key for key in constants if key >= SAVED - INF and key - SAVED < sp]:
                        del constants[key]
                    if mode in (ROOT, CONT):
                        forget_escaped()        # its stores through pointers it loads are not in a summary
                    for off, value in carried.items():           # the words the summary says it leaves
                        mask = early(value)
                        if mask:
                            # A word it may not have written keeps what it held: probing, what this
                            # walk wrote there, or what its caller had (still marked); in the walk,
                            # what the word held.
                            value = without_early(value)
                            if mode == PROBE:
                                held = before.get(off, EARLY)
                                value |= without_early(held) | marked(early(held) & mask)
                            else:
                                value |= before.get(off, STALE)
                        memory[off] = normal(value)
                    if not decodable(function, site + 4) and not self.isolation(destination)[2]:
                        return []                 # a callee that never returns, followed by data
                    return [after]

                def inline():
                    if len(ctx) >= MAX_DEPTH:
                        if mode == PROBE:
                            raise _NotIsolated
                        refuse(function, f"calls nested too deeply to check at 0x{site:08X}")
                    regs[14] = frozenset({("R", len(ctx) + 1)})
                    return [(ctx + ((destination, site + 4, sp),), destination)]

                if mode == PROBE:
                    if destination is None:
                        # Premised like any unresolved call, where the summary is used with
                        # dependent words in the frames.
                        exits["premises"].add(("call", function, site, self.chain(target, constants),
                                               self.destination(target, constants), passed(), sp))
                    else:
                        new = apply()
                        return inline() if new is None else skip(new)
                elif mode == KNOWN:
                    pass
                elif exposed and destination is not None:
                    if regs[FLAGS] or any(taints(regs[number]) for number in range(13)):
                        return inline()
                    new = apply()
                    return inline() if new is None else skip(new)
                elif exposed:
                    arguments_refused("an indirect call", registers, stacked)
                    self.premises.add(("call", function, site, self.chain(target, constants),
                                       self.destination(target, constants),
                                       tuple(n for n in registers if n in CALLEE_SAVED) +
                                       ((12,) if scratch() else ()), tuple(stacked),
                                       bool(regs[FLAGS])))
                # What code that is not walked may hand back of the frame addresses it was given.
                if mode != KNOWN:
                    forget_escaped()
                    given = frozenset().union(*(frames(regs[number]) for number in (0, 1, 2, 3, 12)),
                                              *(frames(memory[off]) for off in memory
                                                if sp <= off < entry_sp and off not in pushed))
                    if given:
                        escaped.add(("kept", function, site, None, INF, tuple(sorted(given, key=repr))))
                handed = released() if mode != KNOWN else frozenset()
                for number in (0, 1, 2, 3):
                    regs[number] = EMPTY | handed
                regs[12] = normal(regs[12] | EMPTY | handed)    # it need not write IP
                regs[14] = EMPTY
                # No register value is carried across a call that is not walked; what a push
                # saved is (that code does not write pushed words).
                for key in [key for key in constants if key < SAVED - INF]:
                    del constants[key]
                if mode == KNOWN:
                    unknown_words()
                forget_below_sp()
                if destination is not None and not decodable(function, site + 4) and \
                        (self.isolation(destination) or (0, 0, True))[2] is False:
                    return []               # a callee that never returns, followed by data
                return [after]

            if mnemonic == "push":
                listed = [register(operand) for operand in operands]
                sp -= 4 * len(listed)
                for index, number in enumerate(listed):
                    store(("exact", sp + 4 * index), 4, regs[number], "a push")
                    pushed.add(sp + 4 * index)
                    # What is known of a plain number saved here comes back with the pop.
                    facts = (constants.get(number), constants.get(RANGES - number), constants.get(SIGNED - number))
                    if number < 13 and facts != (None, None, None) and not pointers(regs[number]) and \
                            not taints(regs[number]):
                        constants[SAVED + sp + 4 * index] = facts
            elif mnemonic == "pop":
                listed = [register(operand) for operand in operands]
                if not bottomless and sp + 4 * len(listed) > entry_sp:
                    refuse(function, f"pop below the entry SP at 0x{site:08X}")
                destination = None
                for index, number in enumerate(listed):
                    popped = load(("exact", sp + 4 * index), 4)
                    if number == 15:
                        destination = popped
                    else:
                        regs[number] = popped
                        forget(number)
                        facts = constants.get(SAVED + sp + 4 * index)
                        if facts is not None and not pointers(popped) and not taints(popped):
                            for key, fact in zip((number, RANGES - number, SIGNED - number), facts):
                                if fact is not None:
                                    constants[key] = fact
                    constants.pop(SAVED + sp + 4 * index, None)
                sp += 4 * len(listed)
                if destination is not None:
                    successors = transfer(destination)
            elif mnemonic in ("add", "sub") and operands[0].type == ARM_OP_REG and register(operands[0]) == 13:
                last = operands[-1]
                if last.type == ARM_OP_IMM:
                    amount = last.imm
                elif last.type == ARM_OP_REG and register(last) in constants and not live(regs[register(last)]):
                    amount = constants[register(last)]        # ldr rN,=imm; add sp,rN (a large frame)
                    if amount & 0x80000000:
                        mnemonic, amount = ("sub" if mnemonic == "add" else "add"), -amount & FULL
                else:
                    refuse(function, f"unmodelled SP adjustment at 0x{site:08X}")
                if amount % 4:
                    refuse(function, f"unaligned SP adjustment at 0x{site:08X}")
                sp += amount if mnemonic == "add" else -amount
                if not bottomless and sp > entry_sp:
                    refuse(function, f"SP release above the entry SP at 0x{site:08X}")
            elif mnemonic in ("mov", "movs", "adds", "lsls") and len(operands) in (2, 3) and \
                    operands[1].type == ARM_OP_REG and register(operands[1]) != 15 and \
                    (len(operands) == 2 and mnemonic in ("mov", "movs") or
                     len(operands) == 3 and operands[2].type == ARM_OP_IMM and operands[2].imm == 0):
                destination, source = register(operands[0]), register(operands[1])
                copied = value(operands[1])
                if destination == 13:
                    exact = [token[1] for token in copied if type(token) is tuple and token[0] == "F"]
                    if len(copied) != 1 or len(exact) != 1:
                        refuse(function, f"unmodelled SP write at 0x{site:08X}")
                    sp = exact[0]
                    if not bottomless and sp > entry_sp:
                        refuse(function, f"SP release above the entry SP at 0x{site:08X}")
                elif destination == 15:
                    if copied - {RET} and not any(type(token) is tuple and token[0] in ("L", "R")
                                                  for token in copied):
                        use(copied, "a computed branch")
                        if frames(stale(copied)):
                            refuse(function, f"a branch at 0x{site:08X} targets a frame address")
                        successors = [(ctx, point) for point in self.switch(data, function, end, site)]
                    else:
                        successors = transfer(copied)
                else:
                    write(destination, copied, constants.get(source), constants.get(RANGES - source),
                          constants.get(SIGNED - source))
                    if WIDE - source in constants and RANGES - destination in constants:
                        constants[WIDE - destination] = True
                    if mnemonic != "mov":                    # movs, adds #0, lsls #0 set N and Z
                        set_flags("NZ", bool(taints(copied)))
                        if mnemonic == "adds":
                            set_flags("CV", False)
            elif mnemonic in ("mov", "movs") and len(operands) == 2 and operands[1].type == ARM_OP_IMM:
                write(register(operands[0]), EMPTY, operands[1].imm)
                if mnemonic == "movs":
                    set_flags("NZ", False)
            elif mnemonic in WIDTH and len(operands) == 2 and operands[1].type == ARM_OP_MEM:
                memory_operand = operands[1].mem
                base, data_register = register(memory_operand.base), register(operands[0])
                width, stored = WIDTH[mnemonic], mnemonic.startswith("str")
                if base == 15:
                    literal = ((site + 4) & ~3) + memory_operand.disp
                    if stored or mnemonic != "ldr" or not function <= literal <= end - 4:
                        refuse(function, f"literal outside the indexed span at 0x{site:08X}")
                    write(data_register, EMPTY, struct.unpack_from("<I", data, literal - function)[0])
                else:
                    base_value = frozenset({("F", sp)}) if base == 13 else regs[base]
                    use(base_value, "a memory access base")
                    if memory_operand.index:
                        index = register(memory_operand.index)
                        offset_value = regs[index]
                        use(offset_value, "a memory access index")
                        offset = constants.get(index) if not frames(offset_value) else None
                        span = range_of(index) if offset is None else None
                        if span is not None and WIDE - index in constants and any(
                                overruns(token[1] + span[1], token[1] + span[2]) for token in pointers(base_value)
                                if type(token) is tuple and token[0] == "F"):
                            span = None                     # an unknown index (INDEX_PREMISE)
                        if span is not None and span[2] - span[1] <= MAX_RANGE and pointers(base_value) and \
                                all(type(token) is tuple and token[0] == "F" for token in pointers(base_value)):
                            # base + index with a proved range: the frame words it may reach
                            base_value = frozenset(("FR", token[1] + span[1], token[1] + span[2], span[3])
                                                   if type(token) is tuple and token[0] == "F" else token
                                                   for token in base_value)
                            offset = 0
                        location = where(base_value, offset_value if offset is None else offset)
                        if location is None and frames(offset_value):
                            if vague_in(offset_value):
                                refuse(function, f"an access at 0x{site:08X} goes through a frame address of "
                                                 f"unknown provenance (not a stack array base plus an index)")
                            found = [extent(token, spans) for token in frames(offset_value)]
                            location = ("frame", False, (min(lo for lo, _ in found), max(hi for _, hi in found)), ())
                    else:
                        location = where(base_value, memory_operand.disp)
                    exact = location is not None and location[0] == "exact" and width == 4 and \
                        not location[1] & 3
                    if stored:
                        store(location, width, regs[data_register], surely=pointers(base_value) == base_value)
                        # What is known of a plain number stored to one frame word comes back with
                        # a word load from it, as with a push, until the word is written again.
                        facts = (constants.get(data_register), constants.get(RANGES - data_register),
                                 constants.get(SIGNED - data_register))
                        if exact and facts != (None, None, None) and not pointers(regs[data_register]) and \
                                not taints(regs[data_register]) and location[1] in memory:
                            constants[SAVED + location[1]] = facts
                    elif location is not None:
                        write(data_register, load(location, width, mnemonic in ("ldrsb", "ldrsh")),
                              span=narrow(mnemonic))
                        facts = constants.get(SAVED + location[1]) if exact else None
                        if facts is not None and not pointers(regs[data_register]) and \
                                not taints(regs[data_register]):
                            for key, fact in zip((data_register, RANGES - data_register, SIGNED - data_register),
                                                 facts):
                                if fact is not None:
                                    constants[key] = fact
                    else:
                        # A word read from ROM at a known address is a known value (a function
                        # pointer in a ROM table or variable resolves a call-via destination).
                        address = constants.get(base, -1) + memory_operand.disp
                        if mnemonic == "ldr" and not memory_operand.index and address % 4 == 0 and \
                                match.ROM_BASE <= address <= match.ROM_BASE + len(self.rom) - 4:
                            write(data_register, EMPTY,
                                  struct.unpack_from("<I", self.rom, address - match.ROM_BASE)[0])
                        else:
                            write(data_register, span=narrow(mnemonic))
            elif mnemonic in ("stm", "ldm"):
                base = register(operands[0])
                base_value = regs[base]
                use(base_value, "a block transfer base")
                listed = [register(operand) for operand in operands[1:]]
                start = where(base_value, 0)
                for index, number in enumerate(listed):
                    location = shifted(start, 4 * index)
                    if mnemonic == "stm":
                        store(location, 4, regs[number], "a block store", surely=pointers(base_value) == base_value)
                    elif location is not None:
                        write(number, load(location, 4))
                    else:
                        write(number)
                if mnemonic == "stm" or base not in listed:
                    write(base, address_of(shifted(start, 4 * len(listed))))
            elif mnemonic == "bl":
                target = operands[0].imm
                if function < target < end:
                    # agbcc's long jump inside a function, or a local call: LR is the return point.
                    successors = [(ctx, target)]
                    write(14, frozenset({("L", site + 4)}))
                else:
                    successors = call(target)
            elif mnemonic in ("svc", "swi"):
                for number in (0, 1, 2, 3):
                    use(regs[number], f"R{number} at a SWI")
                if mode == PROBE:
                    exits["premises"].add(("swi", function, site, operands[0].imm if operands else 0,
                                           passed(), sp))
                registers = [n for n in range(4, 12) if live(regs[n])]
                stacked = sorted(off - sp for off, word in memory.items() if taints(word))
                number_ = operands[0].imm if operands else 0
                given_frames = any(pointers(regs[n]) or fragment(regs[n]) for n in (0, 1, 2, 3)) or any(
                    pointers(word) or fragment(word) for off, word in memory.items()
                    if sp <= off < entry_sp and off not in pushed)
                if mode in (ROOT, CONT) and (registers or stacked or regs[FLAGS] or live(regs[12]) or
                                             number_ in BIOS_WRITES and given_frames):
                    arguments_refused("a SWI", registers, stacked)
                    self.premises.add(("swi", function, site, operands[0].imm if operands else 0,
                                       tuple(registers) + ((12,) if scratch() else ()), tuple(stacked),
                                       bool(regs[FLAGS])))
                handed = released(bios=True, writes=BIOS_WRITES.get(number_, (None, None))[1]) \
                    if mode != KNOWN else frozenset()
                for number in (0, 1, 2, 3):
                    regs[number] = EMPTY | handed
                regs[12] = normal(regs[12] | EMPTY | handed)    # the BIOS restores IP
                for key in [key for key in constants if key < SAVED - INF]:
                    del constants[key]
                if mode == KNOWN:
                    unknown_words()
                elif mode in (ROOT, CONT):
                    forget_escaped()
                forget_below_sp()
            elif mnemonic == "bx":
                successors = transfer(regs[register(operands[0])])
            elif mnemonic.startswith("b") and CS_GRP_JUMP in instruction.groups and \
                    len(operands) == 1 and operands[0].type == ARM_OP_IMM:
                branch = operands[0].imm
                if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
                    if regs[FLAGS] & frozenset(CONDITION_FLAGS[instruction.cc]):
                        refuse(function, f"a conditional branch at 0x{site:08X} tests flags set from "
                                         f"a watched callee-saved register's value")
                    if known_flags is not None:
                        successors = [(ctx, branch if condition(instruction.cc, known_flags)
                                       else site + instruction.size)]
                    elif compared_with is not None and range_of(compared_with[0]) is not None:
                        # The compared register's range on each edge; an empty one is infeasible.
                        import stack_index_precondition_profile as bounds
                        number, other, proved = compared_with
                        before = range_of(number)
                        taken, fallen = bounds.refine(CONDITION_CODES[instruction.cc], before, other)
                        # The bound a comparison with a proved value sets on an edge proves the
                        # range there, whether or not it cuts the range it found: the same
                        # comparison from any higher range bounds it on that edge too.
                        probe = (before[0], before[1], max(before[2], bounds.SIGNED_MAX), before[3])
                        capped = bounds.refine(CONDITION_CODES[instruction.cc], probe, other)
                        successors = [(ctx, target, {number: span}, proved and (span[2] < before[2] or
                                                                              cap is not None and cap[2] < probe[2]))
                                      for target, span, cap in ((branch, taken, capped[0]),
                                                                (site + instruction.size, fallen, capped[1]))
                                      if span is not None]
                    else:
                        successors = [(ctx, branch), (ctx, site + instruction.size)]
                else:
                    successors = [(ctx, branch)]
            elif mnemonic in ("cmp", "cmn", "tst"):
                if mode == PROBE:
                    # An input that decides a branch: where its caller knows its value, the walk
                    # there follows only the paths it takes (``"compared"``).
                    for operand in operands:
                        if operand.type == ARM_OP_REG:
                            exits["accesses"].update(("compared", token[1], 0, 0) for token in regs[register(operand)]
                                                     if type(token) is tuple and token[0] == "A" and
                                                     isinstance(token[1], int))
                for operand in operands:
                    # A dead frame address a callee returned may be compared: no access follows.
                    use(frozenset(token for token in value(operand) if token != DEAD and
                                  not (is_partial(token) and token[1] == DEAD)), "a comparison")
                # TST sets only N and Z; C and V keep what they depended on.
                set_flags("NZ" if mnemonic == "tst" else "NZCV", False)
                known = [operand.imm & FULL if operand.type == ARM_OP_IMM else
                         constants.get(register(operand)) for operand in operands]
                if mnemonic != "tst" and len(known) == 2 and None not in known:
                    constants[KNOWN_FLAGS] = compared(mnemonic, *known)
                if mnemonic == "cmp" and operands[0].type == ARM_OP_REG:
                    # Kept with the decided flags too: a join may drop those but keep this.
                    import stack_index_precondition_profile as bounds
                    other = bounds.const(operands[1].imm) if operands[1].type == ARM_OP_IMM else \
                        range_of(register(operands[1]))
                    if range_of(register(operands[0])) is not None and other is not None:
                        constants[COMPARED] = (register(operands[0]), other,
                                               operands[1].type == ARM_OP_IMM or
                                               WIDE - register(operands[1]) not in constants)
            elif mnemonic in ALU and operands[0].type == ARM_OP_REG and register(operands[0]) not in (13, 15) \
                    and all(operand.type in (ARM_OP_REG, ARM_OP_IMM) for operand in operands):
                self.alu(function, site, mnemonic, operands, regs, constants, write, set_flags, sp, range_of, spans,
                         inputs=mode == PROBE and self.leaf(root), overruns=overruns)
            else:
                read, written = instruction.regs_access()
                read = [register(number) for number in read]
                written = [register(number) for number in written]
                for number in read:
                    if number is not None and number not in (15,):
                        use(frozenset({("F", sp)}) if number == 13 else regs[number],
                            "an arithmetic or logical operation")
                        if number == 13 or number is not None and pointers(regs[number]):
                            if mode == PROBE:
                                raise _NotIsolated
                            refuse(function, f"unmodelled use of a frame address at 0x{site:08X}: "
                                             f"{instruction.mnemonic} {instruction.op_str}")
                if 13 in written or 15 in written:
                    refuse(function, f"unmodelled SP or PC write at 0x{site:08X}: "
                                     f"{instruction.mnemonic} {instruction.op_str}")
                for number in written:
                    if number is not None:
                        write(number)
            if mode == KNOWN and not ctx and site == until:
                continue                                    # the constants there are the answer
            pushed = {off for off in pushed if off >= sp}
            for key in [key for key in constants if key >= SAVED - INF and key - SAVED < sp]:
                del constants[key]                          # released by an SP adjustment
            outgoing = (tuple(regs), tuple(sorted(memory.items())), sp, tuple(sorted(constants.items())),
                        tuple(sorted(pushed)), tuple(sorted(escaped, key=repr)), tuple(sorted(definite, key=repr)))
            for successor in successors:
                if len(successor) == 4:               # a refined range on this edge
                    edge = dict(outgoing[3])
                    for number, span in successor[2].items():
                        edge.pop(number, None)
                        edge.pop(RANGES - number, None)
                        if successor[3]:
                            edge.pop(WIDE - number, None)
                        if span[1] == span[2]:
                            edge[number] = span[1]
                        else:
                            edge[RANGES - number] = span
                    enqueue(successor[0], successor[1], outgoing[:3] + (tuple(sorted(edge.items())),) + outgoing[4:])
                else:
                    enqueue(successor[0], successor[1], outgoing)
        if mode == ROOT:
            for function, site, words in exits["arguments written"]:
                if not set(words) <= exits["arguments read"]:
                    refuse(function, f"a store at 0x{site:08X} writes the owner's frame above the checked "
                                     f"callee's entry SP")
                self.premises.add(("args", function, site, words))
            return exits["copies"], exits["flags"]
        if mode == PROBE:
            return frozenset(exits["accesses"]), tuple(exits["registers"]), exits["returns"], \
                frozenset(exits["premises"]), tuple(sorted((exits["left"] or {}).items())), \
                tuple(sorted(exits["definite"] or (), key=repr)), exits["clobbers"]
        if mode == KNOWN:
            state = states.get(((), until))
            return dict(state[3]) if state else {}
        return None

    @staticmethod
    def alu(function, site, mnemonic, operands, regs, constants, write, set_flags, sp, range_of, spans,
            inputs=False, overruns=lambda lo, hi: True):
        def rebuilt(tokens):
            """An address rebuilt from bits: of unknown provenance; ("FX", ...) for bits read from
            words that may hold plain data instead (premised where used).  In the probe of a
            callee that calls nothing (``inputs``), arithmetic on its inputs stays tagged with
            them: where its caller's inputs are plain data, so is the result."""
            out = frozenset(token if type(token) is tuple and token[0] == "FU" else
                            ("FX",) + token[1:] if type(token) is tuple and token[0] in ("FL", "FX") else
                            ("AF", token[1], False) if inputs and type(token) is tuple and token[0] == "AF" else FV
                            for token in tokens if token != UNK)
            return out or frozenset({FV})

        """A Thumb-1 data-processing instruction: the result's dependence on watched values,
        bit by bit, the frame address it may be, the unsigned range of a plain-number result,
        and the condition flags it sets."""
        import stack_index_precondition_profile as bounds

        def span_of(item):
            if item.type == ARM_OP_IMM:
                return bounds.const(item.imm)
            return range_of(register(item)) if register(item) not in (13, 15) else None

        def wide(item):
            """Whether an operand's range is only a widened one (an unknown index)."""
            return item.type == ARM_OP_REG and WIDE - register(item) in constants
        def operand(item):
            if item.type == ARM_OP_IMM:
                return {}, item.imm & FULL, frozenset()
            number = register(item)
            if number == 15:
                return {}, None, frozenset()
            if number == 13:
                return {}, None, frozenset({("F", sp)})
            return taints(regs[number]), constants.get(number), \
                pointers(regs[number]) | bits(regs[number]) | lifted(regs[number])

        def scalar(item):
            """Whether the operand may be something other than an address the walk tracks."""
            if item.type != ARM_OP_REG or register(item) in (13, 15):
                return item.type == ARM_OP_IMM or register(item) == 15
            value = regs[register(item)]
            return len(pointers(value)) < len(value)

        name = ALU[mnemonic]
        destination = register(operands[0])
        if name in ("mvn", "neg"):
            a, b = operand(operands[1]), ({}, None, frozenset())
        elif len(operands) == 3:
            a, b = operand(operands[1]), operand(operands[2])
        else:
            a, b = operand(operands[0]), operand(operands[1])
        (ma, ca, fa), (mb, cb, fb) = a, b
        if name in ("mvn", "neg"):
            ra, rb = span_of(operands[1]), None
        elif len(operands) == 3:
            ra, rb = span_of(operands[1]), span_of(operands[2])
        else:
            ra, rb = span_of(operands[0]), span_of(operands[1])
        unproved = any(map(wide, [operands[1]] if name in ("mvn", "neg") else
                           operands[1:3] if len(operands) == 3 else operands[0:2]))
        either = merge(ma, mb)
        carry = None                                         # the shifter's carry-out dependence
        if name == "and":
            result = {n: m & cb for n, m in ma.items()} if cb is not None else \
                {n: m & ca for n, m in mb.items()} if ca is not None else either
        elif name == "orr":
            result = {n: m & ~cb for n, m in ma.items()} if cb is not None else \
                {n: m & ~ca for n, m in mb.items()} if ca is not None else either
        elif name == "bic":
            result = {n: m & ~cb for n, m in ma.items()} if cb is not None else \
                {n: m & ca for n, m in mb.items()} if ca is not None else either
        elif name in ("eor", "mvn"):
            result = either
        elif name in ("lsl", "lsr", "asr") and cb is not None and not mb and not fb:
            amount = cb & 0xFF
            sign = {n: FULL if m >> 31 else 0 for n, m in ma.items()}
            if amount == 0:
                result = ma                              # C unchanged
            elif amount >= 32:
                result = sign if name == "asr" else {}
                bit = 31 if name == "asr" else None if amount > 32 else 0 if name == "lsl" else 31
                carry = bool(bit is not None and any(m >> bit & 1 for m in ma.values()))
            else:
                result = {n: m << amount for n, m in ma.items()} if name == "lsl" else \
                    {n: m >> amount | (sign[n] << (32 - amount) if name == "asr" else 0) for n, m in ma.items()}
                bit = 32 - amount if name == "lsl" else amount - 1
                carry = any(m >> bit & 1 for m in ma.values())
        elif name in ("lsl", "lsr", "asr", "ror", "mul"):
            result = {n: FULL for n in either}                 # unknown amount, a rotate or a product
            # An unknown amount may be 0, which leaves C as it was.
            carry = bool(either) or (name != "mul" and "C" in regs[FLAGS])
        elif name in ("adc", "sbc") and "C" in regs[FLAGS]:
            refuse(function, f"a carry from a watched callee-saved register's value is used at 0x{site:08X}")
        else:                                                 # add, sub, adc, sbc, neg
            result = {n: upward(m) for n, m in either.items()}
        result = {n: m & FULL for n, m in result.items() if m & FULL}
        # The unsigned range of the result (an operand that may be an address counts as any number).
        wide = bounds.TOP
        sa, sb = ra if ra is not None else wide, rb if rb is not None else wide
        span = None
        if name == "and" and (ca is not None or cb is not None):
            mask, other = (cb, sa) if cb is not None else (ca, sb)
            span = bounds.norm("S", 0, min(mask, other[2]), 0)
        elif name in ("lsl", "lsr") and cb is not None and (cb & 0xFF) < 32:
            span = (bounds.shift_left if name == "lsl" else bounds.shift_right)(sa, cb & 0xFF)
        elif name == "lsr" and cb is not None:
            span = bounds.const(0)
        elif name == "add" and (ra is not None and rb is not None):
            span = bounds.add_values(ra, rb)
        elif name == "sub" and ra is not None and rb is not None and ra[1] >= rb[2]:
            span = bounds.norm("S", ra[1] - rb[2], ra[2] - rb[1], min(ra[3], rb[3]))
        # A result below RAM_BASE, or an arithmetic shift right by 7 or more (a value in
        # [-2**24, 2**24)), is no frame address.
        small = span is not None and span[2] < RAM_BASE or name == "asr" and cb is not None and (cb & 0xFF) >= 7

        def signed_of(item, unsigned):
            if item.type == ARM_OP_IMM:
                return item.imm & FULL, item.imm & FULL
            if register(item) in (13, 15):
                return None
            known = constants.get(SIGNED - register(item))
            if known is None and unsigned is not None and unsigned[2] < 1 << 31:
                known = unsigned[1], unsigned[2]
            return known
        if name in ("mvn", "neg"):
            za, zb = signed_of(operands[1], ra), None
        elif len(operands) == 3:
            za, zb = signed_of(operands[1], ra), signed_of(operands[2], rb)
        else:
            za, zb = signed_of(operands[0], ra), signed_of(operands[1], rb)
        srange = None                   # the signed range of a small result (a negative one too)
        if name == "add" and za and zb:
            srange = za[0] + zb[0], za[1] + zb[1]
        elif name == "sub" and za and zb:
            srange = za[0] - zb[1], za[1] - zb[0]
        elif name == "lsl" and za and cb is not None and (cb & 0xFF) < 32:
            srange = za[0] << (cb & 0xFF), za[1] << (cb & 0xFF)
        elif name == "asr" and za and cb is not None and (cb & 0xFF) < 32:
            srange = za[0] >> (cb & 0xFF), za[1] >> (cb & 0xFF)
        elif name == "neg" and za:
            srange = -za[1], -za[0]
        if srange is not None and not -(1 << 31) <= srange[0] <= srange[1] < 1 << 31:
            srange = None
        if srange is not None and srange[1] < RAM_BASE:
            small = True                # below RAM_BASE, or negative: no frame address
        if fa or fb:
            def signed(constant):
                return constant if constant < 0x80000000 else constant - (1 << 32)
            items = [operands[1]] if name in ("mvn", "neg") else \
                list(operands[1:3]) if len(operands) == 3 else list(operands[0:2])

            def known_of(item):
                """The bits of an operand that are the same for every frame address."""
                if item.type == ARM_OP_IMM:
                    return known_constant(item.imm)
                number = register(item)
                if number == 15:
                    return 0, 0
                if number == 13:
                    return known_frame(frozenset({("F", sp)}))
                if number in constants:
                    return known_constant(constants[number])
                return constants.get(KBITS - number) or known_frame(regs[number]) or (0, 0)
            known = known_op(name, known_of(items[0]), known_of(items[1]) if len(items) == 2 else (0, 0),
                             cb if name in ("lsl", "lsr", "asr") else None)

            def origin_of(item):
                """The frame addresses and probed inputs an operand derives from."""
                if item.type != ARM_OP_REG or register(item) == 15:
                    return frozenset()
                number = register(item)
                if number == 13:
                    return frozenset({("F", sp)})
                value = regs[number]
                if FS in value or vague_in(value) and ORIGIN - number not in constants:
                    return None                                  # bits whose source is not known
                return frozenset(token for token in value if type(token) is tuple and token[0] in ("F", "FR", "FW")) | \
                    frozenset(token[1] for token in value if is_fs(token) and len(token) > 1) | \
                    frozenset(("AF", token[1], False) for token in value if is_argument(token)) | \
                    (constants.get(ORIGIN - number, frozenset()) if vague_in(value) else frozenset())
            origins = [origin_of(item) for item in items]
            origin = None if None in origins else frozenset().union(*origins)
            if (known[0] | known[1]) == FULL and not result:
                # The same value for every frame address (x != 0, the IWRAM page, a shift that
                # leaves only the page bits): it carries no address.
                write(destination, EMPTY, constant=known[1])
            else:
                # Bits of an address: FS, or a probed input's arithmetic proved below RAM_BASE.
                bitlike = frozenset(token for token in fa | fb if token[0] in ("FS", "FL", "FX", "FU") or
                                    token[0] == "AF" and token[2])
                real_a, real_b = fa - bitlike, fb - bitlike
                if real_a or real_b:
                    # Bits of a frame address beside an address, plus an index: still bits of one,
                    # unless the index is a constant in RAM, from which an address could be rebuilt.
                    other = cb if real_a else ca
                    found = (rebuilt(bitlike) if other is not None and RAM_BASE <= other < 0x04000000
                             else frozenset(("AF", token[1], True) if token[0] == "AF" else token
                                            for token in bitlike)) if bitlike else frozenset()
                    if name == "add" and real_a and not fb and cb is not None and not mb:
                        address = frozenset(moved(token, signed(cb)) for token in real_a)
                    elif name == "add" and real_b and not fa and ca is not None and not ma:
                        address = frozenset(moved(token, signed(ca)) for token in real_b)
                    elif name == "sub" and real_a and not fb and cb is not None and not mb:
                        address = frozenset(moved(token, -signed(cb)) for token in real_a)
                    elif name == "add" and real_a and not real_b and rb is not None and not mb and \
                            rb[2] - rb[1] <= MAX_RANGE and all(token[0] == "F" for token in real_a) and \
                            not (unproved and any(overruns(token[1] + rb[1], token[1] + rb[2]) for token in real_a)):
                        address = frozenset(("FR", token[1] + rb[1], token[1] + rb[2], rb[3]) for token in real_a)
                    elif name == "add" and real_b and not real_a and ra is not None and not ma and \
                            ra[2] - ra[1] <= MAX_RANGE and all(token[0] == "F" for token in real_b) and \
                            not (unproved and any(overruns(token[1] + ra[1], token[1] + ra[2]) for token in real_b)):
                        address = frozenset(("FR", token[1] + ra[1], token[1] + ra[2], ra[3]) for token in real_b)
                    elif name in ("add", "sub") and len(items) == 2 and \
                            (real_a and not real_b or name == "add" and real_b and not real_a):
                        # A stack array base plus or minus an index (perhaps bits of an address): still
                        # in that array (INDEX_PREMISE).
                        address = frozenset(vague(token, spans) for token in real_a | real_b)
                    else:
                        # Any other arithmetic on a frame address (a shift, a mask, a sum of two): a
                        # number below RAM_BASE is bits of one (``FS``); anything else is an address of
                        # unknown provenance, and an access through it refuses.
                        # The difference of two frame addresses is a distance within the stack, no
                        # address.
                        # Of two tracked frame addresses it is the same for every frame address.
                        distance = name == "sub" and len(items) == 2 and bool(real_a) and bool(real_b)
                        # So is the difference of two addresses within one probed input's object.
                        tracked = distance and not bitlike and \
                            (all(token[0] in ("F", "FR", "FW") for token in real_a | real_b) or
                             all(token[0] in ("A", "AV") for token in real_a | real_b) and
                             len({token[1] for token in real_a | real_b}) == 1)
                        address, found = (frozenset(), frozenset()) if tracked else \
                            (unknown_of(real_a | real_b | bitlike, small or distance) - EMPTY, frozenset())
                    address |= found
                elif small:
                    # Bits of an address stay bits: maybe bits (read where plain data may have been)
                    # only where every operand's are.
                    address = frozenset(token if is_fs(token) or token[0] == "FU" else
                                        ("FL",) + token[1:] if token[0] in ("FL", "FX") else
                                        ("AF", token[1], True) if token[0] == "AF" else bits_of(token)
                                        for token in fa | fb)
                elif name in ("add", "sub", "orr", "eor") and len(items) == 2 and bool(fa) != bool(fb):
                    # Bits of a frame address added to a value with no frame provenance address that
                    # value's object, unless that value is a constant in RAM, from which a frame address
                    # could be rebuilt.
                    other = cb if fa else ca
                    if other is not None and RAM_BASE <= other < 0x04000000:
                        address = rebuilt(fa | fb)
                    else:
                        # A probed callee's input bits plus a number it cannot bound: bits where the
                        # caller's input is bits of an address (the walk there may prove the sum
                        # below RAM_BASE and keep them), plain data where it is plain.
                        address = frozenset(("AF", token[1], True) for token in fa | fb if token[0] == "AF")
                else:
                    address = rebuilt(fa | fb)
                if FS in address and origin:
                    # Bits of what it was computed from: frame addresses, or a probed callee's
                    # inputs (bits of one, where the caller knows it).
                    address = (address - {FS}) | frozenset(("AF", source[1], True) if is_argument(source)
                                                           else bits_of(source) for source in origin)
                # The operand that may be a plain number keeps the result possibly one too.
                maybe = fa and scalar(items[0]) or len(items) == 2 and fb and scalar(items[1]) or not address
                # Bits of an address (an input's too) keep the range proved for them.
                bits_only = all(token[0] in ("FS", "FL") or token[0] == "AF" and token[2] for token in address)
                write(destination, tainted(result, frozenset()) | address | (EMPTY if maybe else frozenset()),
                      span=span if bits_only else None, signed=srange if bits_only else None)
                if known != (0, 0) and not maybe and not result:
                    constants[KBITS - destination] = known      # for a later step (x != 0)
                if FV in address and origin:
                    constants[ORIGIN - destination] = origin
        else:
            write(destination, tainted(result), span=span, signed=srange)
        if RANGES - destination in constants and unproved:
            constants[WIDE - destination] = True             # derived from an unknown index
        if mnemonic == "add":                                 # high-register or SP/PC add: no flags
            return
        set_flags("NZ", bool(result))
        if name in ("add", "sub", "adc", "sbc", "neg"):
            set_flags("CV", bool(either))
        elif carry is not None:
            set_flags("C", carry)

    @staticmethod
    def switch(data, target, end, site):
        """The case targets of the agbcc word switch whose dispatch ends at ``site``.

        Only the kit's own switch recognisers are used: the guarded word table of
        ``analyze.refinement_word_switch`` (also with one interposed pool word), a pool with
        interposed words or backward cases (``match.switch_layout``), and the preloaded
        table pointer (``match.preloaded_switch_layout``)."""
        import analyze

        def targets(descriptor):
            return sorted({target + addend for word, addend in descriptor["relocations"]
                           if word != descriptor["literal"]})

        for options in ({}, {"one_object_word_switch": True}):
            descriptor = analyze.refinement_word_switch(data, target, site, end, _ENGINE,
                                                        same_owner_long_branches=True, **options)
            if descriptor is not None and target + descriptor["dispatch"] + 8 == site:
                return targets(descriptor)

        def table(literal, bound):
            if literal is None or not 0 <= literal <= len(data) - 4 or (target + literal) % 4:
                return None
            pointer = struct.unpack_from("<I", data, literal)[0] - target
            if pointer != literal + 4 or literal + 8 + 4 * bound > len(data):
                return None
            return {offset: struct.unpack_from("<I", data, offset)[0] - target
                    for offset in range(literal, literal + 8 + 4 * bound, 4)}

        def instruction(offset):
            if not 0 <= offset <= len(data) - 2:
                return None
            found = next(_ENGINE.disasm(data[offset:offset + 2], target + offset, 1), None)
            return found if found is not None and found.size == 2 else None

        dispatch = site - target - 8
        load = instruction(dispatch + 2)
        if load is not None and load.mnemonic == "ldr" and load.operands[1].type == ARM_OP_MEM and \
                register(load.operands[1].mem.base) == 15:
            literal = (((target + dispatch + 6) & ~3) + load.operands[1].mem.disp) - target
            for guard in (4, 6, 8):
                compare = instruction(dispatch - guard)
                if compare is None or compare.mnemonic != "cmp" or compare.operands[1].type != ARM_OP_IMM:
                    continue
                relocations = table(literal, compare.operands[1].imm)
                if relocations is None:
                    continue
                for layout in ({"allow_backward_cases": True}, {"interposed_pool": True}):
                    try:
                        descriptor = match.switch_layout(data, target, relocations, **layout)
                    except ValueError:
                        continue
                    if descriptor["dispatch"] == dispatch:
                        return targets(descriptor)
        literal = site - target + 8                      # the preloaded layout's table pointer
        encoding = match.preloaded_switch_encoding(data, target, literal)
        if encoding is not None:
            relocations = table(literal, encoding[4])
            if relocations is not None:
                # The layout needs the pool's one object word; only its position matters here.
                word = struct.unpack_from("<I", data, literal - 4)[0] if literal >= 4 else None
                try:
                    descriptor = match.preloaded_switch_layout(data, target, relocations,
                                                               {literal - 4: ("pool_word", word)})
                except (ValueError, struct.error):
                    descriptor = None
                if descriptor is not None and target + descriptor["dispatch"] + 6 == site:
                    return targets(descriptor)
        refuse(target, f"a computed branch at 0x{site:08X} is not a recognised word switch")


_CHECKERS = weakref.WeakKeyDictionary()


class Context:
    """The ROM and function mapping of a walk that has no buffer proof (a report replay that
    repeats the check its issuance made with one)."""

    def __init__(self, rom, entries):
        self.rom, self.entries = rom, entries


_PARENTS = weakref.WeakKeyDictionary()


def delegate(child, parent):
    """Make the check of a delegate proof (one a proof builds to inspect a callee for it) part
    of ``parent``'s, so the premises it records are stated in the parent's report."""
    _PARENTS[child] = parent


def checker_for(proof):
    """The memoised checker of one buffer proof (its ROM and function mapping)."""
    while proof in _PARENTS:
        proof = _PARENTS[proof]
    checker = _CHECKERS.get(proof)
    if checker is None or checker.rom is not proof.rom:
        checker = _CHECKERS[proof] = Checker(proof.rom, proof.entries)
        attach_image(checker, proof)
    return checker


def attach_image(checker, proof):
    """Give ``checker`` the boot IWRAM image of ``proof`` (iwram_image_profile), when the rule applies to
    it: every checker a buffer proof walks with, its own (checker_for) and the call-via target rule's
    crossing checkers, resolves and reads the image the same way."""
    import iwram_image_profile as iwram_image
    if iwram_image.applies(proof):
        checker.image_span = iwram_image.watch_span(proof)
        checker.image_target = iwram_image.watch_target(proof)
    return checker


def core_check(proof, caller, site, target, registers, constants=None):
    """Check a core-walk call at ``site`` in ``caller`` while the capstone ``registers`` (in
    R4-R11) hold frame aliases, and the caller's code after it.  The core's own constants
    are not used: it carries R4-R11 values across calls, and this check does not."""
    from capstone.arm import ARM_REG_R0
    watched = frozenset(register - ARM_REG_R0 for register in registers
                        if ARM_REG_R0 + 4 <= register <= ARM_REG_R0 + 11)
    if watched:
        checker_for(proof).call(target, watched, caller=caller, site=site)


def merged_premises(records):
    """One record per site: the registers and words a site relies on in any context."""
    sites = {}
    for record in records:
        if record[0] == "dangling":
            sites[record] = ()
            continue
        cut = 3 if record[0] in ("stale", "stale+", "rebuilt", "rebuilt+", "bytes", "bytes+",
                                 "unset", "unset+", "args") else \
            4 if record[0] in ("index", "index+", "swi", "swi+", "escape", "bits") else 5
        head, rest = record[:cut], record[cut:]
        if record[0] in ("index", "index+", "escape", "bits", "stale", "stale+", "rebuilt", "rebuilt+",
                         "bytes", "bytes+", "unset", "unset+", "args"):
            old = sites.get(head, ((),) * len(rest))
            sites[head] = tuple(tuple(sorted(set(a) | set(b))) for a, b in zip(old, rest))
            continue
        registers, stacked, flagged = sites.get(head, ((), (), False))
        sites[head] = (tuple(sorted(set(registers) | set(rest[0]))), tuple(sorted(set(stacked) | set(rest[1]))),
                       flagged or rest[2])
    return [head + rest for head, rest in sorted(sites.items(), key=repr)]


def premise_lines(proof):
    """One report line per call or SWI admitted under ``PREMISE`` or ``BIOS_PREMISE``, per indexed
    stack access admitted under ``INDEX_PREMISE``, per stale reach (``STALE_PREMISE``) and per
    escape (``ESCAPE_PREMISE``) while verifying with ``proof``, and one fact line per escape a
    global may still hold when its frame is released."""
    while proof in _PARENTS:
        proof = _PARENTS[proof]
    try:
        checker = _CHECKERS.get(proof)
    except TypeError:          # no weak reference, so never a proof the walk ran with
        return []
    if checker is None:
        return []
    lines = []
    for record in merged_premises(checker.premises):
        first = len(lines)
        try:
            if record[0].startswith("stale"):
                _, function, site, words = record
                lines.append(f"{PREMISE_PREFIX} code not walked from 0x{site:08X} in 0x{function:08X} can reach the "
                             f"uninitialised, partly overwritten or unknown-provenance frame word{'s' if len(words) > 1 else ''} at "
                             f"{','.join(f'sp{offset:+d}' for offset in words)}; {STALE_PREMISE}")
                continue
            if record[0] == "args":
                _, function, site, words = record
                lines.append(f"{PREMISE_PREFIX} store at 0x{site:08X} in 0x{function:08X} above its entry SP, to the "
                             f"word{'s' if len(words) > 1 else ''} at "
                             f"{','.join(f'entry SP+{offset}' for offset in words)}; {ARGS_PREMISE}")
                continue
            if record[0].startswith("unset"):
                kind_, function, site, words = record
                depth = " at any recursion depth" if kind_.endswith("+") else ""
                lines.append(f"{PREMISE_PREFIX} word load at 0x{site:08X} in 0x{function:08X}{depth} of the frame "
                             f"word{'s' if len(words) > 1 else ''} at {','.join(f'sp{offset:+d}' for offset in words)}, "
                             f"which may not have been written before it; {UNSET_PREMISE}")
                continue
            if record[0].startswith("bytes"):
                kind_, function, site, words = record
                depth = " at any recursion depth" if kind_.endswith("+") else ""
                lines.append(f"{PREMISE_PREFIX} narrow load at 0x{site:08X} in 0x{function:08X}{depth} of the frame "
                             f"word{'s' if len(words) > 1 else ''} at {','.join(f'sp{offset:+d}' for offset in words)}, "
                             f"which may hold plain data or part of a frame address; {READ_PREMISE}")
                continue
            if record[0].startswith("rebuilt"):
                kind_, function, site, words = record
                depth = " at any recursion depth" if kind_.endswith("+") else ""
                lines.append(f"{PREMISE_PREFIX} word load at 0x{site:08X} in 0x{function:08X}{depth} of the frame "
                             f"word{'s' if len(words) > 1 else ''} at {','.join(f'sp{offset:+d}' for offset in words)}, "
                             f"which a narrow store through a stack array address may have partly overwritten while "
                             f"{'they' if len(words) > 1 else 'it'} held a frame address; {REBUILT_PREMISE}")
                continue
            if record[0] == "escape":
                _, function, site, target, addressed, stacked = record
                words = ",".join(f"sp{offset:+d}" for offset in stacked)
                relied = f", with the frame word{'s' if len(stacked) > 1 else ''} at {words} depending on owner " \
                         f"stack addresses" if stacked else ""
                lines.append(f"{PREMISE_PREFIX} address of the frame word{'s' if len(addressed) > 1 else ''} at "
                             f"{','.join(f'sp{offset:+d}' for offset in addressed)} stored to {target} at 0x{site:08X} "
                             f"in 0x{function:08X}{relied}; {ESCAPE_PREMISE}")
                continue
            if record[0] == "bits":
                _, function, site, target, addressed, stacked = record
                words = ",".join(f"sp{offset:+d}" for offset in stacked)
                relied = f", with the frame word{'s' if len(stacked) > 1 else ''} at {words} depending on owner " \
                         f"stack addresses" if stacked else ""
                lines.append(f"{PREMISE_PREFIX} bits of the address of the frame word{'s' if len(addressed) > 1 else ''} "
                             f"at {','.join(f'sp{offset:+d}' for offset in addressed)} stored to {target} at "
                             f"0x{site:08X} in 0x{function:08X}{relied}; {BITS_PREMISE}")
                continue
            if record[0] == "dangling":
                _, function, site, target, returner, at = record
                lines.append(f"{FACT_PREFIX} {target} may still hold the frame address stored at 0x{site:08X} in "
                             f"0x{function:08X} when 0x{returner:08X} returns at 0x{at:08X}, releasing that frame; "
                             f"{DANGLING_FACT}")
                continue
            if record[0].startswith("index"):
                kind_, function, site, kind, excluded = record
                words = ",".join(f"sp{offset:+d}" for offset in excluded)
                depth = " at any recursion depth" if kind_.endswith("+") else ""
                invariant = f"; game-state invariant: {GAME_STATE_INVARIANTS[site]}" if site in GAME_STATE_INVARIANTS else ""
                lines.append(f"{PREMISE_PREFIX} indexed stack {kind} at 0x{site:08X} in 0x{function:08X}{depth}, excluding "
                             f"the frame word{'s' if len(excluded) > 1 else ''} at {words} (saved, released or in "
                             f"another function's frame); {INDEX_PREMISE}{invariant}")
                continue
            depth = " at any recursion depth" if record[0].endswith("+") else ""
            if record[0].startswith("call"):
                _, function, site, chain, destination, registers, stacked, flagged = record
                through = " then ".join(f"_call_via_r{link}" if link < 16 else f"the bx r3 at 0x{link:08X}"
                                        for link in chain)
                where = "to an unknown address" if destination is None else \
                    f"resolved to 0x{destination:08X} ({region(destination)})"
                head, premise = f"call at 0x{site:08X} in 0x{function:08X}{depth} through {through} {where}", PREMISE
            else:
                _, function, site, number, registers, stacked, flagged = record
                routine = f" ({BIOS_WRITES[number][0]})" if number in BIOS_WRITES else ""
                head = f"SWI 0x{number:02X}{routine} at 0x{site:08X} in 0x{function:08X}{depth}"
                premise = bios_premise(number)
            saved = [register for register in registers if register != 12]
            parts = [",".join(f"R{register}" for register in saved)] if saved else []
            if stacked:
                words = ",".join(f"sp{offset:+d}" for offset in stacked)
                parts.append(f"the frame word{'s' if len(stacked) > 1 else ''} at {words}")
            if flagged:
                parts.append("the condition flags")
            relied = f"with {' and '.join(parts)} depending on owner stack addresses" if parts else \
                "given frame addresses"
            if 12 in registers:
                relied = (f"{relied} and" if parts else "with") + " R12 holding a frame address a callee returned"
                if record[0].startswith("call"):     # at a SWI the BIOS dispatcher saves and restores R12
                    premise = f"{premise.replace(', and returns', ', returns')}, and {R12_PREMISE}"
            lines.append(f"{PREMISE_PREFIX} {head}, {relied}; {premise}")
        finally:
            if record[0].endswith("+"):        # stated at several depths: what the claim covers
                site = template_site(record)
                lines[first:] = [recursion_text(line, site, checker.recursion.get(site, ()),
                                                checker.recursive.get(site, ()), checker.frames) for line in lines[first:]]
    return lines


def recursion_text(line, site, callees, recursive, frames):
    """A line of a site that a summary states at several depths: the recursions it runs at every
    depth of, with their frames, and what the claim covers.  The words named are offsets from the
    SP of the site's shallowest execution; every word of the stack between an execution's SP and
    the entry of the callee whose summary states the site is covered too, as a summary converges
    only on words it names from one SP (``collapsed``)."""
    def name(function):
        return f"0x{function:08X}"
    loops = sorted(recursive)
    if loops:
        depth = " at every recursion depth of " + " and of ".join(
            name(function) + (f" (a frame of {-frames[function]} bytes)" if frames.get(function) else "")
            for function in loops)
    else:
        depth = " at several call depths"
    within = f" in 0x{site[0]:08X}"
    line = line.replace(" at any recursion depth", depth, 1) if " at any recursion depth" in line else \
        line.replace(within, within + depth, 1)
    entry = " or ".join(name(function) for function in sorted(callees)) or "the summarised callee"
    return (f"{line}; the claim covers the frame words named, at offsets from the SP of the site's "
            f"shallowest execution, and every word of the stack between the SP of each execution and the "
            f"entry of {entry} (the callee whose summary states this site), not only the words a walk reached")


def region(address):
    """The GBA memory region of an address outside the ROM image."""
    regions = {0x00: "BIOS", 0x02: "EWRAM", 0x03: "IWRAM", 0x04: "I/O", 0x05: "palette RAM",
               0x06: "VRAM", 0x07: "OAM", 0x0E: "SRAM", 0x0F: "SRAM"}
    page = address >> 24
    if 0x0A <= page <= 0x0D:
        return "ROM mirror"
    if 0x08 <= page <= 0x09:
        return "ROM space beyond the image"
    return regions.get(page, "unmapped")
