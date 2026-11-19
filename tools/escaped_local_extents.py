"""Escaped-local extents for the allowlisted volatile semantic check.

volatile_semantics makes every local frame byte observable once a stack
address escapes (a call argument or a stored value): from then on each frame
store is a trace event, each escape snapshots the whole frame, and a frame
load after a call reads whatever the call left.  That is sound, but it also
compares the compiler's spill slots, which no C code can reach, so a real
and a stripped compile that allocate their spills differently are refused
although they behave the same (0x0811B3B0: `str r2, [sp, #0x30]` spills a
byte in one compile and an address in the other).

When main's check has refused, this rule re-runs it once with the frame
split in two: the named locals the escaping addresses point into stay
observable exactly as before, and every other slot of the function's own
frame stays internal, as it is before any escape.  The extents come from
the compiler, not from guesses: each compile is repeated with `-g`, its
DWARF 2 debug information gives every named local's frame offset, size and
scope, and the rule applies only when that compile's code is the checked
compile's code.

Obligations, each enforced by a refusal (any refusal keeps main's verdict
and main's message):

1. Same code.  The `-g` compile's .text equals the checked compile's, and
   its parsed instruction stream (labels resolved to positions, literal
   pools to their words) equals the checked one.
   "the -g compile's code differs from the checked compile's"
2. Known layout.  The DWARF has one compile unit whose DIE tree parses in
   full, the function's subprogram has frame base DW_OP_reg13 (sp), and
   every local and parameter of it lives in a register, at a static
   address, nowhere, or at DW_OP_fbreg with a known type size; lexical
   blocks give their code range by labels the function defines.  Inlined
   subroutines and other location forms fail.
   "unsupported debug information: ..."
3. agbcc's frame shape (frame_shape).  Pushes of callee-saved registers
   and lr and high-register moves, then at most one sp decrement, open the
   function; sp changes nowhere else but in epilogues: the matching
   increment, then only pops, r8-r11 restores and the return, entered from
   no label.  An adjustment is an immediate, a literal-pool word, or agbcc's
   `mov`/`lsl` pair.  So sp is the body sp (the DWARF frame base) at every
   call, escape and internal access, and no callee's frame overlaps this
   one.  No named local lies below the body sp or overlaps the saved
   registers.  A pushed argument register (agbcc's varargs prologue pushes
   r0-r3, which the body addresses as data) is no saved register, as in
   volatile_semantics' push area.
   "the stack pointer moves outside the prologue and epilogue" /
   "a named local lies below sp or overlaps the saved registers" /
   "the prologue pushes an argument register"
4. Exact owner.  Every escaping frame address (a call argument, an unnamed
   argument register the callee may read, a stored value) is the body sp
   plus a constant strictly inside exactly one named local whose scope
   covers the escaping instruction; a local it is one past the end of (in
   any scope) escapes with it.  A compiler temporary or a slot outside every local
   fails.
   "escaped frame address sp+X is not inside exactly one named local in scope"
5. Closure.  At every escape, a frame address stored to a frame slot that
   is not internal escapes too, by rule 4; so does one stored there later.
   Such a slot must be an escaped local or a word passed as a stack
   argument, whose readers are listed (rule 8); an incoming-argument word,
   a slot below sp or a variable offset is refused.
   "a frame address is stored to a frame slot outside the named locals"
6. Internal slots.  A frame access is internal only after an escape, at
   the body sp plus a constant, inside [body sp, lowest saved register
   slot), and overlapping no escaped local and no word passed as a stack
   argument to any call so far.  Everything else keeps main's model.
7. No hidden frame contents.  A load of an internal slot must find an
   exact earlier store of the same width (or none).  A frame load that is
   not forwarded (it stopped at a call, or found no store) refuses if an
   untraced store outside the escaped locals - to an internal slot, or to
   the frame before an escape - may overlap it; so no internal value, and
   no frame address kept in one, comes back as an unknown.  A frame read
   before any escape (volatile_semantics' frame_read, kit#346) is no such
   load: its event binds every store it could see.  Every other stored
   frame address has escaped its locals (rules 4 and 5).  A variable frame
   offset overlaps every frame slot but the saved registers (C bounds,
   premise 2): before an escape exactly main's push area (a load of the
   exact word its push still holds), after one every byte a push still
   holds (saved_area), where main keeps only the exact pushed word.
   Known conservative refusal: an untraced store that a later store has
   overwritten still refuses a load it may overlap (a saved slot
   overwritten after an escape, then reloaded past a store at a variable
   offset; agbcc never stores into the push area).
   When a store at a variable frame offset precedes an escape, the escape
   event also binds, in program order, every such store and every constant
   store into an escaped local (in place of main's binding of every local
   byte, since the other slots stay internal), and the record names
   main's frame-read premises.
   "partially overlapping stack access"
8. Consumers.  Every consumer of an escaping frame address is recorded: a
   callee and the register (or stack-argument word) it receives the
   address in, the RAM word it is stored to, or the escaped local or
   stack word it is kept in, with the instruction.  A store target must
   be proven ordinary RAM (a constant or a data symbol in EWRAM or IWRAM),
   never I/O (a DMA source), ROM or an unknown pointer.  memcpy with a
   constant byte count that keeps the access inside the owning local is a
   proven consumer, but only when the ROM copy helper it links to matches
   its pinned SHA-256 and the source defines no memcpy of its own; it
   returns its destination, which stays a tracked frame address.  Every
   other consumer is listed in the report as premised (premise 1).
   "a frame address is stored to X, which is not proven ordinary RAM"
9. A screen for untracked frame addresses, not a proof.  After an escape,
   a store outside the stack whose value contains a load from the frame,
   a result (r0-r3) of a call that was itself handed a frame address, or
   a word load whose memory version is such a call, may go only to proven
   RAM (a word store of it is listed); and a memcpy from the frame whose
   bytes may hold a frame address (one stored in range, or any earlier
   call handed a frame address) may copy only to the frame or to proven
   RAM (then listed).
   "a value that may be a frame address is stored to X, which is not
   proven ordinary RAM" / "memcpy copies frame bytes that may hold a frame
   address to X, which is not proven ordinary RAM"
   Not screened: a frame address that a premised consumer leaves in memory
   and this function reads back in pieces (halfwords, bytes), after a
   later call or store, as the result of a later call, or copies with a
   memcpy from non-frame memory, then hands to hardware.  Those routes rest
   on premise 1 through the premised consumer, which the report lists
   (tests pin each of them).

Internal slots then behave as main treats the whole frame before an
escape: stores are not trace events, loads forward across calls, and a
pointer that does not carry the stack pointer is disjoint from them.  That
needs the premises in Policy.premises, printed in every report that relies
on the rule, with its premised consumers.
"""

import hashlib
import re

import volatile_semantics as semantics
from volatile_semantics import SemanticError, SP, carries, is_stack, linear, signed32

NAME = "escaped-local-extents-v1"
LABELS = ("real", "stripped", "layout-perturbed")
# C's memcpy, by name: the pointer argument registers and the register of the byte count; with a
# constant count inside the owner the access extent is proven, not premised.  The name is the
# compiler's memcpy, linked by the byte match to the ROM's copy helper, which match.py checks
# against its pinned SHA-256 (COPY_HELPER) before the contract may be used.
COPY_CONTRACTS = {"memcpy": {"r0": "r2", "r1": "r2"}}
COPY_HELPER = (0x081443FC, 0x0814445E,
               "aa822d873bad381a62e3c3e07b06003a41beea59bc3edc791f7e316eb08b7ebb")
RAM = ((0x02000000, 0x02040000), (0x03000000, 0x03008000))


class Policy:
    """the one switch a maintainer needs: enabled = False restores main's refusals"""

    name = NAME
    enabled = True
    premises = (
        "each premised consumer listed (a callee given an escaped frame address in the register "
        "named, the RAM word it is stored to, or the local it is kept in, at the instruction "
        "named), and any code reached through a pointer such a consumer keeps, reads and writes "
        "the locals listed with it only within their declared extents, and the decomp's "
        "declared types are the original's; hardware (DMA, BIOS block transfers) gets a frame "
        "address only through such a consumer; a proven consumer is a memcpy, linked to the "
        "pinned ROM copy helper, with a constant count inside its local (C's memcpy contract)",
        "a pointer this function does not compute from sp (an argument, a literal, a value loaded "
        "from memory or returned by a call) addresses no frame byte outside the escaped locals, as "
        "main assumes for the whole frame before an escape; and a variable frame offset reaches "
        "no saved-register slot (C bounds; main assumes the same of the pushed callee-saved "
        "registers and lr)",
        "a callee reads or writes no stack word beyond the stack arguments its prototype names "
        "and takes no input in r4-r11 (the ARM calling convention), as main already assumes "
        "before an escape",
        "the DWARF 2 information of a -g compile whose code is byte-identical gives each named "
        "local's frame slot from the body sp and the code range of its scope",
    )


POLICY = Policy()


# ------------------------------------------------------------------ DWARF 2

def debug_sections(text):
    """{section: [byte or (symbol,) placeholder]} for cc1's .debug_abbrev and .debug_info"""
    sections, current = {}, None
    for raw in text.splitlines():
        line = raw.split("@", 1)[0].strip() if not raw.lstrip().startswith(".ascii") else raw.strip()
        found = re.match(r"\.section\s+([.\w]+)", line)
        if found:
            current = found[1]
            sections.setdefault(current, [])
            continue
        if re.fullmatch(r"\.(?:text|data|bss)\b.*", line):
            current = None
            continue
        if current not in (".debug_abbrev", ".debug_info") or not line:
            continue
        if re.fullmatch(r"[.\w$]+:", line):
            continue
        found = re.fullmatch(r"\.(byte|2byte|4byte)\s+(.+)", line)
        if found:
            size = {"byte": 1, "2byte": 2, "4byte": 4}[found[1]]
            for operand in found[2].split(","):
                operand = operand.strip()
                if re.fullmatch(r"-?(?:0x[0-9a-fA-F]+|\d+)", operand):
                    value = int(operand, 0)
                    if not -(1 << (8 * size - 1)) <= value < 1 << (8 * size):
                        raise SemanticError(f"unsupported debug information: {line}")
                    sections[current] += list((value & ((1 << 8 * size) - 1)).to_bytes(size, "little"))
                elif re.fullmatch(r"[.\w$]+", operand):
                    sections[current] += [(operand,)] + [None] * (size - 1)
                else:
                    raise SemanticError(f"unsupported debug information: {line}")
            continue
        found = re.fullmatch(r'\.ascii\s+"((?:[^"\\]|\\.)*)"', line)
        if found:
            sections[current] += list(found[1].encode("latin-1").decode("unicode_escape")
                                      .encode("latin-1"))
            continue
        raise SemanticError(f"unsupported debug information: {line}")
    return sections


def _byte(data, at):
    value = data[at]
    if not isinstance(value, int):
        raise SemanticError("unsupported debug information: a symbol where a number belongs")
    return value


def _uleb(data, at):
    result = shift = 0
    while True:
        value = _byte(data, at)
        at += 1
        result |= (value & 0x7F) << shift
        shift += 7
        if not value & 0x80:
            return result, at


def _sleb(data, at):
    result = shift = 0
    while True:
        value = _byte(data, at)
        at += 1
        result |= (value & 0x7F) << shift
        shift += 7
        if not value & 0x80:
            return (result - (1 << shift) if value & 0x40 else result), at


def _number(data, at, size):
    if isinstance(data[at], tuple):
        return data[at]                     # a symbol (a code label)
    return int.from_bytes(bytes(_byte(data, at + n) for n in range(size)), "little")


FIXED = {0x01: 4, 0x05: 2, 0x06: 4, 0x07: 8, 0x0B: 1, 0x0C: 1, 0x10: 4, 0x11: 1, 0x12: 2, 0x13: 4}
REFERENCES = (0x11, 0x12, 0x13)


def debug_entries(text):
    """{offset: (tag, attributes, children offsets)} and the root offsets of one DWARF 2 unit"""
    sections = debug_sections(text)
    abbreviations, info = sections.get(".debug_abbrev"), sections.get(".debug_info")
    if not abbreviations or not info:
        raise SemanticError("unsupported debug information: no DWARF 2 sections")
    table, at = {}, 0
    while at < len(abbreviations):
        code, at = _uleb(abbreviations, at)
        if code == 0:
            break
        tag, at = _uleb(abbreviations, at)
        children = _byte(abbreviations, at)
        at += 1
        attributes = []
        while True:
            name, at = _uleb(abbreviations, at)
            form, at = _uleb(abbreviations, at)
            if not name and not form:
                break
            attributes.append((name, form))
        if code in table:
            raise SemanticError("unsupported debug information: a repeated abbreviation")
        table[code] = (tag, children, attributes)
    if any(isinstance(byte, tuple) for byte in abbreviations[at:]) or \
            any(byte for byte in abbreviations[at:]):
        raise SemanticError("unsupported debug information: data after the abbreviations")
    length = _number(info, 0, 4)
    if not isinstance(length, int) or length + 4 != len(info) or _number(info, 4, 2) != 2 or \
            _number(info, 6, 4) != (".debug_abbrev",) or _byte(info, 10) != 4:
        raise SemanticError("unsupported debug information: not one DWARF 2 unit")
    entries, roots, parents, at = {}, [], [], 11
    while at < len(info):
        start = at
        code, at = _uleb(info, at)
        if code == 0:
            if not parents:
                raise SemanticError("unsupported debug information: unbalanced entries")
            parents.pop()
            continue
        if code not in table:
            raise SemanticError("unsupported debug information: an unknown abbreviation")
        tag, children, forms = table[code]
        attributes = {}
        for name, form in forms:
            if form in FIXED:
                value = _number(info, at, FIXED[form])
                at += FIXED[form]
            elif form == 0x08:
                end = at
                while _byte(info, end):
                    end += 1
                value = bytes(info[at:end]).decode("latin-1")
                at = end + 1
            elif form in (0x0A, 0x03, 0x04, 0x09):
                if form == 0x09:
                    size, at = _uleb(info, at)
                else:
                    width = {0x0A: 1, 0x03: 2, 0x04: 4}[form]
                    size = _number(info, at, width)
                    at += width
                value = bytes(_byte(info, at + n) for n in range(size))
                at += size
            elif form == 0x0D:
                value, at = _sleb(info, at)
            elif form == 0x0F:
                value, at = _uleb(info, at)
            else:
                raise SemanticError(f"unsupported debug information: attribute form {form:#x}")
            if form in REFERENCES:
                value = ("ref", value)
            attributes[name] = value
        entries[start] = (tag, attributes, [])
        (entries[parents[-1]][2] if parents else roots).append(start)
        if children:
            parents.append(start)
    if parents:
        raise SemanticError("unsupported debug information: unbalanced entries")
    return entries, roots


TYPE_TAGS = {0x01, 0x04, 0x0F, 0x10, 0x13, 0x15, 0x16, 0x17, 0x21, 0x24, 0x26, 0x35, 0x0D, 0x28,
             0x18, 0x05}


def type_size(entries, reference, active=()):
    """the byte size of the type a DW_AT_type reference names, or None"""
    if not (isinstance(reference, tuple) and reference[0] == "ref") or reference[1] in active \
            or reference[1] not in entries:
        return None
    tag, attributes, children = entries[reference[1]]
    if 0x0B in attributes:
        return attributes[0x0B] if isinstance(attributes[0x0B], int) else None
    if tag == 0x0F:                         # pointer
        return 4
    if tag in (0x16, 0x26, 0x35):           # typedef, const, volatile
        return type_size(entries, attributes.get(0x49), active + (reference[1],))
    if tag == 0x01:                         # array
        size = type_size(entries, attributes.get(0x49), active + (reference[1],))
        ranges = [entries[child] for child in children]
        if size is None or not ranges or any(entry[0] != 0x21 for entry in ranges):
            return None
        for _, bounds, _ in ranges:
            lower, upper = bounds.get(0x22, 0), bounds.get(0x2F)
            if not isinstance(lower, int) or not isinstance(upper, int) or upper < lower:
                return None
            size *= upper - lower + 1
        return size
    return None


class Local:
    """a named local or parameter with a frame home: [offset, offset + size) from the body sp,
    live on the instruction positions of its scope"""

    def __init__(self, name, offset, size, scope):
        self.name, self.offset, self.size, self.scope = name, offset, size, scope

    def live(self, position):
        return all(start <= position < end for start, end in self.scope)

    def __repr__(self):
        return f"{self.name}@{self.offset:+#x}/{self.size}"


def frame_locals(entries, roots, name, labels):
    """the frame-homed locals of function `name` (Local list)"""
    subprograms = [offset for root in roots for offset in entries[root][2]
                   if entries[offset][0] == 0x2E and entries[offset][1].get(0x03) == name]
    if len(subprograms) != 1:
        raise SemanticError(f"unsupported debug information: {len(subprograms)} subprograms for {name}")
    tag, attributes, children = entries[subprograms[0]]
    if attributes.get(0x40) != b"\x5d":
        raise SemanticError("unsupported debug information: the frame base is not sp")
    found = []

    def walk(children, scope):
        for child in children:
            tag, attributes, grandchildren = entries[child]
            if tag in (0x34, 0x05):         # variable, formal parameter
                location = attributes.get(0x02)
                if location is None or (len(location) == 1 and 0x50 <= location[0] <= 0x6F) or \
                        (len(location) == 5 and location[0] == 0x03):
                    continue                # nowhere, a register, a static address
                if not isinstance(location, bytes) or not location or location[0] != 0x91:
                    raise SemanticError("unsupported debug information: a local's location")
                offset, end = _sleb(list(location), 1)
                size = type_size(entries, attributes.get(0x49))
                if end != len(location) or not size:
                    raise SemanticError("unsupported debug information: a frame local's size")
                found.append(Local(attributes.get(0x03, "?"), offset, size, scope))
            elif tag == 0x0B:               # lexical block
                low, high = attributes.get(0x11), attributes.get(0x12)
                if not (isinstance(low, tuple) and isinstance(high, tuple) and
                        low[0] in labels and high[0] in labels and labels[low[0]] <= labels[high[0]]):
                    raise SemanticError("unsupported debug information: a block's code range")
                walk(grandchildren, scope + ((labels[low[0]], labels[high[0]]),))
            elif tag in TYPE_TAGS or tag in (0x0A, 0x18):
                continue                    # types, labels and `...` hold no storage
            else:
                raise SemanticError(f"unsupported debug information: entry tag {tag:#x} in {name}")

    walk(children, ())
    return found


def canonical(function):
    """an instruction stream with labels resolved, comparable across label numberings"""
    instructions, labels, pools = function

    def word(value):
        if isinstance(value, tuple) and value and value[0] == "code":
            return ("code", labels.get(value[1], value[1])) + value[2:]
        return value

    def operand(text):
        found = re.fullmatch(r"(\.L\w+)(.*)", text)
        if found and found[1] in labels:
            return ("label", labels[found[1]], found[2])
        if found and found[1] in pools:
            return ("pool", tuple(word(value) for value in pools[found[1]]), found[2])
        return text

    return [(mnemonic, tuple(operand(text) for text in operands))
            for mnemonic, operands, _ in instructions]


def sp_adjustment(instructions, at, pools):
    """(bytes added to sp, instructions used) for `add sp, sp, #imm`/`sub sp, #imm`,
    `ldr rX, <pool word>; add sp, sp, rX` or `mov rX, #a; lsl rX, rX, #b; add sp, sp, rX`
    at position at, else None"""
    mnemonic, operands, _ = instructions[at]
    if mnemonic in ("add", "sub") and operands[0] == "sp" and len(operands) in (2, 3) and \
            (len(operands) == 2 or operands[1] == "sp"):
        value = semantics.immediate(operands[-1])
        if value is not None:
            value = signed32(value)
            return (value if mnemonic == "add" else -value), 1
    if mnemonic == "ldr" and at + 1 < len(instructions):
        found = re.fullmatch(r"(\.L\w+)", operands[1]) if len(operands) == 2 else None
        words = pools.get(found[1]) if found else None
        following, arguments, _ = instructions[at + 1]
        if words and isinstance(words[0], int) and following == "add" and \
                arguments in (["sp", operands[0]], ["sp", "sp", operands[0]]):
            return semantics.signed32(words[0]), 2
    if mnemonic == "mov" and len(operands) == 2 and at + 2 < len(instructions):
        value = semantics.immediate(operands[1])
        (shift, shifted, _), (following, arguments, _) = instructions[at + 1], instructions[at + 2]
        amount = semantics.immediate(shifted[-1]) if shift == "lsl" and \
            shifted[:-1] in ([operands[0]], [operands[0], operands[0]]) else None
        if value is not None and amount is not None and following == "add" and \
                arguments in (["sp", operands[0]], ["sp", "sp", operands[0]]):
            return value << amount, 3
    return None


def writes_sp(mnemonic, operands):
    if mnemonic in ("push", "pop"):
        return True
    if mnemonic.rstrip("s") in ("mov", "add", "sub", "ldr", "neg", "mvn", "and", "orr", "eor",
                                "bic", "mul", "lsl", "lsr", "asr", "ror") and operands and \
            operands[0] == "sp":
        return True
    return bool(operands) and operands[0].rstrip("!") == "sp" and mnemonic.startswith(("ldm", "stm"))


def frame_shape(function):
    """(saved bytes, frame bytes) of agbcc's frame: pushes (of no argument register) and
    high-register moves, then at most one sp decrement, open the function; sp changes nowhere
    else but in epilogues (the matching increment, then only pops, register moves and the
    return, entered from no label)"""
    instructions, labels, pools = function
    targets = set(labels.values())
    at, saved = 0, 0
    while at < len(instructions):
        mnemonic, operands, _ = instructions[at]
        if mnemonic == "push":
            names = semantics.register_list(operands[0])
            if set(names) & set(semantics.ARGUMENT_REGISTERS):
                # their slots are data a variable offset may reach, not saved registers
                # (volatile_semantics keeps no argument register private either)
                raise SemanticError("the prologue pushes an argument register")
            saved += 4 * len(names)
        elif not (mnemonic == "mov" and len(operands) == 2 and
                  semantics.register(operands[1]) in ("r8", "r9", "r10", "r11")):
            break
        at += 1
    frame = 0
    adjustment = sp_adjustment(instructions, at, pools) if at < len(instructions) else None
    if adjustment is not None and adjustment[0] < 0:
        frame, at = -adjustment[0], at + adjustment[1]
    while at < len(instructions):
        mnemonic, operands, _ = instructions[at]
        adjustment = sp_adjustment(instructions, at, pools)
        if not ((adjustment is not None and frame and adjustment[0] == frame) or
                (adjustment is None and mnemonic == "pop" and not frame)):
            if adjustment is not None or writes_sp(mnemonic, operands):
                raise SemanticError("the stack pointer moves outside the prologue and epilogue")
            at += 1
            continue
        # an epilogue: [the increment], then pops and register moves up to the return,
        # with no label after its first instruction
        start, at = at, at + (adjustment[1] if adjustment is not None else 0)
        while True:
            if at >= len(instructions) or any(start < target <= at for target in targets):
                raise SemanticError("an epilogue is entered from a label or does not return")
            mnemonic, operands, _ = instructions[at]
            at += 1
            if mnemonic == "bx" or (mnemonic == "pop" and "pc" in semantics.register_list(operands[0])):
                break
            if mnemonic != "pop" and not (mnemonic == "mov" and len(operands) == 2 and
                                          semantics.register(operands[0]) in ("r8", "r9", "r10", "r11")):
                raise SemanticError("an epilogue does more than restore registers")
    return saved, frame


class FrameModel:
    """one compile's named frame locals for one function; state() starts a path.

    base and top are the body sp and the lowest saved-register slot, as offsets
    from the entry sp (frame_shape)."""

    def __init__(self, function, label, frame, parsed, objects=None, contracts=True):
        saved, size = frame_shape(parsed)
        self.contracts = COPY_CONTRACTS if contracts else {}
        self.objects = dict(objects or {})  # data symbol -> address, to prove RAM store targets
        self.consumers = set()              # (kind, text): every consumer of an escaped address
        self.function, self.label, self.locals = function, label, list(frame)
        self.top, self.base = -saved, -saved - size
        for local in self.locals:
            start = self.base + local.offset
            if local.offset < 0 or (start < self.top + saved and self.top < start + local.size):
                raise SemanticError(f"a named local lies below sp or overlaps the saved registers "
                                    f"({local!r})")
        self.escaped = set()                # every local some path let escape

    def state(self):
        return FrameState(self)


def frame_models(label, assembly, debug_assembly, objects=None, contracts=True):
    """{(label, function): FrameModel} for one compile and its -g twin"""
    plain, _ = semantics.parse_assembly(assembly)
    debug, _ = semantics.parse_assembly(debug_assembly)
    if sorted(plain) != sorted(debug) or any(canonical(plain[name]) != canonical(debug[name])
                                            for name in plain):
        raise SemanticError("the -g compile's code differs from the checked compile's")
    if set(plain) & set(COPY_CONTRACTS):
        raise SemanticError("the source defines its own memcpy")
    entries, roots = debug_entries(debug_assembly)
    models = {}
    for name in sorted(plain):
        labels = debug[name][1]
        models[(label, name)] = FrameModel(name, label, frame_locals(entries, roots, name, labels),
                                           plain[name], objects, contracts)
    return models


# ------------------------------------------------------------- the executor

class FrameState:
    """per path: the escaped locals and the stack argument words"""

    def __init__(self, model):
        self.model, self.base, self.top = model, model.base, model.top
        self.escaped, self.visible = [], []
        self.receiving = set()              # trace events of calls handed a frame address

    def at_body(self, executor, text, what):
        sp = executor.regs["sp"]
        if not is_stack(sp) or signed32(linear(sp)[0]) != self.base:
            executor.fail(text, f"{what} with the stack pointer away from the body's")

    def escape(self, executor, pointers, text):
        """the locals the pointers address escape, and so does every frame address stored
        where an escaped local, a callee or an unknown pointer can read it"""
        self.at_body(executor, text, "a frame address escapes")
        pending, seen, kept = list(pointers), set(), []
        while pending:
            while pending:
                pointer = pending.pop()
                if pointer in seen:
                    continue
                seen.add(pointer)
                if not is_stack(pointer):
                    executor.fail(text, "a stack address escapes at a variable offset")
                at = signed32(linear(pointer)[0]) - self.base
                live = [local for local in self.model.locals if local.live(executor.pc)]
                owners = [local for local in live if local.offset <= at < local.offset + local.size]
                if len(owners) != 1:
                    executor.fail(text, f"escaped frame address sp{at:+#x} is not inside exactly "
                                  "one named local in scope")
                # it may also be one past the end of the local before it (in any scope)
                for local in owners + [local for local in self.model.locals
                                       if at == local.offset + local.size]:
                    if local not in self.escaped:
                        self.escaped.append(local)
                        self.model.escaped.add(local)
            for entry in executor.memory:
                if entry[0] == "store" and not entry[5] and carries(entry[2], SP) and \
                        carries(entry[3], SP) and not self.private(executor, entry[2], entry[1]) and \
                        entry[3] not in seen:
                    self.frame_target(executor, entry[2], entry[1], text)
                    pending.append(entry[3])
                    kept.append(entry)
        for entry in kept:
            self.kept(executor, entry[2], entry[3])

    def owners(self, executor, pointer):
        """the local an escaping frame address is strictly inside, and those it is one past"""
        at = signed32(linear(pointer)[0]) - self.base
        inside = [local for local in self.model.locals
                  if local.offset <= at < local.offset + local.size and local.live(executor.pc)]
        return at, inside, [local for local in self.model.locals if at == local.offset + local.size]

    @staticmethod
    def named(inside, past):
        return ", ".join([local.name for local in inside] + [f"one past {local.name}" for local in past])

    def frame_target(self, executor, address, width, text):
        """a frame address may be kept in the frame only where its readers are listed:
        an internal slot, an escaped local, or a word passed as a stack argument"""
        start = signed32(linear(address)[0]) if is_stack(address) else None
        if start is None or not (self.inside_escaped(address, width) or
                                 any(low <= start and start + width <= high for low, high in self.visible)):
            executor.fail(text, "a frame address is stored to a frame slot outside the named locals")

    def ram(self, address):
        """the address when it is proven ordinary RAM (a constant or a data symbol), else None"""
        constant, terms = linear(address)
        if terms:
            (term, factor), = terms.items() if len(terms) == 1 else ((None, None),)
            if factor != 1 or not (isinstance(term, tuple) and term[0] == "sym") or \
                    term[1] not in self.model.objects:
                return None
            constant += self.model.objects[term[1]]
        constant &= 0xFFFFFFFF
        return constant if any(low <= constant < high for low, high in RAM) else None

    def tainted(self, value):
        """a value that may be a frame address no one tracks: one read back from the frame, a
        result of a call handed a frame address, or a word of memory read after such a call"""
        if not isinstance(value, tuple):
            return False
        if value and value[0] == "load" and len(value) == 4:
            width, address, version = value[1], value[2], value[3]
            if (isinstance(address, tuple) and address[:1] == ("frame",)) or carries(address, SP) or \
                    (width == 4 and isinstance(version, tuple) and version[:1] == ("call",) and
                     version[1] in self.receiving):
                return True
        if value and value[0] in ("ret", "clobber") and value[1] in self.receiving:
            return True
        return any(self.tainted(part) for part in value if isinstance(part, tuple))

    def stored(self, executor, address, value, width, text):
        """a store outside the frame after an escape: a value that may be an untracked frame
        address may not reach anything but proven RAM, and a word of it there is listed"""
        if not self.escaped or not self.tainted(value):
            return
        if self.ram(address) is None:
            executor.fail(text, f"a value that may be a frame address is stored to "
                          f"{semantics.show(address)}, which is not proven ordinary RAM")
        if width == 4:
            self.model.consumers.add(("premised", f"word that may be a frame address stored to "
                                      f"{semantics.show(address)} at #{executor.pc}"))

    def kept(self, executor, address, value):
        """list a frame address kept in an escaped local or a stack-argument word"""
        at, inside, past = self.owners(executor, value)
        start = signed32(linear(address)[0]) - self.base
        holders = [local.name for local in self.escaped
                   if local.offset <= start < local.offset + local.size] or [f"stack word sp{start:+#x}"]
        self.model.consumers.add(("premised", f"kept in {', '.join(holders)} at #{executor.pc}: "
                                  + self.named(inside, past)))

    def returned(self, executor, target, arguments):
        """memcpy returns its destination (C's contract): keep it a tracked frame address"""
        if isinstance(target, str) and target in self.model.contracts and arguments:
            executor.regs["r0"] = arguments[0]

    def consumers(self, executor, target, values, text):
        """record every consumer of an escaping frame address: values are (register, value) of
        a call (target) or a store (target None, the stored-to address in values[0][0]).
        A memcpy/memset whose constant count keeps the access inside the owner is proven;
        any other consumer is listed with the premise that it stays inside the owner."""
        site = f"#{executor.pc}"
        if target is None:
            (address, value), = values
            if self.ram(address) is None:
                executor.fail(text, f"a frame address is stored to {semantics.show(address)}, which "
                              "is not proven ordinary RAM (I/O, ROM or an unknown pointer)")
            at, inside, past = self.owners(executor, value)
            self.model.consumers.add(("premised", f"stored to {semantics.show(address)} at {site}: "
                                      + self.named(inside, past)))
            return
        callee = target if isinstance(target, str) else semantics.show(target[1]) \
            if target[0] == "via" else f"swi {target[1]}"
        contract = self.model.contracts.get(target) if isinstance(target, str) else None
        arguments = dict(values)
        if contract:                        # before this call joins the receiving calls
            self.copied(executor, callee, arguments, site, text)
        if any(carries(value, SP) for _, value in values):
            self.receiving.add(len(executor.trace))
        for register, value in values:
            if not carries(value, SP):
                continue
            at, inside, past = self.owners(executor, value)
            owner = inside[0]
            if contract and register in contract:
                count = arguments.get(contract[register])
                if type(count) is int and 0 < count and at + count <= owner.offset + owner.size:
                    self.model.consumers.add(("proven", f"{callee} {register} at {site}: {owner.name} "
                                              f"+{at - owner.offset:#x}, {count} bytes"))
                    continue
            self.model.consumers.add(("premised", f"{callee} {register} at {site}: "
                                      + self.named(inside, past)))

    def copied(self, executor, callee, arguments, site, text):
        """memcpy from the frame copies whatever the source bytes hold: if they may hold a frame
        address (one stored there, or anything a call handed a frame address may have left),
        the destination must be the frame or proven RAM, and the copy is listed"""
        source, destination, count = arguments.get("r1"), arguments.get("r0"), arguments.get("r2")
        if source is None or not carries(source, SP):
            return
        start = signed32(linear(source)[0]) if is_stack(source) else None
        span = count if type(count) is int and start is not None else None
        holds = bool(self.receiving) or span is None or any(
            entry[0] == "store" and carries(entry[3], SP) and carries(entry[2], SP) and
            (not is_stack(entry[2]) or (signed32(linear(entry[2])[0]) < start + span and
                                        start < signed32(linear(entry[2])[0]) + entry[1]))
            for entry in executor.memory)
        if not holds:
            return
        if not carries(destination, SP) and self.ram(destination) is None:
            executor.fail(text, f"{callee} copies frame bytes that may hold a frame address to "
                          f"{semantics.show(destination)}, which is not proven ordinary RAM")
        if not carries(destination, SP):
            self.model.consumers.add(("premised", f"frame bytes that may hold a frame address "
                                      f"copied by {callee} to {semantics.show(destination)} at {site}"))

    def ordering(self, executor):
        """the escape snapshot applies constant stores in order but sees no store at a variable
        frame offset, which may land on an escaped local before or after them: when there is
        one, the escape also binds every such store and every constant store into an escaped
        local, in program order (as volatile_semantics.show_stores prints them)"""
        stores = [entry for entry in executor.memory if entry[0] == "store" and not entry[5] and
                  carries(entry[2], SP)]
        if not any(not is_stack(entry[2]) for entry in stores):
            return ()
        return (tuple(("store", executor.observed(entry[2]) if is_stack(entry[2]) else entry[2], entry[1],
                       entry[3])
                      for entry in stores if not is_stack(entry[2]) or
                      any(self.escaped_byte(signed32(linear(entry[2])[0]) + byte) for byte in range(entry[1]))),)

    def inside_escaped(self, address, width):
        """every byte of a constant frame access lies in escaped locals (the escape snapshots
        compared them, and a call may change them)"""
        if not is_stack(address):
            return False
        start = signed32(linear(address)[0])
        return all(self.escaped_byte(start + byte) for byte in range(width))

    def escaped_byte(self, offset):
        return any(self.base + local.offset <= offset < self.base + local.offset + local.size
                   for local in self.escaped)

    def saved_area(self, executor, address, width):
        """inside the saved-register slots [top, entry sp), every byte still holding its push: a
        byte that any other fixed-slot store has overwritten, or that a pop has released, is
        local, as in volatile_semantics' push area (kit#346).  That area (load's saved) also
        requires the exact pushed word; relation uses it alone before an escape, and this test
        only after one.  Under frame_shape the release test and the fail-closed end are defence
        in depth: pushes fill [top, 0) before any access, and the only loads after a pop are
        the pops' own exact reads"""
        if not is_stack(address):
            return False
        start = signed32(linear(address)[0])
        if not (self.top <= start and start + width <= 0):
            return False
        for byte in range(start, start + width):
            for entry in reversed(executor.memory):
                if entry[0] == "release" and byte < entry[1]:
                    return False
                if entry[0] == "store" and is_stack(entry[2]) and \
                        signed32(linear(entry[2])[0]) <= byte < signed32(linear(entry[2])[0]) + entry[1]:
                    if not entry[5]:
                        return False
                    break
            else:
                return False                # not pushed yet: fail closed
        return True

    def private(self, executor, address, width):
        if not is_stack(address):
            return False
        sp = executor.regs["sp"]
        if not is_stack(sp) or signed32(linear(sp)[0]) != self.base:
            return False
        start = signed32(linear(address)[0])
        end = start + width
        if start < self.base or end > self.top:
            return False
        if any(start < self.base + local.offset + local.size and self.base + local.offset < end
               for local in self.escaped):
            return False
        return not any(start < high and low < end for low, high in self.visible)

    def reload(self, executor, address, width, text):
        """a frame load that is not forwarded stopped at a call, or found no store: an untraced
        store outside the escaped locals (to an internal slot, or to the frame before an
        escape) that may overlap it would be hidden by the call, a frame address among them
        included: refuse.  Every other store of a frame address escaped its locals (rules 4
        and 5), so reading one back as an unknown value reaches only observable bytes."""
        for entry in executor.memory:
            if entry[0] == "store" and entry[4] is None and not self.inside_escaped(entry[2], entry[1]) \
                    and executor.relation(address, width, entry[2], entry[1]) != "disjoint":
                executor.fail(text, "partially overlapping stack access")

    def call(self, executor, count, text):
        self.at_body(executor, text, "a call")
        if count > 4:
            self.visible.append((self.base, self.base + 4 * (count - 4)))


# -------------------------------------------------------------- the driver

def retry(refusal, assemblies, debug_compile, compare, objects=None, rom=None):
    """re-run a refused check with escaped-local extents; the record lines, or raise refusal

    assemblies: {label: checked assembly}; debug_compile(label) -> the -g
    compile's assembly, after checking its .text against the checked one;
    compare() runs the check (volatile_semantics.compare) and returns its results.
    objects (or a callable giving it) maps data symbols to addresses, to prove RAM store targets.
    """
    if not POLICY.enabled:
        raise refusal
    try:
        objects = objects() if callable(objects) else objects
        start, end, digest = COPY_HELPER
        contracts = rom is not None and \
            hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() == digest
        models = {}
        for label in LABELS:
            if label in assemblies:
                models.update(frame_models(label, assemblies[label], debug_compile(label), objects,
                                           contracts))
        token = semantics.FRAME_MODELS.set(models)
        try:
            results = compare()
        finally:
            semantics.FRAME_MODELS.reset(token)
    except Exception:                       # anything unproven keeps main's verdict and message
        raise refusal from None
    return results, record(models)


def record(models):
    """the report line: per compile, the escaped locals and every consumer of their addresses
    (proven or premised), then the premises"""
    groups = {}
    for label in LABELS:
        for (owner, name), model in sorted(models.items()):
            if owner != label or not model.escaped:
                continue
            shown = ", ".join(repr(local) for local in
                              sorted(model.escaped, key=lambda local: (local.offset, local.name)))
            for kind in ("premised", "proven"):
                listed = sorted(text for which, text in model.consumers if which == kind)
                if listed:
                    shown += f"; {kind} consumers: " + "; ".join(listed)
            groups.setdefault((name, shown), []).append(label)
    escaped = [f"{' and '.join(labels)} `{name}`: {shown}" for (name, shown), labels in groups.items()]
    return (f"* allowlisted volatile escaped-local extents ({NAME}): after a frame address escapes, "
            "only the named locals it reaches stay observable (slots from each compile's -g twin, "
            "code identical); " + (" | ".join(escaped) or "no local escaped") + "; premises: " +
            "; ".join(f"({n}) {text}" for n, text in enumerate(POLICY.premises, 1)))
