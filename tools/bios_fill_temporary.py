"""Admit the SDK's BIOS fill temporary where the ROM shows it (bios-fill-temporary-v1, kit issue 164).

The GBA SDK fills memory through the BIOS with a volatile temporary:

    #define CpuFill16(value, dest, size) \\
    { vu16 tmp = (vu16)(value); \\
      CpuSet((void *)&tmp, dest, CPU_SET_16BIT | CPU_SET_SRC_FIXED | ((size)/(16/8) & 0x1FFFFF)); }

    #define CpuFastFill(value, dest, size) \\
    { vu32 tmp = (vu32)(value); \\
      CpuFastSet((void *)&tmp, dest, CPU_FAST_SET_SRC_FIXED | ((size)/(32/8) & 0x1FFFFF)); }

and CpuFill32 is CpuFill16 with a vu32 and 32-bit units.  In FFTA CpuSet is func_0814186C, `swi 0x0B; bx lr`,
and CpuFastSet is func_08141868, `swi 0x0C; bx lr`; CpuFastSet copies words only, eight at a time, so its count
of words rounds up to a multiple of 8 and its control word has no unit bit.
agbcc gives a volatile temporary its frame slot as it expands the declaration, a slot the next block may reuse; a
plain local whose address is taken gets one only later, and keeps it.  A `volatile` token of the
addressed source that no other exception admits is admitted here when it belongs to such a fill and all of this
holds:

1. Source (fill_groups).  The fill is the block

       { volatile T t = [(volatile T)] value; F([(void *) | (const void *)]&t, dest, control); }

   with F func_0814186C and T u16 or u32, or F func_08141868 and T u32, written in a function or as the whole
   body of a function-like macro that is defined once and never undefined; t occurs nowhere else in the block (a
   macro's arguments may still name it; 5 and 6 see what they do with it).  A block's tokens (the declaration's
   and the cast's) are one group; a macro's are one group however often it is used.  Line splices are read as
   cpp joins them; a token a splice splits is not considered.
2. Census.  volatile_rom_proof's Unit: the unit compiled from a copy whose candidate tokens are fresh markers is
   the tree's, byte for byte, once the markers are turned back; a block's markers reach the unit once, a macro's
   once per expansion.
3. ROM.  The addressed function compiled as written (R) equals the ROM at every byte the linker does not fill
   in, and the ROM's func_0814186C is `swi 0x0B; bx lr` and its func_08141868 `swi 0x0C; bx lr` wherever a fill
   calls them.  No other function of the unit holds a volatile reference.
4. Necessity.  For each group the unit compiled with the group's tokens removed has other code, keeps only
   volatile frame stores R makes, and has that many fewer (its markers' reaches); the groups account for every
   volatile frame store in R.
5. Each fill in R's expand RTL (fills): a call of func_0814186C or func_08141868 whose r0 is a frame slot and
   whose r2 is a constant with bit 24 (one source unit) set, and whose block holds one volatile store of the
   temporary's width to that slot.  For CpuSet bit 26 (32-bit units) is set exactly for a word temporary; for
   CpuFastSet the temporary is a word and the control word has no bit outside 0-20 and 24.  Its r1 and its r3
   (which the BIOS does not read), when frame addresses, are in the slot's frame and miss the slot: r1 with all
   the bytes it is filled over (the control word's count of units, for CpuFastSet rounded up to 8 words), r3
   itself.  No insn outside a fill's block (its first insn to its call) reads, writes or forms an address in the
   slot; no frame reference of the function has an unknown offset, unless it lies on no path to or from any fill
   on the expand RTL's control-flow graph, loops included (apart()).  (A pseudo with several definitions, such as
   the pointers a block move advances, is read through the definition that reaches the reference in a straight
   line, with no branch target between.)  So the slot is the block's alone: a later block may give it to its own
   temporary, but no later statement reads it.
6. Each fill in R's code, which is the ROM's (rom_fill).  The fill's BL is its call's one site; a call that left no
   site (cross-jumping replaced the end of its block by a branch into another fill's identical tail) has the BL that
   the last insn of its block the code still holds reaches in a straight line, through unconditional branches only.
   On every path into the BL: no access has a register offset whose base or index holds a stack address (its
   address is unknown), one store of the temporary's width is the only access to the slot, r0 holds the slot's
   address at the BL, r1 holds no stack address whose filled bytes reach the slot and r3 none in it, r2 and the
   stored register, where the path sets them to a literal the ROM holds or to an immediate, are the fill's control
   word and the value its RTL store writes, and the BL reaches the fill's BIOS call.  (agbcc may keep a constant in
   a callee-saved register across calls and copy it from there; the path does not show that constant, and 5 reads it
   off the RTL.)  A path is the straight line before the BL, back to a branch target, a branch, a call, or a change
   of sp.  A path that shows no access to the slot may take the slot's address from a callee-saved register (r4-r11)
   it reads before writing: agbcc may form the address once and keep it there across branches, loops and calls.
   The register is taken as sp+K when every route into the path, walked backwards on the ROM's control-flow graph,
   reaches a write of it whose own straight line makes it sp+K, with one K for all, before any other write of it,
   any change of sp, a SWI or the function's entry; and when every call those routes cross passes kit #350's
   callee-saved check (callee_saved_watch, Carrier), which walks the callee and requires the register and SP
   returned unchanged and no bit of the register used.  The record names the register, its forming sites, the
   calls and the premises that check states.  When that line starts at a branch target and holds no access to the slot r0 points at, the paths are
   instead each of the target's predecessors (the fall-through, which may not be a call, every B and B<cond> to it,
   and every far jump to it: agbcc's long branch, a BL the listing marks `@ far jump` to a branch target of the
   function; a BL to the function's entry is a recursive call, which returns), read the same way and followed by the
   line, up to MAX_PATHS paths of MAX_WINDOW instructions.  No other way in may exist: a function with a jump
   through a register other than a return's bx (agbcc's jump tables and indirect jumps are `mov pc, rN`), with a
   jump to no branch target or a BL into its body that is no marked far jump, or holding the target's address in a
   word that is no instruction or forming it with `add rN, pc, #K`, refuses.  A path that joins, or one into a BL
   several fills share, comes from one fill's block (its insns before the BL's own line belong to that block and to
   no other fill's) and stores with an insn that is one of those fills' stores; each fill sharing the BL has a path,
   and all its paths fill from one slot.  The order of the store and of the forming of the address is free: a
   halfword has no sp-relative store, so its address is formed first, while a word may be stored at sp+K before r0
   is formed.  Either way the qualifier's evidence is 4, the code it changes.

The record prints each fill's ROM site, slot, control word and any branch target its path joins at, the BIOS
call's bytes and the digests of R's code and of each variant's.
"""
from collections import Counter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import struct
import tempfile

import volatile_rom_proof as proof
from volatile_rom_proof import ProofError, code, rtl_mode, rtl_flags

SCHEMA = "bios-fill-temporary-v1"
RECORD = "* allowlisted volatile BIOS fill temporary:"
BASE = 0x08000000
CPUSET, CPUSET_NAME, CPUSET_BYTES = 0x0814186C, "func_0814186C", bytes.fromhex("0bdf7047")
CPUFASTSET, CPUFASTSET_NAME, CPUFASTSET_BYTES = 0x08141868, "func_08141868", bytes.fromhex("0cdf7047")
# a BIOS fill's callee: name -> (address, the ROM's bytes there, those bytes as code, the BIOS call)
CALLEES = {CPUSET_NAME: (CPUSET, CPUSET_BYTES, "swi 0x0B; bx lr", "CpuSet"),
           CPUFASTSET_NAME: (CPUFASTSET, CPUFASTSET_BYTES, "swi 0x0C; bx lr", "CpuFastSet")}
FIXED_SOURCE, WORD_UNITS, COUNT = 1 << 24, 1 << 26, 0x1FFFFF
WIDTHS = {"u16": 2, "u32": 4}
MODES = {"HI": 2, "SI": 4}
MAX_GROUPS = 8
ACCESS_WIDTHS = {"str": 4, "ldr": 4, "strh": 2, "ldrh": 2, "ldrsh": 2, "strb": 1, "ldrb": 1, "ldrsb": 1}
MAX_WINDOW = 64
MAX_PATHS = 8
# a fill slot's address carried in a callee-saved register (Carrier): the instructions the routes into a path may
# visit, and the calls they may cross
MAX_CARRY = 2048
MAX_CARRY_CALLS = 64
# capstone's names of the callee-saved registers r4-r11, by number
CALLEE_SAVED = {"r4": 4, "r5": 5, "r6": 6, "r7": 7, "r8": 8, "r9": 9, "sb": 9, "r10": 10, "sl": 10, "r11": 11,
                "fp": 11}
TOKEN = re.compile(r"[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+[uUlL]*|[0-9]+[uUlL]*|##|->|<<|>>|&&|\|\||[-+*/%&|^!=<>]=|\S")
DEFINE = re.compile(r"#[ \t]*define[ \t]+(?P<name>[A-Za-z_]\w*)\((?P<params>[^()]*)\)")


# ------------------------------------------------------------------ the source

def joined_view(raw):
    """(raw with its line splices joined, the raw offset of each joined character)"""
    out, back, i = [], [], 0
    while i < len(raw):
        if raw.startswith("\\\n", i):
            i += 2
            continue
        out.append(raw[i])
        back.append(i)
        i += 1
    back.append(len(raw))
    return "".join(out), back


def tokens(code_view, start=0, end=None):
    return [(m[0], m.start()) for m in TOKEN.finditer(code_view, start, len(code_view) if end is None else end)]


def expression(toks, i, stops):
    """index after a balanced token run from i that ends before a top-level token in stops"""
    depth = 0
    while i < len(toks):
        word = toks[i][0]
        if depth == 0 and word in stops:
            return i
        if word in "{};":
            return None
        depth += word == "("
        depth -= word == ")"
        if depth < 0:
            return None
        i += 1
    return None


def parse_fill(toks, i):
    """(end, fill) for a fill block starting at toks[i] (`{`), else None; fill gives the qualifier token indices"""
    def word(k):
        return toks[k][0] if k < len(toks) else None
    if word(i) != "{" or word(i + 1) != "volatile" or word(i + 2) not in WIDTHS:
        return None
    kind, name, qualifiers = word(i + 2), word(i + 3), [i + 1]
    if not name or not re.fullmatch(r"[A-Za-z_]\w*", name) or name in WIDTHS or word(i + 4) != "=":
        return None
    k = i + 5
    if [word(k), word(k + 1), word(k + 2), word(k + 3)] == ["(", "volatile", kind, ")"]:
        qualifiers.append(k + 1)
        k += 4
    # a top-level comma ends the value too: a second declarator is no fill
    value_end = expression(toks, k, {";", ","})
    if value_end is None or value_end == k:
        return None
    k = value_end + 1
    callee = word(k)
    if callee not in CALLEES or word(k + 1) != "(" or (callee == CPUFASTSET_NAME and kind != "u32"):
        return None
    k += 2
    for cast in (["(", "void", "*", ")"], ["(", "const", "void", "*", ")"]):
        if [word(k + j) for j in range(len(cast))] == cast:
            k += len(cast)
            break
    if [word(k), word(k + 1), word(k + 2)] != ["&", name, ","]:
        return None
    dest_end = expression(toks, k + 3, {","})
    if dest_end is None or dest_end == k + 3:
        return None
    control_end = expression(toks, dest_end + 1, {")"})
    if control_end is None or control_end == dest_end + 1:
        return None
    if [word(control_end), word(control_end + 1), word(control_end + 2)] != [")", ";", "}"]:
        return None
    end = control_end + 3
    if [t for t, _ in toks[i:end]].count(name) != 2:
        return None
    return end, {"width": WIDTHS[kind], "type": kind, "temporary": name, "qualifiers": qualifiers, "callee": callee}


def fill_groups(raw):
    """[group] of the fills a source spells, each {kind, name, type, width, temporary, callee, offsets (raw), line}"""
    import plausible
    joined, back = joined_view(raw)
    view = plausible.strip_comments_and_strings(joined)
    directives = [m.span() for m in plausible.DIRECTIVE.finditer(view)]
    groups = []

    def group(kind, name, fill, toks):
        offsets = [back[toks[q][1]] for q in fill["qualifiers"]]
        if any(raw[o:o + 8] != "volatile" for o in offsets):
            return None
        return dict(kind=kind, name=name, type=fill["type"], width=fill["width"], temporary=fill["temporary"],
                    callee=fill["callee"], offsets=offsets, line=1 + raw.count("\n", 0, offsets[0]))

    for start, end in directives:
        header = DEFINE.match(view, start + len(view[start:end]) - len(view[start:end].lstrip(" \t")))
        if header is None or header.end() > end:
            continue
        toks = tokens(view, header.end(), end)
        parsed = parse_fill(toks, 0) if toks else None
        if parsed is None or parsed[0] != len(toks):
            continue
        name = header["name"]
        spelt = [m for m in re.finditer(r"(?m)^[ \t]*#[ \t]*(?:define|undef)[ \t]+" + re.escape(name) + r"\b", view)]
        if len(spelt) != 1:
            continue
        found = group("macro", name, parsed[1], toks)
        if found:
            groups.append(found)
    outside = []
    last = 0
    for start, end in directives:
        outside.append((last, start))
        last = end
    outside.append((last, len(view)))
    for start, end in outside:
        toks = tokens(view, start, end)
        for i, (word, _) in enumerate(toks):
            if word != "{":
                continue
            parsed = parse_fill(toks, i)
            if parsed is not None:
                found = group("block", None, parsed[1], toks)
                if found:
                    groups.append(found)
    return groups


# ------------------------------------------------------------------ the expand RTL

def reaching(function, number, at):
    """(insn, value) of the definition of pseudo `number` that the insn at index `at` reads: the nearest one
    before it with no branch target, barrier or insn whose register writes are not read between, else None"""
    opaque = {uid for uid, _ in function.opaque}
    for insn in reversed(function.insns[:at]):
        if insn.code in ("code_label", "barrier") or insn.uid in opaque:
            return None
        mine = [value for other, value in function.defs.get(number, []) if other is insn]
        if mine:
            return (insn, mine[0]) if len(mine) == 1 else None
    return None


def frame_offset(function, x, depth=0, at=None):
    """(frame register, constant offset) of an address built from a frame register by constants, through
    single-definition pseudos, else None (the resolver keeps no frame offsets).  Read at insn index `at`, a pseudo
    with several definitions has the one that reaches it in a straight line: a block move (movstrsi) advances its
    own pointers, so they have two"""
    if depth > 32:
        return None
    head = code(x)
    if head == "reg":
        number = int(x[1])
        if number < proof.FIRST_PSEUDO:
            return (number, 0) if number in proof.FRAME_REGISTERS else None
        definitions = function.defs.get(number, [])
        if len(definitions) == 1:
            insn, value = definitions[0]
            return frame_offset(function, value, depth + 1, None if at is None else insn.index)
        found = reaching(function, number, at) if at is not None else None
        return frame_offset(function, found[1], depth + 1, found[0].index) if found else None
    if head in ("plus", "minus") and len(x) == 3:
        sign = 1 if head == "plus" else -1
        for inner, constant, factor in ((x[1], x[2], sign), (x[2], x[1], 1)):
            if code(constant) == "const_int" and (head == "plus" or inner is x[1]):
                found = frame_offset(function, inner, depth + 1, at)
                if found is not None:
                    return found[0], found[1] + factor * int(constant[1])
    return None


def mentions_frame(function, x, seen=None):
    """whether x is built, through any definitions, from a frame register.  A value read from memory is not: a
    fill slot's address reaches only its own block's CpuSet call, since storing it or using it anywhere else is a
    touch the slot checks refuse, so no load returns it.  Another local's address that is stored and loaded back,
    or a call's result that points into the frame, could reach the slot only by pointer arithmetic outside the
    object it points to, which C leaves undefined; the rule assumes the program does not do that"""
    seen = set() if seen is None else seen
    if code(x) == "mem":
        return False
    if code(x) == "reg":
        number = int(x[1])
        if number < proof.FIRST_PSEUDO:
            return number in proof.FRAME_REGISTERS
        if number in seen:
            return False
        seen.add(number)
        return any(mentions_frame(function, value, seen) for _, value in function.defs.get(number, []))
    return isinstance(x, list) and any(mentions_frame(function, item, seen) for item in x[1:])


def frame_reference(function, resolver, x, at):
    """(frame register, offset) when x is a frame address at a constant offset; (frame register or None, None)
    when it is one at an offset the proof cannot tell, or may be one; None when it is no frame address"""
    base, _ = resolver.resolve(x, at)
    if base.kind == "frame":
        return frame_offset(function, x, at=at) or (base.value, None)
    if base.kind == "unknown" and mentions_frame(function, x):
        return None, None
    return None


def frame_touches(function, resolver):
    """[(insn index, frame register, offset or None, width or None, what, mem)] of every frame access, and of
    every register set to a frame address"""
    found = []
    for insn in function.insns:
        if insn.pattern is None:
            continue
        for mem, store in proof.walk_mems(insn.pattern, []):
            where = frame_reference(function, resolver, mem[1], insn.index)
            if where is not None:
                found.append((insn.index, where[0], where[1], MODES.get(rtl_mode(mem)) or 8,
                              "store" if store else "load", mem))
        for target, source, _ in function.sets(insn.pattern):
            if code(source) != "mem":
                where = frame_reference(function, resolver, source, insn.index)
                if where is not None:
                    found.append((insn.index, where[0], where[1], None,
                                  "address" if code(target) == "reg" else "escape", None))
    return found


def argument(function, call, number):
    """the value argument register `number` is set to in the call's block, or None"""
    for insn in reversed(function.insns[:call.index]):
        if insn.code in ("code_label", "call_insn", "barrier", "jump_insn"):
            return None
        if insn.pattern is None:
            continue
        sets = function.sets(insn.pattern)
        for target, source, whole in sets:
            if code(target) == "reg" and int(target[1]) == number:
                return insn.equal if insn.equal is not None and len(sets) == 1 and whole else source
    return None


def block_start(function, index):
    """the index of the first insn of the block the insn at index lies in"""
    k = index
    while k > 0 and function.insns[k - 1].code not in ("code_label", "call_insn", "barrier", "jump_insn"):
        k -= 1
    return k


def volatile_frame_stores(function, resolver):
    return [touch for touch in frame_touches(function, resolver)
            if touch[4] == "store" and "v" in rtl_flags(touch[5])]


def filled(control, width, callee=CPUSET_NAME):
    """the bytes the BIOS writes: the control word's count of units (bits 0-20), each of the temporary's width;
    CpuFastSet writes words in runs of eight, so its count rounds up to a multiple of 8"""
    if callee == CPUFASTSET_NAME:
        return -(-(control & COUNT) // 8) * 8 * 4
    return (control & COUNT) * width


def overlaps(start, size, other, other_size):
    return start < other + other_size and other < start + size


def fills(function, taken=None):
    """[fill] of an expand-level function: each {call (insn), slot (frame register, offset), width, control,
    store (insn index), start (insn index), callee (name), store_uid, block (the uids of its insns, in order),
    value (the constant it stores, or None)}; ProofError when a fill or the slots it needs cannot be shown.
    taken is label_words() of the unit's assembly, which apart() reads (None: the RTL alone)"""
    resolver = proof.Resolver(function)
    calls = [(insn, name) for insn in function.insns if insn.code == "call_insn"
             for name in CALLEES if f'"{name}"' in proof.flatten(insn.pattern)]
    touches = frame_touches(function, resolver)
    # a frame reference at an offset the proof cannot place is admitted only apart from every fill (apart())
    unplaced = [touch for touch in touches if touch[2] is None]
    touches = [touch for touch in touches if touch[2] is not None]
    stores = [t for t in touches if t[4] == "store" and "v" in rtl_flags(t[5])]
    found = []
    for call, callee in calls:
        source = argument(function, call, 0)
        slot = frame_offset(function, source, at=call.index) if source is not None else None
        if slot is None:
            continue
        start = block_start(function, call.index)
        mine = [t for t in stores if start <= t[0] < call.index and (t[1], t[2]) == slot]
        if len(mine) != 1:
            continue
        width = mine[0][3]
        if width not in (2, 4):
            raise ProofError(f"the fill at insn UID {call.uid} stores {width} bytes")
        control = argument(function, call, 2)
        value = resolver.resolve(control, call.index)[0] if control is not None else None
        if value is None or value.kind != "int" or value.value is None:
            raise ProofError(f"the fill at insn UID {call.uid} passes no constant control word")
        value = value.value & 0xFFFFFFFF
        if not value & FIXED_SOURCE:
            raise ProofError(f"the fill at insn UID {call.uid} has a control word {value:#010x} without bit 24 "
                             "(a fixed source)")
        if callee == CPUFASTSET_NAME:
            if width != 4:
                raise ProofError(f"the fill at insn UID {call.uid} passes CpuFastSet a {width}-byte temporary")
            if value & ~(FIXED_SOURCE | COUNT):
                raise ProofError(f"the fill at insn UID {call.uid} has a CpuFastSet control word {value:#010x} "
                                 "with a bit outside 0-20 and 24")
        elif bool(value & WORD_UNITS) != (width == 4):
            raise ProofError(f"the fill at insn UID {call.uid} has a control word {value:#010x} whose bit 26 "
                             f"does not match its {width}-byte temporary")
        # the destination, and r3, which the BIOS does not read, hold no address in the slot
        for number, size in ((1, filled(value, width, callee)), (3, 1)):
            passed = argument(function, call, number)
            target = frame_offset(function, passed, at=call.index) if passed is not None else None
            if target is None:
                continue
            if target[0] != slot[0]:
                raise ProofError(f"the fill at insn UID {call.uid} passes r{number} a frame address the proof cannot "
                                 "place against its temporary")
            if overlaps(target[1], size, slot[1], width):
                raise ProofError(f"the fill at insn UID {call.uid} passes r{number} an address that reaches its own "
                                 "temporary")
        stored = [source for target, source, _ in function.sets(function.insns[mine[0][0]].pattern)
                  if target is mine[0][5]]
        known = resolver.resolve(stored[0], mine[0][0])[0] if len(stored) == 1 else None
        found.append(dict(call=call, slot=slot, width=width, control=value, store=mine[0][0], start=start,
                          callee=callee, store_uid=function.insns[mine[0][0]].uid,
                          block=[function.insns[k].uid for k in range(start, call.index + 1)],
                          value=known.value & (1 << 8 * width) - 1
                          if known is not None and known.kind == "int" and known.value is not None else None))
    claimed = {fill["store"] for fill in found}
    for index, register, offset, width, what, mem in stores:
        if index not in claimed:
            raise ProofError(f"insn UID {function.insns[index].uid} holds a volatile frame store that is no fill")
    for index, register, offset, width, what, _ in touches:
        span = width or 1
        sharing = [fill for fill in found if register == fill["slot"][0] and
                   offset < fill["slot"][1] + fill["width"] and fill["slot"][1] < offset + span]
        if not sharing:
            continue
        # a slot block-scoped temporaries share is touched only inside one of their blocks, and there only by the
        # forming of its address and by that block's one volatile store
        within = [fill for fill in sharing if fill["start"] <= index <= fill["call"].index]
        if not within:
            raise ProofError(f"insn UID {function.insns[index].uid} uses the fill temporary's slot outside its "
                             f"block ({what})")
        if what != "address" and index != within[0]["store"]:
            raise ProofError(f"insn UID {function.insns[index].uid} uses the fill temporary's slot beside its "
                             f"store ({what})")
    if unplaced:
        if not found:
            raise ProofError("a frame reference of the function has no constant offset")
        apart(function, unplaced, found, taken)
    return found


def label_uid(x):
    """the code_label UID a `label_ref` of any mode names (a jump table's entries print `(label_ref:SI N)`)"""
    if len(x) != 2 or not str(x[1]).isdigit():
        raise ProofError(f"a label reference the proof cannot read: {x}")
    return int(x[1])


def label_refs(x, found=None):
    """the code_label UIDs a pattern refers to, matched by code with the mode stripped"""
    found = [] if found is None else found
    if isinstance(x, list):
        if code(x) == "label_ref":
            found.append(label_uid(x))
        else:
            for part in x:
                label_refs(part, found)
    return found


TABLES = ("addr_vec", "addr_diff_vec")
# the callees gcc's special_function_p marks as returning twice, after it drops a leading `_`, `__` or `__x`
RETURNS_TWICE = {"setjmp", "setjmp_syscall", "sigsetjmp", "savectx", "qsetjmp", "vfork"}


# thumb.h: a nested function's static chain arrives in r9 (STATIC_CHAIN_REGNUM; no separate incoming register)
STATIC_CHAIN_REGNUM = 9


def mentions_register(x, number):
    if code(x) == "reg" and len(x) > 1 and str(x[1]) == str(number):
        return True
    return isinstance(x, list) and any(mentions_register(item, number) for item in x)


def nested_functions(rtl):
    """the functions of a unit's expand RTL that name the static chain register: every nested function (a GNU
    extension) does, so does a call that passes one its chain, and so does __builtin_setjmp, which clobbers it
    (expand_builtin_setjmp, expr.c).

    expand_function_start (function.c) stores the incoming chain in the frame whenever the function has a
    containing function (current_function_needs_context), unless DECL_NO_STATIC_CHAIN, whose bit is
    DECL_REGISTER, which C cannot set on a function (`register` there is an error, c-decl.c).  The function is
    in the dump even when it is inlined or never called.  A nested function reads the containing function's
    frame through the chain, out of sight of the frame analysis, so a unit holding one is refused; nothing in
    the ROM needs one.  A file-scope function names r9 only through an explicit register variable, which
    refuses too."""
    return sorted(name for name, function in rtl.items() if any(
        mentions_register(x, STATIC_CHAIN_REGNUM) for insn in function.insns for x in (insn.pattern, insn.notes)
        if x is not None))


def returns_twice(name):
    for prefix in ("__x", "__", "_"):
        if name.startswith(prefix):
            name = name[len(prefix):]
            break
    return name in RETURNS_TWICE


def table_at(function, labels, uid):
    """the jump table insn the code_label UID heads, or None"""
    index = labels.get(uid)
    following = function.insns[index + 1] if index is not None and index + 1 < len(function.insns) else None
    if following is not None and following.code == "jump_insn" and code(following.pattern) in TABLES:
        return following
    return None


def jump_targets(function, insn, labels):
    """the code_label UIDs a jump_insn may pass control to besides the next insn; ProofError for a jump whose
    targets the dump does not bound.

    The jumps read: `(set (pc) (label_ref L))`; `(set (pc) (if_then_else C A B))` with each arm a label, the
    next insn `(pc)` or a return; `(return)`; a tablejump, `(parallel [(set (pc) (reg R)) (use (label_ref T))])`
    with T's code_label followed at once by its table; and a table, `addr_vec` or `addr_diff_vec`, whose vector
    holds only labels.  Any other jump - a computed goto, a jump through memory, a tablejump with no table -
    refuses.  Every label a jump refers to anywhere in its pattern is a target (an addr_diff_vec's base label
    too), which can only add edges.
    """
    pattern = insn.pattern
    head = code(pattern)

    def refuse(what):
        raise ProofError(f"jump insn UID {insn.uid} is {what}; the proof cannot bound where it goes")

    if head in TABLES:
        vector = pattern[1] if head == "addr_vec" else pattern[2] if len(pattern) > 2 else None
        if code(vector) != proof.VECTOR or len(vector) < 2 or \
                any(code(entry) != "label_ref" for entry in vector[1:]):
            refuse(f"a jump table ({head}) whose vector is not a list of labels")
    elif head == "return":
        if len(pattern) != 1:
            refuse("a return with operands")
    else:
        if head == "set":
            items = [pattern]
        elif head == "parallel" and len(pattern) == 2 and code(pattern[1]) == proof.VECTOR:
            items = pattern[1][1:]
        else:
            refuse(f"a {head or 'malformed'} jump")
        jumps = [item for item in items if code(item) == "set" and len(item) == 3 and code(item[1]) == "pc"]
        others = [item for item in items if not any(item is jump for jump in jumps)]
        if len(jumps) != 1 or any(code(item) not in ("use", "clobber") for item in others):
            refuse("a jump that is not one set of the pc")
        source = jumps[0][2]
        uses = [item[1] for item in others if code(item) == "use"]
        if code(source) == "label_ref":
            pass
        elif code(source) == "if_then_else" and len(source) == 4:
            if any(code(arm) not in ("label_ref", "pc", "return") for arm in source[2:]):
                refuse("a conditional jump with an arm that is not a label, the next insn or a return")
        elif code(source) == "reg" and len(uses) == 1 and code(uses[0]) == "label_ref" and len(others) == 1:
            if table_at(function, labels, label_uid(uses[0])) is None:
                refuse("a tablejump whose label is not followed by its table")
        else:
            refuse("a computed jump, to a register or memory with no table")
    return label_refs(pattern)


def label_words(assembly):
    """the numbers n of every `.L<n>` a data directive of an agbcc assembly names, i.e. the labels whose
    address the code takes: a jump table's own label (in the constant pool) and its cases, a label value,
    a nonlocal goto's handler, a __builtin_setjmp receiver.  Thumb agbcc has no other way to form a label's
    address (no adr); a label value reaches its register from the constant pool, which the RTL does not show"""
    found = set()
    for line in assembly.splitlines():
        match = re.match(r"\s*(?:\.?\w+:\s*)?\.(?:word|long|4byte|int|short|hword|2byte|byte|quad|8byte)\s+(.*)", line)
        if match:
            found |= {int(number) for number in re.findall(r"\.L(\d+)\b", match[1])}
    return found


def barrier_follows_a_jump(function, barrier):
    """ProofError unless the barrier's nearest preceding insn other than a note is a jump_insn.

    A barrier ends a fall-through.  The graph bounds that only after a jump, whose edges jump_targets() adds.
    After a call it marks a callee the source declares noreturn.  The ROM cannot show that (with or without the
    attribute, the BL can compile to the same bytes), and the insn after the barrier is not the BL's return
    point (agbcc may place a literal pool there), so no edge stands in for the cut one.  After anything else
    (an insn, a label, another barrier, nothing) the cut is unexplained."""
    k = barrier.index - 1
    while k >= 0 and function.insns[k].code == "note":
        k -= 1
    before = function.insns[k] if k >= 0 else None
    if before is not None and before.code == "call_insn":
        raise ProofError(f"barrier UID {barrier.uid} follows call insn UID {before.uid}, so the source declares the "
                         "callee noreturn, which the ROM cannot show; the proof cannot bound where the call returns")
    if before is None or before.code != "jump_insn":
        raise ProofError(f"barrier UID {barrier.uid} follows "
                         + (f"{before.code} UID {before.uid}" if before is not None else "nothing") +
                         ", not a jump; the proof cannot bound where control goes")


def successors(function, taken=None):
    """{insn index: the indices control may pass to next} on the expand RTL.

    Every insn but a barrier falls through to the next. A jump_insn adds
    every label it refers to: a conditional or unconditional jump its
    target, a tablejump its table's label (whose addr_vec then refers to
    every case), and an addr_vec its cases. A barrier passes control
    nowhere, and it refuses unless the nearest insn before it, past notes, is
    a jump (barrier_follows_a_jump: after a call it marks a noreturn callee,
    which the ROM cannot show).
    So the graph has at least the edges the code has, and where
    the dump does not bound them it refuses: a jump jump_targets does not
    read, a label whose address an insn other than a jump takes (a label
    value or a nonlocal goto's handler) unless it heads a jump table, and a
    call that may return twice (setjmp and its kin), since a missing edge
    would make two insns look apart.  So does a label gcc preserves for a
    nonlocal goto (`code_label/s`), and, given the assembly's label_words(),
    any label whose address the code takes other than a jump table's own
    label and its cases: control reaches such a label from outside the
    graph (a nonlocal goto, a longjmp to a __builtin_setjmp receiver).
    """
    labels = {insn.uid: insn.index for insn in function.insns if insn.code == "code_label"}
    for insn in function.insns:
        if insn.code == "code_label" and "s" in insn.flags:
            raise ProofError(f"label UID {insn.uid} is preserved for a nonlocal goto; the proof cannot bound the "
                             "jumps to it")
    if taken is not None:
        numbers = {insn.number: insn.uid for insn in function.insns if insn.code == "code_label"}
        allowed = set()
        for insn in function.insns:
            if insn.code == "jump_insn" and code(insn.pattern) in TABLES:
                head = function.insns[insn.index - 1] if insn.index else None
                if head is not None and head.code == "code_label":
                    allowed.add(head.number)
                allowed |= {function.insns[labels[uid]].number for uid in label_refs(insn.pattern) if uid in labels}
        for number in sorted(taken - allowed):
            raise ProofError(f"the assembly takes the address of label .L{number}"
                             + (f" (UID {numbers[number]})" if number in numbers else "") +
                             ", which is no jump table's label or case; the proof cannot bound the jumps to it")
    graph = {}
    for insn in function.insns:
        if insn.code == "barrier":
            barrier_follows_a_jump(function, insn)
        following = set() if insn.code == "barrier" or insn.index + 1 >= len(function.insns) else {insn.index + 1}
        if insn.code == "jump_insn":
            targets = jump_targets(function, insn, labels)
            if any(uid not in labels for uid in targets):
                raise ProofError(f"jump insn UID {insn.uid} refers to a label the dump does not hold")
            following |= {labels[uid] for uid in targets}
        elif insn.pattern is not None:
            for uid in label_refs(insn.pattern) + label_refs(insn.notes):
                if table_at(function, labels, uid) is None:
                    raise ProofError(f"insn UID {insn.uid} takes the address of label UID {uid}, which heads no "
                                     "jump table; the proof cannot bound the jumps to it")
            if insn.code == "call_insn":
                names = [x.strip('"') for x in proof.flatten(insn.pattern) if isinstance(x, str) and x[:1] == '"']
                if any(returns_twice(name) for name in names):
                    raise ProofError(f"call insn UID {insn.uid} calls a function that may return twice; the proof "
                                     "cannot bound the jumps to its return")
        graph[insn.index] = following
    return graph


def reached(graph, start):
    """the indices some path of one or more steps from start reaches"""
    seen, pending = set(), list(graph.get(start, ()))
    while pending:
        index = pending.pop()
        if index not in seen:
            seen.add(index)
            pending.extend(graph.get(index, ()))
    return seen


def apart(function, unplaced, found, taken=None):
    """F1 for the frame references at offsets the proof cannot place (0811E1F8's `heights[context->mode]`).

    Each must lie on no path to or from any fill: no path from the first
    insn of a fill's block (through its store and its BIOS call) reaches it,
    and no path from it reaches that insn.  Loops count, since a path may go
    round one.  Such a reference may read, write or form any frame address,
    but never on an execution that also runs a fill.  Within one
    invocation it therefore neither changes the temporary between its store
    and the BIOS call nor reads it afterwards, and the frame does not
    outlive the invocation.  Each fill records the references it was
    checked against.
    """
    graph = successors(function, taken)
    for index, register, offset, width, what, mem in unplaced:
        if what == "store" and "v" in rtl_flags(mem):
            raise ProofError(f"insn UID {function.insns[index].uid} holds a volatile frame store at an offset the "
                             "proof cannot place")
        later = reached(graph, index)
        for fill in found:
            if fill["start"] <= index <= fill["call"].index or fill["start"] in later or \
                    index in reached(graph, fill["start"]):
                raise ProofError(f"insn UID {function.insns[index].uid} is a frame reference with no constant "
                                 f"offset on a path to or from the fill at insn UID {fill['call'].uid}")
    for fill in found:
        fill["apart"] = sorted(function.insns[index].uid for index, *_ in unplaced)


# ------------------------------------------------------------------ the ROM

def constant(rom, at, half, known):
    """(register, value) when the Thumb instruction `half` at `at` sets a low register to a constant the ROM shows:
    a literal load, a move of an immediate, or a shift, add or subtract by an immediate of a register in `known`
    ({register: value}); else None"""
    if half & 0xF800 == 0x4800:  # ldr rd, [pc, #imm8 * 4]
        where = ((at + 4) & ~3) + (half & 0xFF) * 4
        if not BASE <= where <= BASE + len(rom) - 4:
            return None
        return f"r{half >> 8 & 7}", struct.unpack_from("<I", rom, where - BASE)[0]
    if half & 0xF800 == 0x2000:  # movs rd, #imm8
        return f"r{half >> 8 & 7}", half & 0xFF
    if half & 0xF800 == 0x0000 and f"r{half >> 3 & 7}" in known:  # lsls rd, rm, #imm5
        return f"r{half & 7}", known[f"r{half >> 3 & 7}"] << (half >> 6 & 31) & 0xFFFFFFFF
    if half & 0xFC00 == 0x1C00 and f"r{half >> 3 & 7}" in known:  # adds / subs rd, rn, #imm3
        sign = -1 if half & 0x0200 else 1
        return f"r{half & 7}", (known[f"r{half >> 3 & 7}"] + sign * (half >> 6 & 7)) & 0xFFFFFFFF
    if half & 0xF000 == 0x3000 and f"r{half >> 8 & 7}" in known:  # adds / subs rd, #imm8
        sign = -1 if half & 0x0800 else 1
        return f"r{half >> 8 & 7}", (known[f"r{half >> 8 & 7}"] + sign * (half & 0xFF)) & 0xFFFFFFFF
    return None


def branch_target(half, at):
    """the target of the Thumb B or B<cond> `half` at `at`, else None"""
    if 0xD000 <= half < 0xDE00:
        offset = half & 0xFF
        return at + 4 + (offset - 0x100 if offset & 0x80 else offset) * 2
    if 0xE000 <= half < 0xE800:
        offset = half & 0x7FF
        return at + 4 + (offset - 0x800 if offset & 0x400 else offset) * 2
    return None


def far_jumps(listing):
    """the .text offsets of agbcc's far jumps in an `as -aln` listing of a -dp assembly: a `bl` to a local label
    that agbcc marks `@ far jump` (or `@far jump`, after the inverse branch of a conditional one)"""
    found = set()
    for line in listing.splitlines():
        match = re.match(r"\s*\d+\s+([0-9a-f]{4})\s+([0-9A-F]+)\s+(.*)$", line)
        if match and re.match(r"bl\s+\.L\w+\s+@ ?far jump\b", match[3].strip()):
            found.add(int(match[1], 16))
    return found


class Carrier:
    """kit #350's callee-saved walk (callee_saved_watch.Checker) of the calls a fill slot's address crosses in a
    callee-saved register.  agbcc may form the address once, keep it in r4-r11 across branches, loops and calls,
    and copy it to r0 at the BL.  "Callee-saved" obliges a callee only to restore the register, not to leave its
    value unused, so each call is walked: it must return the register (and SP) unchanged, and no bit of it may
    reach a use there or in the caller's code after it.  What the walk cannot see (code outside the ROM, a SWI,
    an indexed stack access) it admits under the premises it states, which the record prints."""

    def __init__(self, rom, entries, address):
        self.rom, self.entries, self.address = rom, entries, address

    def check(self, number, sites):
        """the premise and fact texts of the walks of the calls at sites made while r<number> holds the slot's
        address; ProofError when any walk refuses"""
        if not sites:
            return []
        import callee_saved_watch as watch
        context = watch.Context(self.rom, self.entries)
        checker = watch.checker_for(context)
        for site in sites:
            target = proof.decode_bl(self.rom, site)
            if target is None:
                raise ProofError(f"{site:08X} is no BL")
            try:
                checker.call(target, {number}, caller=self.address, site=site)
            except Exception as refusal:        # any refusal: the register is not proved preserved and unused
                raise ProofError(f"the callee-saved check refuses the call at {site:08X} while r{number} holds the "
                                 f"slot's address: {refusal}") from None
        texts = []
        for line in watch.premise_lines(context):
            for prefix, kind in ((watch.PREMISE_PREFIX, "premise"), (watch.FACT_PREFIX, "fact")):
                if line.startswith(prefix):
                    texts.append(f"{kind}: {line[len(prefix):].strip()}")
                    break
            else:
                raise ProofError(f"the callee-saved check states a line of no known kind: {line}")
        return sorted(texts)


def rom_fill(rom, address, compiled, fill, found=None, carrier=None):
    """(BL site, slot offset from sp, the site forming its address, the branch targets its path joins at, each
    (target, predecessor)) of one fill, read off R's code (the ROM's); found is every fill of the function, of
    which those sharing the fill's BL are read with it.  With a Carrier, a path that shows no access to the slot
    may take the slot's address from a callee-saved register formed before calls (carried); fill["carried"]
    states it for the record"""
    _, base, size, _ = compiled["text"]
    instructions, labels = compiled["layout"]
    found = [fill] if found is None else found
    decoder = proof.thumb_decoder()

    def where(k):
        return address + instructions[k] - base

    def inside(k):
        return 0 <= k < len(instructions) and base <= instructions[k] < base + size

    def decode(k):
        at = where(k)
        insn = next(decoder.disasm(rom[at - BASE:at - BASE + 4], at, 1), None)
        if insn is None:
            raise ProofError(f"{at:08X} does not decode")
        return insn

    def half(k):
        return struct.unpack_from("<H", rom, where(k) - BASE)[0]

    def written(insn):
        return {insn.reg_name(r) for r in insn.regs_access()[1]}

    def stops(insn):
        return insn.mnemonic == "bl" or proof.BRANCH.fullmatch(insn.mnemonic) or {"pc", "sp"} & written(insn)

    def sites(uid):
        return [at for at, _ in compiled["uids"].get(uid, []) if at in instructions]

    uids = {}
    for uid in compiled["uids"]:
        for at in sites(uid):
            uids.setdefault(at, set()).add(uid)

    def call_of(one):
        """the index of the BL by which a fill reaches its BIOS call"""
        uid = one["call"].uid
        if len(sites(uid)) > 1:
            raise ProofError(f"the fill at insn UID {uid} is not one BL")
        if sites(uid):
            return instructions.index(sites(uid)[0])
        # cross-jumping kept another fill's identical tail and replaced this one's by a branch into it: the BL
        # is the one the last insn of its block the code holds reaches in a straight line, through unconditional
        # branches only
        last = next((max(sites(other)) for other in reversed(one.get("block", [])) if sites(other)), None)
        k = instructions.index(last) if last is not None else None
        for _ in range(MAX_WINDOW if k is not None else 0):
            k += 1
            if not inside(k):
                break
            insn = decode(k)
            target = jump(k)
            if insn.mnemonic == "bl" and target is None:
                return k
            if target is not None and (half(k) >= 0xE000):
                offset = target - address + base
                if offset not in labels or offset not in instructions:
                    break
                k = instructions.index(offset) - 1
            elif stops(insn):
                break
        raise ProofError(f"the fill at insn UID {uid} is not one BL, and its block reaches none in a straight line")

    def start(k):
        """the first index of the straight line ending with index k: back to a branch target, or to just after a
        branch, a call or a change of sp"""
        first = k
        while first > 0 and k - first < MAX_WINDOW and inside(first - 1) and instructions[first] not in labels:
            if stops(decode(first - 1)):
                break
            first -= 1
        return first

    far = compiled.get("far", set())

    def jump(k):
        """the target of the B, B<cond> or far jump at index k, else None.  A far jump is agbcc's long branch,
        `bl .Ln @ far jump`: a BL the listing marks so, to a branch target of the function other than its entry
        (a BL to the entry is a recursive call, which returns)"""
        target = branch_target(half(k), where(k))
        if target is None and instructions[k] in far:
            callee = proof.decode_bl(rom, where(k))
            if callee is None or not address < callee < address + size or callee - address + base not in labels:
                raise ProofError(f"{where(k):08X} is marked a far jump but reaches no branch target of the function")
            target = callee
        return target

    flow, taken = {}, set()

    def predecessors(first):
        """the indices control reaches the branch target at index first from: the insn before it unless that
        ends the flow, and every branch or far jump to it; ProofError when the function holds a jump the ROM
        cannot place, or the target's address is taken"""
        if not flow:
            covered = set()
            for k in range(len(instructions)):
                if not inside(k):
                    continue
                insn, target = decode(k), jump(k)
                covered |= {instructions[k], instructions[k] + 2} if insn.size == 4 else {instructions[k]}
                callee = proof.decode_bl(rom, where(k)) if insn.mnemonic == "bl" and target is None else None
                if target is None and "pc" in written(insn) and insn.mnemonic not in ("bl", "bx", "pop") or \
                        callee is not None and address < callee < address + size:
                    raise ProofError(f"{where(k):08X} jumps where the ROM does not say; no path crosses a branch "
                                     "target")
                if target is not None:
                    if target - address + base not in labels:
                        raise ProofError(f"{where(k):08X} jumps to {target:08X}, which is no branch target")
                    flow.setdefault(target, []).append(k)
                if half(k) & 0xF800 == 0xA000:  # add rd, pc, #imm8 * 4: an address formed in the code
                    taken.add(((where(k) + 4) & ~3) + (half(k) & 0xFF) * 4)
            # a word of the function that is no instruction (a literal or a jump table) may hold an address
            for at in range(address + (-address & 3), address + size - 3, 4):
                if not {at - address + base, at - address + base + 2} & covered:
                    word = struct.unpack_from("<I", rom, at - BASE)[0]
                    taken.update({word, word & ~1})
        label, previous = where(first), first - 1
        if label in taken:
            raise ProofError(f"the address of the branch target at {label:08X} is taken; no path crosses it")
        before = decode(previous)
        ends = instructions[previous] in far or before.mnemonic in ("b", "bx") or "pc" in written(before) and \
            before.mnemonic not in ("bl", "blx") and branch_target(half(previous), where(previous)) is None
        if not ends and instructions[previous] + before.size != instructions[first]:
            raise ProofError(f"{where(previous):08X} does not fall through to the branch target at {label:08X}")
        return ([] if ends else [previous]) + flow.get(label, [])

    def read(path, seeds=None):
        """the stack addresses the path's registers hold (held), where each was formed, its stack accesses and the
        constants it loads; seeds: {register: (stack offset, index of the site forming it)} it holds on entry"""
        held, formed, accesses, known = {}, {}, [], {}
        for name, (value, site) in (seeds or {}).items():
            held[name] = value
            formed.setdefault(value, site)
        for k in path:
            insn = decode(k)
            if jump(k) is not None:
                continue  # a branch or far jump on the path moves only pc (and lr)
            loaded = constant(rom, insn.address, half(k), known)
            ops = [op.strip() for op in insn.op_str.replace("[", "").replace("]", "").split(",")]
            writes = written(insn)
            if "sp" in writes:
                raise ProofError(f"{insn.address:08X} moves the stack pointer inside the fill")
            value, access = None, None
            immediate = [int(op[1:], 0) for op in ops if op.startswith("#")]
            if insn.mnemonic == "add" and len(ops) == 3 and ops[1] == "sp" and immediate:
                value = immediate[0]
            elif insn.mnemonic == "mov" and ops[1:] == ["sp"]:
                value = 0
            elif insn.mnemonic in ("adds", "subs") and len(ops) in (2, 3) and immediate and \
                    (ops[1] if len(ops) == 3 else ops[0]) in held:
                sign = 1 if insn.mnemonic == "adds" else -1
                value = held[ops[1] if len(ops) == 3 else ops[0]] + sign * immediate[0]
            elif insn.mnemonic in ("mov", "movs") and len(ops) == 2 and ops[1] in held:
                value = held[ops[1]]
            if insn.mnemonic in ("stm", "stmia", "ldm", "ldmia") and ops[0].rstrip("!") in held:
                raise ProofError(f"{insn.address:08X} transfers a block through a stack address inside the fill")
            width = ACCESS_WIDTHS.get(insn.mnemonic)
            if width and len(ops) >= 2 and ops[1] != "pc":
                # a register offset ([rB, rI]) reaches an address the path does not know: refused before the base
                # is read as a held address at displacement 0
                if len(ops) == 3 and not immediate and (ops[1] in held or ops[2] in held):
                    raise ProofError(f"{insn.address:08X} indexes the stack by a register inside the fill")
                displacement = immediate[0] if immediate else 0
                if ops[1] == "sp":
                    access = (displacement, width, insn.mnemonic.startswith("str"), k, known.get(ops[0]))
                elif ops[1] in held:
                    access = (held[ops[1]] + displacement, width, insn.mnemonic.startswith("str"), k,
                              known.get(ops[0]))
            if access:
                accesses.append(access)
            for register in writes:
                held.pop(register, None)
                known.pop(register, None)
            if value is not None:
                held[ops[0]] = value
                formed.setdefault(value, k)
            if loaded is not None:
                known[loaded[0]] = loaded[1]
        return held, formed, accesses, known

    def live_in(path):
        """the callee-saved registers the path reads before it writes them"""
        names, done = [], set()
        for k in path:
            insn = decode(k)
            for name in sorted({insn.reg_name(r) for r in insn.regs_access()[0]} & set(CALLEE_SAVED) - done):
                if name not in names:
                    names.append(name)
            done |= written(insn)
        return names

    def sources(j):
        """the indices control passes to index j from: each executes just before it"""
        if where(j) == address:
            raise ProofError("a route reaches the function's entry, where the register holds the caller's value")
        if instructions[j] in labels:
            return predecessors(j)
        if not inside(j - 1):
            raise ProofError(f"{where(j):08X} follows no instruction of the function")
        before = decode(j - 1)
        ends = instructions[j - 1] in far or before.mnemonic in ("b", "bx") or "pc" in written(before) and \
            before.mnemonic not in ("bl", "blx") and branch_target(half(j - 1), where(j - 1)) is None
        if not ends and instructions[j - 1] + before.size != instructions[j]:
            raise ProofError(f"{where(j - 1):08X} does not fall through to {where(j):08X}")
        return [] if ends else [j - 1]

    def carried_value(first, name):
        """(K, forming sites, calls crossed) when on every route into index first the callee-saved register name
        holds sp+K: each route, walked backwards, reaches a write of it whose own straight line (read()) makes it
        sp+K, with one K for all, before any other write of it, any change of sp, a SWI or the function's entry.
        The calls the routes cross are Carrier's to check."""
        seen, pending, sites, calls = set(), [first], {}, set()
        while pending:
            for k in sources(pending.pop()):
                if k in seen:
                    continue
                seen.add(k)
                if len(seen) > MAX_CARRY:
                    raise ProofError(f"the routes into {where(first):08X} are longer than {MAX_CARRY} instructions")
                insn = decode(k)
                if name in written(insn):
                    value = read(list(range(start(k), k + 1)))[0].get(name)
                    if value is None:
                        raise ProofError(f"{where(k):08X} writes {name} with no stack address")
                    sites[k] = value
                    continue
                call = insn.mnemonic == "bl" and jump(k) is None
                if "sp" in written(insn) and not call:
                    raise ProofError(f"{where(k):08X} changes sp on a route into {where(first):08X}")
                if insn.mnemonic in ("svc", "swi"):
                    raise ProofError(f"{where(k):08X} is a SWI on a route into {where(first):08X}")
                if call:
                    calls.add(k)
                    if len(calls) > MAX_CARRY_CALLS:
                        raise ProofError(f"the routes into {where(first):08X} cross more than {MAX_CARRY_CALLS} "
                                         "calls")
                pending.append(k)
        if len(set(sites.values())) != 1:
            raise ProofError(f"{name} reaches {where(first):08X} " + ("formed nowhere" if not sites else
                             "as different stack addresses: " + ", ".join(
                                 f"sp+{value:#x} at {where(k):08X}" for k, value in sorted(sites.items()))))
        return sites[min(sites)], sorted(sites), sorted(calls)

    def carried(first, path):
        """({register: (K, forming site)}, facts) for the path's live-in callee-saved registers that carry a stack
        address across the calls before it (carried_value, Carrier), and the reasons the others do not"""
        seeds, facts, reasons = {}, [], []
        for name in live_in(path):
            try:
                value, sites, calls = carried_value(first, name)
                premises = carrier.check(CALLEE_SAVED[name], [where(k) for k in calls])
            except ProofError as refusal:
                reasons.append(f"{name}: {refusal}")
                continue
            seeds[name] = (value, sites[0])
            fact = f"sp+{value:#x} held in {name} from {', '.join(f'{where(k):08X}' for k in sites)}"
            if calls:
                fact += (f" across the calls at {', '.join(f'{where(k):08X}' for k in calls)}, each walked by the "
                         f"callee-saved check (it returns {name} unchanged and uses no bit of it)")
            else:
                fact += " across no call"
            facts.append(fact + "".join(f"; callee-saved {text}" for text in premises))
        return seeds, facts, reasons

    index = call_of(fill)
    bl, callee = where(index), fill.get("callee", CPUSET_NAME)
    if proof.decode_bl(rom, bl) != CALLEES[callee][0]:
        raise ProofError(f"the BL at {bl:08X} does not reach {CALLEES[callee][0]:08X}")
    sharing = [fill]
    for one in found:
        try:
            if one is not fill and call_of(one) == index:
                sharing.append(one)
        except ProofError:
            continue  # refused when it is read itself
    width = fill["width"]
    if any(one.get("callee", CPUSET_NAME) != callee or one["width"] != width for one in sharing):
        raise ProofError(f"the fills sharing the BL at {bl:08X} differ in their call or temporary")
    blocks = {uid: n for n, one in enumerate(sharing) for uid in one.get("block", [])}
    stores = {one.get("store_uid") for one in sharing}

    # every path into the BL: the straight line before it, and where that starts at a branch target and shows too
    # little, each predecessor's straight line before it in turn
    first = start(index)
    own = index - first
    pending, paths = [(first, list(range(first, index)), ())], []
    while pending:
        first, path, joins = pending.pop()
        held, formed, accesses, known = read(path)
        slot = held.get("r0")
        mine = [a for a in accesses if slot is not None and overlaps(a[0], a[1], slot, width)]
        facts, reasons = [], []
        if not mine and carrier is not None:
            # the slot's address may come into the path in a callee-saved register, formed before calls
            seeds, facts, reasons = carried(first, path)
            if seeds:
                held, formed, accesses, known = read(path, seeds)
                slot = held.get("r0")
                mine = [a for a in accesses if slot is not None and overlaps(a[0], a[1], slot, width)]
        if not mine and first > 0 and inside(first - 1) and instructions[first] in labels:
            for previous in predecessors(first):
                if previous == first - 1 and stops(decode(previous)) and \
                        branch_target(half(previous), where(previous)) is None:
                    raise ProofError(f"r0 holds no stack address at the BL at {bl:08X}" if slot is None else
                                     f"the slot sp+{slot:#x} of the fill at {bl:08X} is not stored exactly once "
                                     f"with {width} bytes before it")
                line = list(range(start(previous), previous + 1))
                if len(line) + len(path) > MAX_WINDOW:
                    raise ProofError(f"a path into the BL at {bl:08X} is longer than {MAX_WINDOW} instructions")
                pending.append((line[0], line + path, joins + ((where(first), where(previous)),)))
            if len(pending) + len(paths) > MAX_PATHS:
                raise ProofError(f"more than {MAX_PATHS} paths reach the BL at {bl:08X}")
            continue
        if slot is None:
            raise ProofError(f"r0 holds no stack address at the BL at {bl:08X}" +
                             (f" ({'; '.join(reasons)})" if reasons else ""))
        if len(mine) != 1 or mine[0][:3] != (slot, width, True):
            raise ProofError(f"the slot sp+{slot:#x} of the fill at {bl:08X} is not stored exactly once with "
                             f"{width} bytes before it")
        # a path that joins, or one of several fills sharing the BL, comes from one fill's block, which the
        # code before the BL's own line belongs to, and its store is a fill's
        owner = fill
        if joins or len(sharing) > 1:
            owners = {blocks[uid] for k in path[:len(path) - own] for uid in uids.get(instructions[k], ())
                      if uid in blocks}
            if len(owners) != 1:
                raise ProofError(f"the path into the BL at {bl:08X} from {where(path[0]):08X} comes from "
                                 f"{'no' if not owners else 'more than one'} fill's block")
            owner = sharing[owners.pop()]
            if not uids.get(instructions[mine[0][3]], set()) & stores:
                raise ProofError(f"the path into the BL at {bl:08X} stores its slot sp+{slot:#x} at "
                                 f"{where(mine[0][3]):08X}, which is no fill's store")
        for register, span in (("r1", filled(owner["control"], width, callee)), ("r3", 1)):
            if register in held and overlaps(held[register], span, slot, width):
                raise ProofError(f"the fill at {bl:08X} passes {register} sp+{held[register]:#x}, which reaches its "
                                 "own temporary")
        if "r2" in known and known["r2"] != owner["control"]:
            raise ProofError(f"r2 holds {known['r2']:#010x} at the BL at {bl:08X}, not the fill's control word "
                             f"{owner['control']:#010x}")
        value = owner.get("value")
        if value is not None and mine[0][4] is not None and mine[0][4] & (1 << 8 * width) - 1 != value:
            raise ProofError(f"the store at {where(mine[0][3]):08X} writes {mine[0][4] & (1 << 8 * width) - 1:#x} "
                             f"to the slot sp+{slot:#x}, not the fill's value {value:#x}")
        paths.append((owner, slot, where(formed[slot]), joins, facts))
    for one in sharing:
        slots = {slot for owner, slot, _, _, _ in paths if owner is one}
        if len(slots) != 1:
            raise ProofError(f"the fill at insn UID {one['call'].uid} reaches the BL at {bl:08X} by "
                             f"{'no path of its own' if not slots else 'paths with different slots'}")
    _, slot, formed, joins, _ = next(path for path in paths if path[0] is fill)
    fill["carried"] = sorted({fact for owner, _, _, _, facts in paths if owner is fill for fact in facts})
    return bl, slot, formed, joins


# ------------------------------------------------------------------ the proof

def wrappers(rom, callees):
    """ProofError unless the ROM holds each BIOS call the fills name as that call"""
    for callee in sorted(callees):
        at, expected, text, bios = CALLEES[callee]
        if rom[at - BASE:at - BASE + 4] != expected:
            raise ProofError(f"the ROM's {at:08X} is not `{text}` ({bios})")


def prove(tree, project, relpath, raw, admitted, rom=None, dependencies=None):
    """[(raw offset, verdict)] for every qualifier of a fill group no other exception admits, or None when there
    is none; a verdict is ("admitted", record fragment) or ("refused", reason)"""
    match = re.fullmatch(r"src/(?:[^/]+/)*([0-9A-F]{8})\.c", relpath or "")
    if not match:
        return None
    if any(marker in raw for marker in ("??", "%:", "<:", ":>", "<%", "%>", "\0", "\r")):
        return None
    groups = [g for g in fill_groups(raw) if not set(g["offsets"]) & set(admitted)]
    if not groups:
        return None
    if len(groups) > MAX_GROUPS:
        raise ProofError(f"more than {MAX_GROUPS} fill groups")
    address = int(match[1], 16)
    name = f"func_{address:08X}"
    if rom is None:
        from rompath import rom_path
        located = rom_path(project, required=False)
        if located is None:
            raise ProofError("no ROM to read the evidence from")
        rom = Path(located).read_bytes()
    wrappers(rom, {g["callee"] for g in groups})
    offsets = sorted(o for g in groups for o in g["offsets"])
    repeated = frozenset(o for g in groups if g["kind"] == "macro" for o in g["offsets"])
    build = Path(tree).resolve() / "build"
    build.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ffta_bft_", dir=build) as work:
        unit = proof.Unit(tree, relpath, raw, offsets, work, dependencies, repeated)
        real = unit.compile("real", unit.real, name)
        real["far"] = far_jumps((Path(work) / "real" / "f.lst").read_text())
        taken = label_words((Path(work) / "real" / "f.s").read_text())
        proof.function_matches_rom(real["text"], address, rom)
        rtl = real["dumps"]["rtl"]
        nested = nested_functions(rtl)
        if nested:
            raise ProofError(f"the unit names the static chain register r9 ({', '.join(nested)}): a nested function "
                             "reads the containing frame where the proof cannot see it")
        for other, function in rtl.items():
            if other != name and any("v" in rtl_flags(mem) for _, mem, _ in function.mems()):
                raise ProofError(f"another function of the unit, {other}, holds a volatile reference")
        found = sorted(fills(rtl[name], taken), key=lambda fill: fill["store"])
        wrappers(rom, {fill["callee"] for fill in found})
        carry = carrier(project, rom, address, dependencies)
        sites = [rom_fill(rom, address, real, fill, found, carry) for fill in found]
        keys = [store_key(touch) for touch in volatile_frame_stores(rtl[name], proof.Resolver(rtl[name]))]
        if len(keys) != len(found):
            raise ProofError("the fills do not account for every volatile frame store")
        owned, variants = [], []
        for g in groups:
            indices = {offsets.index(o) for o in g["offsets"]}
            stripped = unit.compile(f"s{len(variants)}", unit.variant_without(indices), name)
            if digest(stripped) == digest(real):
                raise ProofError(f"removing the qualifiers of the fill at line {g['line']} does not change the code")
            plain = stripped["dumps"]["rtl"][name]
            left = Counter(store_key(touch) for touch in volatile_frame_stores(plain, proof.Resolver(plain)))
            reaches = {unit.reaches[k] for k in indices}
            if len(reaches) != 1:
                raise ProofError(f"the fill at line {g['line']} does not account for its volatile stores")
            owned.append(account(keys, left, reaches.pop(), g["line"]))
            variants.append(digest(stripped))
        if sum(owned, Counter()) != Counter(keys):
            raise ProofError("the fills do not account for every volatile frame store")
        # for the record: each group takes, slot by slot, the next fills its removal took away
        pending = {key: [k for k, other in enumerate(keys) if other == key] for key in keys}
        owned = [sorted(pending[key].pop(0) for key, count in removed.items() for _ in range(count))
                 for removed in owned]
    verdicts = []
    for g, removed, variant in zip(groups, owned, variants):
        where = f"macro {g['name']}, used {len(removed)} times" if g["kind"] == "macro" else "a block"
        listed = "; ".join(f"{bl:08X} fills from sp+{slot:#x} (address formed at {formed:08X}, "
                           + "".join(f"{fact}, " for fact in found[k].get("carried", ()))
                           + "".join(f"joining at {label:08X} from {at:08X}, " for label, at in joins)
                           + f"control {found[k]['control']:#010x}, {found[k]['width']}-byte units)"
                           for k, (bl, slot, formed, joins) in enumerate(sites) if k in removed)
        calls = "; ".join(f"{CALLEES[callee][0]:08X} is `{CALLEES[callee][2]}` in the ROM"
                          for callee in sorted({found[k]["callee"] for k in removed}))
        apart_uids = sorted({uid for k in removed for uid in found[k].get("apart", ())})
        text = (f"line {g['line']}: volatile {g['type']} {g['temporary']} is the SDK's BIOS fill temporary "
                f"({where}): {listed}; {calls}; code SHA-256 as written `{digest(real)}`, without these qualifiers "
                f"`{variant}`" +
                (f"; frame references at offsets the proof cannot place, on no path to or from a fill: expand "
                 f"insn UIDs {apart_uids}" if apart_uids else ""))
        verdicts += [(o, ("admitted", text)) for o in g["offsets"]]
    return verdicts


def carrier(project, rom, address, dependencies=None):
    """the Carrier of the project's function index, or None when it has none (then no address is carried)"""
    mapping = Path(project) / "config" / "functions.json"
    try:
        raw = mapping.read_bytes()
        entries = json.loads(raw)
    except (OSError, ValueError):
        return None
    if not isinstance(entries, list):
        return None
    if dependencies is not None:
        dependencies.append((str(mapping), sha256(raw).hexdigest()))
    return Carrier(rom, entries, address)


def account(keys, left, reach, line):
    """the volatile frame stores that removing a group's tokens takes away: the variant keeps only stores R makes,
    and loses as many as the tokens reach the unit"""
    removed = Counter(keys) - left
    if left - Counter(keys) or sum(removed.values()) != reach:
        raise ProofError(f"the fill at line {line} does not account for its volatile stores")
    return removed


def store_key(touch):
    """(frame register, offset, width) of a frame store"""
    return touch[1], touch[2], touch[3]


def digest(compiled):
    text, start, size, _ = compiled["text"]
    return sha256(text[start:start + size]).hexdigest()


_CACHE = {}


def cached(tree, project, relpath, raw, admitted):
    if not re.fullmatch(r"src/(?:[^/]+/)*[0-9A-F]{8}\.c", relpath or ""):
        return None
    try:
        from rompath import rom_path
        located = rom_path(project, required=False)
        rom_key = (str(located), os.stat(located).st_size, os.stat(located).st_mtime_ns) if located else None
    except (SystemExit, OSError):
        rom_key = None
    key = (str(Path(tree).resolve()), str(Path(project).resolve()), rom_key, relpath, raw, tuple(sorted(admitted)))

    def current(dependencies):
        try:
            return all(sha256(Path(path).read_bytes()).hexdigest() == value for path, value in dependencies)
        except OSError:
            return False

    if key not in _CACHE or not current(_CACHE[key][1]):
        dependencies = []
        try:
            _CACHE[key] = prove(tree, project, relpath, raw, admitted, dependencies=dependencies), dependencies
        except (ProofError, OSError, UnicodeError, ImportError, KeyError, ValueError, IndexError,
                TypeError) as refusal:
            _CACHE[key] = str(refusal) or type(refusal).__name__, dependencies
    return _CACHE[key][0]


def source_text(tree, relpath):
    return (Path(tree) / relpath).read_text(encoding="utf-8")


def qualifier_offsets(text, tree, project, relpath, admitted):
    """the offsets in text (the file as written, or with its splices joined) of the fill qualifiers admitted"""
    import plausible
    try:
        raw = source_text(tree, relpath)
    except (OSError, UnicodeError, TypeError):
        return set()
    if text == raw:
        position = {o: o for o in range(len(raw) + 1)}
    elif text == plausible.join_splices(raw):
        _, back = joined_view(raw)
        position = {r: j for j, r in enumerate(back)}
        admitted = {back[o] for o in admitted if o < len(back)}
    else:
        return set()
    result = cached(tree, project, relpath, raw, admitted)
    if not isinstance(result, list):
        return set()
    return {position[o] for o, (state, _) in result if state == "admitted" and o in position}


def record(root, address):
    """the report record, or None when the source has no fill this rule admits"""
    import plausible
    root = Path(root)
    sources = sorted((root / "src").rglob(f"{address:08X}.c"))
    if len(sources) != 1:
        return None
    path = sources[0]
    relpath = path.relative_to(root).as_posix()
    try:
        raw = path.read_text(encoding="utf-8")
        admitted = plausible.exempt_qualifiers(raw, relpath, plausible.data_symbols_of(root), root, root,
                                               plausible.include_closure(root, path), fill_temporaries=False)
    except (OSError, UnicodeError, ValueError):
        return None
    result = cached(root, root, relpath, raw, admitted)
    if not isinstance(result, list):
        return None
    fragments = sorted({fragment for _, (state, fragment) in result if state == "admitted"})
    if not fragments:
        return None
    return (f"{RECORD} `{SCHEMA}`, compiled `{proof.CC} {proof.FLAGS}` as written and without each fill's "
            f"qualifiers, with `{proof.DUMP_FLAGS}`; " + " | ".join(fragments))


def main():
    import argparse
    import plausible
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--root", default=".")
    parser.add_argument("address", type=lambda value: int(value, 16))
    args = parser.parse_args()
    root = Path(args.root)
    path, = sorted((root / "src").rglob(f"{args.address:08X}.c"))
    relpath = path.relative_to(root).as_posix()
    raw = path.read_text(encoding="utf-8")
    admitted = plausible.exempt_qualifiers(raw, relpath, plausible.data_symbols_of(root), root, root,
                                           plausible.include_closure(root, path), fill_temporaries=False)
    result = cached(root, root, relpath, raw, admitted)
    if not isinstance(result, list):
        print(result or "no fill temporary")
        return 0 if result is None else 1
    for offset, (state, text) in result:
        print(f"{state}: {text}" if state == "admitted" else f"line {1 + raw.count(chr(10), 0, offset)}: {text}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
