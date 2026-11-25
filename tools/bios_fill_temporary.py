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
   slot; no frame reference of the function has an unknown offset.  So the slot is the block's alone: a later
   block may give it to its own temporary, but no later statement reads it.
6. Each fill in R's code, which is the ROM's (rom_fill): in the straight line before the BL, one store of the
   temporary's width is the only access to the slot, r0 holds the slot's address at the BL, r1 holds no stack
   address whose filled bytes reach the slot and r3 none in it, r2, where the line sets it to a literal the ROM
   holds or to an immediate, is the fill's control word, and the BL reaches the fill's BIOS call.  (agbcc may
   keep the control word in a callee-saved register across calls and copy it to r2; the line does not show that
   constant, and 5 reads it off the RTL.)  The order of the store and of the forming of the address is free: a
   halfword has no sp-relative store, so its address is formed first, while a word may be stored at sp+K before
   r0 is formed.  Either way the qualifier's evidence is 4, the code it changes.

The record prints each fill's ROM site, slot and control word, the BIOS call's bytes and the digests of R's code
and of each variant's.
"""
from collections import Counter
from hashlib import sha256
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

def frame_offset(function, x, depth=0):
    """(frame register, constant offset) of an address built from a frame register by constants, through
    single-definition pseudos, else None (the resolver keeps no frame offsets)"""
    if depth > 32:
        return None
    head = code(x)
    if head == "reg":
        number = int(x[1])
        if number < proof.FIRST_PSEUDO:
            return (number, 0) if number in proof.FRAME_REGISTERS else None
        definitions = function.defs.get(number, [])
        return frame_offset(function, definitions[0][1], depth + 1) if len(definitions) == 1 else None
    if head in ("plus", "minus") and len(x) == 3:
        sign = 1 if head == "plus" else -1
        for inner, constant, factor in ((x[1], x[2], sign), (x[2], x[1], 1)):
            if code(constant) == "const_int" and (head == "plus" or inner is x[1]):
                found = frame_offset(function, inner, depth + 1)
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
        return frame_offset(function, x) or (base.value, None)
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


def fills(function):
    """[fill] of an expand-level function: each {call (insn), slot (frame register, offset), width, control,
    store (insn index), start (insn index), callee (name), store_uid}; ProofError when a fill or the slots it needs
    cannot be shown"""
    resolver = proof.Resolver(function)
    calls = [(insn, name) for insn in function.insns if insn.code == "call_insn"
             for name in CALLEES if f'"{name}"' in proof.flatten(insn.pattern)]
    touches = frame_touches(function, resolver)
    if any(offset is None for _, _, offset, _, _, _ in touches):
        raise ProofError("a frame reference of the function has no constant offset")
    stores = [t for t in touches if t[4] == "store" and "v" in rtl_flags(t[5])]
    found = []
    for call, callee in calls:
        source = argument(function, call, 0)
        slot = frame_offset(function, source) if source is not None else None
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
            target = frame_offset(function, passed) if passed is not None else None
            if target is None:
                continue
            if target[0] != slot[0]:
                raise ProofError(f"the fill at insn UID {call.uid} passes r{number} a frame address the proof cannot "
                                 "place against its temporary")
            if overlaps(target[1], size, slot[1], width):
                raise ProofError(f"the fill at insn UID {call.uid} passes r{number} an address that reaches its own "
                                 "temporary")
        found.append(dict(call=call, slot=slot, width=width, control=value, store=mine[0][0], start=start,
                          callee=callee, store_uid=function.insns[mine[0][0]].uid))
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
    return found


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


def rom_fill(rom, address, compiled, fill):
    """(BL site, slot offset from sp, the site forming its address) of one fill, read off R's code (the ROM's)"""
    _, base, size, _ = compiled["text"]
    instructions, labels = compiled["layout"]
    callee = fill.get("callee", CPUSET_NAME)
    target = CALLEES[callee][0]
    sites = [at for at, _ in compiled["uids"].get(fill["call"].uid, [])]
    if len(sites) != 1:
        raise ProofError(f"the fill at insn UID {fill['call'].uid} is not one BL")
    index = instructions.index(sites[0])
    bl = address + sites[0] - base
    if proof.decode_bl(rom, bl) != target:
        raise ProofError(f"the BL at {bl:08X} does not reach {target:08X}")
    decoder = proof.thumb_decoder()

    def decode(offset):
        where = address + offset - base
        insn = next(decoder.disasm(rom[where - BASE:where - BASE + 4], where, 1), None)
        if insn is None:
            raise ProofError(f"{where:08X} does not decode")
        return insn

    def written(insn):
        return {insn.reg_name(r) for r in insn.regs_access()[1]}

    # the straight line before the BL: back to a branch target, a branch, a call, or a change of sp
    first = index
    while first > 0 and index - first < MAX_WINDOW and base <= instructions[first - 1] < base + size and \
            instructions[first] not in labels:
        before = decode(instructions[first - 1])
        if before.mnemonic == "bl" or proof.BRANCH.fullmatch(before.mnemonic) or {"pc", "sp"} & written(before):
            break
        first -= 1
    held, formed, accesses, known = {}, {}, [], {}
    for k in range(first, index):
        insn = decode(instructions[k])
        loaded = constant(rom, insn.address, struct.unpack_from("<H", rom, insn.address - BASE)[0], known)
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
            displacement = immediate[0] if immediate else 0
            if ops[1] == "sp":
                access = (displacement, width, insn.mnemonic.startswith("str"), k)
            elif ops[1] in held:
                access = (held[ops[1]] + displacement, width, insn.mnemonic.startswith("str"), k)
            elif len(ops) == 3 and not immediate and (ops[1] in held or ops[2] in held):
                raise ProofError(f"{insn.address:08X} indexes the stack by a register inside the fill")
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
    if "r0" not in held:
        raise ProofError(f"r0 holds no stack address at the BL at {bl:08X}")
    slot = held["r0"]
    mine = [a for a in accesses if a[0] < slot + fill["width"] and slot < a[0] + a[1]]
    if len(mine) != 1 or mine[0][:3] != (slot, fill["width"], True):
        raise ProofError(f"the slot sp+{slot:#x} of the fill at {bl:08X} is not stored exactly once with "
                         f"{fill['width']} bytes before it")
    for register, span in (("r1", filled(fill["control"], fill["width"], callee)), ("r3", 1)):
        if register in held and overlaps(held[register], span, slot, fill["width"]):
            raise ProofError(f"the fill at {bl:08X} passes {register} sp+{held[register]:#x}, which reaches its own "
                             "temporary")
    if "r2" in known and known["r2"] != fill["control"]:
        raise ProofError(f"r2 holds {known['r2']:#010x} at the BL at {bl:08X}, not the fill's control word "
                         f"{fill['control']:#010x}")
    return bl, slot, address + instructions[formed[slot]] - base


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
        proof.function_matches_rom(real["text"], address, rom)
        rtl = real["dumps"]["rtl"]
        for other, function in rtl.items():
            if other != name and any("v" in rtl_flags(mem) for _, mem, _ in function.mems()):
                raise ProofError(f"another function of the unit, {other}, holds a volatile reference")
        found = sorted(fills(rtl[name]), key=lambda fill: fill["store"])
        wrappers(rom, {fill["callee"] for fill in found})
        sites = [rom_fill(rom, address, real, fill) for fill in found]
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
        listed = "; ".join(f"{bl:08X} fills from sp+{slot:#x} (address formed at {formed:08X}, control "
                           f"{found[k]['control']:#010x}, {found[k]['width']}-byte units)"
                           for k, (bl, slot, formed) in enumerate(sites) if k in removed)
        calls = "; ".join(f"{CALLEES[callee][0]:08X} is `{CALLEES[callee][2]}` in the ROM"
                          for callee in sorted({found[k]["callee"] for k in removed}))
        text = (f"line {g['line']}: volatile {g['type']} {g['temporary']} is the SDK's BIOS fill temporary "
                f"({where}): {listed}; {calls}; code SHA-256 as written `{digest(real)}`, without these qualifiers "
                f"`{variant}`")
        verdicts += [(o, ("admitted", text)) for o in g["offsets"]]
    return verdicts


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
