"""Admit `volatile` in a source only where the ROM proves it (volatile-rom-proof-v1).

The volatile rule refuses the qualifier because it is the classic way to force
a byte match.  The existing exceptions admit it for the I/O window, for the
allow-listed RAM image of the LCD registers and for a set of reviewed
functions, one module each.  This rule is general: it admits a qualifier of
the addressed source wherever two things hold, and refuses it otherwise.

1. The ROM shows the qualifier's effect on its own accesses.  The unit is
   compiled as written (R) and once more for each candidate qualifier q with
   only q removed (S_q), each time with `-da -dp` as well, which make agbcc
   write its RTL after every pass and tag every assembly instruction with the
   UID of the insn it came from; both are checked not to change the code.
   * S_q's code must differ from R's (removing q changes the bytes);
   * the memory references of the addressed function in the two expand dumps
     (`.rtl`) must be the same sequence of (load or store, mode, address),
     where an address is printed with every single-definition temporary
     substituted and every user variable named by its declaration rank,
     except volatile references of R that S_q does not expand at all (a value
     the plain build never reads: dropped at expand; among equal references
     the first ones pair); q's accesses are the references that are volatile
     in R and plain in S_q or missing from it, no other reference may change,
     and q must have at least one;
   * no access of q may print like a reference of R that is not q's (the
     pairing would be ambiguous), and no two qualifiers may claim the same
     reference;
   * each access of q that R emits is found in R's assembly by its insn UID,
     and its byte offset in the function must hold a Thumb load or store of
     the access's width and direction in the ROM;
   * within S_q's own dumps an insn keeps its UID from pass to pass, so each
     of q's accesses is followed through every pass to S_q's assembly.  It is
     dropped (deleted by jump, by CSE's dead-insn pass, by flow or by jump2),
     merged (its memory reference replaced by an earlier value: cse, gcse,
     cse2) or moved (taken out of place by loop); combined (combine folds it
     into its use: the access stays) and kept do not count, nor does removal
     by regmove, lreg, greg or mach.  q is admitted only if at least one of
     the accesses the ROM holds is dropped, merged or moved; an access R does
     not emit never counts.

   A qualifier whose removal changes nothing, or changes only register
   allocation, constant placement or how instructions combine, is refused:
   the ROM does not show it.

2. Every access of q resolves to a hardware or shared object.  The address is
   resolved on R's expand RTL: single-definition temporaries are substituted,
   a multi-definition pseudo resolves when each definition is the same base
   or the pseudo itself plus a non-pointer offset (an induction variable), a
   sum must have exactly one pointer side, and a hard argument register is
   followed to the function's entry (a parameter) or the call before it (a
   call result).  The objects (OBJECT_WINDOWS, CART_BUS, volatile_objects.json):
   * a constant address, or a data symbol mapped there, in the I/O, palette,
     VRAM, OAM or cartridge backup window, at a constant offset that keeps the
     whole access inside the window;
   * a constant address on the cartridge bus [0x08000000, 0x0E000000) that the
     function itself stores to at the same base, with a store the ROM holds:
     ROM is not writable, so the store is a command to cartridge hardware
     (flash, a development cart);
   * a data symbol listed in tools/volatile_objects.json, mapped to the listed
     address: RAM the hardware reads or writes on its own.  Each entry names
     ROM code that programs a DMA channel with the object as source or
     destination; the code's bytes are pinned by SHA-256 and the transfer is
     read off its instructions at every run (dma_evidence).  Offsets must
     stay inside the listed size; a variable offset from the symbol is
     admitted only under the printed premise that it stays inside the object,
     which the proof does not check (the source may compute it on integers);
   * the result of a scanline payload getter listed in volatile_objects.json:
     the getter's code must be `return 0800C614(*(u32 *)(08005BFC(task) +
     4))`, and both callees' bodies are read too (08005BFC is task + 0x18;
     0800C614 returns a scanline task's payload pointer when its payload
     size is nonzero, else 0).  That payload is what the scanline manager
     0800C4B4 hands the task's callback each frame to fill the bank its HBlank
     DMA transfers, as bg_affine_rows.scanline_pipeline's pinned evidence
     shows.  Every call of the getter's name in the function must be a BL to
     its listed address in the ROM, and each call's argument (r0, resolved
     in the call's block) must not be a constant, a data symbol, a local or
     a scanline payload.  The record prints what the argument is and the one
     premise this needs: it is a task whose data word +4 holds a scanline
     task (the getter does not check the task kind), and offsets stay inside
     that payload, which the proof does not check either.
   A narrowed or extended constant loses its value, so an address computed
   from one refuses.  Volatile locals and frame slots, parameters (callers are
   not traced), other call results, values loaded from memory, unresolved or
   conflicting bases and a variable offset from a constant address are
   refused.

Only code tokens of the addressed source `src/<ADDR>.c` that no other
exception admits are candidates, and none in a preprocessor directive.  A
source with a line splice, a digraph, a trigraph or a NUL byte is never
considered.  Each candidate is renamed to a fresh random marker in a copy of
the unit's files; cpp of the copy with the markers turned back must equal cpp
of the tree byte for byte, and each marker must reach the unit exactly once,
so the variants are exact.  R's addressed function must equal the ROM at every
byte the linker does not fill in (match.py separately requires the whole match).
No other function of the unit may hold a volatile reference.

plausible.py admits exactly the tokens this proof admits, and
plausible.allowlisted_volatile_uses adds its record, which match.py carries
into the report and recomputes on --check-report.  The record prints every
premise: the object and its evidence, each access with its ROM address,
width, direction and fate in the non-volatile build, and the SHA-256 of R's
and S_q's code.

    python tools/volatile_rom_proof.py --root . 0x08A3915C   # the verdict and its reasons
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import re
import secrets
import shlex
import struct
import subprocess
import sys
import tempfile

SCHEMA = "volatile-rom-proof-v1"
RECORD = "* allowlisted volatile ROM proof:"
BASE = 0x08000000
# match.py's compiler, flags and assembler (match.DEFAULT_CC, DEFAULT_FLAGS,
# DEFAULT_AS), pinned so the lint need not import match.py; a test keeps them equal
CC = "$HOME/agbcc/gcc/agbcc"
FLAGS = "-mthumb-interwork -O2"
AS = "arm-none-eabi-as"
DUMP_FLAGS = "-da -dp"
# agbcc's passes in the order rest_of_compilation runs them, by dump suffix
PASSES = ("rtl", "jump", "cse", "addressof", "gcse", "loop", "cse2", "flow", "combine", "regmove",
          "lreg", "greg", "jump2", "mach")
DROPPING = {"jump", "cse", "addressof", "flow", "jump2"}
MERGING = {"cse", "gcse", "cse2"}
# thumb.h: FIRST_PSEUDO_REGISTER 17 (r0-r12, sp, lr, pc, ap); five virtual registers follow
FIRST_PSEUDO = 22
VIRTUAL = range(17, 22)
INCOMING_ARGS = 17
FRAME_REGISTERS = {7, 13, 16} | set(VIRTUAL)
OBJECT_WINDOWS = (("I/O registers", 0x04000000, 0x04000400),
                  ("palette RAM", 0x05000000, 0x05000400),
                  ("VRAM", 0x06000000, 0x06018000),
                  ("OAM", 0x07000000, 0x07000400),
                  ("cartridge backup (SRAM/flash)", 0x0E000000, 0x0E010000))
CART_BUS = (0x08000000, 0x0E000000)
MODE_BYTES = {"QI": 1, "HI": 2, "SI": 4}
MODE_SIZE = {"QI": 1, "HI": 2, "SI": 4, "DI": 8, "SF": 4, "DF": 8}
DMA_SOURCE = {0x040000B0 + 12 * channel: channel for channel in range(4)}
DMA_KINDS = ("dma-source", "dma-target")
GETTER_KIND = "scanline-payload-getter"
# a scanline payload getter returns PAYLOAD(*(u32 *)(TASK_DATA(task) + 4)):
# push {lr}; bl TASK_DATA; ldr r0, [r0, #4]; bl PAYLOAD; pop {r1}; bx r1
GETTER_SHAPE = {0: 0xB500, 3: 0x6840, 6: 0xBC02, 7: 0x4708}
TASK_DATA = 0x08005BFC
TASK_DATA_BODY = (0x3018, 0x4770)                  # adds r0, #0x18; bx lr
PAYLOAD = 0x0800C614
# push {lr}; adds r1, r0, #0; ldrh r0, [r1, #0x10]; movs r2, #0; cmp r0, #0;
# beq 1f; ldr r2, [r1, #0x14]; 1: adds r0, r2, #0; pop {r1}; bx r1
PAYLOAD_BODY = (0xB500, 0x1C01, 0x8A08, 0x2200, 0x2800, 0xD000, 0x694A, 0x1C10, 0xBC02, 0x4708)
MAX_CANDIDATES = 8
MAX_PRINT_DEPTH = 300
OBJECTS = Path(__file__).resolve().with_name("volatile_objects.json")


class ProofError(ValueError):
    """the qualifier is not shown by the ROM, or the proof cannot be run"""


# ------------------------------------------------------------------ RTL dumps

def _tokens(text):
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth == 0 and c == "(" and not (
                (i == 0 or text[i - 1] == "\n") and
                re.match(r"\((?:insn|jump_insn|call_insn|note|code_label|barrier)(?:/[a-z]+)* ", text[i:i + 24])):
            # a pass's own commentary may print RTL over several lines (loop's giv
            # notes): only an insn written at the start of a line is a form
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif c == "(":
            out.append("(")
            depth += 1
            i += 1
        elif c == ")":
            if depth == 0:
                raise ProofError("unbalanced RTL dump")
            out.append(")")
            depth -= 1
            i += 1
        elif c.isspace():
            i += 1
        elif depth == 0:
            # text between forms: only the function headers matter
            end = text.find("\n", i)
            end = n if end < 0 else end
            if text.startswith(";; Function ", i):
                out.append(("function", text[i:end].split()[2]))
            i = end
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in '()"':
                j += 1
            out.append(text[i:j])
            i = j
    if depth:
        raise ProofError("truncated RTL dump")
    return out


def parse_dump(text):
    """{function name: [top-level form]} of one agbcc RTL dump"""
    functions, current, stack = {}, None, []
    for token in _tokens(text):
        if isinstance(token, tuple):
            if token[1] in functions:
                raise ProofError(f"function {token[1]} appears twice in one dump")
            current = functions.setdefault(token[1], [])
        elif token == "(":
            stack.append([])
        elif token == ")":
            done = stack.pop()
            if stack:
                stack[-1].append(done)
            elif current is not None:
                current.append(done)
        else:
            stack[-1].append(token)
    return functions


def code(x):
    """an RTL expression's code (`mem` of `mem/s/v:HI`)"""
    if isinstance(x, list) and x and isinstance(x[0], str) and not x[0].startswith('"'):
        return x[0].split(":")[0].split("/")[0]
    return None


def rtl_flags(x):
    return set(x[0].split(":")[0].split("/")[1:])


def rtl_mode(x):
    return x[0].split(":", 1)[1] if ":" in x[0] else ""


INSN_CODES = ("insn", "jump_insn", "call_insn", "note", "code_label", "barrier")


class Insn:
    def __init__(self, form, index):
        self.code = code(form)
        self.uid = int(form[1])
        self.links = int(form[2]), int(form[3])
        self.index = index
        self.pattern = form[4] if self.code in ("insn", "jump_insn", "call_insn") else None
        self.deleted = self.code == "note" and "NOTE_INSN_DELETED" in form[4:]
        # REG_EQUAL / REG_EQUIV: the value the insn's single destination holds after it
        self.equal = None
        notes = form[7] if self.pattern is not None and len(form) > 7 else None
        while code(notes) in ("expr_list", "insn_list"):
            if rtl_mode(notes) in ("REG_EQUAL", "REG_EQUIV") and self.equal is None:
                self.equal = notes[1]
            notes = notes[2] if len(notes) > 2 else None


def walk_mems(x, out, store=False):
    """append (mem, is store) for every memory reference x reads or writes"""
    if not isinstance(x, list) or not x:
        return out
    head = code(x)
    if head == "mem":
        out.append((x, store))
        walk_mems(x[1], out)
    elif head == "set":
        dest = x[1]
        while code(dest) in ("subreg", "strict_low_part", "zero_extract", "sign_extract"):
            for operand in dest[2:] if code(dest) in ("zero_extract", "sign_extract") else ():
                walk_mems(operand, out)
            dest = dest[1]
        if code(dest) == "mem":
            out.append((dest, True))
            walk_mems(dest[1], out)
        else:
            walk_mems(dest, out)
        walk_mems(x[2], out)
    elif head == "call":
        # the callee's address is not an access
        if code(x[1]) == "mem":
            walk_mems(x[1][1], out)
        for operand in x[2:]:
            walk_mems(operand, out)
    elif head in ("use", "clobber"):
        pass
    else:
        for operand in x[1:]:
            walk_mems(operand, out)
    return out


def regs_in(x, out):
    if isinstance(x, list) and x:
        if code(x) == "reg":
            out.append(x)
        for operand in x[1:]:
            regs_in(operand, out)
    return out


class Function:
    """one function of one dump"""

    def __init__(self, forms):
        self.insns = [Insn(form, index) for index, form in enumerate(
            f for f in forms if isinstance(f, list) and code(f) in INSN_CODES)]
        self.by_uid = {}
        for insn in self.insns:
            if insn.uid in self.by_uid:
                raise ProofError(f"insn UID {insn.uid} appears twice")
            self.by_uid[insn.uid] = insn
        # every insn's chain links must name parsed insns: a form the parser
        # missed would otherwise read as an insn a pass deleted
        for before, insn, after in zip([None] + self.insns[:-1], self.insns, self.insns[1:] + [None]):
            if insn.links != ((before.uid if before else 0), (after.uid if after else 0)):
                raise ProofError(f"the insn chain is broken at UID {insn.uid}")
        self.defs = {}
        users = set()
        for insn in self.insns:
            if insn.pattern is None:
                continue
            for x in regs_in(insn.pattern, []):
                if "v" in rtl_flags(x) and int(x[1]) >= FIRST_PSEUDO:
                    users.add(int(x[1]))
            sets = self.sets(insn.pattern)
            for target, source, whole in sets:
                if code(target) == "reg":
                    value = insn.equal if insn.equal is not None and len(sets) == 1 and whole else source
                    self.defs.setdefault(int(target[1]), []).append((insn, value))
        self.users = sorted(users)
        self._names = {}

    @staticmethod
    def sets(pattern):
        """[(destination register or memory, the value it then holds, whether the set names it whole)].

        A set through a subreg defines the whole register: a subreg as wide
        as the register or wider gives it the value narrowed to its mode, and
        a narrower subreg of a promoted variable (/s) gives it the value
        extended as the variable's signedness says (PROMOTE_MODE).  Any other
        narrower subreg, strict_low_part, zero_extract or sign_extract
        writes only part of it: the value is ["partial"], which the resolver
        cannot resolve."""
        found = []
        for item in [pattern] + (pattern[1:] if code(pattern) == "parallel" else []):
            if code(item) == "set":
                target, source = item[1], item[2]
                whole = code(target) == "reg"
                while code(target) in ("subreg", "strict_low_part", "zero_extract", "sign_extract"):
                    if code(target) == "subreg" and code(target[1]) == "reg":
                        outer, inner = MODE_SIZE.get(rtl_mode(target)), MODE_SIZE.get(rtl_mode(target[1]))
                        if outer is None or inner is None:
                            source = ["partial"]
                        elif outer >= inner:
                            source = [f"truncate:{rtl_mode(target[1])}", source] if inner < 4 else source
                        elif "s" in rtl_flags(target):
                            source = ["zero_extend:SI" if "u" in rtl_flags(target) else "sign_extend:SI",
                                      [f"truncate:{rtl_mode(target)}", source]]
                        else:
                            source = ["partial"]
                    else:
                        source = ["partial"]
                    target = target[1]
                found.append((target, source, whole))
        return found

    def mems(self):
        """[(insn, mem, is store)] in insn order"""
        return [(insn, mem, store) for insn in self.insns if insn.pattern is not None
                for mem, store in walk_mems(insn.pattern, [])]

    def name(self, x, depth=0):
        """x printed with single-definition temporaries substituted, user variables by rank.

        A pseudo with several definitions or none prints `T*`, so two
        references may print alike; token_record refuses such ambiguity.
        Printing has no depth cap: an address too deep to print refuses.
        """
        if depth > MAX_PRINT_DEPTH:
            raise ProofError("an address too deep to print")
        head = code(x)
        if head == "reg":
            number = int(x[1])
            if number < FIRST_PSEUDO:
                return f"h{number}"
            if number in self._names:
                if self._names[number] is None:
                    raise ProofError(f"pseudo {number} is defined through itself")
                return self._names[number]
            if number in self.users:
                printed = f"V{self.users.index(number)}"
            else:
                definitions = self.defs.get(number, [])
                self._names[number] = None
                printed = self.name(definitions[0][1], depth + 1) if len(definitions) == 1 else "T*"
            self._names[number] = printed
            return printed
        if head == "mem":
            return f"[{rtl_mode(x)} {self.name(x[1], depth + 1)}]"
        if isinstance(x, list):
            return "(" + " ".join([x[0] if head is None else head + (":" + rtl_mode(x) if rtl_mode(x) else "")] +
                                  [self.name(item, depth + 1) for item in x[1:]]) + ")"
        return x


def references(function):
    """[(insn uid, store, mode, printed address, volatile, index in the insn)] of a function's expand dump"""
    out, last, index = [], None, 0
    for insn, mem, store in function.mems():
        index = index + 1 if insn.uid == last else 0
        last = insn.uid
        out.append((insn.uid, store, rtl_mode(mem), function.name(mem[1]), "v" in rtl_flags(mem), index))
    return out


def has_reference(insn, store, mode):
    return insn is not None and insn.pattern is not None and any(
        s == store and rtl_mode(m) == mode for m, s in walk_mems(insn.pattern, []))


def fate(dumps, uid, store, mode, final_uids):
    """(category, pass) of one access of the non-volatile build, followed by its insn UID.

    The first pass after which the insn no longer holds a reference of the
    same direction and mode decides.  cse, gcse and cse2 merged it when they
    rewrote it, or deleted it while its block reads or writes the same
    address before it (earlier_same), and dropped it otherwise; jump,
    addressof, flow and jump2 dropped it when they deleted it; loop moved it
    when a new insn holds such a reference (else dropped); combine combined
    it into its use; anything else is other.
    """
    previous = dumps["rtl"]
    for name in PASSES[1:]:
        if name not in dumps:
            continue
        function = dumps[name]
        insn = function.by_uid.get(uid)
        if has_reference(insn, store, mode):
            previous = function
            continue
        deleted = insn is None or insn.deleted or insn.pattern is None
        if name == "loop":
            new = [i for i in function.insns if i.uid not in previous.by_uid and has_reference(i, store, mode)]
            return ("moved" if new else "dropped"), name
        if name in MERGING:
            return ("merged" if not deleted or earlier_same(dumps["rtl"], uid, store, mode) else "dropped"), name
        if name in DROPPING and deleted:
            return "dropped", name
        if name == "combine":
            return "combined", name
        return "other", name
    return ("kept", "final") if uid in final_uids else ("other", "final")


def earlier_same(function, uid, store, mode):
    """whether the insn's block reads or writes the same address and mode before it (no call between):
    a value CSE can reuse, so a deleted load whose block has one was merged into it"""
    insn = function.by_uid.get(uid)
    if insn is None or insn.pattern is None:
        return False
    mine = [function.name(m[1]) for m, s in walk_mems(insn.pattern, []) if s == store and rtl_mode(m) == mode]
    for other in reversed(function.insns[:insn.index]):
        if other.code in ("code_label", "call_insn", "barrier"):
            return False
        if other.pattern is not None and any(rtl_mode(m) == mode and function.name(m[1]) in mine
                                             for m, _ in walk_mems(other.pattern, [])):
            return True
    return False


EVIDENCE = {"dropped", "merged", "moved"}


# ------------------------------------------------------------------ address resolution

class Base(tuple):
    """(kind, value) of a resolved value.

    Address kinds (ADDRESS_KINDS): fixed (a constant address), symbol and
    frame.  A parameter (argument register or stack slot k), a call result
    and a word (a full word loaded from memory or otherwise unknown) may each
    be a pointer or an integer (MAYBE): scaled, narrowed or combined with
    each other they are integers, but added to an address the sum refuses,
    since either side could be the pointer.  int is shown not to be a pointer
    (a constant, a narrow load, a scaled or bitwise value); bottom is a
    pseudo the fixpoint has not reached yet; unknown refuses.
    """
    def __new__(cls, kind, value=None):
        return super().__new__(cls, (kind, value))

    kind = property(lambda self: self[0])
    value = property(lambda self: self[1])


ADDRESS_KINDS = {"fixed", "symbol", "frame"}        # certainly addresses
MAYBE = {"param", "ret", "word"}                    # a pointer or an integer
SCALING = {"mult", "ashift"}
INTEGER_OPS = {"and", "ior", "xor", "not", "neg", "lshiftrt", "ashiftrt", "div", "udiv", "mod", "umod",
               "smin", "smax", "umin", "umax", "abs"}
BOTTOM = (Base("bottom"), None)
UNKNOWN = (Base("unknown"), None)
FIXPOINT_ROUNDS = 64


def join(a, b):
    """the least value covering two definitions of one pseudo"""
    if a[0].kind == "bottom":
        return b
    if b[0].kind == "bottom" or a == b:
        return a
    (x, ox), (y, oy) = a, b
    if "unknown" in (x.kind, y.kind):
        return UNKNOWN
    if x.kind == y.kind == "int":
        return Base("int"), None
    for (p, _), (q, _) in ((a, b), (b, a)):
        # a constant address that an induction steps by a variable amount
        if p.kind == "fixed" and q.kind == "int" and q.value == p.value:
            return p, None
    if x == y:
        return x, None
    if x.kind in ADDRESS_KINDS or y.kind in ADDRESS_KINDS:
        return UNKNOWN
    return Base("word"), None


class Resolver:
    """resolve memory addresses of one expand-level function (Base, constant offset or None).

    Every pseudo's value is the least fixpoint, from bottom, of the join of
    its definitions (a REG_EQUAL or REG_EQUIV note stands for its insn's
    source), so an induction variable `p = p + 8` keeps p's base and two
    counters defined through each other settle together.  A pseudo still at
    bottom, or one that does not settle within FIXPOINT_ROUNDS rounds, is
    unknown.
    """

    def __init__(self, function):
        self.function = function
        self.values = {number: BOTTOM for number in function.defs}
        for _ in range(FIXPOINT_ROUNDS):
            changed = False
            for number, definitions in function.defs.items():
                value = BOTTOM
                for insn, source in definitions:
                    value = join(value, self.resolve(source, insn.index))
                if value != self.values[number]:
                    self.values[number] = value
                    changed = True
            if not changed:
                break
        else:
            self.values = {number: UNKNOWN for number in function.defs}

    def hard(self, number, at):
        """a hard register read by insn index `at`: a parameter or the call result it holds"""
        if number > 3:
            return Base("frame" if number in FRAME_REGISTERS else "unknown", number), None
        for insn in reversed(self.function.insns[:at]):
            if insn.code == "call_insn":
                if number != 0:
                    return Base("unknown", number), None
                callee = [x for x in flatten(insn.pattern) if isinstance(x, str) and
                          re.fullmatch(r'"[A-Za-z_]\w*"', x)]
                return Base("ret", callee[0].strip('"') if len(callee) == 1 else None), 0
            if insn.pattern is not None and any(code(t) == "reg" and int(t[1]) == number
                                                for t, _, _ in self.function.sets(insn.pattern)):
                return Base("unknown", number), None
            if insn.code == "code_label":
                return Base("unknown", number), None
        return Base("param", number), 0

    def resolve(self, x, at, depth=0):
        if depth > 48:
            return UNKNOWN
        head = code(x)
        if head == "const_int":
            return Base("int", int(x[1])), int(x[1])
        if head == "symbol_ref":
            name = x[1][0] if isinstance(x[1], list) and x[1] else x[1]
            return Base("symbol", name.strip('"')), 0
        if head == "const":
            return self.resolve(x[1], at, depth + 1)
        if head == "reg":
            number = int(x[1])
            if number < FIRST_PSEUDO:
                if number in FRAME_REGISTERS:
                    return Base("frame", number), None
                return self.hard(number, at)
            return self.values.get(number, UNKNOWN)
        if head == "mem":
            address = x[1]
            if code(address) == "reg" and int(address[1]) == INCOMING_ARGS:
                return Base("param", 4), None
            if code(address) == "plus" and code(address[1]) == "reg" and int(address[1][1]) == INCOMING_ARGS \
                    and code(address[2]) == "const_int" and int(address[2][1]) % 4 == 0:
                return Base("param", 4 + int(address[2][1]) // 4), None
            return (Base("int"), None) if rtl_mode(x) in ("QI", "HI") else (Base("word"), None)
        parts = [self.resolve(item, at, depth + 1) for item in x[1:] if isinstance(item, list)] \
            if isinstance(x, list) else []
        if any(part[0].kind == "unknown" for part in parts):
            return UNKNOWN
        if any(part[0].kind == "bottom" for part in parts):
            return BOTTOM
        if head in ("subreg", "zero_extend", "sign_extend", "truncate"):
            (inner, offset), = parts
            narrow = rtl_mode(x[1]) in ("QI", "HI")
            if head == "subreg" and not narrow and rtl_mode(x) not in ("QI", "HI"):
                return inner, offset
            # a narrowed or extended integer stays one, but loses its value (an
            # address computed from it refuses); so does a value that may be
            # one; a narrowed address refuses
            if inner.kind == "int":
                return Base("int"), None
            return (Base("int"), None) if inner.kind in MAYBE else UNKNOWN
        if head in ("plus", "minus"):
            (a, oa), (b, ob) = parts
            known = oa is not None and ob is not None
            if head == "minus":
                if a.kind in ADDRESS_KINDS:
                    # a difference of two addresses, added back to another base,
                    # could name any object: refused rather than read as an index
                    return (a, (oa - ob if known else None)) if b.kind == "int" else UNKNOWN
                if b.kind in ADDRESS_KINDS:
                    return UNKNOWN
                if a.kind == "int" and b.kind == "int":
                    return (Base("int", oa - ob), oa - ob) if known else (Base("int"), None)
                if a.kind in ("param", "ret") and b.kind == "int":
                    return a, (oa - ob if known else None)
                return Base("word"), None
            for (p, op), (q, oq) in (((a, oa), (b, ob)), ((b, ob), (a, oa))):
                if p.kind in ADDRESS_KINDS:
                    if q.kind != "int":
                        return UNKNOWN
                    return p, (op + oq if op is not None and oq is not None else None)
            for (p, op), (q, oq) in (((a, oa), (b, ob)), ((b, ob), (a, oa))):
                if p.kind in ("param", "ret") and q.kind == "int":
                    return p, (op + oq if op is not None and oq is not None else None)
            if a.kind == "int" and b.kind == "int":
                if known:
                    return Base("int", oa + ob), oa + ob
                anchor = [o for o in (oa, ob) if o is not None and o >= 0x02000000]
                return (Base("fixed", anchor[0]), None) if anchor else (Base("int"), None)
            return Base("word"), None
        if head in SCALING:
            (a, _), (b, ob) = parts
            factor = ob if b.kind == "int" else None
            # a scaled value is an index: an integer or a value that may be one;
            # a scaled address refuses
            if a.kind not in {"int"} | MAYBE or factor is None or (head == "mult" and factor < 2) or \
                    (head == "ashift" and factor < 1):
                return UNKNOWN
            return Base("int"), None
        if head in INTEGER_OPS:
            return (Base("int"), None) if all(p[0].kind in {"int"} | MAYBE for p in parts) else UNKNOWN
        return UNKNOWN

    def address(self, insn, mem):
        base, offset = self.resolve(mem[1], insn.index)
        if base.kind == "int":
            return (Base("fixed", base.value), 0) if base.value is not None else UNKNOWN
        if base.kind in ("word", "bottom"):
            return UNKNOWN
        return base, offset


def flatten(x):
    out, stack = [], [x]
    while stack:
        item = stack.pop()
        if isinstance(item, list):
            stack.extend(item)
        else:
            out.append(item)
    return out


# ------------------------------------------------------------------ objects

def load_objects(path=OBJECTS):
    """the maintainer's shared-object list; unreadable or malformed is empty"""
    try:
        document = json.loads(Path(path).read_text(encoding="utf-8"))
        entries = document.get("entries", []) if document.get("version") == 1 else []
        return [entry for entry in entries if isinstance(entry, dict)]
    except (OSError, ValueError, AttributeError):
        return []


def thumb_decoder():
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return decoder


def dma_evidence(rom, entry):
    """the premise an entry's ROM code establishes, or ProofError.

    The pinned range must be straight-line Thumb code (forward conditional
    branches only) whose instructions, read with every register unknown at
    its start, store a value derived from the object's address into a
    channel's DMAxSAD (kind dma-source) or DMAxDAD (dma-target) and then a
    word with the enable bit (bit 31) set into the same channel's DMAxCNT.
    A value is derived from the object when it is a literal word inside the
    object, or such a value plus or minus anything else.
    """
    address, size = int(entry["address"], 16), int(entry["size"])
    start, end = int(entry["start"], 16), int(entry["end"], 16)
    if not (BASE <= start < end <= BASE + len(rom)) or end - start > 512 or start % 2 or end % 2:
        raise ProofError("shared-object evidence range is invalid")
    body = rom[start - BASE:end - BASE]
    if sha256(body).hexdigest() != entry["sha256"]:
        raise ProofError(f"shared-object evidence {start:08X}..{end:08X} changed")
    kind = entry["kind"]
    if kind not in ("dma-source", "dma-target"):
        raise ProofError(f"shared-object kind {kind} has no ROM reader")
    values, stores, at = {}, [], start
    for instruction in thumb_decoder().disasm(body, start):
        at = instruction.address + instruction.size
        mnemonic, ops = instruction.mnemonic, [o.strip() for o in instruction.op_str.split(",")]

        def value(name):
            if name.startswith("#"):
                return ("const", int(name[1:], 0) & 0xFFFFFFFF)
            return values.get(name)

        def combine(a, b, op):
            if a is None or b is None:
                if op in ("add", "sub") and (a and a[0] == "obj") and not (b and b[0] == "obj"):
                    return ("obj",)
                if op == "add" and (b and b[0] == "obj") and not (a and a[0] == "obj"):
                    return ("obj",)
                return None
            if a[0] == "const" and b[0] == "const":
                return ("const", (a[1] + b[1] if op == "add" else a[1] - b[1]) & 0xFFFFFFFF)
            if a[0] == "obj" and b[0] != "obj" or op == "add" and b[0] == "obj" and a[0] != "obj":
                return ("obj",)
            return None

        if mnemonic == "ldr" and "[pc" in instruction.op_str:
            target = ((instruction.address + 4) & ~3) + instruction.operands[1].mem.disp
            if not start <= instruction.address < end or not BASE <= target < BASE + len(rom) - 3:
                raise ProofError("shared-object evidence literal outside the ROM")
            word = struct.unpack_from("<I", rom, target - BASE)[0]
            values[ops[0]] = ("obj",) if address <= word < address + size else ("const", word)
        elif mnemonic in ("movs", "mov") and len(ops) == 2:
            values[ops[0]] = value(ops[1])
        elif mnemonic in ("adds", "add", "subs", "sub"):
            op = "add" if mnemonic.startswith("add") else "sub"
            a, b = (ops[0], ops[1]) if len(ops) == 2 else (ops[1], ops[2])
            values[ops[0]] = combine(value(a), value(b), op)
        elif mnemonic in ("lsls", "lsrs") and len(ops) == 3 and ops[2].startswith("#"):
            v = value(ops[1])
            amount = int(ops[2][1:], 0)
            values[ops[0]] = ("const", (v[1] << amount if mnemonic == "lsls" else v[1] >> amount) & 0xFFFFFFFF) \
                if v and v[0] == "const" else None
        elif mnemonic == "orrs":
            a, b = value(ops[0]), value(ops[1])
            ones = (a[1] if a and a[0] in ("const", "ones") else 0) | (b[1] if b and b[0] in ("const", "ones") else 0)
            values[ops[0]] = ("ones", ones) if ones else None
        elif mnemonic == "str":
            memory = instruction.operands[1].mem
            base = values.get(instruction.reg_name(memory.base))
            if memory.index or base is None or base[0] != "const":
                raise ProofError("shared-object evidence stores through an unknown address")
            stores.append(((base[1] + memory.disp) & 0xFFFFFFFF, values.get(ops[0]), instruction.address))
        elif mnemonic in ("cmp", "tst"):
            pass
        elif mnemonic.startswith("b") and mnemonic not in ("bl", "blx", "bx", "b", "bic", "bics") and \
                instruction.operands[0].imm > instruction.address:
            pass
        else:
            # anything else clobbers its first operand, or is refused outright
            if mnemonic in ("ldr", "ldrh", "ldrb", "ldrsh", "ldrsb", "lsls", "lsrs", "asrs", "ands",
                            "eors", "muls", "mvns", "negs", "rsbs") and ops:
                values[ops[0]] = None
            else:
                raise ProofError(f"shared-object evidence holds `{mnemonic}`, which its reader does not model")
    if at != end:
        raise ProofError("shared-object evidence does not end on an instruction")
    want = 0 if kind == "dma-source" else 4
    for index, (target, stored, site) in enumerate(stores):
        channel = DMA_SOURCE.get(target - want)
        if channel is None or stored != ("obj",):
            continue
        control = target - want + 8
        for later, word, control_site in stores[index + 1:]:
            if later == control and word and word[0] in ("const", "ones") and word[1] & 0x80000000:
                register = "SAD" if kind == "dma-source" else "DAD"
                return (f"{entry['symbol']} is a DMA{channel} {kind[4:]}: {site:08X} stores it to "
                        f"DMA{channel}{register} ({target:#010x}) and {control_site:08X} enables the channel "
                        f"(DMA{channel}CNT bit 31) in ROM {start:08X}..{end:08X} (SHA-256 {entry['sha256']})")
    raise ProofError(f"shared-object evidence {start:08X}..{end:08X} shows no DMA {kind[4:]} transfer of "
                     f"{entry['symbol']}")


def decode_bl(rom, at):
    """the target of the Thumb BL pair at ROM address `at`, or None"""
    if not BASE <= at <= BASE + len(rom) - 4 or at % 2:
        return None
    high, low = struct.unpack_from("<HH", rom, at - BASE)
    if high & 0xF800 != 0xF000 or low & 0xF800 != 0xF800:
        return None
    offset = (high & 0x7FF) << 12 | (low & 0x7FF) << 1
    return at + 4 + (offset - (1 << 23) if offset & 1 << 22 else offset)


def call_targets(compiled, address, rom):
    """{callee symbol: {the ROM's BL target at each of its call relocations}} of the compiled function"""
    text, start, size, relocations = compiled
    found = {}
    for at, kind, name in relocations:
        if kind == 10 and start <= at < start + size:
            found.setdefault(name, set()).add(decode_bl(rom, address + at - start))
    return found


def getter_evidence(rom, entry, pipeline=None):
    """the premise a scanline payload getter's ROM code establishes, or ProofError.

    The pinned getter must be exactly GETTER_SHAPE with its two BLs reaching
    TASK_DATA and PAYLOAD, whose bodies must be TASK_DATA_BODY and
    PAYLOAD_BODY; the scanline pipeline (allocator, manager, DMA programming
    and IRQ path) is bg_affine_rows.scanline_pipeline's evidence.  pipeline,
    when given, stands for that check (the synthetic-ROM tests); match.py and
    plausible.py never pass one.
    """
    address = int(entry["address"], 16)
    start, end = int(entry["start"], 16), int(entry["end"], 16)
    if (start, end) != (address, address + 16) or not BASE <= start < end <= BASE + len(rom):
        raise ProofError("payload getter evidence range is invalid")
    body = rom[start - BASE:end - BASE]
    if sha256(body).hexdigest() != entry["sha256"]:
        raise ProofError(f"payload getter evidence {start:08X}..{end:08X} changed")
    half = struct.unpack("<8H", body)
    if any(half[k] != v for k, v in GETTER_SHAPE.items()) or decode_bl(rom, start + 2) != TASK_DATA or \
            decode_bl(rom, start + 8) != PAYLOAD:
        raise ProofError(f"{entry['symbol']} is not `return {PAYLOAD:08X}(*(u32 *)({TASK_DATA:08X}(task) + 4))`")
    for target, expected in ((TASK_DATA, TASK_DATA_BODY), (PAYLOAD, PAYLOAD_BODY)):
        if target - BASE + 2 * len(expected) > len(rom) or \
                struct.unpack_from(f"<{len(expected)}H", rom, target - BASE) != expected:
            raise ProofError(f"{target:08X} is not the scanline task code the getter evidence reads")
    if pipeline is None:
        from bg_affine_rows import scanline_pipeline as pipeline
    try:
        pipeline(rom)
    except (ValueError, ImportError, OSError, struct.error) as error:
        raise ProofError(f"the scanline pipeline evidence does not hold ({error})") from None
    return (f"{entry['symbol']} returns a scanline task's payload: {PAYLOAD:08X}(*(u32 *)({TASK_DATA:08X}(task) + 4)) "
            f"in ROM {start:08X}..{end:08X} (SHA-256 {entry['sha256']}); {TASK_DATA:08X} is task + 0x18 and "
            f"{PAYLOAD:08X} returns the task's +0x14 when its halfword +0x10 is nonzero, else 0; the scanline "
            "manager 0800C4B4 passes that payload to the task's callback each frame to fill the bank its HBlank DMA "
            "transfers (bg_affine_rows.scanline_pipeline: allocator 0800C3CC, manager 0800C4B4, DMA 080009AC and "
            "080008E0, IRQ path)")


def pool_constant(function, value, depth=0):
    """whether value is, through single-definition pseudos, a load from the constant pool (`*.LC`): a
    constant the dump does not print, which the resolver would read as a word loaded from memory"""
    while code(value) == "reg" and int(value[1]) >= FIRST_PSEUDO and depth < 64:
        definitions = function.defs.get(int(value[1]), [])
        if len(definitions) != 1:
            return False
        value, depth = definitions[0][1], depth + 1
    return code(value) == "mem" and code(value[1]) == "symbol_ref" and \
        any(isinstance(x, str) and x.startswith('"*.LC') for x in flatten(value[1]))


def plain_argument(function, value):
    """None when value reaches, through copies of pseudos each set once, a register (a parameter's entry copy or
    a call's result) or a load from memory (the resolver reads a narrow one as an integer); otherwise what it
    is instead: a value computed by arithmetic or set in more than one place, whose kind the resolver may take
    from one side"""
    for _ in range(64):
        if code(value) != "reg" or int(value[1]) < FIRST_PSEUDO:
            break
        definitions = function.defs.get(int(value[1]), [])
        if len(definitions) != 1:
            return "a value set in more than one place" if definitions else "a value never set"
        value = definitions[0][1]
    else:
        return "a value copied too often to read"
    if code(value) in ("reg", "mem"):
        return None
    return f"a computed value ({code(value) or 'unparsed'})"


def call_arguments(function, callee, number=0):
    """[(Base, offset)] of argument register `number` at each call of `callee` in an expand dump: the
    register's last setting in the call's block, resolved (a constant-pool load is a constant). A parameter,
    call result or loaded word that is not that plain value (plain_argument) becomes Base("computed", what it
    is). ProofError when a call's block does not set it"""
    resolver, found = Resolver(function), []
    for call in function.insns:
        if call.code != "call_insn" or f'"{callee}"' not in flatten(call.pattern):
            continue
        for insn in reversed(function.insns[:call.index]):
            if insn.code in ("code_label", "call_insn", "barrier"):
                raise ProofError(f"r{number} is not set in the block of a call of {callee}")
            if insn.pattern is None:
                continue
            sets = function.sets(insn.pattern)
            hits = [(source, whole) for target, source, whole in sets
                    if code(target) == "reg" and int(target[1]) == number]
            if hits:
                source, whole = hits[0]
                value = insn.equal if insn.equal is not None and len(sets) == 1 and whole else source
                if pool_constant(function, value):
                    found.append((Base("int"), None))
                    break
                base, offset = resolver.resolve(value, insn.index)
                what = plain_argument(function, value)
                if base.kind in ("param", "ret", "word") and what:
                    base, offset = Base("computed", what), None
                found.append((base, offset))
                break
        else:
            raise ProofError(f"r{number} is not set before a call of {callee}")
    return found


def task_argument(base, getters):
    """what a getter's argument is, or ProofError when it cannot be a task (a constant, a data symbol, a
    local, a scanline payload or an unresolved value) or is not a plain one (call_arguments)"""
    if base.kind == "computed":
        raise ProofError(f"the getter is passed {base.value}: only a parameter, a call result or a word loaded "
                         "from memory is taken for a task")
    if base.kind == "param":
        return f"parameter r{base.value}" if base.value < 4 else f"stack parameter {base.value - 4}"
    if base.kind == "word":
        return "a word loaded from memory"
    if base.kind == "ret" and base.value not in getters:
        return f"the result of {base.value}" if base.value else "a call result"
    what = {"int": "a constant", "fixed": "a constant", "symbol": f"the data symbol {base.value}",
            "frame": "a local or frame slot", "ret": "a scanline payload"}.get(base.kind, "an unresolved value")
    raise ProofError(f"the getter is passed {what}, which is no task")


def object_premise(base, offset, width, stores_at_base, data_symbols, entries, rom, typed=None, calls=None,
                   pipeline=None, tasks=None):
    """(premise, offset premise or None) for one access, or ProofError.

    calls maps each callee symbol of the function to the ROM's BL targets at
    its calls (call_targets); tasks maps a listed getter to the resolved
    argument of each of its calls (call_arguments).  typed, when given, is a callable that may vouch
    for a parameter or call result (window_scanline's caller-path evidence in
    the instance test); match.py and plausible.py never pass one.
    """
    if typed is not None and base.kind in ("param", "ret"):
        premise = typed(base)
        if premise:
            return premise, None
    if base.kind == "ret":
        listed = [entry for entry in entries if entry.get("kind") == GETTER_KIND and entry.get("symbol") == base.value]
        if listed:
            entry = listed[0]
            if len(listed) != 1:
                raise ProofError(f"{base.value} is listed more than once")
            if (calls or {}).get(base.value) != {int(entry["address"], 16)}:
                raise ProofError(f"not every call of {base.value} in the function reaches {entry['address']} "
                                 "in the ROM")
            if offset is not None and offset < 0:
                raise ProofError(f"{base.value}'s payload{offset:+#x} lies before the payload")
            getters = {item.get("symbol") for item in entries if item.get("kind") == GETTER_KIND}
            arguments = sorted({task_argument(argument, getters) for argument, _ in (tasks or {}).get(base.value, [])})
            if not arguments:
                raise ProofError(f"the argument of {base.value} cannot be read")
            return getter_evidence(rom, entry, pipeline), (
                f"{base.value}'s argument ({', '.join(arguments)}) is a task whose data word +4 holds a scanline "
                f"task ({base.value} does not check the task kind), and offsets stay inside that payload (assumed: "
                "the proof does not bound them)")
    if base.kind == "fixed":
        if offset is None:
            raise ProofError(f"a variable offset from the constant address {base.value:#010x}: nothing bounds it")
        address = base.value + offset
        for name, low, high in OBJECT_WINDOWS:
            if low <= address and address + width <= high:
                return f"{name} at {address:#010x}", None
        if CART_BUS[0] <= address and address + width <= CART_BUS[1]:
            if not stores_at_base:
                raise ProofError(f"{address:#010x} is cartridge ROM space that the function never writes")
            return (f"cartridge bus at {address:#010x}, written by this function (a command to cartridge "
                    "hardware: ROM is not writable)"), None
        raise ProofError(f"{address:#010x} is in no hardware window")
    if base.kind == "symbol":
        mapped = data_symbols.get(base.value)
        try:
            location = int(mapped, 0) if isinstance(mapped, str) else int(mapped)
        except (TypeError, ValueError):
            raise ProofError(f"{base.value} is not mapped by config/data_symbols.json") from None
        listed = [entry for entry in entries if entry.get("symbol") == base.value and entry.get("kind") in DMA_KINDS]
        if listed:
            entry = listed[0]
            if len(listed) != 1 or int(entry["address"], 16) != location:
                raise ProofError(f"{base.value} is listed for another address")
            size = int(entry["size"])
            if offset is not None and not 0 <= offset <= size - width:
                raise ProofError(f"{base.value}+{offset:#x} lies outside its listed {size} bytes")
            premise = dma_evidence(rom, entry)
            return premise, (None if offset is not None else
                             f"variable offsets stay inside {base.value}'s {size} bytes (assumed: the proof does "
                             "not bound them)")
        if offset is None:
            raise ProofError(f"a variable offset from {base.value}, which volatile_objects.json does not size")
        return object_premise(Base("fixed", location), offset, width, stores_at_base, data_symbols, (), rom)[0] \
            .replace(" at ", f" ({base.value}) at ", 1), None
    reasons = {"param": "a parameter (callers are not traced)",
               "ret": "a call result (no listed scanline payload getter)",
               "frame": "a local or frame slot", "loaded": "a pointer loaded from memory",
               "int": "an integer", "unknown": "an unresolved address"}
    raise ProofError(f"the access goes through {reasons.get(base.kind, base.kind)}")


# ------------------------------------------------------------------ the unit and its variants

def candidate_offsets(text, admitted):
    """offsets of the source's `volatile` code tokens that no other exception admits"""
    import plausible
    code_view = plausible.strip_comments_and_strings(text)
    directives = [m.span() for m in plausible.DIRECTIVE.finditer(code_view)]
    found = []
    for match in plausible.VOLATILE_QUALIFIER.finditer(code_view):
        if match.start() in admitted:
            continue
        if match[0] != "volatile" or any(a <= match.start() < b for a, b in directives):
            return None
        found.append(match.start())
    return found


def unsupported_text(text):
    return any(marker in text for marker in ("\\", "??", "%:", "<:", ":>", "<%", "%>", "\0", "\r"))


def run(command, cwd):
    if platform.system() == "Windows":
        import match
        return match.Runner(match.DEFAULT_CC, root=str(cwd)).sh(f"cd {shlex.quote(str(cwd))} && {command}")
    result = subprocess.run(command, shell=True, capture_output=True, text=True, cwd=cwd, timeout=600)
    if result.returncode != 0:
        raise ProofError(f"`{command.split()[0]}` failed: {(result.stderr or result.stdout).strip()[:300]}")
    return result.stdout


def elf_function(data, name):
    """(.text, function offset, size, [(relocation offset, type)]) of an assembled object"""
    if data[:7] != b"\x7fELF\x01\x01\x01":
        raise ProofError("expected a little-endian ELF32 object")
    header = struct.unpack_from("<HHIIIIIHHHHHH", data, 16)
    offset, entry_size, count, names = header[5], header[10], header[11], header[12]
    sections = [struct.unpack_from("<IIIIIIIIII", data, offset + i * entry_size) for i in range(count)]
    section_data = [data[s[4]:s[4] + s[5]] if s[1] != 8 else b"" for s in sections]
    labels = section_data[names]

    def string(table, at):
        return table[at:table.index(b"\0", at)].decode("ascii")

    texts = [i for i, s in enumerate(sections) if string(labels, s[0]) == ".text"]
    if len(texts) != 1:
        raise ProofError("expected one .text section")
    text_index = texts[0]
    found, symbol_names = [], {}
    for table, (s, raw) in enumerate(zip(sections, section_data)):
        if s[1] == 2:
            strings = section_data[s[6]]
            symbol_names[table] = []
            for at in range(0, len(raw), 16):
                symbol, value, size, info, _, index = struct.unpack_from("<IIIBBH", raw, at)
                symbol_names[table].append(string(strings, symbol))
                if string(strings, symbol) == name and index == text_index:
                    found.append((value & ~1, size, value & 1))
    if len(found) != 1 or not found[0][1] or not found[0][2]:
        raise ProofError(f"expected one sized Thumb function {name}")
    relocations = []
    for s, raw in zip(sections, section_data):
        if s[1] == 9 and s[7] == text_index:
            names = symbol_names.get(s[6], [])
            for k in range(0, len(raw), 8):
                at_offset, info = struct.unpack_from("<II", raw, k)
                relocations.append((at_offset, info & 0xFF, names[info >> 8] if info >> 8 < len(names) else ""))
        elif s[1] == 4 and s[7] == text_index:
            raise ProofError("RELA relocations are not expected")
    return section_data[text_index], found[0][0], found[0][1], sorted(relocations)


def listing_uids(listing):
    """{insn uid: [(.text offset, instruction)]} from `as -aln` output of a -dp assembly"""
    uids, current = {}, None
    for line in listing.splitlines():
        match = re.match(r"\s*\d+\s+([0-9a-f]{4})\s+([0-9A-F]+)\s+(.*)$", line)
        if not match:
            if re.match(r"\s*\d+\s+@ 0x", line) or re.match(r"\s*\d+\s+\S*:", line):
                current = None
            continue
        offset, source = int(match[1], 16), match[3]
        tag = re.search(r"@ (\d+)\t", source)
        if tag:
            current = int(tag[1])
            uids.setdefault(current, []).append((offset, source.split("@")[0].strip()))
        elif current is not None and not source.lstrip().startswith((".", "@")):
            uids[current].append((offset, source.split("@")[0].strip()))
    return uids


THUMB_ACCESS = (  # (mask, value, store, width)
    (0xF800, 0x7800, False, 1), (0xFE00, 0x5C00, False, 1), (0xFE00, 0x5600, False, 1),
    (0xF800, 0x7000, True, 1), (0xFE00, 0x5400, True, 1),
    (0xF800, 0x8800, False, 2), (0xFE00, 0x5A00, False, 2), (0xFE00, 0x5E00, False, 2),
    (0xF800, 0x8000, True, 2), (0xFE00, 0x5200, True, 2),
    (0xF800, 0x6800, False, 4), (0xFE00, 0x5800, False, 4),
    (0xF800, 0x6000, True, 4), (0xFE00, 0x5000, True, 4))


def rom_access(rom, address, length, store, width):
    """the ROM address of a load/store of that width and direction in [address, address + length)"""
    for at in range(address, address + length, 2):
        half = struct.unpack_from("<H", rom, at - BASE)[0]
        if any(half & mask == value and s == store and w == width for mask, value, s, w in THUMB_ACCESS):
            return at
    return None


class Unit:
    """the addressed source's unit in a work directory, compiled as variants"""

    def __init__(self, tree, relpath, text, offsets, work, dependencies=None):
        """dependencies, when given, collects (path, SHA-256) of every file the unit reads"""
        import plausible
        self.tree, self.work = Path(tree).resolve(), Path(work)
        command = f"cpp {plausible.CPP_OPTIONS} {shlex.quote(relpath)}"
        run(f"{command} -o {shlex.quote(str(self.work / 'real.i'))}", self.tree)
        real = (self.work / "real.i").read_bytes().decode("utf-8")
        names = set()
        for marker in re.finditer(r'(?m)^#[ \t]+[0-9]+[ \t]+"((?:\\.|[^"\\\n])*)"', real):
            if not (marker[1].startswith("<") and marker[1].endswith(">")):
                names.add(os.path.normpath(marker[1]))
        if any(os.path.isabs(name) or name.split(os.sep)[0] == os.pardir for name in names) or relpath not in names:
            raise ProofError("the unit reads a file outside its tree")
        if dependencies is not None:
            dependencies.extend((str(self.tree / name), sha256((self.tree / name).read_bytes()).hexdigest())
                                for name in sorted(names))
        forbidden = [real] + [(self.tree / name).read_text(encoding="utf-8", errors="replace") for name in names]
        while True:
            markers = ["__" + "".join(secrets.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(6))
                       for _ in offsets]
            if len(set(markers)) == len(markers) and not any(m in t for m in markers for t in forbidden):
                break
        copy = self.work / "copy"
        for name in names:
            target = copy / name
            target.parent.mkdir(parents=True, exist_ok=True)
            data = (self.tree / name).read_text(encoding="utf-8")
            if name == relpath:
                if data != text:
                    raise ProofError("the source changed while it was checked")
                pieces, last = [], 0
                for offset, marker in zip(offsets, markers):
                    if data[offset:offset + 8] != "volatile":
                        raise ProofError("candidate offsets do not hold the qualifier")
                    pieces += [data[last:offset], marker]
                    last = offset + 8
                data = "".join(pieces) + data[last:]
            target.write_text(data, encoding="utf-8")
        run(f"{command} -o {shlex.quote(str(self.work / 'marked.i'))}", copy)
        marked = (self.work / "marked.i").read_bytes().decode("utf-8")
        restored = marked
        for marker in markers:
            if len(re.findall(r"\b" + marker + r"\b", marked)) != 1 or marked.count(marker) != 1:
                raise ProofError("a candidate qualifier does not reach the unit exactly once")
            restored = restored.replace(marker, "volatile")
        if restored != real:
            raise ProofError("the unit changes when only its candidate qualifiers are renamed")
        self.real, self.marked, self.markers = real, marked, markers

    def variant(self, removed):
        text = self.marked
        for index, marker in enumerate(self.markers):
            text = text.replace(marker, " " * 8 if index == removed else "volatile")
        return text

    def compile(self, label, preprocessed, name):
        directory = self.work / label
        directory.mkdir()
        (directory / "f.i").write_text(preprocessed, encoding="utf-8")
        run(f"{CC} {FLAGS} f.i -o p.s && {AS} -mthumb-interwork p.s -o p.o && "
            f"{CC} {FLAGS} {DUMP_FLAGS} f.i -o f.s && {AS} -mthumb-interwork -aln=f.lst f.s -o f.o", directory)
        plain = elf_function((directory / "p.o").read_bytes(), name)
        dumped = elf_function((directory / "f.o").read_bytes(), name)
        if plain != dumped:
            raise ProofError(f"-da -dp changed the {label} compile's code")
        dumps = {}
        for suffix in PASSES:
            path = directory / f"f.i.{suffix}"
            if path.is_file():
                functions = parse_dump(path.read_text(encoding="utf-8", errors="replace"))
                dumps[suffix] = {key: Function(value) for key, value in functions.items()}
        for required in ("rtl", "cse", "flow", "combine", "mach"):
            if name not in dumps.get(required, {}):
                raise ProofError(f"the {label} compile wrote no {required} dump of {name}")
        return {"text": plain, "dumps": dumps, "uids": listing_uids((directory / "f.lst").read_text())}


# ------------------------------------------------------------------ the proof

def prove(tree, project, relpath, text, admitted, data_symbols, entries=None, rom=None, typed=None,
          dependencies=None, pipeline=None):
    """[(source offset, verdict)] for every candidate token; a verdict is
    ("admitted", record fragment) or ("refused", reason).  None when the source
    has no candidate; ProofError when no token can be decided."""
    match = re.fullmatch(r"src/(?:[^/]+/)*([0-9A-F]{8})\.c", relpath or "")
    if not match:
        return None
    if unsupported_text(text):
        raise ProofError("a line splice, digraph, trigraph, NUL or carriage return")
    offsets = candidate_offsets(text, admitted)
    if offsets is None:
        raise ProofError("a candidate is spelt otherwise or sits in a directive")
    if not offsets:
        return None
    if len(offsets) > MAX_CANDIDATES:
        raise ProofError(f"more than {MAX_CANDIDATES} candidate qualifiers")
    address = int(match[1], 16)
    name = f"func_{address:08X}"
    entries = load_objects() if entries is None else entries
    if rom is None:
        from rompath import rom_path
        try:
            located = rom_path(project, required=False)
        except SystemExit as error:
            raise ProofError(str(error)) from None
        if located is None:
            raise ProofError("no ROM to read the evidence from")
        rom = Path(located).read_bytes()
    build = Path(tree).resolve() / "build"
    build.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ffta_vrp_", dir=build) as work:
        unit = Unit(tree, relpath, text, offsets, work, dependencies)
        real = unit.compile("real", unit.real, name)
        stripped = [unit.compile(f"s{k}", unit.variant(k), name) for k in range(len(offsets))]
    verdicts = [verdict(address, name, real, variant, rom, data_symbols, entries, 1 + text.count("\n", 0, offset),
                        typed, pipeline) for offset, variant in zip(offsets, stripped)]
    return list(zip(offsets, settle(verdicts)))


def function_matches_rom(compiled, address, rom):
    text, start, size, relocations = compiled
    body = bytearray(text[start:start + size])
    want = bytearray(rom[address - BASE:address - BASE + size])
    for at, kind, _ in relocations:
        if not start <= at < start + size:
            continue
        if kind not in (2, 10) or at + 4 > start + size:
            raise ProofError(f"relocation type {kind} in the function")
        body[at - start:at - start + 4] = want[at - start:at - start + 4]
    if bytes(body) != bytes(want):
        raise ProofError("the compiled function is not the ROM's (not a match, or another toolchain)")


def verdict(address, name, real, stripped, rom, data_symbols, entries, line, typed=None, pipeline=None):
    """(state, record fragment or reason, the R references the token claims)"""
    try:
        fragment, claimed = token_record(address, name, real, stripped, rom, data_symbols, entries, line, typed,
                                         pipeline)
        return "admitted", fragment, claimed
    except ProofError as refusal:
        return "refused", str(refusal), set()


def settle(verdicts):
    """[(state, text)]: an admitted token that claims a reference another token claims too is refused"""
    out = []
    for index, (state, text, claimed) in enumerate(verdicts):
        shared = any(claimed & other for k, (_, _, other) in enumerate(verdicts) if k != index)
        out.append(("refused", "another qualifier claims the same access") if state == "admitted" and shared
                   else (state, text))
    return out


def align(ours, plain):
    """[(real reference, its plain counterpart or None)] for the qualifier's accesses.

    The plain expand dump's references must be the real one's in order, apart
    from volatile real references the plain build does not expand at all (a
    value it never reads); among equal references the first ones pair.  A
    reference only the plain build has, or one whose flag changes the other
    way, refuses.
    """
    pairs, j = [], 0
    for reference in ours:
        if j < len(plain) and plain[j][1:4] == reference[1:4]:
            if reference[4] and not plain[j][4]:
                pairs.append((reference, plain[j]))
            elif reference[4] != plain[j][4]:
                raise ProofError("a memory reference is volatile only without the qualifier")
            j += 1
        elif reference[4]:
            pairs.append((reference, None))
        else:
            raise ProofError("the two expand dumps differ in their memory references")
    if j != len(plain):
        raise ProofError("the non-volatile build expands a memory reference the real one does not")
    return pairs


def ambiguous(ours, accesses):
    """whether one of the token's accesses prints like a reference of the function that is not the token's:
    the pairing could then have given the token another reference (`T*` prints alike)"""
    claimed = {(reference[0], reference[5]) for reference, _ in accesses}
    signatures = {reference[1:4] for reference, _ in accesses}
    return any(reference[1:4] in signatures and (reference[0], reference[5]) not in claimed for reference in ours)


def token_record(address, name, real, stripped, rom, data_symbols, entries, line, typed=None, pipeline=None):
    function_matches_rom(real["text"], address, rom)
    if real["text"] == stripped["text"]:
        raise ProofError("removing it does not change the code")
    for other in real["dumps"]["mach"]:
        if other != name and any("v" in rtl_flags(m) for _, m, _ in real["dumps"]["mach"][other].mems()):
            raise ProofError(f"{other} holds a volatile reference too")
    mine, theirs = real["dumps"]["rtl"][name], stripped["dumps"]["rtl"][name]
    ours = references(mine)
    accesses = align(ours, references(theirs))
    if not accesses:
        raise ProofError("it qualifies no memory reference of the function")
    claimed = {(reference[0], reference[5]) for reference, _ in accesses}
    if ambiguous(ours, accesses):
        raise ProofError("an access prints like another reference of the function, so which one the qualifier "
                         "changed is ambiguous")
    resolver = Resolver(mine)
    insn_of = {insn.uid: insn for insn in mine.insns}
    sites, stripped_dumps = [], {key: value[name] for key, value in stripped["dumps"].items() if name in value}
    start = real["text"][1]
    resolved = []
    for (uid, store, mode, _, _, index), plain in accesses:
        if mode not in MODE_BYTES:
            raise ProofError(f"a {mode} access")
        insn = insn_of[uid]
        mem, _ = walk_mems(insn.pattern, [])[index]
        base, offset = resolver.address(insn, mem)
        resolved.append((base, offset, MODE_BYTES[mode], store))
        lines = real["uids"].get(uid)
        category, where = fate(stripped_dumps, plain[0], store, mode, stripped["uids"]) if plain else \
            ("dropped", "expand")
        if not lines:
            # R does not emit it: the ROM cannot show its fate, which never counts
            sites.append((None, store, MODE_BYTES[mode], category, where))
            continue
        low = min(at for at, _ in lines) - start
        high = max(at for at, _ in lines) + 2 - start
        if low < 0 or high > real["text"][2]:
            raise ProofError("an access lies outside the function")
        at = rom_access(rom, address + low, high - low, store, MODE_BYTES[mode])
        if at is None:
            raise ProofError(f"the ROM holds no {'store' if store else 'load'} of {MODE_BYTES[mode]} "
                             f"bytes at {address + low:08X}")
        sites.append((at, store, MODE_BYTES[mode], category, where))
    if not any(site[0] is not None and site[3] in EVIDENCE for site in sites):
        raise ProofError("the non-volatile build drops, merges and moves none of its accesses (" +
                         ", ".join(("not emitted" if site[0] is None else f"{site[3]}" +
                                    (f" in {site[4]}" if site[4] != "final" else "")) for site in sites) + ")")
    # only a store the ROM holds makes the function a writer of its base
    stores_at = {base for (base, _, _, store), site in zip(resolved, sites)
                 if store and site[0] is not None and base.kind in ("fixed", "symbol")}
    calls = call_targets(real["text"], address, rom)
    getters = {entry.get("symbol") for entry in entries if entry.get("kind") == GETTER_KIND}
    tasks = {base.value: call_arguments(mine, base.value)
             for base, _, _, _ in resolved if base.kind == "ret" and base.value in getters}
    premises, ranges = [], []
    for base, offset, width, store in resolved:
        object_text, range_text = object_premise(base, offset, width, base in stores_at, data_symbols, entries, rom,
                                                 typed, calls, pipeline, tasks)
        if object_text not in premises:
            premises.append(object_text)
        if range_text and range_text not in ranges:
            ranges.append(range_text)
    width_name = {1: "byte", 2: "halfword", 4: "word"}
    listed = "; ".join(
        (f"{at:08X} {width_name[width]} {'store' if store else 'load'} {category}" +
         (f" ({where})" if where != "final" else "") if at is not None else
         f"a {width_name[width]} {'store' if store else 'load'} the real build does not emit")
        for at, store, width, category, where in sites)
    digest = sha256(real["text"][0]).hexdigest(), sha256(stripped["text"][0]).hexdigest()
    return (f"line {line}: {'; '.join(premises)}" + (f"; premise: {'; '.join(ranges)}" if ranges else "") +
            f"; accesses in the non-volatile build: {listed}; .text with/without `{digest[0]}`/`{digest[1]}`"), \
        claimed


# ------------------------------------------------------------------ plausible.py and the report

_CACHE = {}


def cached_proof(tree, project, relpath, text, admitted, data_symbols):
    if not re.fullmatch(r"src/(?:[^/]+/)*[0-9A-F]{8}\.c", relpath or ""):
        return None
    try:
        from rompath import rom_path
        located = rom_path(project, required=False)
        rom_key = (str(located), os.stat(located).st_size, os.stat(located).st_mtime_ns) if located else None
    except (SystemExit, OSError):
        rom_key = None
    key = (str(Path(tree).resolve()), str(Path(project).resolve()), rom_key, relpath, text, tuple(sorted(admitted)),
           json.dumps(data_symbols, sort_keys=True), OBJECTS.read_bytes() if OBJECTS.is_file() else b"")
    try:
        unit_files = sorted(Path(tree, "include").rglob("*.h")) + sorted(Path(tree, "src").rglob("*.h"))
        key += tuple(sha256(path.read_bytes()).hexdigest() for path in unit_files)
    except OSError:
        return None

    def current(dependencies):
        try:
            return all(sha256(Path(path).read_bytes()).hexdigest() == digest for path, digest in dependencies)
        except OSError:
            return False

    # a cached proof is reused only while every file its compiles read is unchanged
    if key not in _CACHE or not current(_CACHE[key][1]):
        dependencies = []
        try:
            _CACHE[key] = prove(tree, project, relpath, text, admitted, data_symbols,
                                dependencies=dependencies), dependencies
        except (ProofError, OSError, UnicodeError, ImportError, subprocess.SubprocessError, KeyError,
                TypeError, IndexError) as refusal:
            _CACHE[key] = str(refusal) or type(refusal).__name__, dependencies
    return _CACHE[key][0]


def qualifier_offsets(text, tree, project, relpath, admitted, data_symbols):
    """the offsets of the qualifiers this proof admits (plausible.check_view)"""
    result = cached_proof(tree, project, relpath, text, admitted, data_symbols)
    if not isinstance(result, list):
        return set()
    return {offset for offset, (state, _) in result if state == "admitted"}


def record(root, address):
    """the report record, or None when the source has no qualifier this proof admits"""
    import plausible
    root = Path(root)
    sources = sorted((root / "src").rglob(f"{address:08X}.c"))
    if len(sources) != 1:
        return None
    path = sources[0]
    relpath = path.relative_to(root).as_posix()
    try:
        text = path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
        if not plausible.VOLATILE_QUALIFIER.search(plausible.strip_comments_and_strings(text)):
            return None
        data_symbols = plausible.data_symbols_of(root)
        admitted = plausible.exempt_qualifiers(text, relpath, data_symbols, root, root,
                                               plausible.include_closure(root, path))
    except (OSError, UnicodeError, ValueError):
        return None
    result = cached_proof(root, root, relpath, text, admitted, data_symbols)
    if not isinstance(result, list):
        return None
    tokens = [fragment for _, (state, fragment) in result if state == "admitted"]
    if not tokens:
        return None
    return (f"{RECORD} `{SCHEMA}`, compiled `{CC} {FLAGS}` as written and without each qualifier, "
            f"with `{DUMP_FLAGS}` (code unchanged); " + " | ".join(tokens))


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--root", default=".")
    parser.add_argument("address")
    args = parser.parse_args()
    import plausible
    root = Path(args.root).resolve()
    address = int(args.address, 16)
    sources = sorted((root / "src").rglob(f"{address:08X}.c"))
    if len(sources) != 1:
        sys.exit(f"expected one src/**/{address:08X}.c")
    relpath = sources[0].relative_to(root).as_posix()
    text = sources[0].read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
    # as record() and plausible.py: a qualifier only in a comment or a string is no candidate
    if not plausible.VOLATILE_QUALIFIER.search(plausible.strip_comments_and_strings(text)):
        print("no candidate qualifier")
        return 0
    data_symbols = plausible.data_symbols_of(root)
    admitted = plausible.exempt_qualifiers(text, relpath, data_symbols, root, root,
                                           plausible.include_closure(root, sources[0]))
    try:
        result = prove(root, root, relpath, text, admitted, data_symbols)
    except ProofError as refusal:
        print(f"refused: {refusal}")
        return 1
    if result is None:
        print("no candidate qualifier")
        return 0
    for offset, (state, detail) in result:
        print(f"{state}: {detail}" if state == "admitted" else
              f"line {1 + text.count(chr(10), 0, offset)}: {state}: {detail}")
    return 0 if all(state == "admitted" for _, (state, _) in result) else 1


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    sys.exit(main())
