"""Variable indices into private stack arrays under explicit, reviewed runtime premises.

This is an opt-in companion of the core Thumb verifier in match.py, used only by
`named-data-buffer-stack-index-v1`.  Like `local-rom-halfword-table-v1`, which
proves its owner under the premise `(entry_R0 & 255) < 4`, it does not infer a
bound from types or callers.  A variable index into a private stack array is
admitted when, for every such access, either

* in-function value ranges already prove the access in bounds (nothing is
  assumed), or
* the index has a *defined source* and the access is in bounds under one
  recorded premise.  The premise is an unproved runtime premise: nothing here
  proves it, and an owner is admitted only when the decomp root's
  `config/stack_index_premises.json` holds a reviewed entry that repeats every
  premise row exactly (see ``accept``).

Defined sources are the entry registers R0-R3, loads through a defined address
(a struct field), the value a call returned in R0, and constants, combined by
masks, shifts, adds, subtracts, ors and multiplies.  An index that reaches the
access through a join of different derivations, through the stack, or through an
unmodelled instruction has no defined source and the access is refused.

The premise is per access site and says: whenever the site executes, the
unsigned index expression is below K, so that every byte the access can touch
lies inside the array.  The array is the object the compiler addressed:

* its start is the entry-SP-relative address the access has at index 0;
* its end is the nearest of (a) the next origin in the function (an
  address-of-local `add Rd,sp,#k` or `mov Rd,sp`, a ROM copy destination, or a
  local reloaded at a fixed offset, by `ldr Rd,[sp,#k]`, a load through an exact
  stack alias or an `ldm` from one, as a spill is) or the top of the
  frame and, for a load, (b) the end of the run of bytes initialised on every
  path from that start (a ROM table copy, an `stm` copy, plain stores).

Every index value the premise admits is congruent to the index-zero address
modulo the access width, so no admitted access is misaligned.  A struct field
in an index is tagged with its load site, and a row is marked "may be
owner-written" when a store through a non-stack address, or a call, can run
before that load.

Every byte of the array must be an allocated local word (never a saved
register, an incoming argument or below SP), and for loads initialised.  Reads
and writes are both allowed under the premise; a write through a variable
address initialises nothing.  A variable stack address may be copied, moved by
an immediate, combined with further scalar indices, or used as the base of one
load or store.  It may not be stored, pushed, compared, passed in R0-R3, or be
live in a return-visible register at a return.  Escapes of the array's exact
address are the buffer proof's business and still refuse unless a callee is
proved to bound them.

The values the core cannot represent are owned completely by this module: it
re-decodes the verified body as raw Thumb-1 and runs one abstract interpretation
(unsigned intervals with power-of-two congruence, CMP + branch refinement,
threshold widening, word-level frame kinds, a must-initialised byte set, and one
derivation expression per register).
"""
import json

from capstone.arm import ARM_REG_R0, ARM_REG_SP

import named_data_buffer_profile as named
import rom_table_copy_profile as rom_copy

SELECTOR = named.STACK_INDEX_SELECTOR
SCHEMA = named.STACK_INDEX_SCHEMA
CONTROL_FLOW = ("complete named-data owner with ROM-proved bounded buffer callees, ROM table copies "
                "and variable private-stack-array indices proved in bounds or admitted under "
                "reviewed, recorded unproved runtime premises")
MAX_DEPENDENCIES = rom_copy.MAX_DEPENDENCIES
SUMMARY = ("variable private-stack-array indices proved in bounds, each either by in-function "
           "value ranges or under a reviewed, recorded runtime premise that is NOT proved: "
           "the index expression, from entry registers, struct fields and call results, is below "
           "the array extent whenever the access executes")
PREMISES_PATH = "config/stack_index_premises.json"
ROW_KEYS = ("site", "expression", "bound")

MASK = 0xFFFFFFFF
SIGNED_MAX = 0x7FFFFFFF
BIG = 1 << 40
MAX_UPDATES = 50000
MAX_FRAME_WORDS = 1024
ALIAS_WIDEN_AFTER = 16
MAX_EXPR_NODES = 24
TOP = ("S", 0, MASK, 0)
POISON = ("P",)
OPAQUE = ("O",)
EXIT = None
# Mirrors the core: every register but IP, SP and PC is visible after a return.
RETURN_VISIBLE = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14)
ALU_EXPR = {0: "and", 1: "eor", 12: "orr", 13: "mul", 14: "bic"}


class Refusal(ValueError):
    pass


class PremiseRefusal(ValueError):
    """Every access is admissible, but its premises have no reviewed entry; ``entry`` is the one to add."""

    def __init__(self, message, entry):
        super().__init__(message)
        self.entry = entry


def refuse(message):
    raise Refusal(f"stack index: {message}")


# ---- derivation expressions: hashable tuples --------------------------------------
def nodes(expr):
    return 1 + sum(nodes(part) for part in expr if type(part) is tuple)


FOLD = {"add": lambda a, b: a + b, "sub": lambda a, b: a - b, "and": lambda a, b: a & b,
        "orr": lambda a, b: a | b, "eor": lambda a, b: a ^ b, "mul": lambda a, b: a * b}


def make(*expr):
    if any(part is None for part in expr):
        return None
    if expr[0] == "bin" and expr[1] in FOLD and expr[2][0] == "c" and expr[3][0] == "c":
        return ("c", FOLD[expr[1]](expr[2][1], expr[3][1]) & MASK)
    return expr if nodes(expr) <= MAX_EXPR_NODES else None


def render(expr):
    kind = expr[0]
    if kind == "c":
        return str(expr[1]) if expr[1] < 0x10000 else f"0x{expr[1]:08X}"
    if kind == "entry":
        return f"entry_R{expr[1]}"
    if kind == "ret":
        return f"ret(0x{expr[1]:08X})"
    if kind == "ld":
        return f"{'s' if expr[2] else 'u'}{8 * expr[1]}[{render(expr[3])}]@0x{expr[4]:08X}"
    if kind == "sh":
        return f"({render(expr[2])} {expr[1]} {expr[3]})"
    symbol = {"add": "+", "sub": "-", "and": "&", "orr": "|", "eor": "^", "mul": "*",
              "bic": "&~"}[expr[1]]
    return f"({render(expr[2])} {symbol} {render(expr[3])})"


def load_sites(expr):
    """The sites of every struct-field load the expression reads."""
    found = {expr[4]} if expr[0] == "ld" else set()
    for part in expr:
        if type(part) is tuple:
            found |= load_sites(part)
    return found


def shift_expr(operation, value, amount):
    """Compose a constant shift, recognising the u8/u16 narrowing idiom."""
    if value is None:
        return None
    if operation == ">>" and amount in (16, 24) and value[0] == "sh" and \
            value[1] == "<<" and value[3] == amount:
        return make("bin", "and", value[2], ("c", (1 << (32 - amount)) - 1))
    return make("sh", operation, value, amount)


# ---- policy: what the core defers ---------------------------------------------------
class Policy:
    """Collect the core's deferred sites, then prove them in ``finish``."""

    def __init__(self, owner, size):
        self.owner, self.size = owner, size
        self.derivations = set()
        self.accesses = set()
        self.evidence = None

    def applies(self, address, data):
        return address == self.owner and len(data) == self.size

    def defer_derivation(self, instruction, aliases):
        raw = int.from_bytes(bytes(instruction.bytes[:2]), "little")
        if instruction.size != 2 or len(instruction.bytes) != 2:
            return False
        if raw & 0xFE00 == 0x1800:
            operands = (ARM_REG_R0 + ((raw >> 3) & 7), ARM_REG_R0 + ((raw >> 6) & 7))
        elif raw & 0xFF00 == 0x4400:
            destination = (raw & 7) | ((raw >> 4) & 8)
            source = (raw >> 3) & 15
            if destination >= 13 or source in (14, 15):
                return False
            operands = (ARM_REG_R0 + destination, ARM_REG_R0 + source if source != 13 else ARM_REG_SP)
        else:
            return False
        read = set(instruction.regs_access()[0])
        if not (read & (set(aliases) | {ARM_REG_SP})) <= set(operands):
            return False
        self.derivations.add(instruction.address)
        return True

    def defer_access(self, instruction):
        raw = int.from_bytes(bytes(instruction.bytes[:2]), "little")
        if instruction.size != 2 or raw & 0xF000 != 0x5000:
            return False
        self.accesses.add(instruction.address)
        return True

    def finish(self, data, address, instructions, copies):
        self.evidence = prove(data, address, sorted(instruction.address for instruction in instructions),
                              frozenset(self.derivations), frozenset(self.accesses), copies)
        return self.evidence


def manifest_text(evidence):
    return json.dumps(evidence, sort_keys=True, separators=(",", ":"))


def precondition_lines(evidence):
    """One human-readable line per premise; the replayed report must repeat them exactly."""
    lines = []
    for row in evidence["preconditions"]:
        low, high = row["array_sp"]
        entry_low, entry_high = row["array_entry_sp"]
        lines.append(f"* stack index premise: site 0x{row['site']:08X} index {row['expression']} < "
                     f"{row['bound']}, array sp{low:+#x}..{high:+#x} "
                     f"(entry_SP{entry_low:+#x}..{entry_high:+#x}) s={row['scale']}, {row['kind']} "
                     f"width {row['width']}, unproved runtime premise"
                     f"{', may be owner-written' if row['may_be_owner_written'] else ''}, "
                     f"accepted by {row['discharged_by']}")
    return lines


def suggested_entry(evidence):
    """The config entry a reviewer copies once every row has been checked against the callers."""
    return {"review": "<why every execution of each site keeps its index below the bound>",
            "rows": [{"site": f"0x{row['site']:08X}", "expression": row["expression"],
                      "bound": row["bound"]} for row in evidence["preconditions"]]}


def parse_premises(snapshot):
    """Parse the decomp's reviewed premise file: {"0xADDRESS": {"review": str, "rows": [...]}}."""
    if snapshot is None:
        return {}

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate key in stack index premises")
            result[key] = value
        return result

    document = json.loads(snapshot, object_pairs_hook=unique)
    if not isinstance(document, dict):
        raise ValueError("stack index premises must be an object keyed by function address")
    entries = {}
    for key, entry in document.items():
        if not isinstance(key, str) or len(key) != 10 or not key.startswith("0x") or \
                key != f"0x{int(key, 16):08X}":
            raise ValueError("stack index premise keys are canonical 0xXXXXXXXX addresses")
        if not isinstance(entry, dict) or set(entry) != {"review", "rows"} or \
                not isinstance(entry["review"], str) or not entry["review"].strip() or \
                entry["review"].strip().startswith("<") or \
                any(word in entry["review"].upper() for word in ("SCRATCH", "TODO")) or \
                not isinstance(entry["rows"], list) or not entry["rows"]:
            raise ValueError(f"stack index premise entry {key} needs a written review and its rows")
        for row in entry["rows"]:
            if not isinstance(row, dict) or set(row) != set(ROW_KEYS) or \
                    not isinstance(row["site"], str) or not isinstance(row["expression"], str) or \
                    type(row["bound"]) is not int:
                raise ValueError(f"stack index premise rows of {key} are exactly site, expression, bound")
        entries[int(key, 16)] = entry
    return entries


def accept(evidence, address, premises):
    """Bind the reviewed entry for ``address``; refuse, printing the rows to review, without one."""
    generated = suggested_entry(evidence)["rows"]
    entry = premises.get(address) if premises else None
    if generated and (entry is None or entry["rows"] != generated):
        text = json.dumps({f"0x{address:08X}": suggested_entry(evidence)}, indent=2)
        raise PremiseRefusal(
            f"stack index: the premise rows of 0x{address:08X} need a reviewed entry in "
            f"{PREMISES_PATH} that repeats them exactly ("
            f"{'none found' if entry is None else 'the entry differs'}); after checking every "
            f"caller, add:\n{text}", suggested_entry(evidence))
    if not generated and entry is not None:
        raise ValueError(f"stack index: {PREMISES_PATH} lists premises 0x{address:08X} does not need")
    accepted = dict(evidence)
    accepted["preconditions"] = [dict(row, premise_proved=False, discharged_by=PREMISES_PATH)
                                 for row in evidence["preconditions"]]
    accepted["accepted"] = entry
    return accepted


# ---- value domain ----------------------------------------------------------------------
def ctz(value):
    return 32 if value == 0 else min(32, (value & -value).bit_length() - 1)


def norm(kind, lo, hi, modulus, ranged=False, c=None, texpr=None):
    if lo > hi:
        return None
    modulus = min(max(modulus, 0), 32)
    if lo == hi:
        modulus = 32
    else:
        step = 1 << modulus
        hi = lo + ((hi - lo) // step) * step
        if hi == lo:
            modulus = 32
    if kind == "S":
        return ("S", lo, hi, modulus)
    return ("A", lo, hi, modulus, ranged, c, texpr)


def exact_alias(offset):
    return norm("A", offset, offset, 32, False, offset, None)


def const(value):
    return ("S", value & MASK, value & MASK, 32)


def is_ranged(value):
    return value[0] == "P" or value[0] == "A" and value[4]


def join_values(left, right):
    if left == right:
        return left
    if left[0] == "P" or right[0] == "P":
        return POISON
    kinds = {left[0], right[0]}
    if kinds == {"S"}:
        modulus = min(left[3], right[3], ctz(abs(left[1] - right[1])))
        return norm("S", min(left[1], right[1]), max(left[2], right[2]), modulus)
    if kinds == {"A"}:
        if not left[4] and not right[4]:
            return OPAQUE       # differing exact aliases stay in the core's domain
        modulus = min(left[3], right[3], ctz(abs(left[1] - right[1])))
        same = left[5] == right[5] and left[6] == right[6]
        return norm("A", min(left[1], right[1]), max(left[2], right[2]), modulus, True,
                    left[5] if same else None, left[6] if same else None)
    if any(is_ranged(value) for value in (left, right)):
        return POISON
    return OPAQUE


def clip(value, lower, upper):
    """Intersect a scalar with [lower, upper], keeping its congruence; None if empty."""
    _, lo, hi, modulus = value
    step = 1 << modulus
    if lower > lo:
        lo += -(-(lower - lo) // step) * step
    if upper < hi:
        if upper < lo:
            return None
        hi = lo + ((upper - lo) // step) * step
    return norm("S", lo, hi, modulus)


def refine(condition, left, right):
    """Return (taken, fallthrough) refinements of the compared scalar.

    None marks an infeasible edge. Signed conditions refine only when both
    operands are proved non-negative, where they coincide with unsigned ones.
    """
    if left[0] != "S" or right[0] != "S":
        return left, left
    if condition in (10, 11, 12, 13):
        if left[2] > SIGNED_MAX or right[2] > SIGNED_MAX:
            return left, left
        condition = {10: 2, 11: 3, 12: 8, 13: 9}[condition]
    at_least = lambda bound: clip(left, bound, MASK) if bound <= MASK else None
    at_most = lambda bound: clip(left, 0, bound) if bound >= 0 else None
    if condition in (0, 1):
        equal = clip(left, right[1], right[2])
        different = left
        if right[1] == right[2]:
            if right[1] == left[1] == left[2]:
                different = None
            elif right[1] == left[1]:
                different = at_least(right[1] + 1)
            elif right[1] == left[2]:
                different = at_most(right[1] - 1)
        return (equal, different) if condition == 0 else (different, equal)
    if condition == 2:      # CS/HS: left >= right
        return at_least(right[1]), at_most(right[2] - 1)
    if condition == 3:      # CC/LO: left < right
        return at_most(right[2] - 1), at_least(right[1])
    if condition == 8:      # HI: left > right
        return at_least(right[1] + 1), at_most(right[2])
    if condition == 9:      # LS: left <= right
        return at_most(right[2]), at_least(right[1] + 1)
    return left, left


def wrapped(residue, modulus):
    """Any u32 value congruent to residue modulo 2**modulus (after wraparound)."""
    modulus = min(modulus, 32)
    return norm("S", residue % (1 << modulus), MASK, modulus)


def add_values(left, right):
    if left[0] == "S" and right[0] == "S":
        modulus = min(left[3], right[3])
        if left[2] + right[2] > MASK:
            return wrapped(left[1] + right[1], modulus)
        return norm("S", left[1] + right[1], left[2] + right[2], modulus)
    alias, scalar = (left, right) if left[0] == "A" else (right, left)
    return norm("A", alias[1] + scalar[1], alias[2] + scalar[2], min(alias[3], scalar[3]), True)


def shift_left(value, amount):
    if value[2] << amount <= MASK:
        return norm("S", value[1] << amount, value[2] << amount, value[3] + amount)
    return norm("S", 0, MASK - ((1 << amount) - 1), amount)


def shift_right(value, amount):
    if amount >= 32:
        return const(0)
    return norm("S", value[1] >> amount, value[2] >> amount, max(0, value[3] - amount))


def low_zeros(value):
    return min(value[3], ctz(value[1]))


def widen(old, new, thresholds, visits):
    if old is None or new == old or new[0] not in ("S", "A") or old[0] != new[0]:
        return new
    if new[0] == "S":
        lo, hi = new[1], new[2]
        if hi > old[2]:
            hi = next(t for t in thresholds if t >= hi)
        if lo < old[1] and new[3] < 32:
            # Stay in the residue class: the lowest member not below the threshold.
            step = 1 << new[3]
            lo -= ((lo - next(t for t in reversed(thresholds) if t <= lo)) // step) * step
        return norm("S", lo, hi, new[3])
    if visits <= ALIAS_WIDEN_AFTER:
        return new
    lo = -BIG if new[1] < old[1] else new[1]
    hi = BIG if new[2] > old[2] else new[2]
    return norm("A", lo, hi, new[3] if lo == new[1] and hi == new[2] else 0, True)


class State:
    __slots__ = ("kinds", "init", "regs", "exprs", "flags")

    def __init__(self, kinds, init, regs, exprs, flags):
        self.kinds, self.init, self.regs, self.exprs, self.flags = kinds, init, regs, exprs, flags

    def key(self):
        return (self.kinds, self.init, self.regs, self.exprs, self.flags)

    def __eq__(self, other):
        return type(other) is State and self.key() == other.key()

    def copy(self):
        return State(self.kinds, self.init, list(self.regs), list(self.exprs), self.flags)

    def freeze(self):
        self.regs, self.exprs = tuple(self.regs), tuple(self.exprs)
        return self


def depth(state):
    return len(state.kinds)


def sp_alias(state):
    return exact_alias(-4 * depth(state))


def trim_init(init, new_depth):
    floor = -4 * new_depth
    return frozenset(byte for byte in init if byte >= floor)


class Analysis:
    def __init__(self, data, address, derivations, accesses, copies):
        self.data, self.address = data, address
        self.end = address + len(data)
        self.derivations, self.accesses = derivations, accesses
        self.copies = copies        # call site -> (entry-SP-relative destination, byte count)
        self.checked_derivations, self.checked_accesses = set(), set()
        self.records = {}
        self.premises = {}
        self.derived = {}
        self.origins = {destination for destination, _ in copies.values()}
        self.writers = set()        # stores through non-stack addresses, and calls
        self.check = False
        thresholds = {0, MASK}
        for bit in range(33):
            thresholds.update({(1 << bit) - 1, min(MASK, 1 << bit)})
        for site in range(address, self.end - 1, 2):
            raw = self.halfword(site)
            if raw & 0xF800 in (0x2800, 0x2000):
                value = raw & 255
                thresholds.update({max(0, value - 1), value, value + 1})
        self.thresholds = sorted(thresholds)

    def halfword(self, site):
        offset = site - self.address
        if not 0 <= offset <= len(self.data) - 2:
            refuse("instruction leaves the verified body")
        return int.from_bytes(self.data[offset:offset + 2], "little")

    def fail(self, message):
        if self.check:
            refuse(message)

    # ---- values -------------------------------------------------------
    def read(self, state, register):
        if register == 13:
            return sp_alias(state)
        if register == 15:
            refuse("program-counter operand")
        return state.regs[register]

    def expr(self, state, register):
        """The derivation expression of a scalar register, or None."""
        if register in (13, 15):
            return None
        value = state.regs[register]
        if value[0] != "S":
            return None
        if value[1] == value[2] and value[3] == 32:
            return ("c", value[1])
        return state.exprs[register]

    def write(self, state, register, value, expr=None):
        if register in (13, 15):
            refuse("stack-pointer or program-counter write")
        state.regs[register] = value
        state.exprs[register] = expr if value[0] == "S" else None
        if state.flags is not None and (state.flags[0] == register or
                                        state.flags[1] == ("reg", register)):
            state.flags = None

    def scalar_use(self, state, registers, what):
        """Registers read by an instruction that is no allowed ranged use."""
        for register in registers:
            if is_ranged(self.read(state, register)):
                self.fail(f"ranged stack address reaches {what}")

    def no_escape(self, state, registers, what):
        for register in registers:
            if is_ranged(state.regs[register]):
                self.fail(f"ranged stack address escapes through {what}")

    # ---- frame --------------------------------------------------------
    def frame_check(self, state, lo, hi, width, *, load):
        """None if every byte in [lo, hi + width) is allocated (and initialised for loads)."""
        floor = -4 * depth(state)
        if lo < floor or hi + width > 0:
            return ("index range leaves the allocated local frame "
                    f"([{lo}, {hi + width}) outside [{floor}, 0))")
        for byte in range(lo, hi + width):
            if state.kinds[(-byte - 1) // 4] != "L":
                return f"index range overlaps a saved register word at entry-SP{byte:+d}"
        if load and any(byte not in state.init for byte in range(lo, hi + width)):
            return f"index range reads uninitialised local bytes in [{lo}, {hi + width})"
        return None

    def mark(self, state, offset, width):
        floor = -4 * depth(state)
        if floor <= offset and offset + width <= 0:
            state.init = state.init | frozenset(range(offset, offset + width))

    def extent(self, state, start, width, load):
        """Largest end (exclusive) of the array that begins at ``start``."""
        top = start
        while top < 0 and state.kinds[(-top - 1) // 4] == "L":
            top += 1
        end = min([origin for origin in self.origins if origin > start] + [top])
        if load:
            run = start
            while run in state.init and run < end:
                run += 1
            end = min(end, run)
        return end

    def premise(self, state, site, width, load, c, texpr, tlo, tmod, disp):
        """Admit an access under one explicit runtime premise, or refuse.

        ``tlo`` is the lowest address the access reaches and ``tmod`` its congruence: every
        reachable address must be ``start`` plus a multiple of the width, or a premise that
        only bounds the index from above would admit an always-misaligned access."""
        if c is None or texpr is None:
            return "index has no defined source (no premise can be stated)"
        start = c + disp
        end = self.extent(state, start, width, load)
        floor = -4 * depth(state)
        if start < floor or start % width:
            return "array start is below the frame or misaligned"
        tmax = end - width - start
        if tmax < 0:
            return "no array bytes are available at the index-zero address"
        if (tlo - start) % width or (1 << tmod) % width:
            return f"index is not provably {width}-byte aligned"
        problem = self.frame_check(state, start, start + tmax, width, load=load)
        if problem is not None:
            return problem
        scale, index = 1, texpr
        if texpr[0] == "sh" and texpr[1] == "<<":
            scale, index = 1 << texpr[3], texpr[2]
        bound = tmax // scale + 1
        if self.check:
            self.premises[site] = dict(
                site=site, kind="load" if load else "store", width=width, expression=render(index),
                bound=bound, scale=scale, loads=sorted(load_sites(index)),
                array_sp=[start + 4 * depth(state), start + 4 * depth(state) + tmax + width],
                array_entry_sp=[start, start + tmax + width])
        return None

    def access(self, state, site, base_register, displacement, index_register, width, load,
               value_register, signed=False):
        base = self.read(state, base_register)
        index = None if index_register is None else self.read(state, index_register)
        deferred = site in self.accesses
        if index is not None and is_ranged(index):
            self.fail("ranged stack address used as an index register")
        if base[0] == "P":
            self.fail("ranged stack address of mixed provenance used as a base")
        if not load and is_ranged(self.read(state, value_register)):
            self.fail("ranged stack address escapes to memory")
        bounded = deferred or is_ranged(base)
        if bounded:
            if base[0] != "A" or index is not None and index[0] != "S":
                self.fail("deferred access lacks one stack-derived base and a scalar index")
            else:
                hull = base if index is None else add_values(base, index)
                lo, hi, modulus = hull[1] + displacement, hull[2] + displacement, hull[3]
                if base[4]:
                    c, texpr = base[5], base[6]
                    if index is not None:
                        texpr = make("bin", "add", texpr, self.expr(state, index_register))
                else:
                    c = base[1]
                    texpr = None if index is None else self.expr(state, index_register)
                problem = None
                if lo % width or lo != hi and (1 << modulus) % width:
                    problem = f"index range is not {width}-byte aligned on every path"
                else:
                    problem = self.frame_check(state, lo, hi, width, load=load)
                if problem is None:
                    if self.check:
                        self.checked_accesses.add(site)
                        record = ["load" if load else "store", width, lo, hi, modulus]
                        previous = self.records.get(site)
                        if previous is not None and previous != record:
                            refuse("inconsistent bounded access evidence")
                        self.records[site] = record
                        self.premises.pop(site, None)
                else:
                    reason = self.premise(state, site, width, load, c, texpr, lo, modulus, displacement)
                    if reason is None:
                        if self.check:
                            self.checked_accesses.add(site)
                            self.records.pop(site, None)
                    else:
                        self.fail(f"{problem}; {reason}")
                if not load and lo == hi and problem is None:
                    self.mark(state, lo, width)
        elif base[0] == "A" and (index is None or index[0] == "S" and index[1] == index[2]):
            offset = base[1] + displacement + (0 if index is None else index[1])
            if not load:
                self.mark(state, offset, width)
            else:
                # A fixed-offset read through an exact stack alias is a reload like `ldr [sp,#k]`.
                self.origins.add(offset)
        elif not load and base[0] != "A":
            self.writers.add(site)
        if load:
            result = TOP
            if width == 1 and not signed:
                result = ("S", 0, 255, 0)
            elif width == 2 and not signed:
                result = ("S", 0, 0xFFFF, 0)
            expr = None
            if base[0] == "S":
                address = self.expr(state, base_register)
                if index_register is not None:
                    address = make("bin", "add", address, self.expr(state, index_register))
                if displacement:
                    address = make("bin", "add", address, ("c", displacement))
                expr = make("ld", width, signed, address, site)
            self.write(state, value_register, result, expr)

    # ---- transfer -----------------------------------------------------
    def derive(self, state, site, destination, left, right):
        """ADDS Rd,Rn,Rm or high ADD Rd,Rm (Rd = left + right)."""
        a, b = self.read(state, left), self.read(state, right)
        deferred = site in self.derivations
        kinds = (a[0], b[0])
        expr = None
        if "P" in kinds:
            self.fail("ranged stack address of mixed provenance is combined")
            result = POISON
        elif kinds == ("S", "S"):
            if deferred:
                self.fail("deferred index addition has no stack-derived operand")
            result = add_values(a, b)
            expr = make("bin", "add", self.expr(state, left), self.expr(state, right))
        elif kinds in (("A", "S"), ("S", "A")):
            alias, scalar_register = (a, right) if a[0] == "A" else (b, left)
            result = add_values(a, b)
            if deferred or alias[4]:
                scalar = self.expr(state, scalar_register)
                if alias[4]:
                    result = result[:5] + (alias[5], make("bin", "add", alias[6], scalar))
                else:
                    result = result[:5] + (alias[1], scalar)
                if self.check:
                    self.checked_derivations.add(site)
                    self.derived[site] = [result[1], result[2], result[3]]
            elif result[1] != result[2]:
                self.fail("core and bounded analysis disagree on an exact stack alias")
            else:
                result = exact_alias(result[1])
        else:
            if deferred or is_ranged(a) or is_ranged(b):
                self.fail("unsupported combination of stack-derived operands")
                result = POISON
            else:
                result = TOP
        self.write(state, destination, result, expr)

    def immediate(self, state, destination, source, amount):
        value = self.read(state, source)
        expr = None
        if value[0] == "A":
            result = norm("A", value[1] + amount, value[2] + amount, value[3], value[4],
                          None if value[5] is None else value[5] + amount, value[6])
        elif value[0] == "S":
            modulus = min(value[3], ctz(abs(amount)))
            if 0 <= value[1] + amount and value[2] + amount <= MASK:
                result = norm("S", value[1] + amount, value[2] + amount, modulus)
            else:
                result = wrapped(value[1] + amount, modulus)
            if amount:
                expr = make("bin", "add" if amount > 0 else "sub", self.expr(state, source),
                            ("c", abs(amount)))
            else:
                expr = self.expr(state, source)
        else:
            result = value
        self.write(state, destination, result, expr)

    def copy_site(self, state, site):
        destination, count = self.copies[site]
        floor = -4 * depth(state)
        if destination < floor or destination + count > 0:
            refuse("ROM copy destination leaves the frame")
        self.mark(state, destination, count)
        return exact_alias(destination)

    def step(self, state, site):
        """Return [(successor or EXIT, state or None)] for one instruction."""
        raw = self.halfword(site)
        state = state.copy()
        r = lambda n: n & 7
        follow = site + 2
        if raw & 0xF800 == 0xF000:
            second = self.halfword(site + 2)
            if second & 0xF800 != 0xF800:
                refuse("unsupported long branch encoding")
            offset = ((raw & 0x7FF) << 12) | ((second & 0x7FF) << 1)
            if offset & 0x400000:
                offset -= 0x800000
            target = site + 4 + offset
            if self.address <= target < self.end:
                refuse("same-owner long branches are outside this policy")
            self.no_escape(state, range(4), "a call argument register")
            self.writers.add(site)
            result = None
            if site in self.copies:
                result = self.copy_site(state, site)
            for register in (0, 1, 2, 3, 12, 14):
                state.regs[register] = TOP
                state.exprs[register] = None
            if result is not None:
                state.regs[0] = result
            else:
                state.exprs[0] = make("ret", site)
            state.flags = None
            return [(site + 4, state)]
        if raw & 0xF000 == 0xD000:
            condition = (raw >> 8) & 15
            if condition >= 14:
                refuse("software interrupts and undefined encodings are outside this policy")
            displacement = raw & 0xFF
            target = site + 4 + 2 * (displacement - 256 if displacement & 0x80 else displacement)
            taken, fall = state, state
            if state.flags is not None:
                register, (kind, operand) = state.flags
                right = const(operand) if kind == "imm" else self.read(state, operand)
                taken_value, fall_value = refine(condition, state.regs[register], right)
                taken, fall = None, None
                if taken_value is not None:
                    taken = state.copy()
                    taken.regs[register] = taken_value
                if fall_value is not None:
                    fall = state.copy()
                    fall.regs[register] = fall_value
            return [(target, taken), (follow, fall)]
        if raw & 0xF800 == 0xE000:
            displacement = raw & 0x7FF
            return [(site + 4 + 2 * (displacement - 2048 if displacement & 0x400 else displacement), state)]
        if raw & 0xFF00 == 0x4700:
            if raw & 0x87:
                refuse("unsupported branch-exchange form")
            self.no_escape(state, RETURN_VISIBLE, "a return register")
            return [(EXIT, None)]
        if raw & 0xFE00 == 0xBC00:
            count = bin(raw & 0x1FF).count("1")
            if count > depth(state):
                refuse("pop leaves the tracked frame")
            state.kinds = state.kinds[:-count]
            state.init = trim_init(state.init, depth(state))
            for register in range(8):
                if raw & (1 << register):
                    self.write(state, register, TOP)
            if raw & 0x100:
                self.no_escape(state, RETURN_VISIBLE, "a return register")
                return [(EXIT, None)]
            return [(follow, state)]
        if raw & 0xFE00 == 0xB400:
            registers = [register for register in range(8) if raw & (1 << register)]
            if raw & 0x100:
                registers.append(14)
            self.no_escape(state, registers, "a push")
            before = depth(state)
            state.kinds = state.kinds + ("S",) * len(registers)
            state.init = state.init | frozenset(range(-4 * depth(state), -4 * before))
            return [(follow, state)]
        if raw & 0xFF00 == 0xB000:
            words = raw & 0x7F
            if raw & 0x80:
                if depth(state) + words > MAX_FRAME_WORDS:
                    refuse("frame exceeds the bounded tracked size")
                state.kinds = state.kinds + ("L",) * words
            else:
                if words > depth(state):
                    refuse("stack release leaves the tracked frame")
                state.kinds = state.kinds[:len(state.kinds) - words]
                state.init = trim_init(state.init, depth(state))
            return [(follow, state)]
        if raw & 0xF800 == 0xA800:
            offset = -4 * depth(state) + 4 * (raw & 255)
            self.origins.add(offset)
            self.write(state, r(raw >> 8), exact_alias(offset))
            return [(follow, state)]
        if raw & 0xF800 == 0x4800:
            literal = ((site + 4) & ~3) + 4 * (raw & 255)
            value = TOP
            if self.address <= literal and literal + 4 <= self.end:
                value = const(int.from_bytes(self.data[literal - self.address:literal - self.address + 4], "little"))
            self.write(state, r(raw >> 8), value)
            return [(follow, state)]
        if raw & 0xF000 == 0x5000:
            operation = (raw >> 9) & 7
            width = (4, 2, 1, 1, 4, 2, 1, 2)[operation]
            self.access(state, site, r(raw >> 3), 0, r(raw >> 6), width, operation >= 3,
                        r(raw), signed=operation in (3, 7))
            return [(follow, state)]
        if raw & 0xE000 == 0x6000:
            byte = raw & 0x1000
            width = 1 if byte else 4
            self.access(state, site, r(raw >> 3), ((raw >> 6) & 31) * width, None, width,
                        bool(raw & 0x800), r(raw))
            return [(follow, state)]
        if raw & 0xF000 == 0x8000:
            self.access(state, site, r(raw >> 3), ((raw >> 6) & 31) * 2, None, 2,
                        bool(raw & 0x800), r(raw))
            return [(follow, state)]
        if raw & 0xF000 == 0x9000:
            offset = -4 * depth(state) + 4 * (raw & 255)
            if raw & 0x800:
                # A word reloaded by a fixed SP offset is a scalar (a spill) or a constant-index
                # element; either way no premise may let a variable index range over it.  A
                # store alone is no boundary: agbcc at -O2 never spills without reloading, and
                # constant-index element stores and aggregate copy tails write array words.
                self.origins.add(offset)
                self.write(state, r(raw >> 8), TOP)
            else:
                if is_ranged(state.regs[r(raw >> 8)]):
                    self.fail("ranged stack address escapes to memory")
                self.mark(state, offset, 4)
            return [(follow, state)]
        if raw & 0xF000 == 0xC000:
            base = r(raw >> 8)
            registers = [register for register in range(8) if raw & (1 << register)]
            pointer = state.regs[base]
            if is_ranged(pointer):
                self.fail("block transfer through a ranged stack address")
            if raw & 0x800:
                if pointer[0] == "A" and pointer[1] == pointer[2]:
                    self.origins.add(pointer[1])     # a block reload of local words
                for register in registers:
                    self.write(state, register, TOP)
            else:
                self.no_escape(state, registers, "a block store")
                if pointer[0] == "A" and pointer[1] == pointer[2]:
                    self.mark(state, pointer[1], 4 * len(registers))
                elif pointer[0] != "A":
                    self.writers.add(site)
            if not (raw & 0x800 and base in registers):
                moved = pointer
                if pointer[0] == "A" and pointer[1] == pointer[2]:
                    moved = exact_alias(pointer[1] + 4 * len(registers))
                elif pointer[0] == "S" and pointer[1] == pointer[2]:
                    moved = pointer[:1] + (pointer[1] + 4 * len(registers),
                                           pointer[2] + 4 * len(registers)) + pointer[3:]
                    if moved[2] > MASK:
                        moved = TOP
                elif pointer[0] == "S":
                    moved = TOP
                self.write(state, base, moved)
            return [(follow, state)]
        if raw & 0xFC00 == 0x4400:
            operation = (raw >> 8) & 3
            destination = (raw & 7) | ((raw >> 4) & 8)
            source = (raw >> 3) & 15
            if operation == 0:
                self.derive(state, site, destination, destination, source)
            elif operation == 1:
                self.scalar_use(state, (destination, source), "a comparison")
                state.flags = (destination, ("reg", source)) if destination < 13 and source < 13 else None
                return [(follow, state)]
            elif operation == 2:
                if destination == 15:
                    if source != 14:
                        refuse("unsupported program-counter move")
                    self.no_escape(state, RETURN_VISIBLE, "a return register")
                    return [(EXIT, None)]
                value = self.read(state, source)
                if source == 13:
                    self.origins.add(value[1])
                self.write(state, destination, value, None if source in (13, 15) else
                           self.expr(state, source))
            return [(follow, state)]
        if raw & 0xFC00 == 0x4000:
            operation = (raw >> 6) & 15
            destination, source = r(raw), r(raw >> 3)
            a, b = state.regs[destination], state.regs[source]
            expr_a, expr_b = self.expr(state, destination), self.expr(state, source)
            self.scalar_use(state, (source,) if operation in (9, 15) else (destination, source),
                            "an arithmetic or logical operation")
            state.flags = None
            if operation == 10:
                state.flags = (destination, ("reg", source))
                return [(follow, state)]
            if operation in (8, 11):
                return [(follow, state)]
            result, expr = TOP, None
            if operation in ALU_EXPR:
                expr = make("bin", ALU_EXPR[operation], expr_a, expr_b)
            if a[0] == "S" and b[0] == "S":
                if operation == 0:      # each operand's known low zero bits survive
                    zeros = max(low_zeros(a), low_zeros(b))
                    result = norm("S", 0, min(a[2], b[2]), zeros) if zeros < 32 else const(0)
                elif operation in (1, 12):
                    bound = (1 << max(a[2], b[2]).bit_length()) - 1
                    zeros = min(low_zeros(a), low_zeros(b))
                    result = norm("S", 0, bound, zeros if zeros < 32 else 0)
                elif operation == 13 and a[2] * b[2] <= MASK:
                    result = norm("S", a[1] * b[1], a[2] * b[2], 0)
                elif operation == 14:
                    result = norm("S", 0, a[2], 0)
            self.write(state, destination, result, expr)
            state.flags = None
            return [(follow, state)]
        if raw & 0xE000 == 0x0000 and raw & 0x1800 != 0x1800:
            operation, amount = (raw >> 11) & 3, (raw >> 6) & 31
            destination, source = r(raw), r(raw >> 3)
            value = state.regs[source]
            if operation == 0 and amount == 0:
                self.write(state, destination, value, self.expr(state, source))
            else:
                self.scalar_use(state, (source,), "a shift")
                result = TOP
                symbol = ("<<", ">>", ">>s")[operation]
                shift = amount or 32 if operation else amount
                if value[0] == "S":
                    if operation == 0:
                        result = shift_left(value, amount)
                    elif operation == 1:
                        result = shift_right(value, amount or 32)
                    elif amount and value[2] <= SIGNED_MAX:
                        result = shift_right(value, amount)
                self.write(state, destination, result,
                           shift_expr(symbol, self.expr(state, source), shift))
            state.flags = None
            return [(follow, state)]
        if raw & 0xF800 == 0x1800:
            operation = (raw >> 9) & 3
            destination, source, third = r(raw), r(raw >> 3), r(raw >> 6)
            if operation == 0:
                self.derive(state, site, destination, source, third)
            elif operation == 1:
                self.scalar_use(state, (source, third), "a register subtraction")
                a, b = state.regs[source], state.regs[third]
                result = TOP
                if a[0] == "S" and b[0] == "S":
                    modulus = min(a[3], b[3])
                    result = norm("S", a[1] - b[2], a[2] - b[1], modulus) if a[1] >= b[2] else \
                        wrapped(a[1] - b[1], modulus)
                self.write(state, destination, result,
                           make("bin", "sub", self.expr(state, source), self.expr(state, third)))
            else:
                self.immediate(state, destination, source, third if operation == 2 else -third)
            state.flags = None
            return [(follow, state)]
        if raw & 0xE000 == 0x2000:
            operation, register, value = (raw >> 11) & 3, r(raw >> 8), raw & 255
            if operation == 0:
                self.write(state, register, const(value))
            elif operation == 1:
                self.scalar_use(state, (register,), "a comparison")
                state.flags = (register, ("imm", value))
                return [(follow, state)]
            else:
                self.immediate(state, register, register, value if operation == 2 else -value)
            state.flags = None
            return [(follow, state)]
        refuse(f"unsupported instruction 0x{raw:04x} at 0x{site:08X}")

    # ---- driver -------------------------------------------------------
    def successors(self, site):
        raw = self.halfword(site)
        if raw & 0xF800 == 0xF000:
            return (site + 4,)
        if raw & 0xF000 == 0xD000:
            displacement = raw & 0xFF
            return (site + 4 + 2 * (displacement - 256 if displacement & 0x80 else displacement), site + 2)
        if raw & 0xF800 == 0xE000:
            displacement = raw & 0x7FF
            return (site + 4 + 2 * (displacement - 2048 if displacement & 0x400 else displacement),)
        if raw & 0xFF00 == 0x4700 or raw & 0xFF00 == 0xBD00 or raw == 0x46F7:
            return ()
        return (site + 2,)

    def reaches(self, sources):
        """Every site reachable in one or more steps from any of ``sources``."""
        seen, pending = set(), [successor for source in sources for successor in self.successors(source)]
        while pending:
            site = pending.pop()
            if site in seen or not self.address <= site < self.end:
                continue
            seen.add(site)
            pending.extend(self.successors(site))
        return seen

    def syntactic_sites(self):
        sites, pending = set(), [self.address]
        while pending:
            site = pending.pop()
            if site in sites:
                continue
            if not self.address <= site < self.end or site % 2:
                refuse("control flow leaves the verified body")
            sites.add(site)
            raw = self.halfword(site)
            if raw & 0xF800 == 0xF000:
                sites.add(site + 2)
            pending.extend(self.successors(site))
        return sites

    def join_states(self, old, new, site, visits):
        if old is None:
            return new
        if old.kinds != new.kinds:
            refuse("inconsistent frame layout at a control-flow join")
        regs = []
        for previous, incoming in zip(old.regs, new.regs):
            joined = join_values(previous, incoming)
            regs.append(widen(previous, joined, self.thresholds, visits))
        exprs = tuple(left if left == right else None for left, right in zip(old.exprs, new.exprs))
        flags = old.flags if old.flags == new.flags else None
        return State(old.kinds, old.init & new.init, tuple(regs), exprs, flags)

    def run(self):
        exprs = tuple(("entry", n) if n < 4 else None for n in range(16))
        entry = State((), frozenset(), tuple([TOP] * 16), exprs, None)
        states, visits, pending, updates = {self.address: entry}, {}, [self.address], 0
        while pending:
            site = pending.pop()
            for successor, outgoing in self.step(states[site], site):
                if successor is EXIT or outgoing is None:
                    continue
                outgoing.freeze()
                visits[successor] = visits.get(successor, 0) + 1
                merged = self.join_states(states.get(successor), outgoing, successor, visits[successor])
                if merged != states.get(successor):
                    updates += 1
                    if updates > MAX_UPDATES:
                        refuse("value-range proof budget exhausted")
                    states[successor] = merged
                    pending.append(successor)
        self.check = True
        for site in sorted(states):
            self.step(states[site], site)
        return states


def prove(data, address, verified_sites, derivations, accesses, copies):
    analysis = Analysis(bytes(data), address, derivations, accesses, dict(copies))
    sites = analysis.syntactic_sites()
    if sites - set(verified_sites) - {site + 2 for site in sites
                                       if analysis.halfword(site) & 0xF800 == 0xF000} or \
            set(verified_sites) - sites:
        refuse("raw Thumb CFG differs from the verified instruction set")
    states = analysis.run()
    reachable_derivations = {site for site in derivations if site in states}
    reachable_accesses = {site for site in accesses if site in states}
    if reachable_derivations - analysis.checked_derivations or \
            reachable_accesses - analysis.checked_accesses:
        refuse("a deferred stack index site was not proved")
    if not analysis.records and not analysis.premises:
        refuse("no variable stack index access to prove")
    # A field the owner may itself have written before the load is not purely the caller's.
    written = analysis.reaches(analysis.writers)
    preconditions = []
    for _, row in sorted(analysis.premises.items()):
        loads = row.pop("loads")
        preconditions.append(dict(row, may_be_owner_written=any(site in written for site in loads)))
    return {"schema": SCHEMA,
            "accesses": [[site - address, *record] for site, record in sorted(analysis.records.items())],
            "derivations": [[site - address, *record] for site, record in sorted(analysis.derived.items())],
            "preconditions": preconditions}


class StackIndexBufferProof(rom_copy.RomTableCopyBufferProof):
    """The ROM-table-copy buffer walk with variable stack indices deferred to the analysis above."""

    def __init__(self, rom, mapping, index, objects, *, rodata=None, data=None, address=None):
        super().__init__(rom, mapping, index, objects, rodata=rodata, data=data, address=address)
        self.index_policy = Policy(address, len(data))

    def index_copies(self):
        return {site: (record["destination_offset"], record["count"])
                for site, record in self.copies.items()}

    def copy_manifest(self):
        """Struct and plain-store initialisation needs no helper; only report the copies seen."""
        if self.copies:
            return super().copy_manifest()
        return dict(schema=rom_copy.SCHEMA, helper=None, contract=rom_copy.CONTRACT, copies=[],
                    object_initializer=self.rodata, conditions=[], physical_access_proved=False,
                    nonaliasing_proved=False)
