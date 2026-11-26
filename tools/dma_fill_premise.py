"""Immediate DMA fills from a local unit whose destination or count is not exact (extends kit #239).

`dma_fill_profile` admits `DmaFill16(3, 0, dst, n)`-style fills only when the destination and the
whole control word are exact, and the span lies in palette RAM, VRAM, OAM, EWRAM or IWRAM below the
stack floor.  A fill whose destination is a pointer the caller passes, or whose count comes from a
struct, can write the stack for some inputs, so nothing here proves it safe.  This module admits
such a fill only under a reviewed, recorded runtime premise, the same kind as
`config/stack_index_premises.json`:

* every other #239 check still holds (exact DMA source register base on every path, the straight
  window, the control read-back, a source unit in allocated local words that holds no stack
  address);
* bits 16-31 of the control word are known on every path, and they are an immediate,
  fixed-source, incrementing-destination enable without repeat or Game Pak DRQ, with bits 16-20
  clear.  Bit 26 gives the unit.  Only the count may be unknown;
* the destination and the control each have one derivation on every path: entry registers R0-R3,
  constants, and loads tagged with their site (a load is a leaf: the value that load reads at run
  time, with no claim about what the word holds, so no fact about a frame word crosses a call);
  combined by shifts, adds, subtracts, ands, ors, eors and bics.  R0-R3, R12 and LR are forgotten at
  a call; R4-R11 are kept under the ordinary ABI premise the #239 profile already states;
* the decomp root's `config/dma_fill_premises.json` holds a reviewed entry for the function that
  repeats every generated row exactly.  The row's claim is fixed (CLAIM): whenever the fill runs,
  its destination span lies wholly in one stackless region or in IWRAM below the stack floor.

The accepted entry's review text is hashed into each record, so editing it invalidates the report;
replay re-reads the file.  A function with an entry but no premised fill refuses.
"""
import hashlib
import json
from pathlib import Path



def _sip():
    """The stack-index profile, for its expression constructors (imported late: it imports match)."""
    import stack_index_precondition_profile
    return stack_index_precondition_profile

PREMISES_PATH = "config/dma_fill_premises.json"
ROW_KEYS = ("site", "channel", "unit", "destination", "control")
MASK = 0xFFFFFFFF
MAX_UPDATES = 4096
FIELD = "* DMA fill destination premise: "
CLAIM = ("whenever the fill starts, the destination with its low bits cleared to the unit, and the "
         "unit x count bytes from it (count: the low 14 bits of the control on DMA0-2, 0 meaning 0x4000; the "
         "low 16 bits on DMA3, 0 meaning 0x10000; GBATEK), lie wholly in palette RAM, VRAM, OAM or EWRAM, or "
         "in IWRAM below the stack floor")
UNKNOWN = (None, 0, 0)          # (expression, known-bit mask, known bits)


def snapshot(root):
    """The decomp's reviewed DMA fill premise file, or None."""
    try:
        return (Path(root) / PREMISES_PATH).read_bytes()
    except FileNotFoundError:
        return None


def _reg(number):
    from capstone.arm_const import ARM_REG_R0
    return ARM_REG_R0 + number


def _const(value):
    value &= MASK
    return (("c", value), MASK, value)


def _known(value):
    """The exact value when every bit is known, else None."""
    return value[2] if value[1] == MASK else None


def _value(expr, mask, bits):
    if mask == MASK:
        return _const(bits)
    return (expr, mask, bits & mask)


def _load(width, address, site):
    """A load of `width` bytes through the address value; zero-extended, so the high bits are known."""
    expr = address[0]
    high = MASK & ~((1 << (8 * width)) - 1) if width < 4 else 0
    if expr is None:
        return (None, high, 0)
    if expr[0] == "sp":
        node = ("fld", width, expr[1], site)
    else:
        node = _sip().make("ld", width, False, expr, site)
    return (node, high, 0) if node is not None else (None, high, 0)


def _add(left, right, subtract=False):
    a, b = _known(left), _known(right)
    if a is not None and b is not None:
        return _const(a - b if subtract else a + b)
    if b == 0:                                              # a register copy (adds rd, rs, #0)
        return left
    if left[0] is not None and left[0][0] == "sp" and b is not None:
        return (("sp", left[0][1] + (-b if subtract else b)), 0, 0)
    if not subtract and right[0] is not None and right[0][0] == "sp" and a is not None:
        return (("sp", right[0][1] + a), 0, 0)
    if left[0] is None or right[0] is None or "sp" in (left[0][0], right[0][0]):
        return UNKNOWN
    return (_sip().make("bin", "sub" if subtract else "add", left[0], right[0]), 0, 0)


def _bitwise(kind, left, right):
    a_mask, a_bits, b_mask, b_bits = left[1], left[2], right[1], right[2]
    if kind == "and":
        mask = (a_mask & b_mask) | (a_mask & ~a_bits) | (b_mask & ~b_bits)
        bits = a_bits & b_bits
    elif kind == "orr":
        mask = (a_mask & b_mask) | (a_mask & a_bits) | (b_mask & b_bits)
        bits = a_bits | b_bits
    elif kind == "eor":
        mask, bits = a_mask & b_mask, a_bits ^ b_bits
    else:                                                   # bic: left & ~right
        mask = (a_mask & b_mask) | (a_mask & ~a_bits) | (b_mask & b_bits)
        bits = a_bits & ~b_bits
    mask &= MASK
    expr = None
    if left[0] is not None and right[0] is not None and "sp" not in (left[0][0], right[0][0]):
        expr = _sip().make("bin", kind, left[0], right[0])
    return _value(expr, mask, bits & mask)


def _shift(operation, value, amount):
    """lsl/lsr by an immediate (0 < amount <= 32); asr keeps no known bits above a known sign."""
    mask, bits = value[1], value[2]
    if operation == "<<":
        mask, bits = ((mask << amount) | ((1 << amount) - 1)) & MASK, (bits << amount) & MASK
    elif operation == ">>":
        mask = ((mask >> amount) | (MASK & ~(MASK >> amount))) & MASK
        bits = bits >> amount
    else:
        sign = mask >> 31 & 1
        mask, bits = ((mask >> amount) | ((MASK & ~(MASK >> amount)) if sign else 0)) & MASK, \
            ((bits >> amount) | ((MASK & ~(MASK >> amount)) if sign and bits >> 31 else 0)) & MASK
    expr = None
    if value[0] is not None and value[0][0] != "sp":
        expr = _sip().shift_expr({"<<": "<<", ">>": ">>", "asr": ">>s"}[operation], value[0], amount)
    return _value(expr, mask, bits & mask)


def _code(instruction):
    return int.from_bytes(bytes(instruction.bytes), "little") if instruction.size == 2 else None


def step(instruction, state, data, address):
    """The state after one instruction: (SP depth below entry or None, {register: value})."""
    from capstone import CS_GRP_CALL
    depth, regs = state
    out = dict(regs)
    if CS_GRP_CALL in instruction.groups:
        return depth, {register: value for register, value in regs.items()
                       if _reg(4) <= register <= _reg(11)}
    code = _code(instruction)
    for register in instruction.regs_access()[1]:
        out.pop(register, None)
    if code is None:
        return depth, out
    read = lambda n: regs.get(_reg(n), UNKNOWN)
    low = (code & 7, (code >> 3) & 7, (code >> 6) & 7)
    result = None
    if code & 0xFE00 == 0xB400:                     # push
        return (None if depth is None else depth + 4 * (bin(code & 0x1FF).count("1"))), out
    if code & 0xFE00 == 0xBC00:                     # pop
        return (None if depth is None else depth - 4 * (bin(code & 0x1FF).count("1"))), out
    if code & 0xFF00 == 0xB000:                     # add/sub sp, #imm
        amount = (code & 0x7F) * 4
        return (None if depth is None else depth + (amount if code & 0x80 else -amount)), out
    if code & 0xF800 == 0x2000:
        result = _reg((code >> 8) & 7), _const(code & 0xFF)
    elif code & 0xF800 == 0x4800:
        offset = ((instruction.address + 4) & ~3) + (code & 0xFF) * 4 - address
        if not 0 <= offset <= len(data) - 4:
            raise ValueError("DMA fill literal escapes the complete function")
        result = _reg((code >> 8) & 7), _const(int.from_bytes(data[offset:offset + 4], "little"))
    elif code & 0xFF00 == 0x4600:
        destination, source = (code & 7) | ((code >> 4) & 8), (code >> 3) & 15
        if destination < 13:
            if source == 13:
                result = _reg(destination), ((("sp", -depth), 0, 0) if depth is not None else UNKNOWN)
            elif source < 13:
                result = _reg(destination), regs.get(_reg(source), UNKNOWN)
    elif code & 0xF800 == 0xA800:                   # add rd, sp, #imm
        result = _reg((code >> 8) & 7), ((("sp", -depth + (code & 0xFF) * 4), 0, 0)
                                         if depth is not None else UNKNOWN)
    elif code & 0xF800 in (0x0000, 0x0800, 0x1000):
        amount = (code >> 6) & 31
        kind = {0x0000: "<<", 0x0800: ">>", 0x1000: "asr"}[code & 0xF800]
        if kind == "<<" and amount == 0:
            result = _reg(low[0]), read(low[1])
        else:
            result = _reg(low[0]), _shift(kind, read(low[1]), amount or 32)
    elif code & 0xF800 == 0x1800:
        right = _const(low[2]) if code & 0x0400 else read(low[2])
        result = _reg(low[0]), _add(read(low[1]), right, bool(code & 0x0200))
    elif code & 0xF000 == 0x3000:
        destination = (code >> 8) & 7
        if code & 0x1800 == 0x1000:                 # adds rd, #imm
            result = _reg(destination), _add(read(destination), _const(code & 0xFF))
        elif code & 0x1800 == 0x1800:               # subs rd, #imm
            result = _reg(destination), _add(read(destination), _const(code & 0xFF), True)
    elif code & 0xFC00 == 0x4000:                   # ALU
        operation = (code >> 6) & 15
        kind = {0: "and", 1: "eor", 12: "orr", 14: "bic"}.get(operation)
        if kind is not None:
            result = _reg(low[0]), _bitwise(kind, read(low[0]), read(low[1]))
    elif code & 0xF800 == 0x9800:                   # ldr rd, [sp, #imm]
        if depth is not None:
            result = _reg((code >> 8) & 7), _load(4, (("sp", -depth + (code & 0xFF) * 4), 0, 0),
                                                  instruction.address)
    elif code & 0xFE00 in (0x5A00, 0x5C00):         # ldrh / ldrb rd, [rb, ro]: zero-extended, no derivation
        width = 2 if code & 0xFE00 == 0x5A00 else 1
        result = _reg(low[0]), (None, MASK & ~((1 << (8 * width)) - 1), 0)
    elif code & 0xF800 in (0x6800, 0x7800, 0x8800):  # ldr / ldrb / ldrh rd, [rb, #imm]
        width = {0x6800: 4, 0x7800: 1, 0x8800: 2}[code & 0xF800]
        base = _add(read(low[1]), _const(((code >> 6) & 31) * width))
        result = _reg(low[0]), _load(width, base, instruction.address)
    if result is not None and (result[1][0] is not None or result[1][1]):
        out[result[0]] = result[1]
    return depth, out


def derivations(instructions, edges, address, data):
    """{site: (depth, {register: value})} holding before each reached instruction of the walk's CFG.

    Joins keep a register only where both paths give the same expression; known bits are
    intersected.  SP depth must agree or becomes unknown (the walk already requires agreement).
    """
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError("DMA fill derivations require the exact closed walk CFG")
    entry = {_reg(n): (("entry", n), 0, 0) for n in range(4)}
    states, pending, updates = {address: (0, entry)}, [address], 0
    while pending:
        site = pending.pop()
        outgoing = step(instructions[site], states[site], data, address)
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("DMA fill derivations leave the walk CFG")
            previous = states.get(successor)
            if previous is None:
                merged = outgoing
            else:
                regs = {}
                for register in previous[1].keys() & outgoing[1].keys():
                    left, right = previous[1][register], outgoing[1][register]
                    mask = left[1] & right[1] & ~(left[2] ^ right[2]) & MASK
                    expr = left[0] if left[0] == right[0] else None
                    if expr is not None or mask:
                        regs[register] = (expr, mask, left[2] & mask)
                merged = (previous[0] if previous[0] == outgoing[0] else None, regs)
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:
                    raise ValueError("DMA fill derivation budget exhausted")
                states[successor] = merged
                pending.append(successor)
    return states


def render(expr):
    """The notation of config/stack_index_premises.json, with entry-SP-relative frame loads."""
    kind = expr[0]
    if kind == "fld":
        return f"u{8 * expr[1]}[entry_SP{expr[2]:+#x}]@0x{expr[3]:08X}"
    if kind == "c":
        return f"0x{expr[1]:08X}" if expr[1] >= 0x10000 else str(expr[1])
    if kind == "entry":
        return f"entry_R{expr[1]}"
    if kind == "ld":
        return f"{'s' if expr[2] else 'u'}{8 * expr[1]}[{render(expr[3])}]@0x{expr[4]:08X}"
    if kind == "sh":
        return f"({render(expr[2])} {expr[1]} {expr[3]})"
    if kind == "bin":
        symbol = {"add": "+", "sub": "-", "and": "&", "orr": "|", "eor": "^", "bic": "&~"}[expr[1]]
        return f"({render(expr[2])} {symbol} {render(expr[3])})"
    raise ValueError("DMA fill derivation has no rendering")


def high_control(value, channel):
    """The unit of a control word whose bits 16-31 are known and form an immediate fixed-source enable."""
    if value[1] >> 16 != 0xFFFF:
        raise ValueError("DMA fill control is not an exact immediate fixed-source enable (bits 16-31 are not "
                         "known on every path)")
    control = value[2] & 0xFFFF0000
    if not control >> 31 & 1 or control >> 28 & 3 or control >> 27 & 1 or control >> 25 & 1 or \
            control >> 23 & 3 != 2 or control >> 21 & 3 or control >> 16 & 31:
        raise ValueError("DMA fill control is not an exact immediate fixed-source enable")
    return 4 if control >> 26 & 1 else 2


def parse(snapshot):
    """{address: entry} from the reviewed file; the review rules of config/stack_index_premises.json."""
    if snapshot is None:
        return {}

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate key in DMA fill premises")
            result[key] = value
        return result

    document = json.loads(snapshot, object_pairs_hook=unique)
    if not isinstance(document, dict):
        raise ValueError("DMA fill premises must be an object keyed by function address")
    entries = {}
    for key, entry in document.items():
        if not isinstance(key, str) or len(key) != 10 or not key.startswith("0x") or \
                key != f"0x{int(key, 16):08X}":
            raise ValueError("DMA fill premise keys are canonical 0xXXXXXXXX addresses")
        if not isinstance(entry, dict) or set(entry) != {"review", "rows"} or \
                not isinstance(entry["review"], str) or not entry["review"].strip() or \
                entry["review"].strip().startswith("<") or \
                any(word in entry["review"].upper() for word in ("SCRATCH", "TODO")) or \
                not isinstance(entry["rows"], list) or not entry["rows"]:
            raise ValueError(f"DMA fill premise entry {key} needs a written review and its rows")
        for row in entry["rows"]:
            if not isinstance(row, dict) or set(row) != set(ROW_KEYS) or \
                    not all(isinstance(row[name], str) for name in ("site", "destination", "control")) or \
                    type(row["channel"]) is not int or type(row["unit"]) is not int:
                raise ValueError(f"DMA fill premise rows of {key} are exactly "
                                 f"{', '.join(ROW_KEYS)}")
        entries[int(key, 16)] = entry
    return entries


def accept(address, rows, snapshot):
    """The sha256 of the reviewed entry's review text for `rows`; refuse, printing the entry, otherwise."""
    entry = parse(snapshot).get(address)
    if entry is None or entry["rows"] != rows:
        text = json.dumps({f"0x{address:08X}": {
            "review": "<why every execution of each fill keeps its destination span off the stack>",
            "rows": rows}}, indent=2)
        raise ValueError(f"DMA fill destination premise: the rows of 0x{address:08X} need a reviewed entry in "
                         f"{PREMISES_PATH} that repeats them exactly "
                         f"({'none found' if entry is None else 'the entry differs'}); after checking every "
                         f"caller, add:\n{text}")
    return hashlib.sha256(entry["review"].encode()).hexdigest()


def unneeded(address, snapshot):
    """Refuse an entry for a function whose fills all have exact destinations and controls."""
    if address in parse(snapshot):
        raise ValueError(f"DMA fill destination premise: {PREMISES_PATH} lists premises 0x{address:08X} "
                         f"does not need")


def line(record, address):
    return (f"{FIELD}site 0x{address + record['site']:08X} DMA{record['channel']} unit {record['unit']} "
            f"destination {record['destination']} control {record['control']}: {CLAIM}; unproved runtime "
            f"premise, accepted by {PREMISES_PATH}")
