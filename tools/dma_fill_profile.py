"""Immediate fixed-source DMA fills whose source is a local unit (kit #239).

`DmaFill16(3, 0, dst, n)` keeps the fill value in a local halfword and writes the
local's address to a DMA source register (DMAxSAD).  The root walk refuses that
store as a stack-alias escape.  This module admits exactly that store, on the
plain direct-call path, when the transfer it starts is an immediate fill that
reads one local unit and writes a destination span that cannot be the stack:

1. At the escape check (``Fills.admit``): a 16-bit ``str rS, [rB]`` (no offset)
   whose only offending register is the alias rS, with rB not an alias, and
   whose next instructions in the bytes have the window shape below.  The
   site, the alias offset and the frame state are recorded; nothing else about
   the alias changes.  Every other store keeps its refusal there.
2. After the walk (``Fills.finish``), over the walk's own CFG and exact
   constants (``exact_values``):

   * rB holds exactly one DMA source register on every reaching path;
   * one straight window follows (each instruction reached only from the one
     before; no call, branch, return, memory access or rB write) holding
     exactly one destination store ``str rD, [rB, #4]`` and then the control
     store ``str rC, [rB, #8]``, and the next instruction reads the control back;
   * the control is an exact immediate, fixed-source, incrementing-destination
     enable without repeat or DRQ, unused bits clear; bit 26 gives the unit;
   * the source unit lies in allocated local words for every recorded state;
   * the destination is exact and aligned, and its whole span lies in palette
     RAM, VRAM, OAM or EWRAM, or in IWRAM below the stack floor that the ROM's
     boot code and the stated stack premise give (``stack_floor``).

The report states every premise on its own line (``PREMISES``).  Everything
not admitted here keeps its existing refusal.
"""
import json

MASK = 0xFFFFFFFF
SOURCE_REGISTERS = {0x040000B0: 0, 0x040000BC: 1, 0x040000C8: 2, 0x040000D4: 3}
# Byte ranges [start, end).  Every live stack word lies in IWRAM (the stack premise
# below), so a span wholly inside one of these holds no stack word.
STACKLESS = (("palette", 0x05000000, 0x05000400), ("vram", 0x06000000, 0x06018000),
             ("oam", 0x07000000, 0x07000400), ("ewram", 0x02000000, 0x02040000))
IWRAM_START = 0x03000000
# The ROM's boot code (0x08000000 and 0x080000C0-0x080000FC): `b 0x080000C0`;
# `mov r0, #0x12; msr cpsr_fc, r0; ldr sp, [pc, #0x28]` (IRQ mode, SP from 0x080000F8);
# `mov r0, #0x1f; msr cpsr_fc, r0; ldr sp, [pc, #0x18]` (System mode, SP from
# 0x080000F4); the two literal words 0x03007EC0 and 0x03007FA0.
BOOT_ENTRY = bytes.fromhex("2e0000ea")
BOOT_STACKS = bytes.fromhex("1200a0e300f029e128d09fe51f00a0e300f029e118d09fe5")
BOOT_SPS = bytes.fromhex("c07e0003a07f0003")
MAX_STACK_BYTES = 0x4000
MAX_WINDOW = 16
MAX_UPDATES = 4096
SUMMARY = (
    "`gba-dma-immediate-local-fill-v1` immediate fixed-source DMA fills from a local unit: a stack address "
    "stored to DMA0-3SAD (exact on every path) is followed on one straight window by the destination, an exact "
    "control word (enable, immediate start, fixed source, incrementing destination, no repeat or DRQ, unused "
    "bits clear) and the control read-back; the source unit lies in allocated local words that hold no stack address; the whole destination "
    "span lies in palette RAM, VRAM, OAM or EWRAM, or in IWRAM below the stack floor 0x03003EC0 that the pinned "
    "boot code gives; no fill value, destination content, initialization or termination theorem")
PREMISES = (
    "GBATEK (DMA Transfers): DMAxSAD and DMAxDAD are write-only; an immediate transfer with a fixed source "
    "reads the source unit count times, writes only the destination span and holds the CPU until it ends",
    "the channel is idle when the control word is written",
    "no interrupt reprograms the channel between the source store and the enable",
    "no later transfer starts from the stale source address without rewriting it",
    "every live stack word (System/User, IRQ or BIOS supervisor) lies in IWRAM at or above 0x03003EC0: the "
    "System stack grows at most 16 KiB below its boot SP 0x03007EC0, and the IRQ and supervisor stacks lie above "
    "it",
    "R4-R11 are preserved across each call the facts cross (the ordinary ARM ABI summary); trusted, not proved")
SUMMARY_FIELD = "* DMA fills: "
PREMISE_FIELD = "* DMA fill premise: "
MANIFEST_FIELD = "* DMA fill manifest: "
MARKER = "* DMA fill"


def _register(number):
    from capstone.arm_const import ARM_REG_R0
    return ARM_REG_R0 + number


def _code(instruction):
    return int.from_bytes(bytes(instruction.bytes), "little") if instruction.size == 2 else None


def _literal(data, address, instruction, code):
    offset = ((instruction.address + 4) & ~3) + (code & 0xFF) * 4 - address
    if not 0 <= offset <= len(data) - 4:
        raise ValueError("DMA fill literal escapes the complete function")
    return int.from_bytes(data[offset:offset + 4], "little")


def transfer(instruction, incoming, data, address):
    """(register, value) for an exact 16-bit Thumb result, else None.

    The forms are decoded from the bytes alone; none of them is conditional.
    """
    code = _code(instruction)
    if code is None:
        return None
    low = (code & 7, (code >> 3) & 7, (code >> 6) & 7)
    if code & 0xF800 == 0x2000:
        return _register((code >> 8) & 7), code & 0xFF
    if code & 0xF800 == 0x4800:
        return _register((code >> 8) & 7), _literal(data, address, instruction, code)
    if code & 0xFF00 == 0x4600:
        # Only R0-R12 hold facts (SP, LR and PC are not ARM_REG_R0 + n in capstone).
        destination, source = (code & 7) | ((code >> 4) & 8), (code >> 3) & 15
        value = incoming.get(_register(source)) if source < 13 else None
        return (_register(destination), value) if value is not None and destination < 13 else None
    if code & 0xF800 in (0x0000, 0x0800):
        # LSLS #0 is MOVS rd, rs; LSRS #0 encodes a shift by 32.
        source = incoming.get(_register(low[1]))
        shift = (code >> 6) & 31
        if source is None:
            return None
        if code & 0xF800 == 0 and shift == 0:
            return _register(low[0]), source
        shift = shift or 32
        return _register(low[0]), (source << shift) & MASK if code & 0xF800 == 0 else source >> shift
    if code & 0xF800 == 0x1800:
        left = incoming.get(_register(low[1]))
        right = low[2] if code & 0x0400 else incoming.get(_register(low[2]))
        if left is None or right is None:
            return None
        return _register(low[0]), (left - right if code & 0x0200 else left + right) & MASK
    if code & 0xF000 == 0x3000:
        destination = _register((code >> 8) & 7)
        source = incoming.get(destination)
        if source is None:
            return None
        return destination, (source - (code & 0xFF) if code & 0x0800 else source + (code & 0xFF)) & MASK
    if code & 0xFFC0 in (0x4000, 0x4040, 0x4300, 0x4380):    # ands, eors, orrs, bics
        left, right = incoming.get(_register(low[0])), incoming.get(_register(low[1]))
        if left is None or right is None:
            return None
        kind = code & 0xFFC0
        return _register(low[0]), (left & right if kind == 0x4000 else left ^ right if kind == 0x4040 else
                                   left | right if kind == 0x4300 else left & ~right & MASK)
    return None


def exact_values(instructions, edges, address, data):
    """{site: {register: value}} holding before each reached instruction.

    Joins keep only equal values; a call keeps only R4-R11 (the ordinary ARM ABI
    premise the walk already states); any other register write drops the fact
    unless ``transfer`` gives an exact result.
    """
    from capstone import CS_GRP_CALL
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError("DMA fill facts require the exact closed walk CFG")
    states, pending, updates = {address: {}}, [address], 0
    saved = range(_register(4), _register(12))
    while pending:
        site = pending.pop()
        instruction, incoming = instructions[site], states[site]
        if CS_GRP_CALL in instruction.groups:
            outgoing = {register: fact for register, fact in incoming.items() if register in saved}
        else:
            outgoing = dict(incoming)
            for register in instruction.regs_access()[1]:
                outgoing.pop(register, None)
            result = transfer(instruction, incoming, data, address)
            if result is not None:
                outgoing[result[0]] = result[1]
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("DMA fill facts leave the walk CFG")
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: value for register, value in previous.items() if outgoing.get(register) == value}
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:
                    raise ValueError("DMA fill fact budget exhausted")
                states[successor] = merged
                pending.append(successor)
    return states


def _store(instruction, base, word):
    """The source register of a 16-bit `str rX, [base, #4*word]`, else None."""
    code = _code(instruction)
    if code is None or code & 0xF800 != 0x6000 or (code >> 6) & 31 != word or (code >> 3) & 7 != base:
        return None
    return code & 7


def _inert(instruction, base):
    """A 16-bit shift, add/sub, immediate, ALU or register move, or PC literal load, not writing the base.

    None of these accesses memory or branches.  A move that writes SP or PC, or
    reads PC, is refused by the walk itself.
    """
    code = _code(instruction)
    return code is not None and (code < 0x4400 or code & 0xFF00 == 0x4600 or code & 0xF800 == 0x4800) and \
        _register(base) not in instruction.regs_access()[1]


def _straight(site, instructions, predecessors):
    """The next instruction when it is reached only from `site` (which never branches here)."""
    following = site + instructions[site].size
    return following if following in instructions and predecessors.get(following) == {site} else None


def window(site, base, following):
    """(destination store, control store, read-back) sites after the source store at `site`.

    following(site) is the next site on the one straight path, or None; the
    walk's CFG gives it after the walk, the bytes give it at the escape check.
    """
    cursor, destination_store = site, None
    for _ in range(MAX_WINDOW):
        cursor, instruction = following(cursor)
        if instruction is None:
            break
        if _store(instruction, base, 1) is not None and destination_store is None:
            destination_store = cursor
        elif _store(instruction, base, 2) is not None and destination_store is not None:
            readback, instruction = following(cursor)
            code = _code(instruction) if instruction is not None else None
            if code is None or code & 0xFFF8 != 0x6880 | base << 3:
                raise ValueError("DMA fill requires the control read-back immediately after the enable")
            return destination_store, cursor, readback
        elif not _inert(instruction, base):
            break
    raise ValueError("DMA fill requires one straight destination and control store after the source store")


def stack_floor(rom):
    """The lowest address the premise lets a live stack word take, from the ROM's boot code.

    The boot code must be exactly the pinned sequence (BOOT_ENTRY, BOOT_STACKS,
    BOOT_SPS): it sets the IRQ SP to 0x03007FA0 and the System SP to 0x03007EC0.
    The stack premise is one-sided: no live stack word lies below the System SP
    less MAX_STACK_BYTES (the IRQ and BIOS supervisor stacks lie above the
    System SP).  None when the ROM differs, so no IWRAM span qualifies.
    """
    if rom is None or rom[:4] != BOOT_ENTRY or rom[0xC0:0xD8] != BOOT_STACKS or rom[0xF4:0xFC] != BOOT_SPS:
        return None
    return int.from_bytes(BOOT_SPS[:4], "little") - MAX_STACK_BYTES


def region(destination, size, floor):
    """The one region holding the whole span: a stackless one, or IWRAM below the stack floor."""
    for name, start, end in STACKLESS:
        if start <= destination and destination + size <= end:
            return name
    if floor is not None and IWRAM_START <= destination and destination + size <= floor:
        return "iwram"
    raise ValueError("DMA fill destination span is not wholly in a stackless region or in IWRAM below the "
                     "stack floor")


def control_unit(control, channel):
    """(unit bytes, count) of an exact immediate fixed-source enable, else ValueError."""
    if not control >> 31 & 1 or control >> 28 & 3 or control >> 27 & 1 or control >> 25 & 1 or \
            control >> 23 & 3 != 2 or control >> 21 & 3 or control >> 16 & 31 or \
            channel != 3 and control >> 14 & 3:
        raise ValueError("DMA fill control is not an exact immediate fixed-source enable")
    count = control & 0xFFFF    # bits 14-15 are clear on DMA0-2 (above)
    return (4 if control >> 26 & 1 else 2), count or (0x10000 if channel == 3 else 0x4000)


class Fills:
    """The recorder the plain root walk consults at its stack-alias escape check.

    `rom` is the selected ROM; only its boot code is read, for an IWRAM destination.
    """

    def __init__(self, rom=None):
        self.rom = rom
        self.observations = {}
        self.records = None

    def admit(self, data, address, instruction, site, aliases, stack, offending, pointers):
        """Defer the escape refusal of a plain source store followed by the fill's shape in the bytes.

        pointers holds the offsets of the local words that hold a stack address on this path.
        Every other escape keeps its refusal at the same instruction.
        """
        from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        code = _code(instruction)
        if self.records is not None or code is None or code & 0xFFC0 != 0x6000:
            return False
        source, base = _register(code & 7), _register((code >> 3) & 7)
        if set(offending) != {source} or base in aliases:
            return False
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        decoded = {site: instruction}

        def following(cursor):
            after = cursor + decoded[cursor].size
            item = next(decoder.disasm(data[after - address:after - address + 4], after, 1), None)
            decoded[after] = item
            return after, item
        try:
            window(site, (code >> 3) & 7, following)
        except ValueError:
            return False
        self.observations.setdefault(site, []).append((code & 7, (code >> 3) & 7, aliases[source], tuple(stack),
                                                       frozenset(pointers)))
        return True

    def finish(self, data, address, instructions, edges, predecessors):
        from match import BufferCallProof
        if self.records is not None:
            raise ValueError("DMA fill record is already complete")
        records = []
        values = exact_values(instructions, edges, address, data) if self.observations else {}
        for site in sorted(self.observations):
            observed = self.observations[site]
            if len({(source, base, offset) for source, base, offset, _, _ in observed}) != 1:
                raise ValueError("DMA fill source differs between paths")
            _, base, offset, _, _ = observed[0]
            channel = SOURCE_REGISTERS.get(values.get(site, {}).get(_register(base)))
            if channel is None:
                raise ValueError("DMA source store base is not exactly one DMA source register on every path")

            def following(cursor):
                cursor = _straight(cursor, instructions, predecessors)
                return cursor, instructions.get(cursor)
            destination_store, control_store, readback = window(site, base, following)
            control = values[control_store].get(_register(_store(instructions[control_store], base, 2)))
            if control is None:
                raise ValueError("DMA fill control is not an exact immediate fixed-source enable")
            unit, count = control_unit(control, channel)
            for _, _, _, stack, pointers in observed:
                BufferCallProof.access(offset, unit, stack)
                # The transfer copies the unit out: a word that holds a stack address would escape.
                if any(word in pointers for word in range(offset - offset % 4, offset + unit, 4)):
                    raise ValueError("DMA fill source unit is a pointer-bearing local word")
            destination = values[destination_store].get(_register(_store(instructions[destination_store], base, 1)))
            if destination is None or destination % unit:
                raise ValueError("DMA fill destination is not an exact unit-aligned address")
            span = region(destination, unit * count, stack_floor(self.rom))
            records.append(dict(site=site - address, channel=channel, source=offset, frame=4 * len(observed[0][3]),
                                unit=unit, destination_store=destination_store - address,
                                control_store=control_store - address, readback=readback - address,
                                control=control, destination=destination, bytes=unit * count, region=span))
        self.records = records

    def report_lines(self):
        """The summary, one line per premise in order, and the canonical manifest; none without a record."""
        if not self.records:
            return []
        return [SUMMARY_FIELD + SUMMARY, *(PREMISE_FIELD + premise for premise in PREMISES),
                MANIFEST_FIELD + "`" + json.dumps(dict(sites=self.records), sort_keys=True, separators=(",", ":")) + "`"]


def report_fields(lines):
    """The report's DMA fill lines (every line starting with the marker, indented or not)."""
    return [line for line in lines if line.lstrip().startswith(MARKER)]


def check_report(fills, lines):
    """Replay: the record recomputed from the bytes and the ROM gives exactly the report's lines,
    as one block right after its one stack-frame line."""
    lines = list(lines)
    expected = fills.report_lines()
    if expected != report_fields(lines):
        raise ValueError("DMA fill lines differ")
    if expected:
        frames = [index for index, line in enumerate(lines) if line.startswith("* stack frame: ")]
        if len(frames) != 1 or lines[frames[0] + 1:frames[0] + 1 + len(expected)] != expected:
            raise ValueError("DMA fill lines must follow the stack-frame line")
