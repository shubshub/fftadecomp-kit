"""The pinned copy helper func_081443FC as a summarised call in the default buffer walk (kit #240).

A local buffer passed to the 98-byte copy helper makes the buffer walk enter the
helper and refuse at its alignment test (`orrs r0, r5` at 0x0814440A), which
reads the pointer's value.  The walk explores that path for every count, so a
local alias in R0 or R1 at a call to the helper is refused today in every walk
that does not summarise it (`named-data-buffer-rom-table-copy-v1` and the
stack-index selectors do, for constant ROM sources and counts up to 15).

This module summarises such a call in the plain stack-argument buffer proof of
the default path, and nowhere else.  It applies in every walk of a function's
own frame that the proof runs (the owner's, and the frame walk of each inspected
callee), at a direct `bl` to the helper with a tracked local alias in R0 or R1:

1. the helper is authenticated exactly as `rom_table_copy_profile.helper_facts`
   does it (the indexed 98-byte span in both indexes, `COPY_SHA256`, the
   byte-loop path, the closed CFG, no register above R5 written), and the mapped
   span the walk would enter is that body;
2. R2 is an exact constant count n, 1 <= n <= MAX_COUNT;
3. no alias is in R2 or LR, and every alias argument and stack-passed pointer
   word is a valid local pointer;
4. the helper's effect for this n is proved by executing its pinned bytes on
   the symbolic Thumb interpreter below, once per (destination mod 4, source
   mod 4) pair.  Each run starts from symbolic destination, source and stack
   regions, opaque memory and opaque entry registers, and must show: no
   branch reads data or unknown pointer bits; the writes are exactly
   [dst, dst+n) plus the helper's own save words below SP; the reads are
   within [src, src+n) and those save words; only source bytes are written to
   the destination, each to its own offset, and no pointer is stored; the
   return is through the saved entry LR with SP, R4-R11, R12 and LR restored;
   R0 = dst, R1 = the entry LR, R2 = -1 and R3 = src+n at the return; the
   entry value of R3 and R12 is never read, and R12 is never written;
5. a local destination lies in allocated local words and holds no
   pointer-bearing or return-carrying word;
6. a local source lies in allocated local words and holds no pointer-bearing
   word;
7. a local source and a local destination are disjoint;
8. the proof has no word-provenance, callee-frame or other summary context.

Result: R0 is the destination alias, R3 is the alias src+n when the source is
local (the helper leaves R3 one past the source), and an alias in R12 is kept.
R1 (the entry LR), R2 and the flags are dropped as unknown scalars, and so is an
alias in R3 at the call, which the helper overwrites before reading.  Every
returned alias is then checked like any alias, as after a walked callee that
returns the same pointer.

The interpreter below is specific to this helper: it refuses any encoding
outside the small subset the 98 pinned bytes use, so a body that differs is
refused.  A separate kit lemma already executes the same helper symbolically,
but only for a fixed aligned 80-byte copy (compiler_copy80_prerequisite) or for
the four small byte-path counts (compiler_small_local_copy_prerequisite); the
caller-side check here needs the write and read sets for an arbitrary count
under every (dst, src) alignment, which those do not give.  The test module
cross-checks this interpreter against the kit's independent concrete executor
on concrete inputs.

Every distinct observation is recorded, bound into the buffer fingerprint and
written as one report line; replay recomputes them.  The alias pass that
follows a caller's pointer into an inspected callee does not carry the count,
so a callee that forwards the caller's pointer to the helper is walked, and
refused, as before.

Not proved: the physical stack, the readability or writability of a source or
destination that is not local, that such a range does not overlap the live
frame, the helper's save words or code (the standing premise of the buffer
walk for every untracked pointer), or termination beyond the bounded run.
"""
from dataclasses import dataclass
import hashlib
import json

import match

POLICY = 'pinned-copy-helper-summary-v1'
HELPER = 0x081443FC
MAX_COUNT = 256
MAX_STEPS = 8192
FRAME_WORDS = 3
MASK = 0xFFFFFFFF
R0 = match.ARM_REG_R0
R2, R3, R12, LR = R0 + 2, R0 + 3, match.ARM_REG_R12, match.ARM_REG_LR


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Pointer:
    """An address inside one symbolic region: the destination, the source or the stack."""
    region: str
    offset: int


@dataclass(frozen=True)
class Token:
    """The opaque entry value of one register."""
    name: str


@dataclass(frozen=True)
class SourceByte:
    """The opaque byte at one source offset."""
    index: int


@dataclass(frozen=True)
class Part:
    """Byte `index` of an opaque register value saved to memory."""
    token: Token
    index: int


@dataclass(frozen=True)
class Word:
    """A loaded word of four opaque bytes."""
    cells: tuple


@dataclass(frozen=True)
class LowBits:
    """A value of which only the low two bits are known."""
    bits: int


def _split(value):
    if type(value) is int:
        return tuple(value >> (8 * i) & 255 for i in range(4))
    if isinstance(value, Word):
        return value.cells
    if isinstance(value, Token):
        return tuple(Part(value, i) for i in range(4))
    raise ValueError('copy helper stores a pointer or a partly known value')


def _join(cells):
    if all(type(cell) is int for cell in cells):
        return sum(cell << (8 * i) for i, cell in enumerate(cells))
    if all(isinstance(cell, Part) and cell.token == cells[0].token and cell.index == i
           for i, cell in enumerate(cells)):
        return cells[0].token
    return Word(tuple(cells))


def _add_flags(left, right):
    result = (left + right) & MASK
    return (bool(result >> 31), result == 0, left + right > MASK,
            bool((left ^ result) & (right ^ result) & 0x80000000))


def _sub_flags(left, right):
    result = (left - right) & MASK
    return (bool(result >> 31), result == 0, left >= right,
            bool((left ^ right) & (left ^ result) & 0x80000000))


# The flags (N, Z, C, V) each condition reads, by the 4-bit field of a conditional branch.
_CONDITIONS = (
    ((1,), lambda n, z, c, v: z), ((1,), lambda n, z, c, v: not z),
    ((2,), lambda n, z, c, v: c), ((2,), lambda n, z, c, v: not c),
    ((0,), lambda n, z, c, v: n), ((0,), lambda n, z, c, v: not n),
    ((3,), lambda n, z, c, v: v), ((3,), lambda n, z, c, v: not v),
    ((1, 2), lambda n, z, c, v: c and not z), ((1, 2), lambda n, z, c, v: not c or z),
    ((0, 3), lambda n, z, c, v: n == v), ((0, 3), lambda n, z, c, v: n != v),
    ((0, 1, 3), lambda n, z, c, v: not z and n == v), ((0, 1, 3), lambda n, z, c, v: z or n != v))


def run(body, entry, count, destination_alignment, source_alignment, *, maximum=MAX_COUNT):
    """Execute the helper bytes once on symbolic regions; return the observed effect.

    ``maximum`` bounds the count (the buffer summary keeps MAX_COUNT); the
    step budget bounds the run either way.

    Destination and source are distinct regions whose base addresses are
    unknown, apart from their low two bits.  Every value the helper could only
    know by reading memory or an entry register is opaque, and any branch,
    address or arithmetic that would depend on one is refused.  So a returned
    result holds for every base address with these low bits and every memory
    content.
    """
    require(type(body) is bytes and len(body) % 2 == 0 and type(entry) is int and
            type(maximum) is int and type(count) is int and 0 <= count <= maximum and
            destination_alignment in range(4) and source_alignment in range(4),
            'copy helper run requires exact bounded inputs')
    entry_tokens = [Token(f'entry-r{i}') for i in range(16)]
    registers = list(entry_tokens)
    registers[0], registers[1], registers[2] = Pointer('destination', 0), Pointer('source', 0), count
    registers[13] = Pointer('stack', 0)
    alignment = dict(destination=destination_alignment, source=source_alignment, stack=0)
    memory = {('source', i): SourceByte(i) for i in range(count)}
    unread, entry_reads = {3, 12}, set()
    reads, writes, trace = [], [], []
    flags = (None, None, None, None)

    def get(register):
        if register in unread:
            entry_reads.add(register)
        return registers[register]

    def put(register, value):
        unread.discard(register)
        registers[register] = value

    def cells(pointer, width, write):
        require(isinstance(pointer, Pointer), 'copy helper accesses memory through a non-pointer')
        low, high = pointer.offset, pointer.offset + width
        require(width == 1 or (alignment[pointer.region] + low) % 4 == 0,
                'copy helper word access is unaligned in this case')
        if pointer.region == 'stack':
            stack_pointer = registers[13]
            require(isinstance(stack_pointer, Pointer) and stack_pointer.region == 'stack' and
                    -4 * FRAME_WORDS <= stack_pointer.offset <= low and high <= 0,
                    'copy helper stack access leaves its own save words')
        else:
            require(0 <= low and high <= count and
                    pointer.region == ('destination' if write else 'source'),
                    'copy helper access leaves the source and destination ranges')
        return [(pointer.region, offset) for offset in range(low, high)]

    def load(pointer, width):
        keys = cells(pointer, width, False)
        require(all(key in memory for key in keys), 'copy helper reads a byte it did not save')
        reads.append([pointer.region, pointer.offset, width])
        values = tuple(memory[key] for key in keys)
        return _join(values) if width == 4 else values[0]

    def store(pointer, width, value):
        keys = cells(pointer, width, True)
        values = _split(value) if width == 4 else (
            value & 255 if type(value) is int else
            value if isinstance(value, (SourceByte, Part)) else _split(value)[0],)
        if pointer.region == 'destination':
            require(all(isinstance(cell, SourceByte) for cell in values),
                    'copy helper writes a non-source value to the destination')
        for key, cell in zip(keys, values):
            memory[key] = cell
        writes.append([pointer.region, pointer.offset, width])

    def add(value, delta):
        if type(value) is int:
            return (value + delta) & MASK
        require(isinstance(value, Pointer), 'copy helper computes with an opaque value')
        return Pointer(value.region, value.offset + delta)

    def low_bits(value):
        if type(value) is int:
            return value & 3
        if isinstance(value, Pointer):
            return (alignment[value.region] + value.offset) & 3
        require(isinstance(value, LowBits), 'copy helper computes with an opaque value')
        return value.bits

    def logical(value, old):
        if type(value) is int:
            return (bool(value >> 31), value == 0, old[2], old[3])
        return (None, None, old[2], old[3])

    pc, returned = entry, False
    for _ in range(MAX_STEPS):
        offset = pc - entry
        require(pc % 2 == 0 and 0 <= offset <= len(body) - 2, 'copy helper leaves its pinned bytes')
        raw = int.from_bytes(body[offset:offset + 2], 'little')
        trace.append(offset)
        next_pc = pc + 2
        if raw & 0xFE00 == 0xB400:                      # PUSH {rlist[, lr]}
            selected = [i for i in range(8) if raw >> i & 1] + ([14] if raw & 0x100 else [])
            require(selected, 'copy helper pushes no register')
            values = [get(register) for register in selected]
            registers[13] = add(registers[13], -4 * len(selected))
            for index, value in enumerate(values):
                store(add(registers[13], 4 * index), 4, value)
        elif raw & 0xFE00 == 0xBC00:                    # POP {rlist}; a PC pop is not modelled
            require(not raw & 0x100, 'copy helper pops the program counter')
            selected = [i for i in range(8) if raw >> i & 1]
            require(selected, 'copy helper pops no register')
            values = [load(add(registers[13], 4 * index), 4) for index in range(len(selected))]
            registers[13] = add(registers[13], 4 * len(selected))
            for register, value in zip(selected, values):
                put(register, value)
        elif raw & 0xFF87 == 0x4700:                    # BX Rm
            require(get(raw >> 3 & 15) == entry_tokens[14], 'copy helper returns other than to its entry LR')
            returned = True
            break
        elif raw & 0xF000 == 0xD000 and raw >> 8 & 15 < 14:
            used, test = _CONDITIONS[raw >> 8 & 15]
            require(all(flags[i] is not None for i in used), 'copy helper branch reads an unknown flag')
            if test(*flags):
                delta = (raw & 255) << 1
                next_pc = pc + 4 + (delta - 0x200 if delta & 0x100 else delta)
        elif raw & 0xF800 == 0xE000:
            delta = (raw & 0x7FF) << 1
            next_pc = pc + 4 + (delta - 0x1000 if delta & 0x800 else delta)
        elif raw & 0xF800 == 0x2000:                    # MOVS Rd, #imm8
            put(raw >> 8 & 7, raw & 255)
            flags = logical(raw & 255, flags)
        elif raw & 0xF800 == 0x2800:                    # CMP Rn, #imm8
            value = get(raw >> 8 & 7)
            require(type(value) is int, 'copy helper compares an opaque value or a pointer')
            flags = _sub_flags(value, raw & 255)
        elif raw & 0xF000 == 0x3000:                    # ADDS/SUBS Rd, #imm8
            register, immediate = raw >> 8 & 7, raw & 255
            value = get(register)
            subtract = raw & 0x800
            put(register, add(value, -immediate if subtract else immediate))
            flags = ((_sub_flags if subtract else _add_flags)(value, immediate)
                     if type(value) is int else (None,) * 4)
        elif raw & 0xFC00 == 0x1C00:                    # ADDS/SUBS Rd, Rn, #imm3
            value, immediate = get(raw >> 3 & 7), raw >> 6 & 7
            subtract = raw & 0x200
            put(raw & 7, add(value, -immediate if subtract else immediate))
            flags = ((_sub_flags if subtract else _add_flags)(value, immediate)
                     if type(value) is int else (None,) * 4)
        elif raw & 0xFC00 == 0x4000:                    # data processing, register forms
            operation, destination, source = raw >> 6 & 15, raw & 7, raw >> 3 & 7
            left, right = get(destination), get(source)
            if operation == 0:                          # ANDS
                if type(left) is int and type(right) is int:
                    value = left & right
                else:
                    mask, other = (right, left) if type(right) is int else (left, right)
                    require(type(mask) is int and mask <= 3,
                            'copy helper masks more than the known low pointer bits')
                    value = low_bits(other) & mask
                put(destination, value)
                flags = logical(value, flags)
            elif operation == 12:                       # ORRS
                if type(left) is int and type(right) is int:
                    value = left | right
                else:
                    value = LowBits(low_bits(left) | low_bits(right))
                put(destination, value)
                flags = logical(value, flags)
            elif operation == 9:                        # NEGS Rd, Rm
                require(type(right) is int, 'copy helper negates an opaque value or a pointer')
                put(destination, -right & MASK)
                flags = _sub_flags(0, right)
            elif operation == 10:                       # CMP Rn, Rm
                require(type(left) is int and type(right) is int,
                        'copy helper compares an opaque value or a pointer')
                flags = _sub_flags(left, right)
            else:
                raise ValueError(f'copy helper executes an unmodelled encoding {raw:04X}')
        elif raw & 0xF000 == 0xC000:                    # LDMIA/STMIA Rn!, {rlist}
            base, selected = raw >> 8 & 7, [i for i in range(8) if raw >> i & 1]
            require(selected and base not in selected, 'copy helper block transfer list is ambiguous')
            pointer = get(base)
            if raw & 0x800:
                values = [load(add(pointer, 4 * index), 4) for index in range(len(selected))]
                for register, value in zip(selected, values):
                    put(register, value)
            else:
                for index, register in enumerate(selected):
                    store(add(pointer, 4 * index), 4, get(register))
            put(base, add(pointer, 4 * len(selected)))
        elif raw & 0xF000 == 0x7000:                    # LDRB/STRB Rd, [Rn, #imm5]
            pointer = add(get(raw >> 3 & 7), raw >> 6 & 31)
            if raw & 0x800:
                put(raw & 7, load(pointer, 1))
            else:
                store(pointer, 1, get(raw & 7))
        else:
            raise ValueError(f'copy helper executes an unmodelled encoding {raw:04X}')
        pc = next_pc
    require(returned, 'copy helper run reached no return within its step budget')
    require(registers[13] == Pointer('stack', 0) and registers[14] == entry_tokens[14] and
            all(registers[i] == entry_tokens[i] for i in range(4, 13)),
            'copy helper does not restore SP, LR, R4-R11 and R12')
    require(registers[0] == Pointer('destination', 0) and registers[1] == entry_tokens[14] and
            registers[2] == MASK and registers[3] == Pointer('source', count),
            'copy helper return registers differ from R0 = dst, R1 = LR, R2 = -1, R3 = src+n')
    # No modelled encoding writes R8-R12 or LR, so R12 is never written.
    require(not entry_reads, 'copy helper reads the entry R3 or R12')
    # Stores outside [0, count) were refused above, so this makes the write set exactly [0, count).
    require(all(memory.get(('destination', i)) == SourceByte(i) for i in range(count)),
            'copy helper does not copy each source byte to its destination offset')
    return dict(destination_alignment=destination_alignment, source_alignment=source_alignment,
                steps=len(trace), trace=trace, reads=reads, writes=writes)


def contract(body, count):
    """All 16 alignment cases for one count, and their digest."""
    cases = [run(body, HELPER, count, d, s) for d in range(4) for s in range(4)]
    return dict(count=count, cases=len(cases),
                steps=[min(case['steps'] for case in cases), max(case['steps'] for case in cases)],
                execution_sha256=hashlib.sha256(json.dumps(cases, separators=(',', ':')).encode()).hexdigest())


class CopySummaries:
    """The copy summaries of one plain buffer proof: helper identity, contracts and sites."""

    def __init__(self, rom, mapping, index):
        require(all(type(value) is bytes for value in (rom, mapping, index)),
                'copy summaries require immutable ROM and index snapshots')
        self.rom, self.mapping, self.index = rom, mapping, index
        self.helper = self.body = None
        self.contracts = {}
        self.observations = {}

    @staticmethod
    def covers(address, arguments):
        """A call to the helper with a local alias in R0 or R1, which the walk always refuses."""
        return address == HELPER and (R0 in arguments or R0 + 1 in arguments)

    def identity(self, proof):
        if self.helper is None:
            import rom_table_copy_profile as rom_copy
            self.helper = rom_copy.helper_facts(self.rom, self.mapping, self.index)
            self.body = self.rom[HELPER - match.ROM_BASE:HELPER - match.ROM_BASE + 98]
        require(proof.span(HELPER) == self.body, 'mapped helper span differs from the pinned helper')
        return self.body

    def call(self, proof, arguments, stack, incoming, protected, *, constants, site, words):
        """Apply the summary inside BufferCallProof.check_call."""
        try:
            require(proof.copy_summaries is self and proof.stack_arguments and not words and not (
                proof.word_provenance or proof.callee_frames or proof.single_word_stores or
                proof.forwarded_stack_arguments or proof.exact_alias_state_budget is not None or
                proof.bios_fill_proof is not None or proof.discarded_exit_scratch is not None or
                proof.runtime_summaries is not None),
                'copy summary excludes word-provenance, callee-frame and other summary contexts')
            require(type(site) is int, 'copy summary requires an actual direct call site')
            require(R2 not in arguments and LR not in arguments, 'copy summary refuses a local pointer in R2 or LR')
            for offset in (*arguments.values(), *incoming.values()):
                proof.validate_pointer_value(offset, stack)
            count = constants.get(R2)
            require(type(count) is int and 1 <= count <= MAX_COUNT,
                    f'copy summary count must be an exact constant from 1 to {MAX_COUNT}')
            body = self.identity(proof)
            if count not in self.contracts:
                self.contracts[count] = contract(body, count)
            destination, source = arguments.get(R0), arguments.get(R0 + 1)
            for start, write in ((destination, True), (source, False)):
                if start is None:
                    continue
                for offset in range(start, start + count):
                    proof.access(offset, 1, stack)
                first, last = (start + 4 * len(stack)) // 4, (start + count - 1 + 4 * len(stack)) // 4
                require(not any(start < slot + 4 and start + count > slot for slot in protected) and
                        not (write and any(stack[slot][0] for slot in range(first, last + 1))),
                        'copy destination overlaps a pointer-bearing or return-carrying word' if write else
                        'copy source overlaps a pointer-bearing word')
            require(destination is None or source is None or
                    destination + count <= source or source + count <= destination,
                    'copy source and destination overlap')
            # R0 (the destination), R3 = src+n (one past a local source) and an R12 alias are
            # handed back; dropping R3 would leave a live frame pointer unchecked.
            result = {}
            if destination is not None:
                result[R0] = destination
            if source is not None:
                # The helper leaves R3 = src+n: a local frame pointer when the source is local.
                result[R3] = source + count
            if R12 in arguments:
                result[R12] = arguments[R12]
            proof.dependencies[HELPER] = body
            dropped = sorted([register - R0, arguments[register]]
                             for register in (R3, R0 + 1) if register in arguments and register not in result)
            record = dict(site=site, count=count, frame_bytes=4 * len(stack),
                          destination=destination, source=source,
                          dropped=dropped,
                          returned=sorted([register - R0, offset] for register, offset in result.items()),
                          incoming=sorted([slot, target] for slot, target in incoming.items()),
                          protected=sorted(protected))
            self.observations[json.dumps(record, sort_keys=True)] = record
        except ValueError as error:
            raise ValueError(f'buffer callee 0x{HELPER:08X}: {error}') from error
        return proof.word_result(result, {})

    def evidence(self):
        return dict(policy=POLICY, helper=self.helper,
                    contracts=[self.contracts[count] for count in sorted(self.contracts)],
                    observations=[self.observations[key] for key in sorted(self.observations)])

    def lines(self):
        """One report line per observation; empty when nothing was summarised."""
        def where(offset, frame):
            return 'external' if offset is None else f'sp{offset + frame:+d}'
        lines = []
        for key in sorted(self.observations):
            record = self.observations[key]
            frame = record['frame_bytes']
            digest = self.contracts[record['count']]['execution_sha256'][:16]
            returned = ' '.join(f'r{register}=sp{offset + frame:+d}' for register, offset in record['returned'])
            dropped = ' '.join(f'r{register}=sp{offset + frame:+d}' for register, offset in record['dropped'])
            lines.append(f'* buffer copy summary: `{POLICY}` 0x{HELPER:08X} at 0x{record["site"]:08X}: '
                         f'count {record["count"]}, destination {where(record["destination"], frame)}, '
                         f'source {where(record["source"], frame)}; returns {returned or "none"}; '
                         f'drops {dropped or "none"}; pointer words {len(record["protected"])}; '
                         f'contract 16 cases {digest}')
        return lines
