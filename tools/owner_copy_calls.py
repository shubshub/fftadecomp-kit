"""Copy calls of a closed restoring owner: CpuSet copy control words.

A restoring owner must bind every reached PC-relative word in the typed address
domain [0x02000000, 0x09000000) to a typed object or function, so that no
address is written in the source as a bare number.  A CpuSet copy control
whose count has bit 26 set (32-bit units) lies in that domain without being an
address: 0x04000080 copies 0x80 words.  ``copy_controls`` takes such a word
out of the typed coverage only when the owner's own CFG proves it is a number
passed to CpuSet and nothing else:

* the word is a whole CpuSet copy control: count (bits 0-20) at least 1, bit
  26 the unit (4 bytes; 2 when clear), bit 24 (fill) clear and no other bit
  set; it is not a switch word and not a relocated literal;
* every load of it is a 16-bit ``ldr rd, [pc, #imm]``, and from each load the
  value is followed over the complete CFG (may-analysis, union at joins) through
  register copies only (``adds rd, rs, #0``, ``movs rd, rs``, ``mov rd, rs``
  into r0-r12): any other instruction that reads a register holding it
  (arithmetic, compare, store, address, push, indirect branch) is refused;
* the flags a copy sets from it are followed too, and a conditional
  instruction or a flag read while they may still hold them is refused; only
  a flag-setting instruction clears them, not a call (a BIOS SWI returns with
  the caller's flags);
* at a call it may be only in r2, only when the target is the CpuSet wrapper
  0x0814186C, whose four indexed bytes must be exactly ``svc 0x0B; bx lr``;
  r0-r3 and r12 at any other call, or r0, r1, r3 and r12 at that one, refuse;
  after any call r0-r3, r12 and LR are the callee's (the ordinary returning
  ABI the owner proof already uses), except that r2 after CpuSet stays
  followed: an instruction that reads it before rewriting it refuses.  A
  later call with r2 still unwritten is not refused: under that ABI the
  callee takes only arguments the caller set (agbcc sets every argument it
  passes), and 08078818 calls func_0808A604(4, 1) right after CpuSet;
* it does not survive a return (in r0-r12 after the returning instruction);
* each load reaches at least one CpuSet call, and at every such call a
  must-analysis (equal facts only at joins) shows r2 is this exact word on
  every path.

Each call is recorded with its control, unit, units and bytes, and with the
provenance the must-analysis gives r0 (source) and r1 (destination): a typed
literal plus offset, the word one load instruction read from a typed literal
plus offset (with that load's site, so a later call or store that may change
the object does not make the record name a stale value), a constant, or
unknown.  Data symbols are points, so no object extent,
containment, nonalias, readability or writability is proved for either range;
the frame proof of the owner, which runs unchanged, is what bounds any local
pointer.  The BIOS routine is the GBATEK premise; r4-r11 kept across calls is
the owner proof's ordinary returning ABI premise.
"""
import hashlib
import struct

from capstone.arm import (ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R12,
                          ARM_REG_LR, ARM_REG_PC, ARM_REG_CPSR, ARM_CC_AL, ARM_CC_INVALID)

import bios_cpuset_fill_profile as cpuset
import rom_mirror

MASK = 0xFFFFFFFF
R2 = ARM_REG_R0 + 2
ARGUMENTS = frozenset(range(ARM_REG_R0, ARM_REG_R0 + 4)) | {ARM_REG_R12}
CLOBBERED = ARGUMENTS | {ARM_REG_LR}
GENERAL = frozenset(range(ARM_REG_R0, ARM_REG_R12 + 1))
COUNT = 0x1FFFFF
FILL = 1 << 24
WORDS = 1 << 26
CONTROL_SCHEMA = 'owner-cpuset-copy-control-words-v1'
CONTROL_CONTRACT = (
    'reached unrelocated PC words that are whole CpuSet copy controls (count bits 0-20 at least 1, '
    'unit 4 bytes if bit26 else 2, bit24 clear, no other bit) and whose every load reaches, through '
    'register copies only, nothing but r2 of a direct call to the exact indexed CpuSet wrapper '
    '0x0814186C; no other read, flag use, other argument or return; r2 is the word on every path '
    'to each such call; per call the control, bytes and source/destination provenance are '
    'recorded. GBATEK CpuSet premise; r4-r11 kept across calls under the ordinary returning ABI; '
    'no object extent, containment, nonalias, readability, writability, initialization or '
    'termination theorem')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def literal_offset(instruction, address, size):
    """The owner offset of the aligned word a 16-bit `ldr rd, [pc, #imm]` reads, or None."""
    operands = instruction.operands
    if instruction.mnemonic != 'ldr' or instruction.size != 2 or len(operands) != 2 or \
            operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_MEM or \
            operands[1].mem.base != ARM_REG_PC or operands[1].mem.index:
        return None
    offset = ((instruction.address + 4) & ~3) + operands[1].mem.disp - address
    return offset if 0 <= offset <= size - 4 and (address + offset) % 4 == 0 else None


def _add(value, delta):
    if type(value) is int:
        return (value + delta) & MASK
    return (*value[:-1], (value[-1] + delta) & MASK)


def value(instruction, incoming, address, data):
    """The exact value one unconditional 16-bit instruction writes to its first register, or None.

    A value is an int, ``('literal', offset, delta)`` (the owner word at
    ``offset``, in the typed domain, plus delta) or ``('loaded', offset, field,
    load, delta)`` (the word the instruction at owner offset ``load`` read from
    that literal plus ``field``, plus delta).
    """
    operands = instruction.operands
    if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or instruction.size != 2 or \
            not operands or operands[0].type != ARM_OP_REG or operands[0].reg not in GENERAL:
        return None
    name, destination = instruction.mnemonic, operands[0].reg

    def known(operand):
        return incoming.get(operand.reg) if operand.type == ARM_OP_REG and operand.reg in GENERAL else None

    if name in ('mov', 'movs') and len(operands) == 2:
        return operands[1].imm & MASK if operands[1].type == ARM_OP_IMM else known(operands[1])
    if name in ('adds', 'subs') and len(operands) == 3 and operands[2].type == ARM_OP_IMM:
        base = known(operands[1])
        return None if base is None else _add(base, operands[2].imm if name == 'adds' else -operands[2].imm)
    if name in ('adds', 'subs') and len(operands) == 2 and operands[1].type == ARM_OP_IMM:
        base = incoming.get(destination)
        return None if base is None else _add(base, operands[1].imm if name == 'adds' else -operands[1].imm)
    if name == 'adds' and len(operands) == 3 and operands[2].type == ARM_OP_REG:
        left, right = known(operands[1]), known(operands[2])
        if type(left) is int and right is not None:
            return _add(right, left)
        if type(right) is int and left is not None:
            return _add(left, right)
        return None
    if name in ('lsl', 'lsls') and len(operands) == 3 and operands[2].type == ARM_OP_IMM and \
            0 <= operands[2].imm <= 31:
        base = known(operands[1])
        return (base << operands[2].imm) & MASK if type(base) is int else None
    offset = literal_offset(instruction, address, len(data))
    if offset is not None:
        word = struct.unpack_from('<I', data, offset)[0]
        return ('literal', offset, 0) if rom_mirror.typed_domain(word) else word
    if name == 'ldr' and len(operands) == 2 and operands[1].type == ARM_OP_MEM and \
            not operands[1].mem.index and operands[1].mem.base in GENERAL:
        base = incoming.get(operands[1].mem.base)
        if type(base) is tuple and base[0] == 'literal':
            return ('loaded', base[1], (base[2] + operands[1].mem.disp) & MASK, instruction.address - address, 0)
    return None


def states(instructions, edges, address, branches, calls, data):
    """The must-analysis: exact value facts at the entry of every reached instruction."""
    facts, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        instruction, incoming = instructions[site], facts[site]
        outgoing = dict(incoming)
        if site in calls:
            for register in CLOBBERED:
                outgoing.pop(register, None)
        elif site in branches:
            outgoing.pop(ARM_REG_LR, None)
        else:
            for register in instruction.regs_access()[1]:
                outgoing.pop(register, None)
            result = value(instruction, incoming, address, data)
            if result is not None:
                outgoing[instruction.operands[0].reg] = result
        for successor in edges[site]:
            require(successor in instructions, 'argument CFG leaves exact instruction boundaries')
            previous = facts.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: fact for register, fact in previous.items() if outgoing.get(register) == fact}
            if previous != merged:
                facts[successor] = merged
                pending.append(successor)
    require(set(facts) == set(instructions), 'argument proof does not cover every reached instruction')
    return facts


def _copy(instruction):
    """(destination, source, sets flags) of a 16-bit register copy, or None."""
    if instruction.size != 2:
        return None
    code = int.from_bytes(instruction.bytes, 'little')
    if code & 0xFFC0 in (0x1C00, 0x0000):  # adds rd, rs, #0 / movs rd, rs
        return ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7), True
    if code & 0xFF00 == 0x4600:  # mov rd, rs
        destination, source = ((code >> 4) & 8) | (code & 7), (code >> 3) & 15
        if destination > 12 or source > 12:
            return None
        return ARM_REG_R0 + destination, ARM_REG_R0 + source, False
    return None


def control_uses(instructions, edges, branches, calls, load):
    """The CpuSet call sites the value loaded at ``load`` reaches; any other use refuses.

    The state is (registers that may hold the value, registers CpuSet may
    have left it in, flags that may have been set from it).
    """
    seed = instructions[load].operands[0].reg
    require(seed in GENERAL, 'CpuSet copy control load requires a general register')
    empty = frozenset()
    marks, pending, uses = {load: (empty, empty, False)}, [load], set()
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        held, left, flags = marks[site]
        reads, writes = map(set, instruction.regs_access())
        conditional = instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID)
        require(not flags or not conditional and ARM_REG_CPSR not in reads,
                'flags set from a CpuSet copy control are read')
        if site in calls:
            passed = held & ARGUMENTS
            require(passed <= {R2} and (not passed or calls[site] == cpuset.ADDRESS),
                    'CpuSet copy control reaches a call other than as the CpuSet r2 control')
            if passed:
                uses.add(site)
            # r0-r3, r12 and LR are the callee's after any call (ordinary returning ABI);
            # r2 after CpuSet is still followed until it is rewritten, and may not be read.
            held, left = held - CLOBBERED, frozenset(passed)
        elif site in branches:
            held = held - {ARM_REG_LR}
        else:
            require(not left & reads, 'register CpuSet may leave its control in is read before it is rewritten')
            if site == load:
                held = (held - writes) | {seed}
            elif held & reads:
                copy = _copy(instruction)
                require(copy is not None and reads == {copy[1]} and copy[1] in held,
                        'CpuSet copy control is read other than by a register copy')
                held = (held - writes) | {copy[0]}
                flags = flags or copy[2]
            else:
                held = held - writes
                if instruction.update_flags or ARM_REG_CPSR in writes:
                    flags = False
            left = left - writes
            if not edges[site]:
                require(not held, 'CpuSet copy control survives a return')
        for successor in edges[site]:
            previous = marks.get(successor)
            merged = (held, left, flags) if previous is None else (
                previous[0] | held, previous[1] | left, previous[2] or flags)
            if merged != previous:
                marks[successor] = merged
                pending.append(successor)
    require(uses, 'CpuSet copy control load reaches no CpuSet call')
    return sorted(uses)


def wrapper(rom, mapping, index):
    """The exact indexed CpuSet wrapper, as a dependency record."""
    from inert_spin_profile import validate_span
    import match
    body = rom[cpuset.ADDRESS - match.ROM_BASE:cpuset.ADDRESS - match.ROM_BASE + len(cpuset.WRAPPER)]
    require(body == cpuset.WRAPPER, 'CpuSet copy control requires the exact CpuSet SWI 0x0B wrapper')
    validate_span(body, cpuset.ADDRESS, rom, mapping, index)
    return [cpuset.ADDRESS, len(body), hashlib.sha256(body).hexdigest()]


def origin(fact, names):
    """A JSON record of one argument's provenance; ``names`` maps literal offsets to symbols."""
    if type(fact) is int:
        return {'constant': fact}
    if type(fact) is tuple and fact[0] == 'literal':
        return {'object': names[fact[1]], 'offset': fact[2]}
    if type(fact) is tuple:
        return {'loaded_from': names[fact[1]], 'field': fact[2], 'load': fact[3], 'offset': fact[4]}
    return {'unknown': True}


def copy_controls(instructions, edges, address, branches, calls, partition, data, remaining,
                  names, rom, mapping, index):
    """The proved copy control words among ``remaining`` owner offsets, or None when there are none.

    ``names`` maps each relocated literal offset to its symbol; a literal fact
    that reaches an argument without a name refuses.
    """
    rows = [row for row in partition['words'] if row['load_sites'] and not row['switch_word'] and
            row['address'] - address in remaining and rom_mirror.typed_domain(row['value']) and
            row['value'] & COUNT and not row['value'] & ~(COUNT | WORDS)]
    if not rows:
        return None
    facts = states(instructions, edges, address, branches, calls, data)
    words = []
    for row in rows:
        offset, control = row['address'] - address, row['value']
        uses = set()
        for load in row['load_sites']:
            require(literal_offset(instructions[load], address, len(data)) == offset,
                    'CpuSet copy control load requires a 16-bit PC-relative LDR')
            uses.update(control_uses(instructions, edges, branches, calls, load))
        unit = 4 if control & WORDS else 2
        records = []
        for site in sorted(uses):
            arguments = facts[site]
            require(arguments.get(R2) == ('literal', offset, 0),
                    'CpuSet copy control is not r2 on every path to its call')
            try:
                source, destination = (origin(arguments.get(ARM_REG_R0 + n), names) for n in (0, 1))
            except KeyError as error:
                raise ValueError('CpuSet copy argument names an unbound literal') from error
            records.append(dict(site=site - address, source=source, destination=destination))
        words.append(dict(offset=offset, control=control, unit_bytes=unit, units=control & COUNT,
                          bytes=unit * (control & COUNT),
                          loads=sorted(load - address for load in row['load_sites']), calls=records))
    return dict(schema=CONTROL_SCHEMA, contract=CONTROL_CONTRACT, wrapper=wrapper(rom, mapping, index),
                words=words, object_extent_proved=False)


CONTROL_PREMISES = ('GBATEK CpuSet reads and writes only the spans its control describes; r4-r11 are kept '
                    'across calls under the ordinary returning ABI; no object extent, containment or nonalias '
                    'is proved for either range')


def where(fact):
    """A short printed form of one provenance record; a loaded word names its load site."""
    if 'constant' in fact:
        return f'0x{fact["constant"]:08X}'
    if 'object' in fact:
        return f'{fact["object"]}+0x{fact["offset"]:X}'
    if 'loaded_from' in fact:
        return f'*({fact["loaded_from"]}+0x{fact["field"]:X})@+0x{fact["load"]:X}+0x{fact["offset"]:X}'
    return 'unknown'


def control_lines(record):
    """The premises, then one report line per recorded CpuSet copy call."""
    return [f'* CpuSet copy control premises: {CONTROL_PREMISES}'] + [f'* CpuSet copy control: word +0x{word["offset"]:X} = 0x{word["control"]:08X} '
            f'({word["units"]} x {word["unit_bytes"]} = {word["bytes"]} bytes) at call +0x{call["site"]:X}: '
            f'source {where(call["source"])}, destination {where(call["destination"])}; extent not proved'
            for word in record['words'] for call in word['calls']]
