"""Explicit local alias-word slots and exact MOVS 1/2/3 index evidence."""
from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_REG,
    ARM_OP_MEM, ARM_OP_IMM, ARM_REG_R0, ARM_REG_SP)
import zero_index_stack_profile as zero_index

SELECTOR = 'local-alias-word-slots-small-index-v1'
SCHEMA = 'thumb-local-alias-word-slots-small-index-v1'
UNKNOWN = frozenset(((0, False),))
MAX_UPDATES = 4096
FORMAL_MOVS10_POLICY = 'formal-stack-leaf-movs10-local-alias-v1'
FORMAL_MOVS10_DOMAIN = (1, 2, 3, 10)


def validate(policy):
    if type(policy) is not str or policy != SELECTOR:
        raise ValueError('local alias slots require their explicit versioned policy')


def prove_constants(instructions, edges, address, *, constant_domain=None):
    """Intersect exact reaching MOVS facts; every call erases these facts."""
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError('small local indices require their exact complete CFG')
    if constant_domain is not None and (type(constant_domain) is not tuple or
            constant_domain != FORMAL_MOVS10_DOMAIN or
            any(type(value) is not int for value in constant_domain)):
        raise ValueError('formal MOVS10 constants require their exact finite domain')
    allowed = (1, 2, 3) if constant_domain is None else constant_domain
    states, pending, updates = {address: {}}, [address], 0
    while pending:
        site = pending.pop(); instruction = instructions[site]
        outgoing = dict(states[site])
        if CS_GRP_CALL in instruction.groups:
            outgoing.clear()
        else:
            _, written = instruction.regs_access()
            for register in written: outgoing.pop(register, None)
            operands = instruction.operands
            encoded = int.from_bytes(instruction.bytes, 'little')
            if instruction.size == 2 and encoded & 0xF800 == 0x2000 and \
                    encoded & 255 in allowed and instruction.mnemonic == 'movs' and \
                    instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and len(operands) == 2 and \
                    operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_R0 + ((encoded >> 8) & 7) and \
                    operands[1].type == ARM_OP_IMM and operands[1].imm == encoded & 255:
                outgoing[operands[0].reg] = (encoded & 255, frozenset((site,)))
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError('small local index CFG leaves its exact boundaries')
            previous = states.get(successor)
            merged = outgoing if previous is None else {register: (value, origins | outgoing[register][1])
                for register, (value, origins) in previous.items()
                if register in outgoing and outgoing[register][0] == value}
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES: raise ValueError('small local index proof-state budget exceeded')
                states[successor] = merged; pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError('small local index facts do not cover the complete CFG')
    return states


def indexed_byte(instruction, constants, aliases):
    decoded = zero_index.signed_load(instruction)
    if decoded is None: return None
    base, index, width = decoded
    if width != 1 or index in aliases or index not in constants: return None
    value, origins = constants[index]
    if value not in (1, 2, 3): return None
    return base, index, value, tuple(sorted(origins))


def word(instruction):
    """Authenticate exact Thumb STR/LDR immediate local words, no writeback."""
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_MEM or \
            instruction.writeback or operands[1].shift.type or operands[1].shift.value or operands[1].subtracted:
        raise ValueError('alias slots require exact aligned Thumb STR/LDR local words')
    encoded = int.from_bytes(instruction.bytes, 'little')
    memory = operands[1].mem
    if encoded & 0xF000 == 0x9000:
        load = bool(encoded & 0x0800)
        register, base, displacement = ARM_REG_R0 + ((encoded >> 8) & 7), ARM_REG_SP, 4 * (encoded & 255)
    elif encoded & 0xF000 == 0x6000:
        load = bool(encoded & 0x0800)
        register, base, displacement = ARM_REG_R0 + (encoded & 7), ARM_REG_R0 + ((encoded >> 3) & 7), 4 * ((encoded >> 6) & 31)
    else:
        raise ValueError('alias slots require exact aligned Thumb STR/LDR local words')
    if instruction.mnemonic != ('ldr' if load else 'str') or operands[0].reg != register or \
            memory.base != base or memory.index or memory.disp != displacement:
        raise ValueError('alias slot instruction bytes and decoded operands differ')
    return load, register


def store(slots, offset, width, values=None):
    """Full scalar overwrites clear pointers; partial writes retain tainted words."""
    for start in tuple(slots):
        if offset < start + 4 and start < offset + width:
            if offset == start and width == 4: slots.pop(start)
            else: slots[start] = slots[start] | UNKNOWN
    if values is not None:
        if width != 4 or offset % 4:
            raise ValueError('local alias spills require aligned allocated words')
        slots[offset] = values


def release(slots, depth):
    return {word: frozenset((offset, live and word >= -4 * depth and offset >= -4 * depth)
        for offset, live in values) for word, values in slots.items()}


def join(previous, incoming):
    return tuple(sorted((word, tuple(sorted(previous.get(word, UNKNOWN) | incoming.get(word, UNKNOWN))))
        for word in previous.keys() | incoming.keys()))
