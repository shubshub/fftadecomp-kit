"""Exact zero register-index evidence for native local signed byte/halfword loads."""
from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_REG, ARM_OP_MEM,
    ARM_OP_IMM, ARM_REG_R0)

SELECTOR = 'zero-register-index-local-signed-loads-v1'
MAX_UPDATES = 4096


def signed_load(instruction):
    """Authenticate the original Thumb LDRSB/LDRSH register-offset encoding."""
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL,ARM_CC_INVALID) or \
            len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[1].type != ARM_OP_MEM:
        return None
    encoded = int.from_bytes(instruction.bytes,'little')
    kind = {0x5600:('ldrsb',1),0x5E00:('ldrsh',2)}.get(encoded & 0xFE00)
    memory = operands[1].mem
    if kind is None or instruction.mnemonic != kind[0] or \
            operands[0].reg != ARM_REG_R0+(encoded & 7) or \
            memory.base != ARM_REG_R0+((encoded >> 3) & 7) or \
            memory.index != ARM_REG_R0+((encoded >> 6) & 7) or \
            memory.disp or memory.scale != 1 or instruction.writeback or \
            operands[1].shift.type or operands[1].shift.value or operands[1].subtracted:
        return None
    return memory.base,memory.index,kind[1]


def zero_transfer(instruction,incoming):
    """Only exact MOVS #0 and authenticated register copies introduce zero."""
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL,ARM_CC_INVALID):
        return None
    encoded = int.from_bytes(instruction.bytes,'little')
    if encoded & 0xF8FF == 0x2000 and instruction.mnemonic == 'movs' and len(operands) == 2 and \
            operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_R0+((encoded >> 8) & 7) and \
            operands[1].type == ARM_OP_IMM and operands[1].imm == 0:
        return operands[0].reg,frozenset((instruction.address,))
    source = destination = None
    if encoded & 0xFF00 == 0x4600 and instruction.mnemonic == 'mov' and len(operands) == 2 and \
            all(op.type == ARM_OP_REG for op in operands):
        destination = ARM_REG_R0+(encoded & 7)+((encoded >> 4) & 8)
        source = ARM_REG_R0+((encoded >> 3) & 15)
        if operands[0].reg != destination or operands[1].reg != source:return None
    elif encoded & 0xFFC0 == 0x1C00 and instruction.mnemonic == 'adds' and len(operands) == 3 and \
            operands[0].type == operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and operands[2].imm == 0:
        destination,source = ARM_REG_R0+(encoded & 7),ARM_REG_R0+((encoded >> 3) & 7)
        if operands[0].reg != destination or operands[1].reg != source:return None
    if source in incoming:return destination,incoming[source]
    return None


def prove_zeros(instructions,edges,address):
    """Intersect every reaching path; writes and every call erase zero facts."""
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError('zero index requires its exact complete native CFG')
    states,pending,updates = {address:{}},[address],0
    while pending:
        site = pending.pop();instruction = instructions[site]
        incoming = states[site];outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            outgoing.clear()
        else:
            _,written = instruction.regs_access()
            for register in written:outgoing.pop(register,None)
            transfer = zero_transfer(instruction,incoming)
            if transfer is not None:outgoing[transfer[0]] = transfer[1]
        for successor in edges[site]:
            if successor not in instructions:raise ValueError('zero index CFG escapes exact instruction boundaries')
            previous = states.get(successor)
            merged = outgoing if previous is None else {register:origins | outgoing[register]
                for register,origins in previous.items() if register in outgoing}
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:raise ValueError('zero index proof-state budget exceeded')
                states[successor] = merged;pending.append(successor)
    if set(states) != set(instructions):raise ValueError('zero index facts do not cover the complete native CFG')
    return states
