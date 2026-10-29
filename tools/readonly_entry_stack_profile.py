"""Explicit entry ABI contract for one read-only incoming Thumb stack word."""
from capstone.arm import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0, ARM_REG_SP,
                          ARM_CC_AL, ARM_CC_INVALID)

SCHEMA = 'thumb-readonly-entry-stack-word-v1'
CONTRACT = ('entry SP+0 provides one readable aligned 4-byte incoming ABI word; '
            'contents unknown, caller allocation and memory value are premises')


def validate(policy):
    if type(policy) is not dict or set(policy) != {'schema', 'words'} or \
            type(policy['schema']) is not str or policy['schema'] != SCHEMA or \
            type(policy['words']) is not list or len(policy['words']) != 1 or \
            type(policy['words'][0]) is not int or policy['words'][0] != 0:
        raise ValueError('entry stack requires the explicit read-only word0 ABI contract')
    return policy


def read_word(instruction, frame_words, policy):
    """Authenticate encoding and normalize the displacement to original entry SP."""
    validate(policy)
    operands = instruction.operands
    raw = bytes(instruction.bytes)
    encoded = int.from_bytes(raw, 'little')
    if type(frame_words) is not int or frame_words < 0 or instruction.size != 2 or \
            len(raw) != 2 or encoded & 0xF800 != 0x9800 or instruction.address % 2 or \
            instruction.mnemonic != 'ldr' or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            len(operands) != 2 or operands[0].type != ARM_OP_REG or \
            operands[0].reg != ARM_REG_R0 + ((encoded >> 8) & 7) or \
            operands[1].type != ARM_OP_MEM or operands[1].mem.base != ARM_REG_SP or \
            operands[1].mem.index or operands[1].mem.disp != 4 * (encoded & 0xFF) or \
            operands[1].subtracted or operands[1].shift.type or operands[1].shift.value or instruction.writeback:
        raise ValueError('entry stack permits only exact direct aligned 2-byte Thumb LDR words')
    offset = 4 * (encoded & 0xFF) - 4 * frame_words
    if offset != 0:
        raise ValueError('entry stack read leaves the declared incoming word0')
    return offset
