"""Inventory-only opt-in for one read-only ARMv4T Thumb SP comparison."""
from capstone.arm import (ARM_CC_AL, ARM_INS_CMP, ARM_OP_REG,
                          ARM_REG_CPSR, ARM_REG_R0, ARM_REG_SP)

SELECTOR = 'thumb-sp-r0-compare-inventory-v1'


def verify_instruction(instruction):
    """Check exact CMP SP,R0 bytes/effects; export no pointer or numeric fact."""
    operands = instruction.operands
    read, written = instruction.regs_access()
    if instruction.id != ARM_INS_CMP or instruction.mnemonic != 'cmp' or \
            instruction.size != 2 or bytes(instruction.bytes) != b'\x85\x45' or \
            instruction.cc != ARM_CC_AL or not instruction.update_flags or \
            instruction.writeback or len(operands) != 2 or \
            any(operand.type != ARM_OP_REG or operand.shift.type or operand.shift.value or
                operand.subtracted for operand in operands) or \
            tuple(operand.reg for operand in operands) != (ARM_REG_SP, ARM_REG_R0) or \
            set(read) != {ARM_REG_SP, ARM_REG_R0} or set(written) != {ARM_REG_CPSR}:
        raise ValueError('SP comparison requires exact unconditional read-only Thumb CMP SP,R0 effects')
