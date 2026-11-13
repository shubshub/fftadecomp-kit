"""Pinned proofs that a ROM callee never writes R7/R8.

Bounded loop replay trusts un-inspected calls to preserve the R4-R11 counters
it tracks.  For the one real user (func_0812E4F4's counter in R7, with R8 held
across the same calls) that premise is checked here instead: the callee bytes
are pinned by SHA-256, linearly decoded outside their literal words and
dispatch tables, and every register write, branch target, indirect jump and
call is checked.  Anything not understood refuses, so the pair stays "trusted".

A pin is (end, SHA-256 of the span, ((table address, entries), ...)).  The
dispatch tables are the only indirect-jump targets accepted, and each entry
must be a plain address of an instruction start inside the span (as agbcc
emits them for `mov pc, r0`).
"""
import hashlib
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_INT
from capstone.arm_const import (ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, ARM_REG_R0,
                                ARM_INS_B, ARM_INS_BL, ARM_INS_BX, ARM_INS_LDR, ARM_INS_MOV)

ROM_BASE = 0x08000000
PINS = {
    0x080C7EA4: (0x080C817C, "29dd15c43bb1bffac2764ef500fea0cc258ebea77360b3d04e0ee382b738ffcb",
                 ((0x080C7EC0, 69),)),
    0x080CA7A4: (0x080CA8FE, "ff46b43099ea0296e3f9646af8166d45efb5375d73b657984d4b2370b01221f1",
                 ((0x080CA7CC, 19),)),
    0x080C95A8: (0x080C95C0, "1972a08b68f4413fbec69e9c0ceef5227ed3608bb39299597a4de0c061164b84", ()),
}
REGISTERS = (ARM_REG_R0 + 7, ARM_REG_R0 + 8)


def _prove(rom, address, active):
    if address not in PINS or address in active:
        raise ValueError("callee is not pinned or recurses")
    end, digest, tables = PINS[address]
    if not ROM_BASE <= address < end <= ROM_BASE + len(rom) or \
            hashlib.sha256(rom[address - ROM_BASE:end - ROM_BASE]).hexdigest() != digest:
        raise ValueError("pinned callee bytes differ")
    data = {}
    for start, count in tables:
        data.update({start + offset: 4 for offset in range(0, 4 * count, 4)})
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions, cursor = {}, address
    while cursor < end:
        if cursor in data:
            cursor += 4
            continue
        decoded = next(decoder.disasm(rom[cursor - ROM_BASE:min(cursor + 4, end) - ROM_BASE], cursor, count=1), None)
        if decoded is None or cursor + decoded.size > end:
            raise ValueError("undecodable callee byte")
        instructions[cursor] = decoded
        cursor += decoded.size
        if decoded.id == ARM_INS_LDR and decoded.operands[1].type == ARM_OP_MEM and \
                decoded.operands[1].mem.base == ARM_REG_PC:
            literal = ((decoded.address + 4) & ~3) + decoded.operands[1].mem.disp
            if not (address <= literal and literal + 4 <= end):
                raise ValueError("literal outside the callee")
            data[literal] = 4
    for start, count in tables:
        for offset in range(0, 4 * count, 4):
            entry = struct.unpack_from("<I", rom, start + offset - ROM_BASE)[0]
            if entry not in instructions:
                raise ValueError("dispatch entry is not a callee instruction")
    nested = []
    for instruction in instructions.values():
        written = instruction.regs_access()[1]
        if any(register in written for register in REGISTERS):
            raise ValueError("callee writes a tracked register")
        if CS_GRP_INT in instruction.groups:
            raise ValueError("software interrupt")
        operands = instruction.operands
        if instruction.id == ARM_INS_BL:
            nested.append(operands[0].imm)
        elif CS_GRP_CALL in instruction.groups:
            raise ValueError("indirect call")
        elif instruction.id == ARM_INS_B:
            if operands[0].imm not in instructions:
                raise ValueError("branch leaves the callee")
        elif instruction.id == ARM_INS_MOV and operands[0].type == ARM_OP_REG and \
                operands[0].reg == ARM_REG_PC and not tables:
            raise ValueError("unpinned indirect jump")
    for target in nested:
        _prove(rom, target, active | {address})


def preserves_r7_r8(rom, address):
    """True only when the pinned callee (and its pinned callees) never write R7 or R8."""
    try:
        _prove(rom, address, frozenset())
    except (ValueError, IndexError, struct.error):
        return False
    return True
