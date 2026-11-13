"""Pinned proofs that a ROM callee never writes R7/R8.

Bounded loop replay trusts un-inspected calls to preserve the R4-R11 counters
it tracks.  For the one real user (func_0812E4F4's counter in R7, with R8 held
across the same calls) that premise is checked here instead: the callee bytes
are pinned by SHA-256 and decoded by reachability from the entry.  Every
reached instruction is checked for register writes, calls and PC writes, and
code may not reach a literal word, a dispatch table or the end of the span.
Only `B`, `BL`, `bx lr`, `pop {..., pc}`, `pop {rX}` + `bx rX` (both only
after a `push {..., lr}` entry) and the agbcc switch idiom may write PC.
Anything not understood refuses, so the pair stays "trusted".

The decode is ARMv4T, the ARM7TDMI's: every instruction is 2 bytes except a BL
(`F000-F7FF` then `F800-FFFF`), the mnemonic must be on the ARMv4T Thumb list
(no cbz/it/udf/bkpt/blx/sxt/uxt/rev/cps/setend/nop, no 32-bit encodings, no
low-register hi-register-format mov/add/cmp), and no reached instruction may
start inside another.  SP is tracked exactly from the entry `push`: that push
is the only push, SP is touched only by it and by pops, nothing reads SP, and no
non-BL instruction writes LR.  Every return sits at depth zero, where `pop`
takes the saved link register and `bx lr` is only valid when no call ran.
A callee that saves registers but not LR (`push {r4}; ...; pop {r4}; bx lr`) is
refused: the pop back to depth zero must be a return pair.  Instruction
addresses must be even (`mov pc` ignores bit 0).

A pin is (end, SHA-256 of the span, ((table address, entries), ...)).  The
switch idiom is `cmp rX,#K` guarded by `bls`/`bhi`, then
`lsls r0,rX,#2; ldr r1,[pc,#..]; adds r0,r0,r1; ldr r0,[r0]; mov pc,r0`; K+1
must equal the pinned entry count, the literal must be the pinned table
address, and each entry must be an instruction start inside the span.  Only the
`cmp` may reach the guard, nothing may branch into the middle of the idiom or
around its bound check, and no table entry may land in `cmp`..`mov pc`.
"""
import hashlib
import struct

from capstone import Cs, CsError, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL, CS_GRP_INT
from capstone import arm_const
from capstone.arm_const import (ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, ARM_REG_R0,
                                ARM_INS_ADD, ARM_INS_B, ARM_INS_BL, ARM_INS_BX, ARM_INS_CMP,
                                ARM_INS_LDR, ARM_INS_LSL, ARM_INS_MOV, ARM_INS_POP, ARM_INS_PUSH,
                                ARM_REG_LR, ARM_REG_SP, ARM_CC_AL, ARM_CC_HI, ARM_CC_LS)

ROM_BASE = 0x08000000
PINS = {
    0x080C7EA4: (0x080C817C, "29dd15c43bb1bffac2764ef500fea0cc258ebea77360b3d04e0ee382b738ffcb",
                 ((0x080C7EC0, 69),)),
    0x080CA7A4: (0x080CA8FE, "ff46b43099ea0296e3f9646af8166d45efb5375d73b657984d4b2370b01221f1",
                 ((0x080CA7CC, 19),)),
    0x080C95A8: (0x080C95C0, "1972a08b68f4413fbec69e9c0ceef5227ed3608bb39299597a4de0c061164b84", ()),
}
REGISTERS = (ARM_REG_R0 + 7, ARM_REG_R0 + 8)
ARMV4T = frozenset(getattr(arm_const, "ARM_INS_" + name) for name in (
    "ADC ADD ADR AND ASR B BIC BL BX CMN CMP EOR LDM LDR LDRB LDRH LDRSB LDRSH LSL LSR MOV MUL MVN "
    "ORR POP PUSH ROR RSB SBC STM STR STRB STRH SUB TST").split())


def _decode(decoder, rom, cursor, address, end):
    if cursor & 1:
        raise ValueError("odd instruction address")
    if not address <= cursor < end:
        raise ValueError("control leaves the callee")
    decoded = next(decoder.disasm(rom[cursor - ROM_BASE:min(cursor + 4, end) - ROM_BASE], cursor, count=1), None)
    if decoded is None or cursor + decoded.size > end:
        raise ValueError("undecodable callee byte")
    if decoded.id not in ARMV4T:
        raise ValueError("instruction is not ARMv4T Thumb")
    first = struct.unpack_from("<H", rom, cursor - ROM_BASE)[0]
    if decoded.id == ARM_INS_BL:
        if decoded.size != 4 or first & 0xF800 != 0xF000 or \
                struct.unpack_from("<H", rom, cursor + 2 - ROM_BASE)[0] & 0xF800 != 0xF800:
            raise ValueError("not an ARMv4T BL pair")
    elif decoded.size != 2:
        raise ValueError("32-bit instruction is not ARMv4T")
    elif first & 0xFC00 == 0x4400 and first & 0xC0 == 0 and first & 0x300 != 0x300:
        raise ValueError("low-register hi-register-format operation is undefined on ARMv4T")
    return decoded


def _is_literal_load(instruction):
    return instruction.id == ARM_INS_LDR and instruction.operands[1].type == ARM_OP_MEM and \
        instruction.operands[1].mem.base == ARM_REG_PC


def _literal(instruction):
    return ((instruction.address + 4) & ~3) + instruction.operands[1].mem.disp


def _switch(decoder, rom, at, address, end, tables):
    """(table address, entries, entry address, sources allowed into it) of the switch ending at `at`."""
    load, add, pool, scale = (_decode(decoder, rom, at - back, address, end) for back in (2, 4, 6, 8))
    r0, r1 = ARM_REG_R0, ARM_REG_R0 + 1
    if not (load.id == ARM_INS_LDR and load.operands[0].reg == r0 and load.operands[1].type == ARM_OP_MEM
            and len(load.operands) == 2 and load.operands[1].mem.base == r0
            and not load.operands[1].mem.index and load.operands[1].mem.disp == 0
            and add.id == ARM_INS_ADD and [o.reg for o in add.operands] == [r0, r0, r1]
            and _is_literal_load(pool) and pool.operands[0].reg == r1
            and scale.id == ARM_INS_LSL and scale.operands[0].reg == r0 and scale.operands[2].imm == 2):
        raise ValueError("indirect jump is not the switch idiom")
    entry = scale.address
    guard = _decode(decoder, rom, entry - 2, address, end)
    if guard.id == ARM_INS_B and guard.cc == ARM_CC_AL:
        jump = _decode(decoder, rom, entry - 4, address, end)
        if not (jump.id == ARM_INS_B and jump.cc == ARM_CC_LS and jump.operands[0].imm == entry):
            raise ValueError("switch bound is not checked")
        compare, allowed = _decode(decoder, rom, entry - 6, address, end), {jump.address}
    elif guard.id == ARM_INS_B and guard.cc == ARM_CC_HI:
        compare, allowed = _decode(decoder, rom, entry - 4, address, end), {guard.address}
    else:
        raise ValueError("switch bound is not checked")
    if not (compare.id == ARM_INS_CMP and compare.operands[0].reg == scale.operands[1].reg
            and compare.operands[1].type == ARM_OP_IMM):
        raise ValueError("switch bound is not checked")
    table = struct.unpack_from("<I", rom, _literal(pool) - ROM_BASE)[0]
    if (table, compare.operands[1].imm + 1) not in tables:
        raise ValueError("switch table or bound disagrees with the pin")
    return table, compare.operands[1].imm + 1, entry, allowed, compare.address


def _prove(rom, address, active):
    if address not in PINS or address in active:
        raise ValueError("callee is not pinned or recurses")
    end, digest, tables = PINS[address]
    if not ROM_BASE <= address < end <= ROM_BASE + len(rom) or \
            hashlib.sha256(rom[address - ROM_BASE:end - ROM_BASE]).hexdigest() != digest:
        raise ValueError("pinned callee bytes differ")
    data = set()
    for start, count in tables:
        if not (address <= start and start + 4 * count <= end):
            raise ValueError("dispatch table outside the callee")
        data.update(range(start, start + 4 * count))
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    first = _decode(decoder, rom, address, address, end)
    framed = first.id == ARM_INS_PUSH and any(o.reg == ARM_REG_LR for o in first.operands)
    instructions, depths, work, edges, paired, switches, nested = {}, {}, [(address, 0)], {}, set(), [], []
    link_returns = False

    def edge(source, target, depth):
        edges.setdefault(target, set()).add(source)
        work.append((target, depth))

    while work:
        cursor, depth = work.pop()
        if cursor in instructions:
            if depths[cursor] != depth:
                raise ValueError("stack depth differs between paths")
            continue
        instruction = instructions[cursor] = _decode(decoder, rom, cursor, address, end)
        depths[cursor] = depth
        following = cursor + instruction.size
        if _is_literal_load(instruction):
            literal = _literal(instruction)
            if not (address <= literal and literal + 4 <= end):
                raise ValueError("literal outside the callee")
            data.update(range(literal, literal + 4))
        reads, writes = instruction.regs_access()
        if any(register in writes for register in REGISTERS):
            raise ValueError("callee writes a tracked register")
        if CS_GRP_INT in instruction.groups:
            raise ValueError("software interrupt")
        if instruction.id != ARM_INS_BL and ARM_REG_LR in writes:
            raise ValueError("link register overwritten")
        operands = instruction.operands
        if instruction.id == ARM_INS_PUSH:
            if cursor != address:
                raise ValueError("push other than the entry push")
            depth -= 4 * len(operands)
        elif instruction.id == ARM_INS_POP:
            depth += 4 * len(operands)
            if depth > 0:
                raise ValueError("pop below the entry stack depth")
        elif ARM_REG_SP in reads or ARM_REG_SP in writes or any(
                o.type == ARM_OP_MEM and ARM_REG_SP in (o.mem.base, o.mem.index) for o in operands):
            raise ValueError("stack pointer used outside the entry push and exit pops")
        if instruction.id == ARM_INS_BL:
            nested.append(operands[0].imm)
            edge(cursor, following, depth)
        elif instruction.id == ARM_INS_B:
            edge(cursor, operands[0].imm, depth)
            if instruction.cc != ARM_CC_AL:
                edge(cursor, following, depth)
        elif instruction.id == ARM_INS_BX:
            if not (operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_LR):
                raise ValueError("indirect jump")
            if depth != 0:
                raise ValueError("return with the entry frame still pushed")
            link_returns = True
        elif instruction.id == ARM_INS_POP and any(o.reg == ARM_REG_PC for o in operands):
            if not framed or depth != 0:
                raise ValueError("return without the pushed link register")
        elif instruction.id == ARM_INS_POP and depth == 0:
            pair = _decode(decoder, rom, following, address, end) if len(operands) == 1 else None
            if not (framed and pair is not None and pair.id == ARM_INS_BX and pair.operands[0].type == ARM_OP_REG
                    and pair.operands[0].reg == operands[0].reg):
                raise ValueError("pop is not a return")
            instructions[following] = pair
            depths[following] = 0
            paired.add(following)
        elif CS_GRP_CALL in instruction.groups:
            raise ValueError("indirect call")
        elif ARM_REG_PC in writes or (
                operands and operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_PC):
            if instruction.id != ARM_INS_MOV or not tables:
                raise ValueError("unpinned indirect jump")
            start, count, entry, allowed, compare = _switch(decoder, rom, cursor, address, end, tables)
            targets = [struct.unpack_from("<I", rom, start + 4 * index - ROM_BASE)[0] for index in range(count)]
            if any(compare <= target <= cursor for target in targets):
                raise ValueError("dispatch entry inside the switch idiom")
            switches.append((cursor, entry, allowed, compare))
            for target in targets:
                if not address <= target < end:
                    raise ValueError("dispatch entry is not a callee instruction")
                edge(cursor, target, depth)
        else:
            edge(cursor, following, depth)
    if link_returns and nested:
        raise ValueError("bx lr after a call")
    if set(edges) & paired:
        raise ValueError("branch into a return pair")
    for at, entry, allowed, compare in switches:
        for inside in range(compare + 2, at + 1, 2):
            if edges.get(inside, set()) - (allowed if inside == entry else {inside - 2}):
                raise ValueError("branch into the switch idiom or around its bound check")
    starts = sorted(instructions)
    if any(later < item + instructions[item].size for item, later in zip(starts, starts[1:])):
        raise ValueError("instruction starts inside another")
    if {byte for item in instructions.values() for byte in range(item.address, item.address + item.size)} & data:
        raise ValueError("code reaches data")
    for target in nested:
        _prove(rom, target, active | {address})


def preserves_r7_r8(rom, address):
    """True only when the pinned callee (and its pinned callees) never write R7 or R8."""
    try:
        _prove(rom, address, frozenset())
    except (ValueError, IndexError, struct.error, CsError):
        return False
    return True
