"""Same-owner Thumb BL control flow with a complete restoring-frame proof.

This is a local edge, not a direct-call ABI summary. BL overwrites LR; it
does not clobber argument registers or return to its following instruction.
The enclosing profile must establish complete, unique original ELF and ROM
ownership and replay compilation before recording a source match.
"""

from capstone.arm import (ARM_OP_IMM, ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0,
                          ARM_REG_R4, ARM_REG_R11, ARM_REG_R12, ARM_REG_LR,
                          ARM_REG_PC, ARM_REG_SP, ARM_CC_AL, ARM_CC_INVALID)


SCHEMA = "thumb-same-owner-long-bl-restoring-frame-v1"


def validate_record(value):
    if type(value) is not dict or set(value) != {"schema", "edges"} or \
            value["schema"] != SCHEMA or type(value["edges"]) is not list or not value["edges"]:
        raise ValueError("invalid versioned local long-branch record")
    previous = -4
    for edge in value["edges"]:
        if type(edge) is not list or len(edge) != 2 or \
                any(type(offset) is not int or offset < 0 or offset % 2 for offset in edge) or \
                edge[0] < previous + 4 or edge[1] == 0:
            raise ValueError("local long-branch edges require ordered exact integer boundaries")
        previous = edge[0]
    return value


def target(instruction, start, end):
    """Recognize only an unconditional, complete, non-entry local Thumb BL."""
    operands = instruction.operands
    if instruction.mnemonic != "bl" or instruction.size != 4 or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            len(operands) != 1 or operands[0].type != ARM_OP_IMM:
        raise ValueError("local long branch requires an ordinary unconditional Thumb BL")
    raw = bytes(instruction.bytes)
    first, second = int.from_bytes(raw[:2], "little"), int.from_bytes(raw[2:], "little")
    destination = operands[0].imm
    displacement = ((first & 0x7ff) << 12) | ((second & 0x7ff) << 1)
    if displacement & 0x400000:
        displacement -= 0x800000
    if first & 0xf800 != 0xf000 or second & 0xf800 != 0xf800 or \
            instruction.address + 4 + displacement != destination or \
            destination % 2 or not start < destination < end:
        raise ValueError("local long branch must target a non-entry boundary in its sole owner")
    return destination


def record(instructions, address):
    instructions = tuple(instructions)
    end = max(item.address + item.size for item in instructions)
    branches = []
    for instruction in sorted(instructions, key=lambda item: item.address):
        if instruction.mnemonic == "bl" and len(instruction.operands) == 1 and \
                instruction.operands[0].type == ARM_OP_IMM and \
                address <= instruction.operands[0].imm < end:
            branches.append([instruction.address - address,
                             target(instruction, address, end) - address])
    return {"schema": SCHEMA, "edges": branches} if branches else None


def prove_frame(instructions, edges, address, branches, calls):
    """Prove saved registers, fixed SP, and entry-LR return on every CFG path.

    Caller-clobbered registers lose provenance only on actual external calls.
    Local BL loses LR provenance only. Incoming stack reads, stack aliases,
    writes over saved slots, and returns to a local BL continuation fail.
    Ordinary calls retain the toolkit's existing external ABI-summary boundary.
    """
    from match import thumb_stack_adjustment
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError("local long branch requires its complete enclosing CFG")
    end = max(item.address + item.size for item in instructions.values())
    reached = {site: target(item, address, end) for site, item in instructions.items()
               if item.mnemonic == "bl" and len(item.operands) == 1 and
               item.operands[0].type == ARM_OP_IMM and
               address <= item.operands[0].imm < end}
    if branches != reached or set(branches) & set(calls) or \
            any(destination not in instructions or edges[site] != (destination,)
                for site, destination in branches.items()):
        raise ValueError("local long branches require exact reachable in-owner edges without fallthrough")
    preserved = tuple(range(ARM_REG_R4, ARM_REG_R11 + 1))
    initial = {register: ("entry", register) for register in preserved}
    initial[ARM_REG_LR] = ("entry-return",)
    states = {address: (tuple(sorted(initial.items())), ())}
    pending, returns, maximum = [address], set(), 0
    clobbered = (*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12, ARM_REG_LR)
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        registers, stack = dict(states[site][0]), list(states[site][1])
        operands = instruction.operands
        regs = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        adjustment = thumb_stack_adjustment(instruction)
        name = instruction.mnemonic
        if name == "push":
            if ARM_REG_PC in regs or ARM_REG_SP in regs:
                raise ValueError("local branch frame cannot save PC or SP")
            stack[:0] = [("saved", registers.get(register)) for register in regs]
        elif name == "pop":
            if len(regs) > len(stack) or any(kind != "saved" for kind, _ in stack[:len(regs)]):
                raise ValueError("local branch pop leaves the established saved frame")
            for register, (_, value) in zip(regs, stack):
                registers.pop(register, None)
                if value is not None:
                    registers[register] = value
            del stack[:len(regs)]
        elif adjustment is not None:
            if adjustment < 0:
                stack[:0] = [("local", None)] * -adjustment
            elif adjustment > len(stack) or any(kind != "local" for kind, _ in stack[:adjustment]):
                raise ValueError("local branch SP release leaves the allocated local frame")
            else:
                del stack[:adjustment]
        elif site in branches:
            # The saved entry LR remains in its frame; the machine LR now
            # contains this local edge's continuation, never an ABI return.
            registers.pop(ARM_REG_LR, None)
        elif site in calls:
            for register in clobbered:
                registers.pop(register, None)
        else:
            _, written = instruction.regs_access()
            assigned = None
            if name in ("mov", "movs") and len(operands) == 2 and \
                    operands[0].type == operands[1].type == ARM_OP_REG:
                assigned = (operands[0].reg, registers.get(operands[1].reg))
            for operand in operands:
                if operand.type != ARM_OP_MEM:
                    continue
                if operand.mem.index == ARM_REG_SP:
                    raise ValueError("local branch frame excludes indexed stack aliases")
                if operand.mem.base != ARM_REG_SP:
                    continue
                if name not in ("ldr", "str") or instruction.size != 2 or \
                        len(operands) != 2 or len(regs) != 1 or operand.mem.index or \
                        operand.mem.disp < 0 or operand.mem.disp % 4:
                    raise ValueError("local branch frame requires direct aligned stack words")
                slot = operand.mem.disp // 4
                if slot >= len(stack):
                    raise ValueError("local branch access leaves its established frame")
                if name == "str":
                    if stack[slot][0] != "local":
                        raise ValueError("local branch write overwrites a saved register")
                    stack[slot] = ("local", registers.get(regs[0]))
                else:
                    assigned = (regs[0], stack[slot][1])
            if ARM_REG_SP in regs or ARM_REG_SP in written:
                raise ValueError("local branch frame excludes stack-address materialization")
            for register in written:
                registers.pop(register, None)
            if assigned is not None and assigned[1] is not None:
                registers[assigned[0]] = assigned[1]
        maximum = max(maximum, 4 * len(stack))
        if not edges[site]:
            return_register = (regs[0] if name == "bx" and len(regs) == 1 else
                               ARM_REG_PC if name == "pop" and ARM_REG_PC in regs else
                               ARM_REG_PC if name == "mov" and regs == (ARM_REG_PC, ARM_REG_LR) else None)
            if return_register is None or registers.get(return_register) != ("entry-return",) or \
                    stack or any(registers.get(register) != initial[register] for register in preserved):
                raise ValueError("local branch exit must restore SP, r4-r11 and the original entry LR")
            returns.add(site)
        outgoing = (tuple(sorted(registers.items())), tuple(stack))
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("local branch frame escaped its complete CFG")
            previous = states.get(successor)
            merged = outgoing
            if previous is not None:
                if len(previous[1]) != len(stack) or any(a[0] != b[0] for a, b in zip(previous[1], stack)):
                    raise ValueError("local branch has inconsistent frame shapes at a CFG join")
                merged = (tuple((register, value) for register, value in previous[0]
                                if registers.get(register) == value),
                          tuple((kind, old if old == new else None)
                                for (kind, old), (_, new) in zip(previous[1], stack)))
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions) or not returns:
        raise ValueError("local branch frame proof does not cover the complete reachable owner")
    return {"schema": SCHEMA, "instructions": len(instructions), "maximum_frame_bytes": maximum,
            "returns": sorted(returns), "preserved": "r4-r11,sp,entry-lr",
            "external_calls": "existing-direct-call-ABI-summary"}
