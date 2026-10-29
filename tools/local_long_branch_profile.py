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
ALIAS_SCHEMA = "thumb-same-owner-long-bl-local-alias-frame-v1"


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


def prove_frame(instructions, edges, address, branches, calls, *,
                stack_aliases=False, buffer_proof=None, runtime_calls=None,
                call_preservation=None, bounded_output_proof=None, zero_index_profile=None):
    """Prove saved registers, fixed SP, and entry-LR return on every CFG path.

    Caller-clobbered registers lose provenance only on actual external calls.
    Local BL loses LR provenance only. Incoming stack reads, writes over saved
    slots, and returns to a local BL continuation fail. Stack aliases require
    explicit opt-in; passing them requires the existing native buffer proof.
    Ordinary calls retain the toolkit's existing external ABI-summary boundary.
    """
    from match import thumb_stack_adjustment, stack_alias_assignment, BufferCallProof
    if type(stack_aliases) is not bool or buffer_proof is not None and (
            not stack_aliases or type(buffer_proof) is not BufferCallProof or
            buffer_proof.stack_arguments):
        raise ValueError("local aliases require explicit Boolean policy and native buffer proof")
    if bounded_output_proof is not None:
        from bounded_stack_output_profile import BoundedOutputProof
        if type(bounded_output_proof) is not BoundedOutputProof or not stack_aliases or buffer_proof is not None:
            raise ValueError("bounded output requires its explicit native alias proof")
    if runtime_calls is not None:
        from function_thunk_profile import ALIASES
        from match import UDIVSI3_ADDRESS, RUNTIME_HELPERS, is_udivsi3_address
        allowed = dict(ALIASES, __udivsi3=UDIVSI3_ADDRESS)
        if type(runtime_calls) is not dict or not runtime_calls or any(
                type(site) is not int or type(name) is not str or name not in allowed or
                calls.get(site) != allowed[name]
                for site, name in runtime_calls.items()) or set(runtime_calls) != {
                    site for site, destination in calls.items()
                    if destination in RUNTIME_HELPERS.values() or is_udivsi3_address(destination)}:
            raise ValueError("runtime frame checks require exact complete canonical call bindings")

    zero_states = None
    zero_accesses = set()
    if zero_index_profile is not None:
        import zero_index_stack_profile as zero_index
        if type(zero_index_profile) is not str or zero_index_profile != zero_index.SELECTOR or not stack_aliases:
            raise ValueError("zero index local loads require their explicit native alias policy")
        zero_states = zero_index.prove_zeros(instructions,edges,address)

    def access(offset, width, stack):
        position = offset + 4 * len(stack)
        if offset % width or position < 0 or offset + width > 0 or \
                any(stack[slot][0] != "local"
                    for slot in range(position // 4, (position + width - 1) // 4 + 1)):
            raise ValueError("local alias access leaves aligned allocated local words")
        return position // 4

    def alias_offset(register, aliases):
        values = aliases[register]
        if len(values) != 1 or not next(iter(values))[1]:
            raise ValueError("local alias use has ambiguous or expired lifetime")
        return next(iter(values))[0]
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
    if call_preservation is not None and (type(call_preservation) is not dict or
            set(call_preservation) != set(calls) or any(
                type(registers) is not frozenset or registers - set(preserved)
                for registers in call_preservation.values())):
        raise ValueError("strict frame calls require complete explicit preserved-register sets")
    initial = {register: ("entry", register) for register in preserved}
    initial[ARM_REG_LR] = ("entry-return",)
    states = {address: (tuple(sorted(initial.items())), (), ())}
    pending, returns, maximum = [address], set(), 0
    alias_sites, alias_accesses, alias_calls = set(), set(), set()
    clobbered = (*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12, ARM_REG_LR)
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        registers, stack = dict(states[site][0]), list(states[site][1])
        aliases = {register: frozenset(values) for register, values in states[site][2]}
        operands = instruction.operands
        regs = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        adjustment = thumb_stack_adjustment(instruction)
        name = instruction.mnemonic
        if name == "push":
            if ARM_REG_PC in regs or ARM_REG_SP in regs:
                raise ValueError("local branch frame cannot save PC or SP")
            if set(regs) & aliases.keys():
                raise ValueError("local aliases cannot be pushed or spilled")
            stack[:0] = [("saved", registers.get(register)) for register in regs]
        elif name == "pop":
            if len(regs) > len(stack) or any(kind != "saved" for kind, _ in stack[:len(regs)]):
                raise ValueError("local branch pop leaves the established saved frame")
            for register, (_, value) in zip(regs, stack):
                aliases.pop(register, None)
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
                # Keep dangling values tainted until overwritten. Reallocating
                # the same offset must not revive a released pointer lifetime.
                aliases = {register: frozenset((offset, live and offset >= -4 * len(stack))
                                               for offset, live in values)
                           for register, values in aliases.items()}
        elif site in branches:
            # The saved entry LR remains in its frame; the machine LR now
            # contains this local edge's continuation, never an ABI return.
            registers.pop(ARM_REG_LR, None)
            aliases.pop(ARM_REG_LR, None)
        elif site in calls:
            if runtime_calls is not None and site in runtime_calls:
                if set(clobbered) & aliases.keys():
                    raise ValueError("canonical runtime arguments carry local stack provenance")
                runtime_name = runtime_calls[site]
                if runtime_name != "__udivsi3":
                    target_register = ARM_REG_R0 + int(runtime_name.removeprefix("_call_via_r"))
                    if target_register in aliases or registers.get(target_register) == ("entry-return",):
                        raise ValueError("indirect runtime target carries stack or entry-return provenance")
            if set(clobbered) & aliases.keys():
                if buffer_proof is None and bounded_output_proof is None:
                    raise ValueError("local aliases crossing calls require native buffer proof")
                offsets = {register: alias_offset(register, aliases)
                           for register in clobbered if register in aliases}
                native_stack = [(False, kind == "saved", kind == "local")
                                for kind, _ in stack]
                if (bounded_output_proof.check_call(calls[site],offsets,native_stack,site=site)
                        if bounded_output_proof is not None else
                        buffer_proof.check_call(calls[site], offsets, native_stack)):
                    raise ValueError("local alias return requires a separate provenance policy")
                # A proved callee may write through any passed local buffer.
                # Do not retain a saved-register token in potentially changed bytes.
                stack = [(kind, None if kind == "local" else value) for kind, value in stack]
                alias_calls.add(site)
            destroyed = set(clobbered)
            if call_preservation is not None:
                destroyed.update(set(preserved) - call_preservation[site])
            for register in destroyed:
                registers.pop(register, None)
                aliases.pop(register, None)
        else:
            read, written = instruction.regs_access()
            assignment = None
            if stack_aliases:
                exact = {register: alias_offset(register, aliases)
                         for register in aliases if register in read}
                assignment = stack_alias_assignment(instruction, exact, len(stack), {})
                if assignment is not None:
                    if assignment[0] in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR):
                        raise ValueError("local alias cannot overwrite a control register")
                    access(assignment[1], 1, stack)
                    alias_sites.add(site)
            allowed_aliases = {assignment[2]} if assignment is not None else set()
            assigned = None
            if name in ("mov", "movs") and len(operands) == 2 and \
                    operands[0].type == operands[1].type == ARM_OP_REG:
                assigned = (operands[0].reg, registers.get(operands[1].reg))
            for operand in operands:
                if operand.type != ARM_OP_MEM:
                    continue
                if operand.mem.index == ARM_REG_SP:
                    raise ValueError("local branch frame excludes indexed stack aliases")
                if operand.mem.base in aliases:
                    width = {"ldr": 4, "str": 4, "ldrh": 2, "strh": 2,
                             "ldrb": 1, "strb": 1, "ldrsh": 2, "ldrsb": 1}.get(name)
                    certified_zero = False
                    if zero_states is not None and operand.mem.index:
                        decoded = zero_index.signed_load(instruction)
                        certified_zero = decoded is not None and decoded[1] in zero_states[site] and decoded[1] not in aliases
                        if certified_zero:
                            zero_accesses.add((site,decoded[0],decoded[1],decoded[2],tuple(sorted(zero_states[site][decoded[1]]))))
                    if width is None or instruction.size != 2 or \
                            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                            len(operands) != 2 or len(regs) != 1 or \
                            operands[0].type != ARM_OP_REG or operand.mem.index and not certified_zero or \
                            instruction.writeback or operand.shift.type or operand.shift.value or \
                            operand.subtracted or operand.mem.disp < 0:
                        raise ValueError("local alias requires an ordinary constant-offset memory access")
                    slot = access(alias_offset(operand.mem.base, aliases) + operand.mem.disp,
                                  width, stack)
                    if name.startswith("str"):
                        if regs[0] in aliases:
                            raise ValueError("local aliases cannot be stored or spilled")
                        stack[slot] = ("local", registers.get(regs[0]) if width == 4 else None)
                    elif width == 4:
                        assigned = (regs[0], stack[slot][1])
                    allowed_aliases.add(operand.mem.base)
                    alias_accesses.add(site)
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
                    if regs[0] in aliases:
                        raise ValueError("local aliases cannot be stored or spilled")
                    if stack[slot][0] != "local":
                        raise ValueError("local branch write overwrites a saved register")
                    stack[slot] = ("local", registers.get(regs[0]))
                else:
                    assigned = (regs[0], stack[slot][1])
            if (ARM_REG_SP in regs and assignment is None) or ARM_REG_SP in written:
                raise ValueError("local branch frame excludes stack-address materialization")
            if (set(read) & aliases.keys()) - allowed_aliases:
                raise ValueError("unsupported local alias use or escape")
            for register in written:
                registers.pop(register, None)
                aliases.pop(register, None)
            if assigned is not None and assigned[1] is not None:
                registers[assigned[0]] = assigned[1]
            if assignment is not None:
                aliases[assignment[0]] = frozenset(((assignment[1], True),))
        maximum = max(maximum, 4 * len(stack))
        if not edges[site]:
            return_register = (regs[0] if name == "bx" and len(regs) == 1 else
                               ARM_REG_PC if name == "pop" and ARM_REG_PC in regs else
                               ARM_REG_PC if name == "mov" and regs == (ARM_REG_PC, ARM_REG_LR) else None)
            if return_register is None or registers.get(return_register) != ("entry-return",) or \
                    stack or any(registers.get(register) != initial[register] for register in preserved):
                raise ValueError("local branch exit must restore SP, r4-r11 and the original entry LR")
            if aliases:
                raise ValueError("local alias escapes through an exit register")
            returns.add(site)
        outgoing = (tuple(sorted(registers.items())), tuple(stack),
                    tuple(sorted((register, tuple(sorted(values))) for register, values in aliases.items())))
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("local branch frame escaped its complete CFG")
            previous = states.get(successor)
            merged = outgoing
            if previous is not None:
                if len(previous[1]) != len(stack) or any(a[0] != b[0] for a, b in zip(previous[1], stack)):
                    raise ValueError("local branch has inconsistent frame shapes at a CFG join")
                old_aliases = {register: frozenset(values) for register, values in previous[2]}
                unknown = frozenset(((0, False),))
                joined_aliases = tuple(sorted((register, tuple(sorted(
                    old_aliases.get(register, unknown) | aliases.get(register, unknown))))
                    for register in old_aliases.keys() | aliases.keys()))
                merged = (tuple((register, value) for register, value in previous[0]
                                if registers.get(register) == value),
                          tuple((kind, old if old == new else None)
                                for (kind, old), (_, new) in zip(previous[1], stack)), joined_aliases)
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions) or not returns:
        raise ValueError("local branch frame proof does not cover the complete reachable owner")
    proof = {"schema": SCHEMA, "instructions": len(instructions), "maximum_frame_bytes": maximum,
            "returns": sorted(returns), "preserved": "r4-r11,sp,entry-lr",
            "external_calls": "existing-direct-call-ABI-summary"}
    if call_preservation is not None:
        proof["external_calls"] = "complete-native-callee-preservation-v1"
        proof["call_preservation"] = [[site, sorted(registers)]
                                      for site, registers in sorted(call_preservation.items())]
    if stack_aliases:
        proof["local_aliases"] = {"schema": ALIAS_SCHEMA, "assignments": sorted(alias_sites),
                                  "accesses": sorted(alias_accesses), "buffer_calls": sorted(alias_calls),
                                  "buffer_fingerprint": (bounded_output_proof or buffer_proof).fingerprint()
                                    if bounded_output_proof or buffer_proof else None}
    if zero_states is not None:
        proof["zero_index_profile"] = zero_index_profile
        proof["zero_index_signed_loads"] = [[site,base,index,width,list(origins)]
            for site,base,index,width,origins in sorted(zero_accesses)]
    return proof
