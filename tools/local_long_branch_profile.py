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
                call_preservation=None, bounded_output_proof=None, zero_index_profile=None,
                entry_stack_policy=None, local_alias_slot_policy=None, finite_stack_index_policy=None):
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

    incoming_reads = set()
    if entry_stack_policy is not None:
        import readonly_entry_stack_profile as entry_stack
        entry_stack.validate(entry_stack_policy)

    zero_states = None
    zero_accesses = set()
    if zero_index_profile is not None:
        import zero_index_stack_profile as zero_index
        if type(zero_index_profile) is not str or zero_index_profile != zero_index.SELECTOR or not stack_aliases:
            raise ValueError("zero index local loads require their explicit native alias policy")
        zero_states = zero_index.prove_zeros(instructions,edges,address)

    slot_states = None
    slot_stores, slot_loads, small_indices, small_additions = set(), set(), set(), set()
    if local_alias_slot_policy is not None:
        import local_alias_slot_profile as alias_slots
        alias_slots.validate(local_alias_slot_policy)
        if not stack_aliases or buffer_proof is not None or bounded_output_proof is not None or entry_stack_policy is not None:
            raise ValueError("local alias slots require exclusive local-only stack alias policy")
        slot_states = alias_slots.prove_constants(instructions, edges, address)

    finite_states = None
    finite_additions, finite_reads = set(), set()
    if finite_stack_index_policy is not None:
        import finite_stack_index_profile as finite
        finite.validate(finite_stack_index_policy)
        if not stack_aliases or any(value is not None for value in (buffer_proof,
                bounded_output_proof, runtime_calls, call_preservation, zero_index_profile,
                entry_stack_policy, local_alias_slot_policy)):
            raise ValueError("finite indices require exclusive local-only conditional ordinary ABI policy")
        finite_states = finite.prove_constants(instructions, edges, address)

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
    states = {address: (tuple(sorted(initial.items())), (), (), ())}
    if finite_states is not None:
        states[address] += (frozenset(),)
    pending, returns, maximum = [address], set(), 0
    finite_updates = 0
    alias_sites, alias_accesses, alias_calls = set(), set(), set()
    clobbered = (*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12, ARM_REG_LR)
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        registers, stack = dict(states[site][0]), list(states[site][1])
        aliases = {register: frozenset(values) for register, values in states[site][2]}
        pointer_slots = {word: frozenset(values) for word, values in states[site][3]}
        initialized = set(states[site][4]) if finite_states is not None else set()
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
                if slot_states is not None:
                    pointer_slots = alias_slots.release(pointer_slots, len(stack))
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
            loaded_alias = None
            if stack_aliases:
                if finite_states is not None:
                    assignment = finite.assignment(instruction, aliases, len(stack), finite_states[site])
                else:
                    exact = {register: alias_offset(register, aliases)
                             for register in aliases if register in read}
                    constants = {} if slot_states is None else {register:value[0] for register,value in slot_states[site].items()}
                    assignment = stack_alias_assignment(instruction, exact, len(stack), constants)
                if assignment is not None:
                    if assignment[0] in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR):
                        raise ValueError("local alias cannot overwrite a control register")
                    if finite_states is None:
                        access(assignment[1], 1, stack)
                    else:
                        for offset in finite.offsets(assignment[1]): access(offset, 1, stack)
                        if instruction.mnemonic == "add" and assignment[2] == ARM_REG_SP and assignment[0] in finite_states[site]:
                            finite_additions.add((site, assignment[0], tuple(sorted(
                                (value, tuple(sorted(origins))) for value,origins in finite_states[site][assignment[0]].items()))))
                    alias_sites.add(site)
                    if slot_states is not None and instruction.mnemonic == "add" and any(op.type == ARM_OP_REG and op.reg == ARM_REG_SP for op in instruction.operands):
                        for register, (value, origins) in slot_states[site].items():
                            if register == assignment[0]:
                                small_additions.add((site, register, value, tuple(sorted(origins))))
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
                    index_displacement = 0
                    if slot_states is not None and operand.mem.index:
                        decoded = alias_slots.indexed_byte(instruction, slot_states[site], aliases)
                        if decoded is not None:
                            certified_zero = True
                            index_displacement = decoded[2]
                            small_indices.add((site, *decoded))
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
                    if finite_states is not None:
                        if name != "ldr" or width != 4 or operand.mem.index:
                            raise ValueError("finite local aliases permit only aligned read-only local words")
                        offsets = tuple(offset + operand.mem.disp for offset in finite.offsets(aliases[operand.mem.base]))
                        slots = [access(offset, width, stack) for offset in offsets]
                        if any(offset not in initialized for offset in offsets):
                            raise ValueError("finite local read requires every alternative initialized on every path")
                        tokens = [stack[position][1] for position in slots]
                        assigned = (regs[0], tokens[0] if all(value == tokens[0] for value in tokens) else None)
                        finite_reads.add((site, operand.mem.base, offsets, width))
                        allowed_aliases.add(operand.mem.base)
                        alias_accesses.add(site)
                        continue
                    offset = alias_offset(operand.mem.base, aliases) + operand.mem.disp + index_displacement
                    slot = access(offset, width, stack)
                    if name.startswith("str"):
                        if regs[0] in aliases:
                            if slot_states is None:
                                raise ValueError("local aliases cannot be stored or spilled")
                            alias_slots.word(instruction)
                            access(alias_offset(regs[0], aliases), 1, stack)
                            allowed_aliases.add(regs[0])
                            slot_stores.add((site, offset, alias_offset(regs[0], aliases)))
                        if slot_states is not None:
                            alias_slots.store(pointer_slots, offset, width, aliases.get(regs[0]))
                        stack[slot] = ("local", registers.get(regs[0]) if width == 4 else None)
                    elif offset - offset % 4 in pointer_slots:
                        if width != 4:
                            raise ValueError("partial load from a local alias slot")
                        alias_slots.word(instruction)
                        loaded_alias = (regs[0], pointer_slots[offset])
                        slot_loads.add((site, offset))
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
                    if entry_stack_policy is None:
                        raise ValueError("local branch access leaves its established frame")
                    offset = entry_stack.read_word(instruction, len(stack), entry_stack_policy)
                    incoming_reads.add((site, offset, bytes(instruction.bytes).hex()))
                    assigned = (regs[0], None)
                elif name == "str":
                    if regs[0] in aliases and slot_states is None:
                        raise ValueError("local aliases cannot be stored or spilled")
                    if stack[slot][0] != "local":
                        raise ValueError("local branch write overwrites a saved register")
                    if slot_states is not None:
                        offset = operand.mem.disp - 4 * len(stack)
                        if regs[0] in aliases:
                            alias_slots.word(instruction)
                            access(alias_offset(regs[0], aliases), 1, stack)
                            allowed_aliases.add(regs[0])
                            slot_stores.add((site, offset, alias_offset(regs[0], aliases)))
                        alias_slots.store(pointer_slots, offset, 4, aliases.get(regs[0]))
                    stack[slot] = ("local", registers.get(regs[0]))
                    if finite_states is not None:
                        initialized.add(operand.mem.disp - 4 * len(stack))
                else:
                    offset = operand.mem.disp - 4 * len(stack)
                    if finite_states is not None and stack[slot][0] == "local" and offset not in initialized:
                        raise ValueError("finite local word is not initialized on every path")
                    if offset in pointer_slots:
                        alias_slots.word(instruction)
                        loaded_alias = (regs[0], pointer_slots[offset])
                        slot_loads.add((site, offset))
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
            if loaded_alias is not None:
                aliases[loaded_alias[0]] = loaded_alias[1]
            if assignment is not None:
                aliases[assignment[0]] = (assignment[1] if finite_states is not None
                    else frozenset(((assignment[1], True),)))
        if finite_states is not None:
            initialized = {offset for offset in initialized if offset >= -4 * len(stack)}
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
                    tuple(sorted((register, tuple(sorted(values))) for register, values in aliases.items())),
                    tuple(sorted((word, tuple(sorted(values))) for word, values in pointer_slots.items())))
        if finite_states is not None:
            outgoing += (frozenset(initialized),)
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
                                for (kind, old), (_, new) in zip(previous[1], stack)), joined_aliases,
                          alias_slots.join({word:frozenset(values) for word,values in previous[3]},pointer_slots)
                            if slot_states is not None else ())
                if finite_states is not None:
                    if any(len(values) > finite.MAX_VALUES for _,values in joined_aliases):
                        raise ValueError("finite local alias alternative budget exceeded")
                    merged += (previous[4] & frozenset(initialized),)
            if previous != merged:
                if finite_states is not None:
                    finite_updates += 1
                    if finite_updates > finite.MAX_UPDATES:
                        raise ValueError("finite local frame proof-state budget exceeded")
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
    if entry_stack_policy is not None:
        proof["entry_stack"] = {"schema": entry_stack.SCHEMA, "words": [0],
            "contract": entry_stack.CONTRACT, "loaded_value": "unknown scalar; no provenance facts",
            "reads": [[site, offset, 4, encoded] for site, offset, encoded in sorted(incoming_reads)]}
    if stack_aliases:
        proof["local_aliases"] = {"schema": ALIAS_SCHEMA, "assignments": sorted(alias_sites),
                                  "accesses": sorted(alias_accesses), "buffer_calls": sorted(alias_calls),
                                  "buffer_fingerprint": (bounded_output_proof or buffer_proof).fingerprint()
                                    if bounded_output_proof or buffer_proof else None}
    if zero_states is not None:
        proof["zero_index_profile"] = zero_index_profile
        proof["zero_index_signed_loads"] = [[site,base,index,width,list(origins)]
            for site,base,index,width,origins in sorted(zero_accesses)]
    if slot_states is not None:
        proof["local_alias_slots"] = {"schema": alias_slots.SCHEMA, "policy": local_alias_slot_policy,
            "stores": [list(row) for row in sorted(slot_stores)],
            "loads": [list(row) for row in sorted(slot_loads)],
            "small_SP_additions": [[site, register, value, list(origins)] for site,register,value,origins in sorted(small_additions)],
            "small_index_byte_loads": [[site, base, index, value, list(origins)] for site,base,index,value,origins in sorted(small_indices)],
            "constant_domain": "exact MOVS 1/2/3 only; all-path intersection; every call kills facts",
            "slot_domain": "own aligned local words; possible-pointer taint joins; partial overwrite invalidates; release expires provenance",
            "callee_pointer_arguments": False}
    if finite_states is not None:
        proof["finite_stack_indices"] = {"schema": finite.SCHEMA, "policy": finite_stack_index_policy,
            "SP_additions": [[site,register,[[value,list(origins)] for value,origins in alternatives]]
                for site,register,alternatives in sorted(finite_additions)],
            "reads": [[site,base,list(offsets),width] for site,base,offsets,width in sorted(finite_reads)],
            "constant_domain": "MOVS0/1, exact LSL2, all-path union of at most2 known values in0/1/4; missing arms unknown; caller-saved calls kill facts",
            "alias_domain": "at most2 live allocated offsets; read-only initialized aligned words on every alternative; no spills, buffer or entry-word premise"}
    return proof
