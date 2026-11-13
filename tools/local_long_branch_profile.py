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


DISCARDED_SCRATCH_SCHEMA = 'thumb-discarded-exit-scratch-v1'
DISCARDED_SCRATCH_CONTRACT = 'r2/r3 are discarded scratch at external returns; no result values are returned through them'


def validate_discarded_exit_scratch(policy):
    if type(policy) is not dict or set(policy) != {'schema', 'registers'} or \
            type(policy['schema']) is not str or policy['schema'] != DISCARDED_SCRATCH_SCHEMA or \
            type(policy['registers']) is not list or policy['registers'] != [2, 3] or \
            any(type(register) is not int for register in policy['registers']):
        raise ValueError('discarded exit scratch requires its exact versioned r2/r3 policy')
    return policy


def prove_frame(instructions, edges, address, branches, calls, *,
                stack_aliases=False, buffer_proof=None, runtime_calls=None,
                call_preservation=None, bounded_output_proof=None, zero_index_profile=None,
                entry_stack_policy=None, local_alias_slot_policy=None, finite_stack_index_policy=None,
                entry_stack_alias_slot_policy=None,
                discarded_exit_scratch=None, formal_stack_callee_proof=None,
                formal_stack_alias_constant_policy=None, formal_stack_entry_word_policy=None,
                formal_stack_entry_words_policy=None, mutable_stack_index_policy=None,
                consumer_scratch_proof=None, entry_recursive_calls=None, native_three_call_policy=None,
                returned_local_alias_policy=None):
    """Prove saved registers, fixed SP, and entry-LR return on every CFG path.

    Caller-clobbered registers lose provenance only on actual external calls.
    Local BL loses LR provenance only. Incoming stack reads, writes over saved
    slots, and returns to a local BL continuation fail. Stack aliases require
    explicit opt-in; passing them requires the existing native buffer proof.
    Ordinary calls retain the toolkit's existing external ABI-summary boundary.
    """
    from match import thumb_stack_adjustment, stack_alias_assignment, BufferCallProof
    from named_data_buffer_profile import RootGuardedSwitchBufferProof
    from bios_word_switch_buffer_profile import BiosWordSwitchBufferProof, RETURN_POLICY
    returned_local_aliases = type(buffer_proof) is BiosWordSwitchBufferProof
    if returned_local_alias_policy is not None or returned_local_aliases:
        if returned_local_alias_policy != RETURN_POLICY or not returned_local_aliases or not stack_aliases or any(
                value is not None for value in (runtime_calls, call_preservation, bounded_output_proof,
                    zero_index_profile, entry_stack_policy, local_alias_slot_policy, finite_stack_index_policy,
                    entry_stack_alias_slot_policy, discarded_exit_scratch, formal_stack_callee_proof,
                    formal_stack_alias_constant_policy, formal_stack_entry_word_policy,
                    formal_stack_entry_words_policy, mutable_stack_index_policy, consumer_scratch_proof,
                    entry_recursive_calls, native_three_call_policy)):
            raise ValueError('returned local aliases require their exclusive explicit native composition')
        buffer_proof.validate_frame(instructions,edges,address,branches,calls)
    root_switch_buffer = type(buffer_proof) is RootGuardedSwitchBufferProof or returned_local_aliases
    from static_callback_r6_frame_profile import RestoringLocalBufferProof
    restoring_local_buffer = type(buffer_proof) is RestoringLocalBufferProof
    from two_word_callback_closure_profile import _ContextRead
    callback_context_buffer = type(buffer_proof) is _ContextRead
    if type(stack_aliases) is not bool or buffer_proof is not None and (
            not stack_aliases or not root_switch_buffer and not restoring_local_buffer and not callback_context_buffer and (
                type(buffer_proof) is not BufferCallProof or buffer_proof.stack_arguments)):
        raise ValueError("local aliases require explicit Boolean policy and native buffer proof")
    if bounded_output_proof is not None:
        from bounded_stack_output_profile import BoundedOutputProof
        if type(bounded_output_proof) is not BoundedOutputProof or not stack_aliases or buffer_proof is not None:
            raise ValueError("bounded output requires its explicit native alias proof")
    entry_alias_words = entry_stack_alias_slot_policy is not None
    if entry_alias_words:
        import local_alias_slot_profile as alias_slots
        import readonly_entry_stack_words_profile as entry_words
        if type(entry_stack_alias_slot_policy) is not str or \
                entry_stack_alias_slot_policy != alias_slots.ENTRY_WORDS_POLICY or not stack_aliases or \
                local_alias_slot_policy != alias_slots.SELECTOR or any(value is not None for value in (
                    buffer_proof, bounded_output_proof, runtime_calls, call_preservation,
                    zero_index_profile, finite_stack_index_policy, discarded_exit_scratch,
                    formal_stack_callee_proof, formal_stack_alias_constant_policy,
                    formal_stack_entry_word_policy, formal_stack_entry_words_policy,
                    mutable_stack_index_policy, consumer_scratch_proof, entry_recursive_calls,
                    native_three_call_policy)):
            raise ValueError('entry words and local alias slots require their exclusive explicit composition')
        alias_slots.validate(local_alias_slot_policy)
        entry_words.validate(entry_stack_policy)
    named_entry_word = formal_stack_entry_word_policy is not None
    if named_entry_word:
        from ordinary_named_output_entry_word_inventory import SELECTOR as NAMED_ENTRY_WORD
        from ordinary_two_output_callees_inventory import NamedReadonlyFormalLeafProof
        import readonly_entry_stack_profile as named_entry
        if type(formal_stack_entry_word_policy) is not str or formal_stack_entry_word_policy != NAMED_ENTRY_WORD or \
                type(formal_stack_callee_proof) is not NamedReadonlyFormalLeafProof:
            raise ValueError('named entry word requires its exact explicit composition and fresh named helper')
        named_entry.validate(entry_stack_policy)
    named_pair_entry_words = formal_stack_entry_words_policy is not None
    if named_pair_entry_words:
        from ordinary_named_pair_entry_words_inventory import NamedPairEntryWordsProof, SELECTOR as NAMED_PAIR_ENTRY_WORDS
        import readonly_entry_stack_words_profile as pair_entry
        if type(formal_stack_entry_words_policy) is not str or formal_stack_entry_words_policy != NAMED_PAIR_ENTRY_WORDS or \
                type(formal_stack_callee_proof) is not NamedPairEntryWordsProof or named_entry_word or \
                formal_stack_alias_constant_policy is not None:
            raise ValueError('named pair entry words require their exact exclusive composition and fresh pair')
        pair_entry.validate(entry_stack_policy)
        if entry_stack_policy['words'] != [0, 1, 2, 3]:
            raise ValueError('named pair requires exactly four explicit incoming words')
    if formal_stack_callee_proof is not None:
        from ordinary_formal_stack_callee_inventory import FormalStackCalleeProof
        from ordinary_two_output_callees_inventory import TwoOutputCalleesProof, NamedReadonlyFormalLeafProof
        from ordinary_second_formal_output_callees_inventory import SecondFormalOutputCalleesProof
        from ordinary_third_formal_output_callees_inventory import ThirdFormalOutputCalleesProof
        from ordinary_named_pair_entry_words_inventory import NamedPairEntryWordsProof
        allowed_formal = (FormalStackCalleeProof, TwoOutputCalleesProof, NamedReadonlyFormalLeafProof,
                          SecondFormalOutputCalleesProof, ThirdFormalOutputCalleesProof)
        if named_pair_entry_words:
            allowed_formal += (NamedPairEntryWordsProof,)
        if type(formal_stack_callee_proof) not in allowed_formal or not stack_aliases or \
                local_alias_slot_policy is None or any(value is not None for value in (
                    buffer_proof, bounded_output_proof, runtime_calls, call_preservation,
                    entry_stack_policy if not (named_entry_word or named_pair_entry_words) else None,
                    finite_stack_index_policy, discarded_exit_scratch)):
            raise ValueError('formal stack callees require their exclusive fresh native proof and local slots')
        formal_stack_callee_proof.validate_calls(calls)
    discarded_aliases = set()
    if restoring_local_buffer or callback_context_buffer:
        buffer_proof.validate_frame(instructions, edges, address, branches, calls,
                                    call_preservation, discarded_exit_scratch)
    if discarded_exit_scratch is not None:
        validate_discarded_exit_scratch(discarded_exit_scratch)
        if not stack_aliases or any(value is not None for value in ((None if restoring_local_buffer else buffer_proof),
                bounded_output_proof, runtime_calls, (None if restoring_local_buffer else call_preservation), entry_stack_policy,
                local_alias_slot_policy, finite_stack_index_policy)):
            raise ValueError('discarded exit scratch requires exclusive local-only alias policy')
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

    if formal_stack_alias_constant_policy is not None:
        import local_alias_slot_profile as alias_slots
        if type(formal_stack_alias_constant_policy) is not str or \
                formal_stack_alias_constant_policy != alias_slots.FORMAL_MOVS10_POLICY or \
                formal_stack_callee_proof is None or local_alias_slot_policy != alias_slots.SELECTOR:
            raise ValueError('formal MOVS10 aliases require their explicit policy and fresh formal leaf proof')

    incoming_reads = set()
    incoming_words_policy = False
    if entry_stack_policy is not None:
        if type(entry_stack_policy) is dict and entry_stack_policy.get('schema') == 'thumb-readonly-entry-stack-words-v1':
            import readonly_entry_stack_words_profile as entry_stack
            incoming_words_policy = True
        else:
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
        if not stack_aliases or buffer_proof is not None or bounded_output_proof is not None or \
                entry_stack_policy is not None and not (named_entry_word or named_pair_entry_words or entry_alias_words):
            raise ValueError("local alias slots require exclusive local-only stack alias policy")
        slot_states = alias_slots.prove_constants(instructions, edges, address,
            constant_domain=None if formal_stack_alias_constant_policy is None else alias_slots.FORMAL_MOVS10_DOMAIN)

    mutable = mutable_stack_index_policy is not None
    mutable_slots = False
    mutable_halfword = False
    mutable_halfword_array = False
    mutable_scalar_slots = False
    scalar_stores, scalar_loads = set(), set()
    halfword_reads = set()
    halfword_array_reads, halfword_array_writes = set(), set()
    if mutable:
        import mutable_stack_index_profile as finite
        finite.validate(mutable_stack_index_policy)
        mutable_three_call = mutable_stack_index_policy == finite.THREE_CALL_SELECTOR
        mutable_overwrite = mutable_stack_index_policy == finite.LEAF_OVERWRITE_SELECTOR
        mutable_consumer = mutable_stack_index_policy in (finite.CONSUMER_SCRATCH_SELECTOR, finite.LEAF_OVERWRITE_SELECTOR, finite.THREE_CALL_SELECTOR)
        mutable_scalar_slots = mutable_stack_index_policy in (finite.SCALAR_SLOT_SELECTOR, finite.CONSUMER_SCRATCH_SELECTOR, finite.LEAF_OVERWRITE_SELECTOR, finite.THREE_CALL_SELECTOR)
        mutable_halfword_array = mutable_stack_index_policy in (finite.HALFWORD_ACCESS_SELECTOR, finite.SCALAR_SLOT_SELECTOR, finite.CONSUMER_SCRATCH_SELECTOR, finite.LEAF_OVERWRITE_SELECTOR, finite.THREE_CALL_SELECTOR)
        mutable_halfword = mutable_stack_index_policy in (finite.LOW_HALFWORD_SELECTOR, finite.HALFWORD_ACCESS_SELECTOR, finite.SCALAR_SLOT_SELECTOR, finite.CONSUMER_SCRATCH_SELECTOR, finite.LEAF_OVERWRITE_SELECTOR, finite.THREE_CALL_SELECTOR)
        mutable_slots = mutable_stack_index_policy in (finite.ALIAS_SLOT_SELECTOR, finite.LOW_HALFWORD_SELECTOR, finite.HALFWORD_ACCESS_SELECTOR, finite.SCALAR_SLOT_SELECTOR, finite.CONSUMER_SCRATCH_SELECTOR, finite.LEAF_OVERWRITE_SELECTOR, finite.THREE_CALL_SELECTOR)
        if mutable_slots:
            import local_alias_slot_profile as alias_slots
        if mutable_halfword:
            import zero_index_stack_profile as zero_index
        if not stack_aliases or any(value is not None for value in (buffer_proof,
                bounded_output_proof, runtime_calls, call_preservation, zero_index_profile,
                entry_stack_policy, local_alias_slot_policy, finite_stack_index_policy,
                discarded_exit_scratch, formal_stack_callee_proof, formal_stack_alias_constant_policy,
                formal_stack_entry_word_policy, formal_stack_entry_words_policy,
                entry_recursive_calls)):
            raise ValueError('mutable indices require exclusive local-only conditional ordinary ABI policy')

    if native_three_call_policy is not None:
        from mutable_three_call_native_profile import SELECTOR as NATIVE_THREE_CALL
        if type(native_three_call_policy) is not str or native_three_call_policy != NATIVE_THREE_CALL or not mutable or not mutable_three_call:
            raise ValueError('native three-call roles require their exclusive explicit frame selector')

    if consumer_scratch_proof is not None or mutable and mutable_consumer:
        from consumer_scratch_alias_profile import ConsumerScratchAliasProof
        expected = ConsumerScratchAliasProof
        if mutable and mutable_overwrite:
            from readonly_leaf_overwrite_profile import ReadonlyLeafOverwriteProof
            expected = ReadonlyLeafOverwriteProof
        if mutable and mutable_three_call:
            from three_call_composition_profile import ThreeCallCompositionProof
            expected = ThreeCallCompositionProof
            if native_three_call_policy is not None:
                from mutable_three_call_native_profile import NativeRoleProof
                expected = NativeRoleProof
        if not mutable or not mutable_consumer or type(consumer_scratch_proof) is not expected:
            raise ValueError('consumer scratch requires its exclusive explicit mutable inventory composition')
        consumer_scratch_proof.bind_frame(instructions, edges, address, branches, calls)

    finite_states = {} if mutable else None
    finite_additions, finite_reads, mutable_writes = set(), set(), set()
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

    def initialized_units(offset, width):
        # One initialized state, with byte coverage only in the explicit halfword policy.
        return range(offset, offset + width) if mutable_halfword_array else (offset,)

    def alias_offset(register, aliases):
        values = aliases[register]
        if len(values) != 1 or not next(iter(values))[1]:
            raise ValueError("local alias use has ambiguous or expired lifetime")
        return next(iter(values))[0]
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError("local long branch requires its complete enclosing CFG")
    entry_sites = set()
    if entry_recursive_calls is not None:
        from entry_recursive_ordinary_call_profile import EntryCalls
        if type(entry_recursive_calls) is not EntryCalls or stack_aliases or any(
                value is not None for value in (buffer_proof, runtime_calls,
                    call_preservation, bounded_output_proof, zero_index_profile,
                    entry_stack_policy, local_alias_slot_policy, finite_stack_index_policy,
                    discarded_exit_scratch, formal_stack_callee_proof,
                    formal_stack_alias_constant_policy, formal_stack_entry_word_policy,
                    formal_stack_entry_words_policy, mutable_stack_index_policy,
                    consumer_scratch_proof)):
            raise ValueError("entry calls require their exclusive ordinary saved-frame contract")
        entry_sites = entry_recursive_calls.validate_cfg(instructions, edges, address, calls)
    end = max(item.address + item.size for item in instructions.values())
    reached = {site: target(item, address, end) for site, item in instructions.items()
               if item.mnemonic == "bl" and len(item.operands) == 1 and
               item.operands[0].type == ARM_OP_IMM and
               address <= item.operands[0].imm < end and site not in entry_sites}
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
    if mutable:
        states = {(address, ((), None)): states[address]}
    pending, returns, maximum = list(states), set(), 0
    finite_updates = 0
    alias_sites, alias_accesses, alias_calls = set(), set(), set()
    clobbered = (*range(ARM_REG_R0, ARM_REG_R0 + 4), ARM_REG_R12, ARM_REG_LR)
    while pending:
        key = pending.pop()
        site, context = key if mutable else (key, None)
        constants, comparison = (dict(context[0]), context[1]) if mutable else ({}, None)
        instruction = instructions[site]
        registers, stack = dict(states[key][0]), list(states[key][1])
        aliases = {register: frozenset(values) for register, values in states[key][2]}
        pointer_slots = {word: frozenset(values) for word, values in states[key][3]}
        initialized = set(states[key][4]) if finite_states is not None else set()
        operands = instruction.operands
        regs = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        adjustment = thumb_stack_adjustment(instruction)
        name = instruction.mnemonic
        if entry_recursive_calls is not None:
            entry_recursive_calls.check_instruction(instruction, registers)
            if site in calls:
                entry_recursive_calls.check_call(registers, stack)
        loaded_scalar = None

        def stored_word(register):
            # Reuse the existing local-word token and all-path stack join. A
            # scalar tag is distinct from entry-register/return provenance.
            token = registers.get(register)
            if mutable_scalar_slots and register in constants and register not in aliases:
                return ("scalar-word", constants[register])
            return token

        def recover_word(register, token, offsets):
            nonlocal loaded_scalar
            if mutable_scalar_slots and token is not None and token[0] == "scalar-word":
                alias_slots.word(instruction)
                loaded_scalar = (register, token[1])
                scalar_loads.add((site, bytes(instruction.bytes).hex(), register, offsets, token[1]))
                return None
            return token

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
                if slot_states is not None or mutable_slots:
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
            returned_aliases = {}
            if discarded_exit_scratch is not None and aliases and not restoring_local_buffer:
                raise ValueError('discarded scratch local aliases cannot cross calls')
            if runtime_calls is not None and site in runtime_calls:
                if set(clobbered) & aliases.keys():
                    raise ValueError("canonical runtime arguments carry local stack provenance")
                runtime_name = runtime_calls[site]
                if runtime_name != "__udivsi3":
                    target_register = ARM_REG_R0 + int(runtime_name.removeprefix("_call_via_r"))
                    if target_register in aliases or registers.get(target_register) == ("entry-return",):
                        raise ValueError("indirect runtime target carries stack or entry-return provenance")
            formal_call = formal_stack_callee_proof is not None and site in formal_stack_callee_proof.sites
            if formal_call:
                writes = formal_stack_callee_proof.check_call(site, calls[site], aliases, stack, pointer_slots)
                for offset, width in writes:
                    first = access(offset, width, stack)
                    last = (offset + width - 1 + 4 * len(stack)) // 4
                    for slot in range(first, last + 1):
                        stack[slot] = ('local', None)
                    alias_slots.store(pointer_slots, offset, width)
                alias_calls.add(site)
            consumer_call = consumer_scratch_proof is not None and bool(set(clobbered) & aliases.keys())
            if consumer_call:
                # Validate actual live allocated aliases using the same frame machinery.
                for register in set(clobbered) & aliases.keys():
                    for offset in finite.offsets(aliases[register]):
                        access(offset, 1, stack)
                before_local = (list(stack), dict(pointer_slots), set(initialized))
                if mutable_three_call:
                    consumer_scratch_proof.check_call(site, calls[site], aliases, stack, pointer_slots, initialized)
                else:
                    consumer_scratch_proof.check_call(site, calls[site], aliases, pointer_slots)
                if before_local != (stack, pointer_slots, initialized):
                    raise ValueError('read-only consumer proof changed local memory provenance')
                alias_calls.add(site)
            if set(clobbered) & aliases.keys() and not formal_call and not consumer_call:
                if buffer_proof is None and bounded_output_proof is None:
                    raise ValueError("local aliases crossing calls require native buffer proof")
                offsets = {register: alias_offset(register, aliases)
                           for register in clobbered if register in aliases}
                native_stack = [(False, kind == "saved", kind == "local")
                                for kind, _ in stack]
                returned_aliases = (bounded_output_proof.check_call(calls[site],offsets,native_stack,site=site)
                        if bounded_output_proof is not None else
                        buffer_proof.check_call(calls[site], offsets, native_stack,
                            **({'site':site} if root_switch_buffer or restoring_local_buffer or callback_context_buffer or buffer_proof.bios_fill_proof is not None else {})))
                if returned_aliases and not returned_local_aliases:
                    raise ValueError("local alias return requires a separate provenance policy")
                if returned_local_aliases:
                    for register, offset in returned_aliases.items():
                        access(offset, 1, stack)
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
            if returned_local_aliases:
                aliases.update({register:frozenset(((offset,True),))
                                for register,offset in returned_aliases.items()})
        else:
            read, written = instruction.regs_access()
            assignment = None
            loaded_alias = None
            if stack_aliases:
                if mutable:
                    assignment = finite.assignment(instruction, aliases, len(stack), constants,
                        halfword_access=mutable_halfword_array)
                elif finite_states is not None:
                    assignment = finite.assignment(instruction, aliases, len(stack), finite_states[site])
                else:
                    exact = {register: alias_offset(register, aliases)
                             for register in aliases if register in read}
                    constant_states = (buffer_proof.constant_states
                        if restoring_local_buffer and buffer_proof.constant_states is not None else slot_states)
                    constants = {} if constant_states is None else {
                        register: value[0] for register, value in constant_states[site].items()}
                    assignment = stack_alias_assignment(instruction, exact, len(stack), constants)
                if assignment is not None:
                    if assignment[0] in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR):
                        raise ValueError("local alias cannot overwrite a control register")
                    if finite_states is None:
                        access(assignment[1], 1, stack)
                    else:
                        for offset in finite.offsets(assignment[1]): access(offset, 1, stack)
                        if mutable:
                            finite_additions.add((site, assignment[0], tuple(finite.offsets(assignment[1]))))
                        elif instruction.mnemonic == "add" and assignment[2] == ARM_REG_SP and assignment[0] in finite_states[site]:
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
                    low_halfword = None
                    index_displacement = 0
                    if mutable_halfword and operand.mem.index:
                        decoded = zero_index.signed_load(instruction)
                        if decoded is not None and decoded[2] == 2 and decoded[1] not in aliases and \
                                constants.get(decoded[1]) == 0:
                            certified_zero = True
                            low_halfword = decoded
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
                        if mutable_halfword_array and name in ('strh', 'ldrh', 'ldrsh'):
                            writing, register, base, index = finite.halfword(instruction)
                            if index and (index in aliases or constants.get(index) != 0):
                                raise ValueError("halfword signed load requires an exact scalar zero index")
                            offsets = finite.offsets(aliases[base])
                            positions = [access(offset, 2, stack) for offset in offsets]
                            event = (site, bytes(instruction.bytes).hex(), name, base, index, offsets)
                            if writing:
                                if register in aliases:
                                    raise ValueError("halfword arrays cannot contain pointer aliases")
                                alternatives = []
                                for offset in offsets:
                                    updated = dict(pointer_slots)
                                    alias_slots.store(updated, offset, 2)
                                    alternatives.append(updated)
                                pointer_slots = alternatives[0]
                                for alternative in alternatives[1:]:
                                    pointer_slots = {word: frozenset(values)
                                        for word, values in alias_slots.join(pointer_slots, alternative)}
                                for position in positions:
                                    # Any partial overwrite destroys a whole-word saved token.
                                    stack[position] = ("local", None)
                                if len(offsets) == 1:
                                    initialized.update(initialized_units(offsets[0], 2))
                                halfword_array_writes.add(event)
                                for offset in offsets:
                                    mutable_writes.add((site, base, offset, 2))
                            else:
                                if any(not set(initialized_units(offset, 2)) <= initialized for offset in offsets):
                                    raise ValueError("halfword read requires both bytes initialized on every path")
                                if any(offset < word + 4 and word < offset + 2
                                        for offset in offsets for word in pointer_slots):
                                    raise ValueError("halfword read overlaps a possible pointer word")
                                halfword_array_reads.add(event)
                                finite_reads.add((site, base, offsets, 2))
                            allowed_aliases.add(base)
                            alias_accesses.add(site)
                            # Partial loads do not restore full-word tokens, numeric or pointer facts.
                            continue
                        if low_halfword is not None:
                            offsets = finite.offsets(aliases[operand.mem.base])
                            for offset in offsets:
                                access(offset, 2, stack)
                                if offset % 4:
                                    raise ValueError("low halfword read requires an aligned enclosing local word")
                                if offset not in initialized:
                                    raise ValueError("low halfword read requires an initialized enclosing local word")
                                if any(offset < word + 4 and word < offset + 2 for word in pointer_slots):
                                    raise ValueError("low halfword read overlaps a possible pointer word")
                            halfword_reads.add((site, bytes(instruction.bytes).hex(), *low_halfword[:2], offsets))
                            finite_reads.add((site, operand.mem.base, offsets, 2))
                            allowed_aliases.add(operand.mem.base)
                            alias_accesses.add(site)
                            # A partial scalar load restores neither full-word tokens
                            # nor pointer/numeric facts. Normal destination kills apply.
                            continue
                        if name not in (("ldr", "str") if mutable else ("ldr",)) or width != 4 or operand.mem.index:
                            raise ValueError("mutable local aliases permit only aligned local-word reads/writes" if mutable
                                else "finite local aliases permit only aligned read-only local words")
                        offsets = tuple(offset + operand.mem.disp for offset in finite.offsets(aliases[operand.mem.base]))
                        slots = [access(offset, width, stack) for offset in offsets]
                        if name == "str":
                            if regs[0] in aliases:
                                raise ValueError("mutable local arrays cannot contain pointer aliases")
                            if mutable_slots:
                                # Each concrete STR writes one alternative, not all of them.
                                alternatives = []
                                for offset in offsets:
                                    updated = dict(pointer_slots)
                                    alias_slots.store(updated, offset, width)
                                    alternatives.append(updated)
                                pointer_slots = alternatives[0]
                                for alternative in alternatives[1:]:
                                    pointer_slots = {word: frozenset(values)
                                        for word, values in alias_slots.join(pointer_slots, alternative)}
                            if mutable_scalar_slots:
                                alias_slots.word(instruction)
                            token = stored_word(regs[0]) if len(slots) == 1 else None
                            for position in slots:
                                stack[position] = ("local", token)
                            if mutable_scalar_slots and token is not None and token[0] == "scalar-word":
                                scalar_stores.add((site, bytes(instruction.bytes).hex(), regs[0], offsets, token[1]))
                            # A may-write to several alternatives initializes none of them.
                            if len(offsets) == 1:
                                initialized.update(initialized_units(offsets[0], 4))
                            for offset in offsets:
                                mutable_writes.add((site, operand.mem.base, offset, width))
                        else:
                            if any(not set(initialized_units(offset, 4)) <= initialized for offset in offsets):
                                raise ValueError("finite local read requires every alternative initialized on every path")
                            if mutable_slots and any(offset in pointer_slots for offset in offsets):
                                alias_slots.word(instruction)
                                loaded_alias = (regs[0], frozenset().union(*(
                                    pointer_slots.get(offset, alias_slots.UNKNOWN) for offset in offsets)))
                                slot_loads.update((site, offset) for offset in offsets)
                            else:
                                tokens = [stack[position][1] for position in slots]
                                token = tokens[0] if all(value == tokens[0] for value in tokens) else None
                                assigned = (regs[0], recover_word(regs[0], token, offsets))
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
                    if regs[0] in aliases and slot_states is None and not mutable_slots:
                        raise ValueError("local aliases cannot be stored or spilled")
                    if stack[slot][0] != "local":
                        raise ValueError("local branch write overwrites a saved register")
                    if slot_states is not None or mutable_slots:
                        offset = operand.mem.disp - 4 * len(stack)
                        if regs[0] in aliases:
                            alias_slots.word(instruction)
                            slot_target = alias_offset(regs[0], aliases)
                            access(slot_target, 1, stack)
                            if mutable_slots and slot_target % 4:
                                raise ValueError("mutable pointer slots require an aligned local target")
                            allowed_aliases.add(regs[0])
                            slot_stores.add((site, offset, slot_target))
                        alias_slots.store(pointer_slots, offset, 4, aliases.get(regs[0]))
                    if mutable_scalar_slots:
                        alias_slots.word(instruction)
                    token = stored_word(regs[0])
                    stack[slot] = ("local", token)
                    if mutable_scalar_slots and token is not None and token[0] == "scalar-word":
                        scalar_stores.add((site, bytes(instruction.bytes).hex(), regs[0], (offset,), token[1]))
                    if finite_states is not None:
                        initialized.update(initialized_units(operand.mem.disp - 4 * len(stack), 4))
                else:
                    offset = operand.mem.disp - 4 * len(stack)
                    if finite_states is not None and stack[slot][0] == "local" and not set(initialized_units(offset, 4)) <= initialized:
                        raise ValueError("finite local word is not initialized on every path")
                    if offset in pointer_slots:
                        alias_slots.word(instruction)
                        loaded_alias = (regs[0], pointer_slots[offset])
                        slot_loads.add((site, offset))
                    else:
                        assigned = (regs[0], recover_word(regs[0], stack[slot][1], (offset,)))
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
                if discarded_exit_scratch is None or set(aliases) - {ARM_REG_R0+2, ARM_REG_R0+3}:
                    raise ValueError("local alias escapes through an exit register")
                for register, alternatives in aliases.items():
                    if len(alternatives) != 1 or any(offset >= 0 for offset, _ in alternatives):
                        # Every real local alias is checked by access(offset, 1)
                        # when formed, so offset zero cannot name a local byte.
                        # The existing join inserts (0, False) solely for an
                        # incoming path with no tracked local alias. Permit that
                        # alternative only at an unobserved scratch exit, under
                        # the explicit completed-replay policy. Actual alias uses
                        # still require one live exact offset in alias_offset.
                        optional_local = (restoring_local_buffer and
                            buffer_proof.proof._optional_local_frame_policy and
                            len(alternatives) == 2 and (0, False) in alternatives and
                            sum(offset < 0 for offset, _ in alternatives) == 1)
                        if not optional_local:
                            raise ValueError('discarded exit scratch requires exact local-offset provenance')
                    for offset, live in alternatives:
                        discarded_aliases.add((site, register-ARM_REG_R0, offset, live))
            returns.add(site)
        outgoing = (tuple(sorted(registers.items())), tuple(stack),
                    tuple(sorted((register, tuple(sorted(values))) for register, values in aliases.items())),
                    tuple(sorted((word, tuple(sorted(values))) for word, values in pointer_slots.items())))
        if finite_states is not None:
            outgoing += (frozenset(initialized),)
        next_context = finite.transfer(instruction, constants, comparison, call=site in calls) if mutable else None
        if loaded_scalar is not None:
            # Normal transfer kills the load destination first. Recovery is
            # allowed only after complete initialized, nonpointer word checks.
            recovered = dict(next_context[0])
            recovered[loaded_scalar[0]] = loaded_scalar[1]
            next_context = (tuple(sorted(recovered.items())), next_context[1])
        successors = finite.successors(instruction, edges[site], comparison) if mutable else edges[site]
        for successor in successors:
            if successor not in instructions:
                raise ValueError("local branch frame escaped its complete CFG")
            successor_key = (successor, next_context) if mutable else successor
            previous = states.get(successor_key)
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
                            if slot_states is not None or mutable_slots else ())
                if finite_states is not None:
                    if any(len(values) > finite.MAX_VALUES for _,values in joined_aliases):
                        raise ValueError("finite local alias alternative budget exceeded")
                    merged += (previous[4] & frozenset(initialized),)
            if previous != merged:
                if finite_states is not None:
                    finite_updates += 1
                    if finite_updates > finite.MAX_UPDATES:
                        raise ValueError("finite local frame proof-state budget exceeded")
                states[successor_key] = merged
                pending.append(successor_key)
    if ({site for site, _ in states} if mutable else set(states)) != set(instructions) or not returns:
        raise ValueError("local branch frame proof does not cover the complete reachable owner")
    proof = {"schema": SCHEMA, "instructions": len(instructions), "maximum_frame_bytes": maximum,
            "returns": sorted(returns), "preserved": "r4-r11,sp,entry-lr",
            "external_calls": "existing-direct-call-ABI-summary"}
    if returned_local_aliases:
        proof["returned_local_alias_policy"] = RETURN_POLICY
    if entry_recursive_calls is not None:
        proof["entry_calls"] = entry_recursive_calls.record()
    if call_preservation is not None:
        proof["external_calls"] = "complete-native-callee-preservation-v1"
        proof["call_preservation"] = [[site, sorted(registers)]
                                      for site, registers in sorted(call_preservation.items())]
    if entry_stack_policy is not None:
        if incoming_words_policy:
            entry_stack.validate_reads((offset for _, offset, _ in incoming_reads), entry_stack_policy)
        proof["entry_stack"] = {"schema": entry_stack.SCHEMA, "words": list(entry_stack_policy['words']),
            "contract": entry_stack.CONTRACT, "loaded_value": "unknown scalar; no provenance facts",
            "reads": [[site, offset, 4, encoded] for site, offset, encoded in sorted(incoming_reads)]}
    if stack_aliases:
        proof["local_aliases"] = {"schema": ALIAS_SCHEMA, "assignments": sorted(alias_sites),
                                  "accesses": sorted(alias_accesses), "buffer_calls": sorted(alias_calls),
                                  "buffer_fingerprint": (bounded_output_proof or buffer_proof).fingerprint()
                                    if bounded_output_proof or buffer_proof else None}
    if consumer_scratch_proof is not None:
        proof['three_call_composition' if mutable_three_call else
              'readonly_leaf_overwrite_aliases' if mutable_overwrite else 'consumer_scratch_aliases'] = consumer_scratch_proof.manifest()
    if discarded_exit_scratch is not None:
        proof['discarded_exit_scratch'] = {'schema': DISCARDED_SCRATCH_SCHEMA,
            'registers': list(discarded_exit_scratch['registers']),
            'contract': DISCARDED_SCRATCH_CONTRACT,
            'residual_aliases': [[site, register, offset, live]
                for site, register, offset, live in sorted(discarded_aliases)],
            'native_nonescape_proof': False}
    if formal_stack_callee_proof is not None:
        proof['formal_stack_callee'] = formal_stack_callee_proof.fingerprint()
    if named_entry_word:
        proof['formal_stack_entry_word_policy'] = formal_stack_entry_word_policy
    if named_pair_entry_words:
        proof['formal_stack_entry_words_policy'] = formal_stack_entry_words_policy
    if entry_alias_words:
        proof['entry_stack_alias_slot_policy'] = entry_stack_alias_slot_policy
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
            "callee_pointer_arguments": formal_stack_callee_proof is not None}
        if formal_stack_alias_constant_policy is not None:
            proof["local_alias_slots"].update(
                constant_policy=formal_stack_alias_constant_policy,
                constant_domain="exact MOVS 1/2/3/10 only; all-path intersection; every call kills facts",
                allowed_MOVS_constants=list(alias_slots.FORMAL_MOVS10_DOMAIN))
    if mutable_slots:
        proof["mutable_local_pointer_slots"] = {"schema": "thumb-mutable-local-pointer-slots-v1",
            "policy": mutable_stack_index_policy, "source_or_ELF_admission": False,
            "provenance_api": "local_alias_slot_profile.word/store/join/release",
            "stores": [list(row) for row in sorted(slot_stores)],
            "loads": [list(row) for row in sorted(slot_loads)],
            "contract": "aligned allocated direct-SP singleton pointer stores; word reload preserves possible aliases; missing/partial/may-write paths retain taint; release expires lifetime",
            "pointee_initialization_from_pointer_store": False}
    if mutable_halfword and not mutable_halfword_array:
        proof["mutable_low_signed_halfword_reads"] = {
            "schema": "thumb-mutable-low-signed-halfword-reads-v1",
            "policy": mutable_stack_index_policy, "source_or_ELF_admission": False,
            "read_width_bytes": 2, "initialized_enclosing_word_bytes": 4,
            "initialization_effect": False, "numeric_result_facts": False,
            "reads": [{"site": site, "bytes": encoded, "base_register": base,
                "index_register": index, "index_value": 0, "offsets": list(offsets)}
                for site, encoded, base, index, offsets in sorted(halfword_reads)],
            "contract": "exact zero-index LDRSH; initialized aligned local low halfword; no pointer overlap, stores or partial-word facts"}
    if mutable_halfword_array:
        def halfword_records(events):
            return [{"site": site, "bytes": encoded, "mnemonic": name,
                "base_register": base, "index_register": index,
                "index_value": 0 if index else None, "offsets": list(offsets),
                "width": 2} for site, encoded, name, base, index, offsets in sorted(events)]
        proof["mutable_halfword_accesses"] = {
            "schema": "thumb-mutable-local-halfword-access-v1",
            "policy": mutable_stack_index_policy, "source_or_ELF_admission": False,
            "initialization_unit_bytes": 1, "numeric_result_facts": False,
            "reads": halfword_records(halfword_array_reads),
            "writes": halfword_records(halfword_array_writes),
            "initialization": "one byte-coverage initialized state; definite singleton writes cover only actual bytes; joins intersect and release prunes",
            "pointer_taint": "existing local_alias_slot store/join/release; partial writes retain taint; partial reads reject any overlap",
            "contract": "live allocated aligned local STRH/LDRH offset0 and exact zero-index LDRSH; no byte access, word-token recovery or new incoming-memory permission"}
    if mutable_scalar_slots:
        def scalar_records(events):
            return [{"site": site, "bytes": encoded, "register": register,
                "offsets": list(offsets), "width": 4, "value": value}
                for site, encoded, register, offsets, value in sorted(events)]
        proof["mutable_scalar_word_slots"] = {
            "schema": "thumb-mutable-local-scalar-word-slots-v1",
            "policy": mutable_stack_index_policy, "source_or_ELF_admission": False,
            "stores": scalar_records(scalar_stores), "loads": scalar_records(scalar_loads),
            "provenance_api": "existing stack word tokens, exact finite contexts and local_alias_slot_profile.word/store/join/release",
            "contract": "exact finite scalar facts from authenticated full aligned allocated word stores; all bytes initialized and identical all-path word token for recovery; partial/unknown writes, lifetime release and pointer taint forbid recovery",
            "incoming_or_partial_memory_facts": False}
    if mutable:
        proof["mutable_stack_indices"] = {"schema": finite.SCHEMA, "policy": mutable_stack_index_policy,
            "assignments": [[site, register, list(offsets)] for site, register, offsets in sorted(finite_additions)],
            "reads": [[site, base, list(offsets), width] for site, base, offsets, width in sorted(finite_reads)],
            "writes": [list(row) for row in sorted(mutable_writes)],
            "contexts": len(states), "source_or_ELF_admission": False,
            "domain": ("exact 32-bit register constants; selected index additions0/2/4/6/8/12; separate path contexts; resource refusal" if mutable_halfword_array else "exact 32-bit register constants; index additions only 0/4/8/12; separate path contexts; resource refusal"),
            "initialization": ("singleton writes cover only actual bytes; reads require all bytes; joins intersect; ambiguous writes initialize none" if mutable_halfword_array else "singleton writes initialize their own aligned local word; joins intersect; ambiguous writes initialize none"),
            "exclusions": ("no nonzero halfword displacements, byte accesses, buffers, incoming words or local aliases in scratch call arguments" if mutable_halfword_array
                else "no halfword stores/upper lanes, buffers, incoming words or local aliases in scratch call arguments" if mutable_halfword
                else "no halfwords, buffers, incoming words or local aliases in scratch call arguments" if mutable_slots
                else "no pointer slots, halfwords, buffers, incoming words or local aliases in scratch call arguments")}
    elif finite_states is not None:
        proof["finite_stack_indices"] = {"schema": finite.SCHEMA, "policy": finite_stack_index_policy,
            "SP_additions": [[site,register,[[value,list(origins)] for value,origins in alternatives]]
                for site,register,alternatives in sorted(finite_additions)],
            "reads": [[site,base,list(offsets),width] for site,base,offsets,width in sorted(finite_reads)],
            "constant_domain": "MOVS0/1, exact LSL2, all-path union of at most2 known values in0/1/4; missing arms unknown; caller-saved calls kill facts",
            "alias_domain": "at most2 live allocated offsets; read-only initialized aligned words on every alternative; no spills, buffer or entry-word premise"}
    if mutable and mutable_three_call:
        proof['mutable_stack_indices']['exclusions'] = (
            'no nonzero halfword displacements, byte accesses, buffers or incoming words; '
            'scratch aliases only at three explicitly selected, independently certified calls')
    return proof
