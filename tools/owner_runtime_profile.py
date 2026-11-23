"""Private inventory composition, never an original-ELF/source admission route.

The caller supplies the frozen native owner reconstruction. Every invocation
replays that graph, its complete partition, canonical runtime identities, ordinary
call bindings, and the opt-in restoring-frame proof. No addressed runtime alias
or inferred dynamic indirect-callee contract is accepted.

SCHEMA records exactly the domain it was written for: constant unsigned division
beside at least one canonical thunk, nothing else, in a whole number of words.
Every other owner the same proofs close is recorded under OPTIONAL_SCHEMA, which
pins each runtime it actually calls and nothing it does not. The pinned signed
remainder is bound under one name per owner, the compiler's __modsi3 or the
addressed func_08142950, and is never part of SCHEMA's domain.
"""

import hashlib
import json
import struct

from capstone import CS_GRP_INT, CS_GRP_CALL, CS_GRP_JUMP
from capstone.arm import (ARM_OP_IMM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R1,
                          ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR,
                          ARM_REG_PC, ARM_OP_MEM, ARM_INS_IT, ARM_INS_ADR, ARM_INS_B,
                          ARM_CC_AL, ARM_CC_INVALID)

import match
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import modsi3_profile as modsi3
import owner_graph_profile as inventory
import analyze
import rom_mirror

SCHEMA = "private-thumb-owner-thunk-udiv-inventory-v1"
OPTIONAL_SCHEMA = "private-thumb-owner-optional-runtime-inventory-v1"


def verify_operations(instructions, edges, address, branches, calls, refinement):
    """Retain ordinary native instruction/control restrictions alongside frame proof."""
    switches = {address + row['dispatch'] + 8 for row in refinement['word_switches']}
    for site, instruction in instructions.items():
        operands = instruction.operands
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        if CS_GRP_INT in instruction.groups or instruction.id in (ARM_INS_IT, ARM_INS_ADR):
            raise ValueError('interrupts and conditional/PC materialization blocks remain unsupported')
        if CS_GRP_CALL in instruction.groups:
            if site not in calls and site not in branches or instruction.mnemonic != 'bl' or \
                    instruction.size != 4 or not unconditional or len(operands) != 1 or \
                    operands[0].type != ARM_OP_IMM:
                raise ValueError('owner call is not an exact unconditional linked Thumb BL')
            continue
        if CS_GRP_JUMP in instruction.groups and instruction.id != ARM_INS_B and \
                edges[site] and site not in switches:
            raise ValueError('owner has an unproved indirect control transfer')
        _, written = instruction.regs_access()
        # Return destinations are separately authenticated by prove_frame.
        # Word switches have exact native layouts and predecessor guards.
        if ARM_REG_PC in written and edges[site] and site not in switches and \
                instruction.id != ARM_INS_B:
            raise ValueError('owner has an unresolved program-counter write')
        for operand in operands:
            if operand.type == ARM_OP_REG and operand.reg == ARM_REG_PC and \
                    edges[site] and site not in switches:
                raise ValueError('owner materializes its program counter')
            if operand.type == ARM_OP_MEM:
                if operand.mem.index == ARM_REG_PC:
                    raise ValueError('owner uses PC as an indexed memory address')
                if operand.mem.base == ARM_REG_PC and (
                        instruction.mnemonic != 'ldr' or operand.mem.index):
                    raise ValueError('owner has unsupported PC-relative memory access')


def prove_divisors(instructions, edges, address, branches, calls, sites):
    """The native MOV-only nonzero-u32 policy over the exact joined CFG.

    Local BL changes LR only; external calls erase the ordinary caller-clobbered
    facts. Facts are retained at joins only when all incoming paths agree. The
    final checks use the converged states, never an optimistic early work item.
    """
    if address not in instructions or set(edges) != set(instructions) or not sites or \
            set(sites) - set(calls) or any(calls[site] != match.UDIVSI3_ADDRESS for site in sites):
        raise ValueError("unsigned division requires exact reached canonical sites")
    clobbered = (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    states, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        incoming = states[site]
        outgoing = dict(incoming)
        if site in branches:
            outgoing.pop(ARM_REG_LR, None)
        elif site in calls:
            for register in clobbered:
                outgoing.pop(register, None)
        else:
            _, written = instruction.regs_access()
            for register in written:
                outgoing.pop(register, None)
            operands = instruction.operands
            if instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and instruction.size == 2 and \
                    instruction.mnemonic in ("mov", "movs") and len(operands) == 2 and \
                    operands[0].type == ARM_OP_REG:
                value = (operands[1].imm if operands[1].type == ARM_OP_IMM else
                         incoming.get(operands[1].reg) if operands[1].type == ARM_OP_REG else None)
                if value is not None:
                    outgoing[operands[0].reg] = value
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("division CFG leaves exact instruction boundaries")
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: value for register, value in previous.items()
                if outgoing.get(register) == value}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError("division proof does not cover every reached instruction")
    divisors = {}
    for site in sorted(sites):
        value = states[site].get(ARM_REG_R1)
        if type(value) is not int or not 1 <= value <= 0xFFFFFFFF:
            raise ValueError(f"division requires a CFG-proven nonzero constant in r1 at {site:08X}")
        divisors[site] = value
    return divisors


REMAINDER_NAMES = ("__modsi3", modsi3.ADDRESSED_NAME)
POSITIVE_DIVISOR = "positive-signed32-constant-divisor"
SIGNED16_OPERANDS = "signed16-dividend-nonzero-divisor"


def remainder_name(bindings):
    """The one name the owner's original relocations give the pinned remainder.

    A malformed or absent record yields the compiler name; the caller then refuses
    any bindings whose calls differ from the replayed inventory.
    """
    calls = bindings.get("calls") if type(bindings) is dict else None
    names = {row[1] for row in calls if type(row) is list and len(row) == 2} \
        if type(calls) is list else set()
    return modsi3.ADDRESSED_NAME if modsi3.ADDRESSED_NAME in names else "__modsi3"


def constant_result(instruction, incoming, address, data):
    """The exact value one unconditional 16-bit instruction writes to a low or high
    general register r0-r12 from known constants, else None."""
    operands = instruction.operands
    if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or instruction.size != 2 or \
            not operands or operands[0].type != ARM_OP_REG or \
            not ARM_REG_R0 <= operands[0].reg <= ARM_REG_R12:
        return None
    name, destination = instruction.mnemonic, operands[0].reg

    def known(operand):
        return incoming.get(operand.reg) if operand.type == ARM_OP_REG and \
            ARM_REG_R0 <= operand.reg <= ARM_REG_R12 else None

    value = None
    if name in ("mov", "movs") and len(operands) == 2:
        value = operands[1].imm if operands[1].type == ARM_OP_IMM else known(operands[1])
    elif name in ("adds", "subs") and len(operands) == 3 and operands[2].type == ARM_OP_IMM and \
            known(operands[1]) is not None:
        value = known(operands[1]) + (operands[2].imm if name == "adds" else -operands[2].imm)
    elif name in ("adds", "subs") and len(operands) == 2 and operands[1].type == ARM_OP_IMM and \
            destination in incoming:
        value = incoming[destination] + (operands[1].imm if name == "adds" else -operands[1].imm)
    elif name in ("lsl", "lsls") and len(operands) == 3 and operands[2].type == ARM_OP_IMM and \
            0 <= operands[2].imm <= 31 and known(operands[1]) is not None:
        value = known(operands[1]) << operands[2].imm
    elif name == "ldr" and len(operands) == 2 and operands[1].type == ARM_OP_MEM and \
            operands[1].mem.base == ARM_REG_PC and not operands[1].mem.index:
        offset = ((instruction.address + 4) & ~3) + operands[1].mem.disp - address
        if 0 <= offset <= len(data) - 4 and (address + offset) % 4 == 0:
            word = struct.unpack_from("<I", data, offset)[0]
            # Every reached word in the typed address domain must carry a typed
            # object, function or switch relocation; a word outside it carries none.
            if not rom_mirror.typed_domain(word):
                value = word
    return None if value is None else value & 0xFFFFFFFF


def prove_remainders(instructions, edges, address, branches, calls, sites, data):
    """One operand record per pinned signed remainder site.

    Either r1 holds a CFG-proven constant in [1, 0x7FFFFFFF], which excludes a zero
    divisor and INT_MIN % -1 for every dividend, or modsi3_profile.prove_operands
    proves a signed16 r0 and a nonzero r1. Facts survive a join only when every
    incoming path agrees; an external call erases r0-r3, r12 and LR, a local BL LR
    only. The final checks use the converged states.
    """
    if address not in instructions or set(edges) != set(instructions) or not sites or \
            set(sites) - set(calls) or any(calls[site] != modsi3.ADDRESS for site in sites):
        raise ValueError("signed remainder requires exact reached canonical sites")
    clobbered = (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    states, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        incoming = states[site]
        outgoing = dict(incoming)
        if site in branches:
            outgoing.pop(ARM_REG_LR, None)
        elif site in calls:
            for register in clobbered:
                outgoing.pop(register, None)
        else:
            _, written = instruction.regs_access()
            for register in written:
                outgoing.pop(register, None)
            value = constant_result(instruction, incoming, address, data)
            if value is not None:
                outgoing[instruction.operands[0].reg] = value
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("remainder CFG leaves exact instruction boundaries")
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: value for register, value in previous.items()
                if outgoing.get(register) == value}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError("remainder proof does not cover every reached instruction")
    records, fallback = {}, set()
    for site in sorted(sites):
        value = states[site].get(ARM_REG_R1)
        if type(value) is int and 1 <= value <= 0x7FFFFFFF:
            records[site] = [site - address, POSITIVE_DIVISOR, value]
        else:
            fallback.add(site)
    if fallback:
        modsi3.prove_operands(instructions, edges, address, fallback)
        records.update({site: [site - address, SIGNED16_OPERANDS] for site in fallback})
    return [records[site] for site in sorted(records)]


def canonical_calls(calls, entries, address, size, rom, remainder="__modsi3"):
    if remainder not in REMAINDER_NAMES:
        raise ValueError("signed remainder binding name is not canonical")
    runtime, ordinary = {}, {}
    names = {target: name for name, target in thunks.ALIASES.items()}
    for site, target in sorted(calls.items()):
        if target in names:
            runtime[site] = names[target]
        elif target == match.UDIVSI3_ADDRESS:
            runtime[site] = "__udivsi3"
        elif target == modsi3.ADDRESS:
            runtime[site] = remainder
        else:
            ordinary[site] = match.function_address_target(
                f"func_{target:08X}", entries, address, size, len(rom))
    return runtime, ordinary


def original_domain(runtime, size):
    """True only for the owners SCHEMA was written for, so its records never change."""
    names = set(runtime.values())
    return "__udivsi3" in names and bool(names & thunks.ALIASES.keys()) and \
        names <= {"__udivsi3", *thunks.ALIASES} and size % 4 == 0


def verify(data, address, rom, mapping, refinement, manifest=None, *, remainder="__modsi3"):
    if type(data) is not bytes or type(rom) is not bytes or type(mapping) is not bytes or \
            type(address) is not int or address % 2:
        raise ValueError("owner composition requires immutable exact Thumb ROM inputs")
    entries = json.loads(mapping)
    owners = [row for row in entries if int(row["rom"], 16) & ~1 == address]
    end = address + len(data)
    if len(owners) != 1 or owners[0].get("mode") != "thumb" or \
            int(owners[0]["rom"], 16) != address or int(owners[0]["end"], 16) != end or \
            not match.ROM_BASE <= address < end <= match.ROM_BASE + len(rom) or \
            data != rom[address - match.ROM_BASE:end - match.ROM_BASE] or any(
                row is not owners[0] and int(row["rom"], 16) < end and
                int(row["end"], 16) > address for row in entries):
        raise ValueError("owner composition requires exact unique nonoverlapping complete ROM ownership")
    fresh = analyze.refine_function(
        data, address, entries, max_bytes=len(data), max_instructions=len(data)//2,
        rom_end=match.ROM_BASE + len(rom), same_owner_long_branches=True)
    if fresh != refinement:
        raise ValueError('owner refinement differs from fresh native CFG/guard replay')
    instructions, edges, branches, calls, words = inventory.graph(data, address, fresh)
    partition = inventory.partition(data, address, refinement, instructions, words)
    verify_operations(instructions, edges, address, branches, calls, fresh)
    if len(instructions) != owners[0]["instrs"]:
        raise ValueError("owner composition instruction count differs from exact mapping")
    runtime, ordinary = canonical_calls(calls, entries, address, len(data), rom, remainder)
    original = original_domain(runtime, len(data))
    # Each runtime identity and operand proof runs exactly when that runtime is
    # called. None of the frame, alias, buffer or partition proofs depends on a
    # runtime being present; without one the frame proof sees ordinary calls only.
    udiv_sites = {site for site, name in runtime.items() if name == "__udivsi3"}
    thunk_names = [name for name in runtime.values() if name in thunks.ALIASES]
    if udiv_sites:
        match.verify_udivsi3_identity(rom, mapping)
    dependencies = thunks.dependencies(thunk_names, rom)
    divisors = prove_divisors(instructions, edges, address, branches, calls,
                             udiv_sites) if udiv_sites else {}
    remainder_sites = {site for site, target in calls.items() if target == modsi3.ADDRESS}
    if remainder_sites:
        modsi3.verify_identity(rom, mapping)
    remainders = prove_remainders(instructions, edges, address, branches, calls,
                                  remainder_sites, data) if remainder_sites else []
    # A stack address handed to an exact indexed BIOS SWI wrapper is summarised, as on
    # the plain path, instead of walked (bios_wrapper_summary_profile): memory wrappers
    # at the owner's own calls only, discharged at the call over this complete CFG.
    buffer = match.BufferCallProof(rom, mapping, bios_wrappers=True)
    buffer.bios_summaries.bind_owner(data, address, instructions, edges)
    # The frame proof names the remainder by its canonical runtime, whatever the
    # relocation called it: its arguments may carry no stack provenance.
    frame_record = frame.prove_frame(instructions, edges, address, branches, calls,
                                    stack_aliases=True, buffer_proof=buffer,
                                    runtime_calls={site: "__modsi3" if site in remainder_sites else name
                                                   for site, name in runtime.items()} or None)
    summaries = buffer.bios_summaries.observed()
    # SCHEMA's domain never contained a summarised BIOS call.
    original = original and not summaries
    observed = {
        "schema": SCHEMA if original else OPTIONAL_SCHEMA, "address": address, "end": end,
        "bytes": len(data),
        "instructions": len(instructions), "body_sha256": hashlib.sha256(data).hexdigest(),
        "mapping_sha256": hashlib.sha256(mapping).hexdigest(),
        "calls": [[site - address, f"func_{target:08X}"]
                  for site, target in sorted(ordinary.items())],
        "runtime_calls": [[site - address, name] for site, name in sorted(runtime.items())],
        "frame": frame_record, "partition": partition,
        "buffer_dependencies": [[target, hashlib.sha256(body).hexdigest()]
                                for target, body in sorted(buffer.dependencies.items())],
        "source_or_original_ELF_admission": False,
    }
    if not original:
        # Each same-owner BL is a jump, recorded as an edge; prove_frame shows no
        # return goes through the LR it leaves.
        observed["local_branches"] = [[site - address, target - address]
                                      for site, target in sorted(branches.items())]
    if thunk_names:
        observed.update(thunk_ABI=thunks.ABI, thunk_dependencies=dependencies)
    if udiv_sites:
        observed.update(
            udiv_runtime=match.UDIVSI3_RUNTIME,
            udiv_dependencies=[list(identity) for identity in match.UDIVSI3_IDENTITIES],
            divisors=[[site - address, value] for site, value in sorted(divisors.items())])
    if remainder_sites:
        observed.update(
            remainder_runtime=modsi3.RUNTIME,
            remainder_dependencies=[list(identity) for identity in modsi3.IDENTITIES],
            remainders=remainders)
    if summaries:
        observed["bios_summaries"] = buffer.bios_summaries.manifest()
    if manifest is not None and (type(manifest) is not dict or
                                json.dumps(manifest, sort_keys=True) !=
                                json.dumps(observed, sort_keys=True)):
        raise ValueError("owner runtime composition manifest differs from fresh native replay")
    return observed
