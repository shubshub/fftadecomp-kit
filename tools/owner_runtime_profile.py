"""Private inventory composition, never an original-ELF/source admission route.

The caller supplies the frozen native owner reconstruction. Every invocation
replays that graph, its complete partition, canonical runtime identities, ordinary
call bindings, and the opt-in restoring-frame proof. No addressed runtime alias
or inferred dynamic indirect-callee contract is accepted.
"""

import hashlib
import json

from capstone import CS_GRP_INT, CS_GRP_CALL, CS_GRP_JUMP
from capstone.arm import (ARM_OP_IMM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R1,
                          ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR,
                          ARM_REG_PC, ARM_OP_MEM, ARM_INS_IT, ARM_INS_ADR, ARM_INS_B,
                          ARM_CC_AL, ARM_CC_INVALID)

import match
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import owner_graph_profile as inventory
import analyze

SCHEMA = "private-thumb-owner-thunk-udiv-inventory-v1"


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


def canonical_calls(calls, entries, address, size, rom):
    runtime, ordinary = {}, {}
    names = {target: name for name, target in thunks.ALIASES.items()}
    for site, target in sorted(calls.items()):
        if target in names:
            runtime[site] = names[target]
        elif target == match.UDIVSI3_ADDRESS:
            runtime[site] = "__udivsi3"
        else:
            ordinary[site] = match.function_address_target(
                f"func_{target:08X}", entries, address, size, len(rom))
    if "__udivsi3" not in runtime.values() or not set(runtime.values()) & thunks.ALIASES.keys():
        raise ValueError("composition requires actual unsigned division and canonical thunk calls")
    return runtime, ordinary


def verify(data, address, rom, mapping, refinement, manifest=None):
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
    runtime, ordinary = canonical_calls(calls, entries, address, len(data), rom)
    match.verify_udivsi3_identity(rom, mapping)
    dependencies = thunks.dependencies([name for name in runtime.values()
                                       if name != "__udivsi3"], rom)
    divisors = prove_divisors(instructions, edges, address, branches, calls,
                             {site for site, name in runtime.items() if name == "__udivsi3"})
    buffer = match.BufferCallProof(rom, mapping)
    frame_record = frame.prove_frame(instructions, edges, address, branches, calls,
                                    stack_aliases=True, buffer_proof=buffer,
                                    runtime_calls=runtime)
    observed = {
        "schema": SCHEMA, "address": address, "end": end, "bytes": len(data),
        "instructions": len(instructions), "body_sha256": hashlib.sha256(data).hexdigest(),
        "mapping_sha256": hashlib.sha256(mapping).hexdigest(),
        "calls": [[site - address, f"func_{target:08X}"]
                  for site, target in sorted(ordinary.items())],
        "runtime_calls": [[site - address, name] for site, name in sorted(runtime.items())],
        "thunk_ABI": thunks.ABI, "thunk_dependencies": dependencies,
        "udiv_runtime": match.UDIVSI3_RUNTIME,
        "udiv_dependencies": [list(identity) for identity in match.UDIVSI3_IDENTITIES],
        "divisors": [[site - address, value] for site, value in sorted(divisors.items())],
        "frame": frame_record, "partition": partition,
        "buffer_dependencies": [[target, hashlib.sha256(body).hexdigest()]
                                for target, body in sorted(buffer.dependencies.items())],
        "source_or_original_ELF_admission": False,
    }
    if manifest is not None and (type(manifest) is not dict or
                                json.dumps(manifest, sort_keys=True) !=
                                json.dumps(observed, sort_keys=True)):
        raise ValueError("owner runtime composition manifest differs from fresh native replay")
    return observed
