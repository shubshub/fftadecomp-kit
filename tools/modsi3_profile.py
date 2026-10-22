"""Pinned Thumb signed remainder and a bounded operand-domain proof."""

import hashlib
import json

SCHEMA = "elf-symbol-thumb-modsi3-s16-v1"
SUMMARY = "pinned Thumb signed remainder with CFG-proven signed16 dividend and nonzero divisor"
RUNTIME = "agbcc-thumb-modsi3-v1"
ADDRESS = 0x08142950
ADDRESSED_NAME = "func_08142950"
IDENTITIES = (
    (ADDRESS, 0x08142A1E,
     "e29c5cee2bafd4fcf3d248a70964d363a3222d67d3eac9031acc95247242fc53"),
    (0x0814274C, 0x0814274E,
     "abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c"),
)


class AddressedRemainderRequired(ValueError):
    pass


def reserved(address):
    return any(start <= address & ~1 < end for start, end, _ in IDENTITIES)


def address_literal(value):
    return 0x02000000 <= value < 0x10000000


def supported_data(value, rom_size):
    return 0x02000000 <= value < 0x04000000 or 0x08000000 <= value < 0x08000000 + rom_size


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SCHEMA.encode("ascii"), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def verify_identity(rom, mapping):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm_const import ARM_INS_BL, ARM_OP_IMM

    if not isinstance(rom, bytes) or not isinstance(mapping, bytes):
        raise ValueError("signed remainder requires ROM and mapping snapshots")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("signed remainder requires a function mapping")
    for start, end, digest in IDENTITIES:
        candidates = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
        if len(candidates) != 1 or int(candidates[0]["rom"], 16) != start or \
                int(candidates[0]["end"], 16) != end or candidates[0].get("mode") != "thumb" or \
                not 0x08000000 <= start < end <= 0x08000000 + len(rom) or \
                any(entry is not candidates[0] and int(entry["rom"], 16) < end and
                    int(entry["end"], 16) > start for entry in entries):
            raise ValueError("signed remainder requires exact unique nonoverlapping runtime spans")
        if hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() != digest:
            raise ValueError("signed remainder runtime or dependency identity differs")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    dependency = next(decoder.disasm(rom[0x142A16:0x142A1A], 0x08142A16, count=1), None)
    if dependency is None or dependency.id != ARM_INS_BL or dependency.size != 4 or \
            len(dependency.operands) != 1 or dependency.operands[0].type != ARM_OP_IMM or \
            dependency.operands[0].imm != 0x0814274C:
        raise ValueError("signed remainder zero-path dependency differs")


def verify_context(data, address, calls, context):
    if not isinstance(context, tuple) or len(context) != 3 or \
            not isinstance(context[2], dict) or not context[2]:
        raise ValueError("signed remainder requires an isolated runtime context")
    rom, mapping, bindings = context
    verify_identity(rom, mapping)
    names = set(bindings.values())
    if names not in ({"__modsi3"}, {ADDRESSED_NAME}) or \
            any(type(site) is not int or calls.get(site) != ADDRESS for site in bindings) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("signed remainder call bindings are incomplete or mixed")
    entries = json.loads(mapping)
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or reserved(address) or len(callers) != 1 or \
            int(callers[0]["rom"], 16) != address or callers[0].get("mode") != "thumb" or \
            int(callers[0]["end"], 16) != address + len(data) or \
            not 0x08000000 <= address < address + len(data) <= 0x08000000 + len(rom) or \
            any(entry is not callers[0] and int(entry["rom"], 16) < address + len(data) and
                int(entry["end"], 16) > address for entry in entries) or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("signed remainder caller requires exact complete mapped ROM bytes")
    return names == {"__modsi3"}


def prove_operands(instructions, edges, address, sites):
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_CC_EQ, ARM_CC_NE,
                                   ARM_INS_ASR, ARM_INS_B, ARM_INS_CMP,
                                   ARM_OP_IMM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R1,
                                   ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)

    caller_clobbered = frozenset((ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3,
                                 ARM_REG_R12, ARM_REG_LR))
    predecessors = {current: set() for current in instructions}
    for current, successors in edges.items():
        for successor in successors:
            predecessors[successor].add(current)
    states = {address: frozenset()}
    pending = [address]
    while pending:
        current = pending.pop()
        instruction = instructions[current]
        incoming = states[current]
        outgoing = set(incoming)
        operands = instruction.operands
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        if CS_GRP_CALL in instruction.groups:
            outgoing = {fact for fact in outgoing if fact[0] not in caller_clobbered}
        else:
            _, written = instruction.regs_access()
            outgoing = {fact for fact in outgoing if fact[0] not in written}
            if unconditional and instruction.size == 2 and operands and \
                    operands[0].type == ARM_OP_REG:
                destination = operands[0].reg
                source = None
                if instruction.mnemonic in ("mov", "movs") and len(operands) == 2:
                    if operands[1].type == ARM_OP_REG:
                        source = operands[1].reg
                    elif operands[1].type == ARM_OP_IMM:
                        value = operands[1].imm & 0xFFFFFFFF
                        signed = value if value < 0x80000000 else value - 0x100000000
                        if -32768 <= signed <= 32767:
                            outgoing.add((destination, "s16"))
                        if value:
                            outgoing.add((destination, "nz"))
                elif instruction.mnemonic in ("add", "adds") and len(operands) == 3 and \
                        operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and \
                        operands[2].imm == 0:
                    source = operands[1].reg
                elif instruction.id == ARM_INS_ASR and len(operands) == 3 and \
                        operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and \
                        operands[2].imm == 16:
                    outgoing.add((destination, "s16"))
                if source is not None:
                    outgoing.update((destination, kind) for register, kind in incoming
                                    if register == source)
        guarded_register = None
        if instruction.id == ARM_INS_B and instruction.size == 2 and \
                instruction.cc in (ARM_CC_EQ, ARM_CC_NE) and \
                predecessors[current] == {current - 2}:
            comparison = instructions[current - 2]
            compared = comparison.operands
            if comparison.id == ARM_INS_CMP and comparison.size == 2 and \
                    comparison.cc in (ARM_CC_AL, ARM_CC_INVALID) and len(compared) == 2 and \
                    compared[0].type == ARM_OP_REG and compared[1].type == ARM_OP_IMM and \
                    compared[1].imm == 0:
                guarded_register = compared[0].reg
        per_successor = {}
        for successor in edges[current]:
            facts = set(outgoing)
            if guarded_register is not None:
                target = operands[0].imm
                fallthrough = current + instruction.size
                if target != fallthrough and ((instruction.cc == ARM_CC_NE and successor == target) or
                                              (instruction.cc == ARM_CC_EQ and successor == fallthrough)):
                    facts.add((guarded_register, "nz"))
            frozen = frozenset(facts)
            per_successor[successor] = per_successor.get(successor, frozen) & frozen
        for successor, facts in per_successor.items():
            previous = states.get(successor)
            merged = facts if previous is None else previous & facts
            if merged != previous:
                states[successor] = merged
                pending.append(successor)
    for site in sites:
        if not {(ARM_REG_R0, "s16"), (ARM_REG_R1, "nz")} <= states.get(site, frozenset()):
            raise ValueError("signed remainder requires proven signed16 r0 and nonzero r1")
