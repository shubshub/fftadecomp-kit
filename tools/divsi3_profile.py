"""Pinned Thumb signed quotient with positive constant divisors."""

import hashlib
import json

SCHEMA = "elf-symbol-thumb-divsi3-positive-constant-v1"
SUMMARY = "pinned Thumb signed quotient with CFG-proven positive signed32 constant divisors"
RUNTIME = "agbcc-thumb-divsi3-v1"
ADDRESS = 0x081426B8
IDENTITIES = (
    (ADDRESS, 0x0814274A,
     "80b13b14c17b297e6c92a50aeddcacdffbe951729bcb1290e205055950655884"),
    (0x0814274C, 0x0814274E,
     "abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c"),
)


def reserved(address):
    return any(start <= address & ~1 < end for start, end, _ in IDENTITIES)


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
        raise ValueError("signed quotient requires ROM and mapping snapshots")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("signed quotient requires a function mapping")
    for start, end, digest in IDENTITIES:
        candidates = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
        if len(candidates) != 1 or int(candidates[0]["rom"], 16) != start or \
                int(candidates[0]["end"], 16) != end or candidates[0].get("mode") != "thumb" or \
                not 0x08000000 <= start < end <= 0x08000000 + len(rom) or \
                any(entry is not candidates[0] and int(entry["rom"], 16) < end and
                    int(entry["end"], 16) > start for entry in entries):
            raise ValueError("signed quotient requires exact unique nonoverlapping runtime spans")
        if hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() != digest:
            raise ValueError("signed quotient runtime or dependency identity differs")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    dependency = next(decoder.disasm(rom[0x142742:0x142746], 0x08142742, count=1), None)
    if dependency is None or dependency.id != ARM_INS_BL or dependency.size != 4 or \
            len(dependency.operands) != 1 or dependency.operands[0].type != ARM_OP_IMM or \
            dependency.operands[0].imm != 0x0814274C:
        raise ValueError("signed quotient zero-path dependency differs")


def verify_context(data, address, calls, context):
    if not isinstance(context, tuple) or len(context) != 4 or \
            not isinstance(context[2], dict) or not context[2] or \
            not isinstance(context[3], dict) or context[3]:
        raise ValueError("signed quotient requires a fresh isolated runtime context")
    rom, mapping, bindings, _ = context
    verify_identity(rom, mapping)
    if set(bindings.values()) != {"__divsi3"} or \
            any(type(site) is not int or calls.get(site) != ADDRESS for site in bindings) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("signed quotient call bindings are incomplete or mixed")
    entries = json.loads(mapping)
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or reserved(address) or len(callers) != 1 or \
            int(callers[0]["rom"], 16) != address or callers[0].get("mode") != "thumb" or \
            int(callers[0]["end"], 16) != address + len(data) or \
            not 0x08000000 <= address < address + len(data) <= 0x08000000 + len(rom) or \
            any(entry is not callers[0] and int(entry["rom"], 16) < address + len(data) and
                int(entry["end"], 16) > address for entry in entries) or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("signed quotient caller requires exact complete mapped ROM bytes")


def prove_divisors(instructions, edges, address, sites):
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_LSL,
                                   ARM_OP_IMM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R1,
                                   ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)

    caller_clobbered = frozenset((ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3,
                                 ARM_REG_R12, ARM_REG_LR))
    states = {address: {}}
    pending = [address]
    while pending:
        current = pending.pop()
        instruction = instructions[current]
        incoming = states[current]
        outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            for register in caller_clobbered:
                outgoing.pop(register, None)
        else:
            _, written = instruction.regs_access()
            for register in written:
                outgoing.pop(register, None)
            operands = instruction.operands
            if instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and instruction.size == 2 and \
                    operands and operands[0].type == ARM_OP_REG:
                value = None
                if instruction.mnemonic in ("mov", "movs") and len(operands) == 2:
                    if operands[1].type == ARM_OP_IMM:
                        value = operands[1].imm & 0xFFFFFFFF
                    elif operands[1].type == ARM_OP_REG:
                        value = incoming.get(operands[1].reg)
                elif instruction.id == ARM_INS_LSL and len(operands) == 3 and \
                        operands[1].type == ARM_OP_REG and operands[2].type == ARM_OP_IMM and \
                        0 <= operands[2].imm <= 31 and operands[1].reg in incoming:
                    value = (incoming[operands[1].reg] << operands[2].imm) & 0xFFFFFFFF
                if value is not None:
                    outgoing[operands[0].reg] = value
        for successor in edges[current]:
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: value for register, value in previous.items()
                if outgoing.get(register) == value}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    divisors = {}
    for site in sorted(sites):
        divisor = states.get(site, {}).get(ARM_REG_R1)
        if type(divisor) is not int or not 1 <= divisor <= 0x7FFFFFFF:
            raise ValueError("signed quotient requires a CFG-proven positive signed32 constant in r1")
        divisors[site] = divisor
    return divisors
