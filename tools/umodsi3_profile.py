"""Pinned Thumb unsigned remainder with nonzero unsigned constant divisors."""

import hashlib
import json

SCHEMA = "elf-symbol-thumb-umodsi3-constant-v1"
SUMMARY = "pinned Thumb unsigned remainder with CFG-proven nonzero unsigned32 constant divisors"
RUNTIME = "agbcc-thumb-umodsi3-v1"
ADDRESS = 0x08142B28
IDENTITIES = (
    (ADDRESS, 0x08142BE8,
     "dec75508b46380e474801d918a5bda44a20bc8ec8a9159dda7f5a5f8a4b02b61"),
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


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("unsigned remainder requires the fixed approved toolchain configuration")


def verify_identity(rom, mapping):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm_const import ARM_INS_BL, ARM_OP_IMM

    if not isinstance(rom, bytes) or not isinstance(mapping, bytes):
        raise ValueError("unsigned remainder requires ROM and mapping snapshots")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("unsigned remainder requires a function mapping")
    for start, end, digest in IDENTITIES:
        candidates = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
        if len(candidates) != 1 or int(candidates[0]["rom"], 16) != start or \
                int(candidates[0]["end"], 16) != end or candidates[0].get("mode") != "thumb" or \
                not 0x08000000 <= start < end <= 0x08000000 + len(rom) or \
                any(entry is not candidates[0] and int(entry["rom"], 16) < end and
                    int(entry["end"], 16) > start for entry in entries):
            raise ValueError("unsigned remainder requires exact unique nonoverlapping runtime spans")
        if hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() != digest:
            raise ValueError("unsigned remainder runtime or dependency identity differs")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    dependency = next(decoder.disasm(rom[0x142BE0:0x142BE4], 0x08142BE0, count=1), None)
    if dependency is None or dependency.id != ARM_INS_BL or dependency.size != 4 or \
            len(dependency.operands) != 1 or dependency.operands[0].type != ARM_OP_IMM or \
            dependency.operands[0].imm != 0x0814274C:
        raise ValueError("unsigned remainder zero-path dependency differs")


def verify_context(data, address, calls, context):
    if not isinstance(context, tuple) or len(context) != 4 or \
            not isinstance(context[2], dict) or not context[2] or \
            not isinstance(context[3], dict) or context[3]:
        raise ValueError("unsigned remainder requires a fresh isolated runtime context")
    rom, mapping, bindings, _ = context
    verify_identity(rom, mapping)
    if set(bindings.values()) != {"__umodsi3"} or \
            any(type(site) is not int or calls.get(site) != ADDRESS for site in bindings) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("unsigned remainder call bindings are incomplete or mixed")
    entries = json.loads(mapping)
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or reserved(address) or len(callers) != 1 or \
            int(callers[0]["rom"], 16) != address or callers[0].get("mode") != "thumb" or \
            int(callers[0]["end"], 16) != address + len(data) or \
            not 0x08000000 <= address < address + len(data) <= 0x08000000 + len(rom) or \
            any(entry is not callers[0] and int(entry["rom"], 16) < address + len(data) and
                int(entry["end"], 16) > address for entry in entries) or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("unsigned remainder caller requires exact complete mapped ROM bytes")


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
        if type(divisor) is not int or not 1 <= divisor <= 0xFFFFFFFF:
            raise ValueError("unsigned remainder requires a CFG-proven nonzero unsigned32 constant in r1")
        divisors[site] = divisor
    return divisors


def verify(data, address, rom, mapping, data_mapping, manifest):
    import struct
    from capstone.arm_const import ARM_OP_MEM, ARM_REG_PC
    from match import (function_address_target, is_udivsi3_address, modsi3, divsi3,
                       software_double, parse_data_symbols, uses_stack_frame,
                       verify_data_literals, verify_leaf_instructions)

    if type(manifest) is not dict or set(manifest) != {"runtime", "calls", "divisors", "data", "frame"} or \
            manifest["runtime"] != RUNTIME or type(manifest["frame"]) is not bool or \
            any(type(manifest[key]) is not list for key in ("calls", "divisors", "data")):
        raise ValueError("invalid unsigned remainder manifest")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("unsigned remainder requires a function mapping")
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls, bindings, literals = {}, {}, {}
    occupied = set()
    for kind in ("calls", "data"):
        previous = -1
        for record in manifest[kind]:
            if type(record) is not list or len(record) != (2 if kind == "calls" else 3):
                raise ValueError("invalid unsigned remainder binding")
            offset, name = record[:2]
            if type(offset) is not int or type(name) is not str or offset <= previous or \
                    offset < 0 or offset + 4 > len(data):
                raise ValueError("unsigned remainder bindings must be ordered complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if occupied & positions:
                raise ValueError("unsigned remainder bindings overlap")
            occupied.update(positions)
            if kind == "calls":
                if offset % 2:
                    raise ValueError("unsigned remainder call is misaligned")
                if name == "__umodsi3":
                    calls[address + offset] = ADDRESS
                    bindings[address + offset] = name
                else:
                    calls[address + offset] = function_address_target(
                        name, entries, address, len(data), len(rom))
            else:
                addend = record[2]
                if (address + offset) % 4 or name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid unsigned remainder object binding")
                value = objects[name] + addend
                if not 0 <= value <= 0xFFFFFFFF or address <= value < address + len(data) or \
                        not modsi3.supported_data(objects[name], len(rom)) or \
                        not modsi3.supported_data(value, len(rom)) or \
                        is_udivsi3_address(value) or modsi3.reserved(value) or divsi3.reserved(value) or \
                        reserved(value) or software_double.reserved(value) or \
                        struct.unpack_from("<I", data, offset)[0] != value:
                    raise ValueError("unsigned remainder literal differs or uses a forbidden address")
                literals[offset] = (name, value)
    expected = {}
    previous = -1
    for record in manifest["divisors"]:
        if type(record) is not list or len(record) != 2:
            raise ValueError("invalid unsigned remainder divisor")
        offset, divisor = record
        if type(offset) is not int or offset <= previous or address + offset not in bindings or \
                type(divisor) is not int or not 1 <= divisor <= 0xFFFFFFFF:
            raise ValueError("unsigned remainder requires ordered nonzero unsigned32 divisors")
        previous = offset
        expected[address + offset] = divisor
    if not bindings or set(expected) != set(bindings):
        raise ValueError("unsigned remainder divisors must cover every runtime call exactly once")
    observed = {}
    instructions = verify_leaf_instructions(
        data, address, True, calls, umodsi3_context=(rom, mapping, bindings, observed))
    if observed != expected or uses_stack_frame(instructions) != manifest["frame"]:
        raise ValueError("unsigned remainder divisor or frame evidence differs from the verified CFG")
    verify_data_literals(instructions, address, literals)
    address_literals = set()
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                if modsi3.address_literal(struct.unpack_from("<I", data, offset)[0]):
                    address_literals.add(offset)
    if address_literals != set(literals):
        raise ValueError("unsigned remainder address-domain literals require exact mapped-data coverage")
    return instructions
