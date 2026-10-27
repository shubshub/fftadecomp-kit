"""Pinned agbcc float helpers with local runtime CFG/ABI evidence."""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

SCHEMA = "elf-symbol-thumb-sf-mul-fixuns-target-v1"
RUNTIME = "agbcc-thumb-sf-mul-fixuns-extend-lt-closure-v2"
ABI = "agbcc-thumb-sf-df-mixed-result-r0-r1-v2"
SEMANTICS = "target-machine-state-v1"
SUMMARY = ("pinned returning Thumb float multiply/unsigned conversion/extension/comparison closure; "
           "entry RAM is a state input; unrestricted IEEE semantics not proved")
OPERATIONS = {"__mulsf3": 0x08143CEC, "__fixunssfsi": 0x081428AC,
              "__extendsfdf2": 0x0814432C, "__ltdf2": 0x0814379C}
ROM_SHA256 = "43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19"
# Complete bodies include every reachable literal and exclude inter-function fill.
# Counts are reachable instructions, not a linear decode through literal words.
IDENTITIES = (
    (0x081428AC, 0x081428E4, 19, "829913a602873567de7f3d182be10fffa86ef45d8ed742b1b4517152402b96a9"),
    (0x08142A20, 0x08142A94, 56, "f642a6a21668da428cbb8304f9710064aca75ff16130add649b86ff4b9e73be3"),
    (0x08142BE8, 0x08142D34, 139, "38aa6a8e47b81d402a011d733156fc99229f9fdf028aee34f5920b3464a5bb00"),
    (0x08142D34, 0x08142E10, 97, "8fb09220b22c69e18dc39f19c8645de020c1d658f48894a5dfe3d68e79f0fb25"),
    (0x08143528, 0x0814362A, 129, "29c2eb0eb1f6a9b824ecfb2bd55d4b006da808992cb6e61f9998057d23c280eb"),
    (0x0814379C, 0x081437EA, 36, "93610c0c0b2e7dd92aba95bfb314fe742a48924abf71d8658d9c01d118af2360"),
    (0x08143958, 0x0814397E, 18, "1fee8cea7a0257110504e0c2d041ed07796499458591a61cd941f8475c7f238b"),
    (0x081439C8, 0x08143A84, 86, "765c352080a3d1f6c0da8210a214648596a5486760b3cedf7d6648fef32cae32"),
    (0x08143A84, 0x08143B02, 61, "d5efb6bd7cf27a8941c36f0b5483da598b2a48309bb282e2b431bcc8321dad39"),
    (0x08143B04, 0x08143C82, 186, "199d30f85b753970b05497963d593f1a8eefee6d51fb2ec4df257d7fba44d750"),
    (0x08143C84, 0x08143CB4, 20, "6426642ff2bd96abcc416bf0b95c40d1098f5e0ea53be0e6f8e88e3d7fb50b78"),
    (0x08143CEC, 0x08143E54, 171, "ddb81777890d79690a3c02c5d524f54fcf019175aa88f81f1355ef91fb70e10e"),
    (0x08143F44, 0x0814402C, 116, "081dc5f333941e61e9ee2ac24ee67ee5076ed1febd02317dd90aa7e2cd75552a"),
    (0x0814413C, 0x08144188, 35, "4a6dcd1364fa48fe4c6028182009503388ca8e55553366fba6ce0265fb818962"),
    (0x08144280, 0x081442EA, 50, "2014feb21890bddf5d00b8ca3ec17a16ed6c61b5de391b3c23abdd9002b1c9a4"),
    (0x0814432C, 0x0814435C, 22, "44270ed4d1de25e093330f5bca55b7b74e149968085e7f89bba389b77ed8dd91"),
    (0x08144378, 0x081443AE, 27, "a2d91a60b907f40dd3bafc448e79c2c4630ba7000195bb54f0f4b26e4e9d9faa"),
)
EDGES = (
    (0x081428B2, 0x0814413C), (0x081428BC, 0x08144280),
    (0x081428CC, 0x08143C84), (0x081428D0, 0x08144280),
    (0x08143C90, 0x08143A84), (0x08143C9A, 0x08143A84),
    (0x08143CA4, 0x08143B04), (0x08143CA8, 0x081439C8),
    (0x08143CFE, 0x08143A84), (0x08143D08, 0x08143A84),
    (0x08143DB4, 0x08142A20), (0x08143E3E, 0x081439C8),
    (0x08144148, 0x08143A84), (0x08144152, 0x08143A84),
    (0x0814417C, 0x08143F44), (0x0814428A, 0x08143A84),
    (0x08142C64, 0x08144378),
    (0x081437AC, 0x08142D34), (0x081437B6, 0x08142D34),
    (0x081437DE, 0x08143528), (0x08143970, 0x08142BE8),
    (0x08144336, 0x08143A84), (0x08144350, 0x08143958),
)
EXTENSION_CLOSURE = (0x08142BE8, 0x08142D34, 0x08143528, 0x0814379C,
                     0x08143958, 0x0814432C, 0x08144378)
FORBIDDEN = ("* buffer", "* unsigned division", "* unsigned remainder", "* signed remainder",
             "* signed quotient", "* software double", "* ashldi3", "* inert spin", "* empty body",
             "* switches", "* switch manifest", "* switch proof", "* function address",
             "* function-address", "* function buffer")
_replay_active = ContextVar("software_float_replay_active", default=False)


def reserved(address):
    return any(start <= address & ~1 < end for start, end, _, _ in IDENTITIES)


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("software_float requires the fixed approved toolchain configuration")


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def fingerprint(address, data, manifest, source_digest, mapping, index, data_mapping, rom):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    digest = hashlib.sha256()
    configuration = repr((DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS))
    for payload in (SCHEMA.encode(), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode(), source_digest.encode(), mapping, index,
                    data_mapping or b"", hashlib.sha256(rom).digest(), configuration.encode()):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def selected(report):
    from software_double_profile import marker_text
    lines = report.splitlines()
    if not any(SCHEMA in line or marker_text(line).startswith("* software float") for line in lines):
        return False
    profiles = [line for line in lines if marker_text(line).startswith("* verification")]
    if profiles != [f"* verification: `{SCHEMA}`"] or \
            any(marker_text(line).startswith(FORBIDDEN) for line in lines):
        raise ValueError("mixed or malformed software_float profile selection")
    return True


def ownership(rom, mapping, index, start, end):
    # Reuse the strict JSON/text ownership parser and complete-span validator.
    from software_double_profile import indices, span_record
    if not isinstance(rom, bytes):
        raise ValueError("software_float requires a ROM snapshot")
    try:
        entries, rows = indices(mapping, index)
        return entries, span_record(start, end, entries, rows, rom)
    except ValueError as error:
        raise ValueError(
            f"software_float requires exact unique nonoverlapping Thumb spans/counts in both indexes: "
            f"[0x{start:08X}, 0x{end:08X})") from error


def dependency_records():
    return [[start, end, digest] for start, end, _, digest in IDENTITIES]


def prove_runtime(rom, entries, start, end, count, dependencies, *, call_edges=None,
                  scalar_entries=None, allowed_writes=None, stack_load_widths=(4,),
                  stack_store_widths=(4,), stack_input_words=(), stack_adjusted_returns=False):
    """Prove this pinned body's local returns and callee-saved/write ABI.

    This is deliberately separate from the caller verifier. Loads are target
    machine state inputs, not invented IEEE values. Stores must stay in local
    stack words or a bounded formal output argument. A dependency's output
    footprint is applied only after its own CFG and register restoration pass.
    Optional policies let pinned closures reuse the same interpreter;
    defaults retain word-only stack accesses and the four-word write bound.
    """
    import struct
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_JUMP, CS_GRP_CALL
    from capstone.arm_const import (ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM,
                                   ARM_REG_R0, ARM_REG_R3, ARM_REG_R4, ARM_REG_R11,
                                   ARM_REG_R12, ARM_REG_SP, ARM_REG_LR, ARM_REG_PC)
    from analyze import refine_function
    body = rom[start - 0x08000000:end - 0x08000000]
    layout = refine_function(body, start, entries, max_bytes=end - start,
                             max_instructions=1024, rom_end=0x08000000 + len(rom),
                             stack_adjusted_returns=stack_adjusted_returns)
    expected_calls = {site: target for site, target in
                      (EDGES if call_edges is None else call_edges) if start <= site < end}
    public = OPERATIONS.values() if scalar_entries is None else scalar_entries
    permitted_writes = ({(number, offset, 4) for number in range(4) for offset in range(0, 16, 4)}
                        if allowed_writes is None else set(allowed_writes))
    if any(not set(widths) <= {1, 2, 4} or 4 not in widths
           for widths in (stack_load_widths, stack_store_widths)) or \
            any(type(offset) is not int or offset != 0 for offset in stack_input_words):
        raise ValueError("software-float runtime stack-access policy is unsupported")
    if not layout["cfg_closed"] or layout["partial_reasons"] or layout["instrs"] != count or \
            layout["candidate_extent"]["end"] != f"0x{end:08X}" or \
            {int(c["site"], 16): int(c["target"], 16) for c in layout["calls"]} != expected_calls:
        raise ValueError("software-float runtime local CFG/closure differs")
    for a, b in layout["gaps"]:
        a, b = int(a, 16), int(b, 16)
        if b - a != 2 or b % 4 or body[a - start:b - start] not in (b"\0\0", b"\xc0\x46"):
            raise ValueError("software-float runtime has an unproved body gap")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    instructions = {i.address: i for a, b in layout["code_ranges"]
                    for i in decoder.disasm(body[int(a, 16) - start:int(b, 16) - start], int(a, 16))}
    unknown = None
    initial = {r: ("entry", r, 0) for r in range(ARM_REG_R0, ARM_REG_R12 + 1)}
    initial[ARM_REG_LR] = ("entry", ARM_REG_LR, 0)
    initial[ARM_REG_SP] = ("stack", 0, 0)
    states, pending, edges, returns, writes = {start: (initial, {}, frozenset())}, [start], {}, set(), set()
    stack_reads = set()

    def adjusted(value, distance):
        if value is None:
            return None
        kind, base, offset = value
        if kind == "constant":
            return (kind, (base + distance) & 0xFFFFFFFF, 0)
        return (kind, base, offset + distance)

    while pending:
        site = pending.pop()
        instruction = instructions.get(site)
        if instruction is None:
            raise ValueError("software-float ABI flow leaves reachable code")
        registers, memory, saved = states[site]
        registers, memory, saved = dict(registers), dict(memory), set(saved)
        sp = registers[ARM_REG_SP][2]
        operands = instruction.operands
        regs = [op.reg for op in operands if op.type == ARM_OP_REG]

        def access(pointer, loading, value=None, width=4):
            if pointer is not None and pointer[0] == "stack":
                offset = pointer[2]
                if loading and width == 4 and offset in stack_input_words:
                    stack_reads.add((offset, width))
                    return unknown
                if width not in (stack_load_widths if loading else stack_store_widths) or \
                        offset % width or not sp <= offset <= -width:
                    raise ValueError("software-float runtime stack access exceeds its frame")
                if loading:
                    return memory.get(offset) if width == 4 else unknown
                if any(offset < slot + 4 and slot < offset + width for slot in saved):
                    raise ValueError("software-float runtime overwrites a saved register")
                if width == 4:
                    memory[offset] = value
                else:
                    for slot in memory:
                        if offset < slot + 4 and slot < offset + width:
                            memory[slot] = unknown
            elif not loading:
                if pointer is None or pointer[0] != "entry" or \
                        not ARM_REG_R0 <= pointer[1] <= ARM_REG_R3 or \
                        (pointer[1] - ARM_REG_R0, pointer[2], width) not in permitted_writes:
                    raise ValueError("software-float runtime has an unbounded external write")
                writes.add((pointer[1] - ARM_REG_R0, pointer[2], width))
            return unknown

        successors = (site + instruction.size,)
        mnemonic = instruction.mnemonic
        if mnemonic == "push":
            sp -= 4 * len(regs)
            for position, reg in enumerate(regs):
                memory[sp + position * 4] = registers.get(reg)
                saved.add(sp + position * 4)
            registers[ARM_REG_SP] = ("stack", 0, sp)
        elif mnemonic == "pop":
            for position, reg in enumerate(regs):
                offset = sp + position * 4
                if offset >= 0 or offset not in saved:
                    raise ValueError("software-float runtime pops outside its saved frame")
                registers[reg] = memory.pop(offset, None)
                saved.remove(offset)
            sp += 4 * len(regs)
            registers[ARM_REG_SP] = ("stack", 0, sp)
        elif mnemonic == "bx":
            if len(regs) != 1 or registers.get(regs[0]) != ("entry", ARM_REG_LR, 0) or sp or saved or \
                    any(registers.get(r) != ("entry", r, 0) for r in range(ARM_REG_R4, ARM_REG_R11 + 1)):
                raise ValueError("software-float runtime return/register restoration is unproved")
            returns.add(site)
            successors = ()
        elif mnemonic == "bl":
            target = expected_calls.get(site)
            if target not in dependencies or operands[0].imm != target:
                raise ValueError("software-float runtime call has no native dependency proof")
            for number, offset, width in dependencies[target]["writes"]:
                access(adjusted(registers.get(ARM_REG_R0 + number), offset), False, width=width)
            for offset, width in dependencies[target].get("stack_reads", ()):
                # A pinned fifth argument must be a fully written local word
                # in this caller, not its saved registers or incoming stack.
                slot = sp + offset
                if width != 4 or slot not in memory or slot in saved:
                    raise ValueError("software-float runtime stack argument is not established")
                access(("stack", 0, slot), True, width=width)
            for reg in (*range(ARM_REG_R0, ARM_REG_R3 + 1), ARM_REG_R12, ARM_REG_LR):
                registers[reg] = unknown
        elif mnemonic.startswith(("ldm", "stm")):
            pointer = registers.get(regs[0])
            for position, reg in enumerate(regs[1:]):
                address = adjusted(pointer, position * 4)
                if mnemonic.startswith("ldm"):
                    registers[reg] = access(address, True)
                else:
                    access(address, False, registers.get(reg))
            if instruction.writeback:
                registers[regs[0]] = adjusted(pointer, 4 * (len(regs) - 1))
        elif mnemonic.startswith(("ldr", "str")):
            mem = next((op.mem for op in operands if op.type == ARM_OP_MEM), None)
            loads = {4: "ldr", 2: "ldrh", 1: "ldrb"}
            stores = {4: "str", 2: "strh", 1: "strb"}
            if mem is None or mem.index or instruction.writeback or \
                    mnemonic not in (*(stores[width] for width in stack_store_widths),
                                     *(loads[width] for width in stack_load_widths)):
                raise ValueError("software-float runtime memory operation is unsupported")
            if mem.base == ARM_REG_PC:
                if mnemonic != "ldr":
                    raise ValueError("software-float runtime writes its literal pool")
                literal = ((site + 4) & ~3) + mem.disp
                registers[regs[0]] = ("constant", struct.unpack_from("<I", body, literal - start)[0], 0)
            else:
                pointer = adjusted(registers.get(mem.base), mem.disp)
                if mnemonic.startswith("ldr"):
                    width = next(width for width, name in loads.items() if name == mnemonic)
                    registers[regs[0]] = access(pointer, True, width=width)
                else:
                    width = next(width for width, name in stores.items() if name == mnemonic)
                    access(pointer, False, registers.get(regs[0]), width=width)
        elif mnemonic in ("mov", "movs", "add", "adds", "sub", "subs"):
            dest = regs[0]
            if mnemonic.startswith("mov"):
                value = registers.get(operands[1].reg) if operands[1].type == ARM_OP_REG else \
                    ("constant", operands[1].imm, 0)
            elif operands[-1].type == ARM_OP_IMM:
                source = dest if len(operands) == 2 else operands[1].reg
                distance = operands[-1].imm * (-1 if mnemonic.startswith("sub") else 1)
                value = adjusted(registers.get(source), distance)
            else:
                value = unknown
            if dest == ARM_REG_SP:
                if value is None or value[:2] != ("stack", 0) or value[2] > 0 or \
                        value[2] % 4 or any(value[2] > offset >= sp for offset in saved):
                    raise ValueError("software-float runtime has an irregular stack adjustment")
                memory = {offset: val for offset, val in memory.items() if offset >= value[2]}
            registers[dest] = value
        elif mnemonic.startswith("b"):
            if len(operands) != 1 or operands[0].type != ARM_OP_IMM:
                raise ValueError("software-float runtime has an unresolved branch")
            successors = (operands[0].imm,) + (() if mnemonic == "b" else successors)
        else:
            _, assigned = instruction.regs_access()
            if ARM_REG_PC in assigned or ARM_REG_SP in assigned or \
                    CS_GRP_CALL in instruction.groups or CS_GRP_JUMP in instruction.groups:
                raise ValueError("software-float runtime contains an unsupported transfer")
            for reg in assigned:
                registers[reg] = unknown
        edges[site] = successors
        outgoing = (registers, memory, frozenset(saved))
        for successor in successors:
            previous = states.get(successor)
            if previous is None:
                merged = outgoing
            else:
                if previous[0][ARM_REG_SP] != registers[ARM_REG_SP] or previous[2] != outgoing[2]:
                    raise ValueError("software-float runtime frame differs at a CFG join")
                merged = ({r: value if value == registers.get(r) else unknown for r, value in previous[0].items()},
                          {offset: value if value == memory[offset] else unknown
                           for offset, value in previous[1].items() if offset in memory}, previous[2])
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(instructions) != set(edges) or returns != {int(site, 16) for site in layout["returns"]}:
        raise ValueError("software-float runtime ABI proof omitted reachable instructions or returns")
    reaching = set(returns)
    while True:
        expanded = reaching | {site for site, targets in edges.items() if any(t in reaching for t in targets)}
        if expanded == reaching:
            break
        reaching = expanded
    if reaching != set(instructions):
        raise ValueError("software-float runtime has a region without a verified return path")
    if start in public and writes:
        raise ValueError("software-float public scalar helper has external writes")
    return {"writes": sorted(writes), "stack_reads": sorted(stack_reads),
            "returns": sorted(returns), "layout": layout}


def verify_identity(rom, mapping, index):
    from software_double_profile import indices, span_record
    if type(rom) is not bytes or hashlib.sha256(rom).hexdigest() != ROM_SHA256:
        raise ValueError("software float requires the approved complete ROM identity")
    entries, rows = indices(mapping, index)
    proofs = {}
    for start, end, count, digest in IDENTITIES:
        entry = span_record(start, end, entries, rows, rom)
        body = rom[start - 0x08000000:end - 0x08000000]
        if entry["instrs"] != count or hashlib.sha256(body).hexdigest() != digest:
            raise ValueError("software-float complete runtime identity differs")
    pending = {start for start, _, _, _ in IDENTITIES}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < next(end for a, end, _, _ in IDENTITIES if a == start))]
        if not ready:
            raise ValueError("software-float dependency closure is recursive or incomplete")
        for start in ready:
            end, count = next((end, count) for a, end, count, _ in IDENTITIES if a == start)
            policy = {}
            if start in EXTENSION_CLOSURE:
                policy = {"allowed_writes": tuple((1, offset, 4) for offset in range(0, 20, 4))
                          if start == 0x08142D34 else (), "stack_load_widths": (1, 2, 4)}
            if start == 0x08142BE8:
                policy["stack_store_widths"] = (1, 2, 4)
            if start == 0x08143958:
                policy.update(stack_input_words=(0,), stack_adjusted_returns=True)
            proofs[start] = prove_runtime(rom, entries, start, end, count, proofs, **policy)
            pending.remove(start)
    return proofs


def verify_context(data, address, calls, context):
    from software_double_profile import indices, span_record
    if type(context) is not tuple or len(context) != 4 or type(context[3]) is not dict or not context[3]:
        raise ValueError("software float requires an isolated canonical runtime context")
    rom, mapping, index, bindings = context
    verify_identity(rom, mapping, index)
    entries, rows = indices(mapping, index)
    span_record(address, address + len(data), entries, rows, rom)
    if reserved(address) or not data or address % 2 or len(data) % 2 or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("software-float caller requires exact complete mapped ROM bytes")
    if any(type(site) is not int or name not in OPERATIONS or calls.get(site) != OPERATIONS[name]
           for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("software-float canonical bindings are incomplete or mixed")
    from match import function_address_target
    for site, target in calls.items():
        if site not in bindings:
            function_address_target(f"func_{target:08X}", entries, address, len(data), len(rom))
            owners = [entry for entry in entries if int(entry["rom"], 16) == target]
            span_record(target, int(owners[0]["end"], 16), entries, rows, rom)


def make_manifest(calls, address, bindings, literals, data_mapping, instructions):
    from match import parse_data_symbols, uses_stack_frame
    objects = parse_data_symbols(data_mapping) if literals else {}
    return {"runtime": RUNTIME, "abi": ABI, "semantics": SEMANTICS,
            "calls": [[site - address, bindings.get(site, f"func_{target:08X}")]
                      for site, target in sorted(calls.items())],
            "data": [[offset, name, value - objects[name]]
                     for offset, (name, value) in sorted(literals.items())],
            "frame": uses_stack_frame(instructions), "dependencies": dependency_records()}


def verify(data, address, rom, mapping, index, data_mapping, manifest):
    import struct
    from capstone.arm_const import ARM_OP_MEM, ARM_REG_PC
    from match import (parse_data_symbols, uses_stack_frame,
                       verify_data_literals, verify_leaf_instructions, modsi3)
    if type(manifest) is not dict or \
            set(manifest) != {"runtime", "abi", "semantics", "calls", "data", "frame", "dependencies"} or \
            manifest["runtime"] != RUNTIME or manifest["abi"] != ABI or \
            manifest["semantics"] != SEMANTICS or manifest["dependencies"] != dependency_records() or \
            type(manifest["frame"]) is not bool or \
            type(manifest["calls"]) is not list or type(manifest["data"]) is not list:
        raise ValueError("invalid software_float manifest")
    _, entry = ownership(rom, mapping, index, address, address + len(data))
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls, bindings, literals, occupied = {}, {}, {}, set()
    for kind in ("calls", "data"):
        previous = -1
        for record in manifest[kind]:
            if type(record) is not list or len(record) != (2 if kind == "calls" else 3):
                raise ValueError("invalid software_float binding")
            offset, name = record[:2]
            if type(offset) is not int or type(name) is not str or offset <= previous or \
                    offset < 0 or offset + 4 > len(data) or \
                    (address + offset) % (2 if kind == "calls" else 4):
                raise ValueError("software_float bindings must be ordered aligned complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if occupied & positions:
                raise ValueError("software_float bindings overlap")
            occupied.update(positions)
            if kind == "calls":
                if name in OPERATIONS:
                    calls[address + offset] = OPERATIONS[name]
                    bindings[address + offset] = name
                else:
                    from match import function_address_target
                    from software_double_profile import indices
                    entries, _ = indices(mapping, index)
                    calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
            else:
                addend = record[2]
                if name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid software_float mapped object")
                value = objects[name] + addend
                # parse_data_symbols rejects reserved bases; validate addends too.
                parse_data_symbols(json.dumps({name: f"0x{value:08X}"}).encode())
                if not modsi3.supported_data(objects[name], len(rom)) or \
                        not modsi3.supported_data(value, len(rom)) or \
                        address <= value < address + len(data) or \
                        struct.unpack_from("<I", data, offset)[0] != value:
                    raise ValueError("software_float literal differs or uses a forbidden address")
                literals[offset] = (name, value)
    instructions = verify_leaf_instructions(
        data, address, True, calls, float_context=(rom, mapping, index, bindings))
    if uses_stack_frame(instructions) != manifest["frame"] or len(instructions) != entry["instrs"]:
        raise ValueError("software_float frame/count differs from the verified CFG")
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
        raise ValueError("software_float address-domain literals require exact mapped-data coverage")
    return instructions


def verify_source(root, address, data, rom, mapping, index, data_mapping, source_digest, manifest):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object, link_calls,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive software_float replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                data_snapshot(root) != data_mapping:
            raise ValueError("software_float replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("software_float replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_software_float_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("software_float source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=120)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                bindings = {}
                got, calls, literals = link_calls(
                    runner, workspace, args, original, address, mapping, len(rom), rom,
                    data_mapping=data_mapping, float_bindings=bindings, float_index=index)
                instructions = verify(got, address, rom, mapping, index, data_mapping, manifest)
                if got != data or make_manifest(calls, address, bindings, literals,
                                                data_mapping, instructions) != manifest:
                    raise ValueError("software_float lacks fresh canonical ELF provenance")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, 120)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("software_float captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
            raise ValueError("software_float replay inputs changed")
        return instructions
    finally:
        _replay_active.reset(token)


def report_matches(report, root, address):
    from software_double_profile import marker_text, unique_members
    from match import DEFAULT_CC, DEFAULT_FLAGS
    from match_evidence import (CALL_SUMMARY, STACK_SUMMARY, source_fingerprint,
                                mapping_snapshot, data_snapshot, report_rom_path)
    try:
        if not selected(report):
            return False
        lines = report.splitlines()
        markers = {"* software float", "* software float manifest", "* software float proof SHA-256"}
        if any(marker_text(line).startswith("* software float") and
               line.split(":", 1)[0] not in markers for line in lines):
            return False

        def single(prefix):
            marker = prefix.split(":", 1)[0].rstrip()
            found = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
            if len(found) != 1 or not found[0].startswith(prefix):
                raise ValueError("missing, malformed or duplicate software_float evidence")
            return found[0][len(prefix):]

        def unquote(prefix):
            value = single(prefix)
            if len(value) < 2 or value[0] != "`" or value[-1] != "`":
                raise ValueError("malformed software_float evidence")
            return value[1:-1]

        mapping, index, objects = mapping_snapshot(root), index_snapshot(root), data_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                single("* control flow: ") != CALL_SUMMARY or single("* software float: ") != SUMMARY or \
                unquote("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or single("* source plausibility: ") != "plausible" or \
                single("* hand-asm allow list: ") != "not listed":
            return False
        candidates = list((Path(root) / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or unquote("* source: ") != candidates[0].relative_to(root).as_posix():
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* software float manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if manifest_text(manifest) != encoded_manifest:
            return False
        frames = [line for line in lines if marker_text(line).startswith("* stack frame")]
        if frames != ([f"* stack frame: {STACK_SUMMARY}"] if manifest.get("frame") is True else []):
            return False
        object_lines = [line for line in lines if marker_text(line).startswith("* data symbols")]
        if object_lines != ([f"* data symbols SHA-256: `{hashlib.sha256(objects).hexdigest()}`"]
                            if manifest.get("data") and objects is not None else []):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        if unquote("* ROM SHA-256: ") != hashlib.sha256(rom).hexdigest() or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                [line for line in lines if marker_text(line).startswith("**MATCH")] != \
                [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                unquote("* software float proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, objects, rom):
            return False
        verify_source(root, address, data, rom, mapping, index, objects, source_digest, manifest)
        return True
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
