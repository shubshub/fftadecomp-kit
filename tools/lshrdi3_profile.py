"""Canonical agbcc split-word logical right shift, with target-machine call semantics."""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

NAME = "lshrdi3"
SCHEMA = "elf-symbol-thumb-lshrdi3-target-v1"
RUNTIME = "agbcc-thumb-lshrdi3-v1"
ABI = "agbcc-thumb-di-r0-r1-shift-r2-v1"
SEMANTICS = "unsigned64-right-shift-count0-63-v1"
SUMMARY = "pinned returning Thumb split-word logical right shift; CFG-proven unsigned C count domain 0..63"
ADDRESS, END, COUNT = 0x08144378, 0x081443AE, 27
DIGEST = "a2d91a60b907f40dd3bafc448e79c2c4630ba7000195bb54f0f4b26e4e9d9faa"
FORBIDDEN = ("* buffer", "* unsigned division", "* unsigned remainder", "* signed remainder",
             "* signed quotient", "* software double", "* inert spin", "* empty body",
             "* switches", "* switch manifest", "* switch proof", "* function address",
             "* function-address", "* function buffer", "* ashldi3", "* software float")
_replay_active = ContextVar("lshrdi3_replay_active", default=False)


def reserved(address):
    return ADDRESS <= address & ~1 < END


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("lshrdi3 requires the fixed approved toolchain configuration")


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
    if not any(SCHEMA in line or marker_text(line).startswith("* lshrdi3") for line in lines):
        return False
    profiles = [line for line in lines if marker_text(line).startswith("* verification")]
    if profiles != [f"* verification: `{SCHEMA}`"] or \
            any(marker_text(line).startswith(FORBIDDEN) for line in lines):
        raise ValueError("mixed or malformed lshrdi3 profile selection")
    return True


def ownership(rom, mapping, index, start, end):
    # Reuse the strict JSON/text ownership parser and complete-span validator.
    from software_double_profile import indices, span_record
    if not isinstance(rom, bytes):
        raise ValueError("lshrdi3 requires a ROM snapshot")
    try:
        entries, rows = indices(mapping, index)
        return entries, span_record(start, end, entries, rows, rom)
    except ValueError as error:
        raise ValueError(
            f"lshrdi3 requires exact unique nonoverlapping Thumb spans/counts in both indexes: "
            f"[0x{start:08X}, 0x{end:08X})") from error


def verify_identity(rom, mapping, index):
    from match import verify_leaf_instructions
    _, entry = ownership(rom, mapping, index, ADDRESS, END)
    body = rom[ADDRESS - 0x08000000:END - 0x08000000]
    if entry["instrs"] != COUNT or hashlib.sha256(body).hexdigest() != DIGEST:
        raise ValueError("lshrdi3 complete runtime identity differs")
    # All three shift cases return through the saved LR and restore r4-r6.
    # No arbitrary external ABI assumption is used for this pinned helper.
    instructions = verify_leaf_instructions(body, ADDRESS, True)
    if len(instructions) != COUNT:
        raise ValueError("lshrdi3 runtime return/count proof differs")


def verify_context(data, address, calls, context):
    if type(context) is not tuple or len(context) != 4 or \
            type(context[3]) is not dict or not context[3]:
        raise ValueError("lshrdi3 requires an isolated canonical runtime context")
    rom, mapping, index, bindings = context
    verify_identity(rom, mapping, index)
    ownership(rom, mapping, index, address, address + len(data))
    if reserved(address) or not data or address % 2 or len(data) % 2 or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("lshrdi3 caller requires exact complete mapped ROM bytes")
    if any(target != ADDRESS for target in calls.values()) or \
            set(bindings.values()) != {"__lshrdi3"} or \
            any(type(site) is not int or calls.get(site) != ADDRESS for site in bindings) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("lshrdi3 call bindings are incomplete or mixed")


def make_manifest(calls, address, bindings, literals, data_mapping, instructions):
    from match import parse_data_symbols, uses_stack_frame
    objects = parse_data_symbols(data_mapping) if literals else {}
    return {"runtime": RUNTIME, "abi": ABI, "semantics": SEMANTICS,
            "calls": [[site - address, bindings.get(site, f"func_{target:08X}")]
                      for site, target in sorted(calls.items())],
            "data": [[offset, name, value - objects[name]]
                     for offset, (name, value) in sorted(literals.items())],
            "frame": uses_stack_frame(instructions)}


def verify(data, address, rom, mapping, index, data_mapping, manifest):
    import struct
    from capstone.arm_const import ARM_OP_MEM, ARM_REG_PC
    from match import (parse_data_symbols, uses_stack_frame,
                       verify_data_literals, verify_leaf_instructions, modsi3)
    if type(manifest) is not dict or \
            set(manifest) != {"runtime", "abi", "semantics", "calls", "data", "frame"} or \
            manifest["runtime"] != RUNTIME or manifest["abi"] != ABI or \
            manifest["semantics"] != SEMANTICS or type(manifest["frame"]) is not bool or \
            type(manifest["calls"]) is not list or type(manifest["data"]) is not list:
        raise ValueError("invalid lshrdi3 manifest")
    _, entry = ownership(rom, mapping, index, address, address + len(data))
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls, bindings, literals, occupied = {}, {}, {}, set()
    for kind in ("calls", "data"):
        previous = -1
        for record in manifest[kind]:
            if type(record) is not list or len(record) != (2 if kind == "calls" else 3):
                raise ValueError("invalid lshrdi3 binding")
            offset, name = record[:2]
            if type(offset) is not int or type(name) is not str or offset <= previous or \
                    offset < 0 or offset + 4 > len(data) or \
                    (address + offset) % (2 if kind == "calls" else 4):
                raise ValueError("lshrdi3 bindings must be ordered aligned complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if occupied & positions:
                raise ValueError("lshrdi3 bindings overlap")
            occupied.update(positions)
            if kind == "calls":
                if name == "__lshrdi3":
                    calls[address + offset] = ADDRESS
                    bindings[address + offset] = name
                else:
                    raise ValueError("lshrdi3 excludes other call targets")
            else:
                addend = record[2]
                if name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid lshrdi3 mapped object")
                value = objects[name] + addend
                # parse_data_symbols rejects reserved bases; validate addends too.
                parse_data_symbols(json.dumps({name: f"0x{value:08X}"}).encode())
                if not modsi3.supported_data(objects[name], len(rom)) or \
                        not modsi3.supported_data(value, len(rom)) or \
                        address <= value < address + len(data) or \
                        struct.unpack_from("<I", data, offset)[0] != value:
                    raise ValueError("lshrdi3 literal differs or uses a forbidden address")
                literals[offset] = (name, value)
    instructions = verify_leaf_instructions(
        data, address, True, calls, ashldi3_context=(rom, mapping, index, bindings))
    if uses_stack_frame(instructions) != manifest["frame"] or len(instructions) != entry["instrs"]:
        raise ValueError("lshrdi3 frame/count differs from the verified CFG")
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
        raise ValueError("lshrdi3 address-domain literals require exact mapped-data coverage")
    return instructions


def verify_source(root, address, data, rom, mapping, index, data_mapping, source_digest, manifest):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object, link_calls,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive lshrdi3 replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                data_snapshot(root) != data_mapping:
            raise ValueError("lshrdi3 replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("lshrdi3 replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_lshrdi3_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("lshrdi3 source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=120)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                from plausible import strip_comments_and_strings
                preprocessed = runner.read_binary(f"{workspace}/f.i").decode("utf-8")
                if re.search(r"\b__lshrdi3\b", strip_comments_and_strings(preprocessed)):
                    raise ValueError("lshrdi3 requires compiler-generated shifts, not source runtime aliases")
                bindings = {}
                got, calls, literals = link_calls(
                    runner, workspace, args, original, address, mapping, len(rom), rom,
                    data_mapping=data_mapping, ashldi3_bindings=bindings, ashldi3_index=index)
                instructions = verify(got, address, rom, mapping, index, data_mapping, manifest)
                if got != data or make_manifest(calls, address, bindings, literals,
                                                data_mapping, instructions) != manifest:
                    raise ValueError("lshrdi3 lacks fresh canonical ELF provenance")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, 120)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("lshrdi3 captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
            raise ValueError("lshrdi3 replay inputs changed")
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
        markers = {"* lshrdi3", "* lshrdi3 manifest", "* lshrdi3 proof SHA-256"}
        if any(marker_text(line).startswith("* lshrdi3") and
               line.split(":", 1)[0] not in markers for line in lines):
            return False

        def single(prefix):
            marker = prefix.split(":", 1)[0].rstrip()
            found = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
            if len(found) != 1 or not found[0].startswith(prefix):
                raise ValueError("missing, malformed or duplicate lshrdi3 evidence")
            return found[0][len(prefix):]

        def unquote(prefix):
            value = single(prefix)
            if len(value) < 2 or value[0] != "`" or value[-1] != "`":
                raise ValueError("malformed lshrdi3 evidence")
            return value[1:-1]

        mapping, index, objects = mapping_snapshot(root), index_snapshot(root), data_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                single("* control flow: ") != CALL_SUMMARY or single("* lshrdi3: ") != SUMMARY or \
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
        encoded_manifest = unquote("* lshrdi3 manifest: ")
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
                unquote("* lshrdi3 proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, objects, rom):
            return False
        verify_source(root, address, data, rom, mapping, index, objects, source_digest, manifest)
        return True
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False


def prove_counts(instructions, edges, address, sites, data):
    """Conservative signed32 intervals prove each incoming r2 is in 0..63.

    Facts survive register copies and bounded, nonwrapping add/subtract. Only
    adjacent CMP/branch pairs with a unique predecessor narrow a successor;
    unknown writes, calls and widening discard facts rather than guessing.
    """
    import struct
    from capstone import CS_GRP_CALL
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_CC_EQ, ARM_CC_NE,
                                   ARM_CC_GE, ARM_CC_GT, ARM_CC_LE, ARM_CC_LT,
                                   ARM_CC_HS, ARM_CC_HI, ARM_CC_LS, ARM_CC_LO,
                                   ARM_INS_B, ARM_INS_CMP, ARM_OP_IMM, ARM_OP_REG,
                                   ARM_OP_MEM, ARM_REG_PC, ARM_REG_R2)
    from match import CALLER_CLOBBERED
    top = (-0x80000000, 0x7fffffff)
    predecessors = {current: set() for current in instructions}
    for current, successors in edges.items():
        for successor in successors:
            predecessors[successor].add(current)
    states, updates, pending = {address: {}}, {}, [address]

    def operand_range(operand, facts):
        if operand.type == ARM_OP_REG:
            return facts.get(operand.reg, top)
        if operand.type == ARM_OP_IMM:
            value = operand.imm & 0xffffffff
            value = value if value < 0x80000000 else value - 0x100000000
            return value, value
        return top

    while pending:
        current = pending.pop()
        ins = instructions[current]
        incoming = states[current]
        outgoing = dict(incoming)
        operands = ins.operands
        if CS_GRP_CALL in ins.groups:
            for register in CALLER_CLOBBERED:
                outgoing.pop(register, None)
        else:
            _, written = ins.regs_access()
            for register in written:
                outgoing.pop(register, None)
            if ins.cc in (ARM_CC_AL, ARM_CC_INVALID) and ins.size == 2 and operands and \
                    operands[0].type == ARM_OP_REG:
                result = top
                if ins.mnemonic in ('mov', 'movs') and len(operands) == 2:
                    result = operand_range(operands[1], incoming)
                elif ins.mnemonic in ('add', 'adds', 'sub', 'subs') and len(operands) in (2, 3):
                    left = operand_range(operands[-2], incoming)
                    right = operand_range(operands[-1], incoming)
                    if ins.mnemonic.startswith('add'):
                        result = left[0] + right[0], left[1] + right[1]
                    else:
                        result = left[0] - right[1], left[1] - right[0]
                    if not top[0] <= result[0] <= result[1] <= top[1]:
                        result = top
                elif ins.mnemonic in ('and', 'ands') and len(operands) == 2:
                    masks = [operand_range(operand, incoming) for operand in operands]
                    limits = [low for low, high in masks if low == high and 0 <= low <= top[1]]
                    if limits:
                        result = 0, min(limits)
                elif ins.mnemonic == 'ldr' and len(operands) == 2 and \
                        operands[1].type == ARM_OP_MEM and operands[1].mem.base == ARM_REG_PC and \
                        not operands[1].mem.index:
                    literal = ((current + 4) & ~3) + operands[1].mem.disp
                    # The enclosing CFG already proves complete referenced words.
                    value = struct.unpack_from('<i', data, literal - address)[0]
                    result = value, value
                if result != top:
                    outgoing[operands[0].reg] = result
        guard = None
        if ins.id == ARM_INS_B and ins.cc not in (ARM_CC_AL, ARM_CC_INVALID) and \
                predecessors[current] == {current - 2} and operands[0].imm != current + ins.size:
            comparison = instructions[current - 2]
            compared = comparison.operands
            if comparison.id == ARM_INS_CMP and len(compared) == 2 and \
                    compared[0].type == ARM_OP_REG:
                value = operand_range(compared[1], incoming)
                if value[0] == value[1]:
                    guard = compared[0].reg, value[0]
        for successor in edges[current]:
            facts = dict(outgoing)
            if guard is not None:
                register, value = guard
                low, high = facts.get(register, top)
                taken = successor == operands[0].imm
                condition = ins.cc
                if not taken:
                    condition = {ARM_CC_EQ: ARM_CC_NE, ARM_CC_NE: ARM_CC_EQ,
                                 ARM_CC_GE: ARM_CC_LT, ARM_CC_LT: ARM_CC_GE,
                                 ARM_CC_GT: ARM_CC_LE, ARM_CC_LE: ARM_CC_GT,
                                 ARM_CC_HS: ARM_CC_LO, ARM_CC_LO: ARM_CC_HS,
                                 ARM_CC_HI: ARM_CC_LS, ARM_CC_LS: ARM_CC_HI}.get(condition)
                if condition == ARM_CC_GE: low = max(low, value)
                elif condition == ARM_CC_GT: low = max(low, value + 1)
                elif condition == ARM_CC_LE: high = min(high, value)
                elif condition == ARM_CC_LT: high = min(high, value - 1)
                elif condition == ARM_CC_EQ: low, high = max(low, value), min(high, value)
                elif 0 <= value <= top[1] and condition in (ARM_CC_LO, ARM_CC_LS):
                    low, high = max(low, 0), min(high, value - (condition == ARM_CC_LO))
                elif 0 <= low <= high and 0 <= value <= top[1]:
                    if condition == ARM_CC_HS: low = max(low, value)
                    elif condition == ARM_CC_HI: low = max(low, value + 1)
                if low > high:
                    continue
                if (low, high) != top:
                    facts[register] = low, high
            previous = states.get(successor)
            if previous is not None:
                merged = {}
                for register in previous.keys() & facts.keys():
                    old, new = previous[register], facts[register]
                    value = min(old[0], new[0]), max(old[1], new[1])
                    if value != old:
                        key = successor, register
                        updates[key] = updates.get(key, 0) + 1
                        if updates[key] > 2:
                            value = top
                    if value != top:
                        merged[register] = value
                facts = merged
            if previous != facts:
                states[successor] = facts
                pending.append(successor)
    counts = {}
    for site in sites:
        count = states.get(site, {}).get(ARM_REG_R2, top)
        if not 0 <= count[0] <= count[1] <= 63:
            raise ValueError('lshrdi3 requires CFG-proven unsigned shift count 0..63 in r2')
        counts[site] = count
    return counts
