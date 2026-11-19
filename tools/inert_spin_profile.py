"""Explicit mixed-return Thumb CFGs whose nonreturning paths end in inert self-branches.

The same selector also admits, through an optional `loop` record, a function
with no return at all whose only cycle is one closed loop of typed calls.
"""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

import rom_mirror


SCHEMA = "elf-symbol-thumb-mixed-return-inert-spin-v1"
SELECTOR = "mixed-return-inert-spin-v1"
CONTROL_FLOW = "mixed verified returns and closed inert Thumb self-spins; termination not proved"
SUMMARY = "every reachable node without a return path is a narrow unconditional self-branch"
TAIL_SUMMARY = ("every reachable node without a return path is a narrow unconditional self-branch "
                "or a straight-line terminal-tail instruction that falls through to one")
LOOP_CONTROL_FLOW = "no reachable return; a straight-line prefix and one closed Thumb call loop without an exit"
LOOP_SUMMARY = ("no reachable node has a return path; a straight-line prefix falls through to one loop of typed "
                "Thumb calls and straight-line instructions without stores or stack changes, closed by a narrow "
                "unconditional backward branch")
DATA_POLICY = b"inert-spin-typed-data-v1"
REPLAY_TIMEOUT = 120
FORBIDDEN_MARKERS = ("* buffer", "* unsigned division", "* signed remainder",
                     "* signed quotient", "* switches", "* switch manifest", "* switch proof",
                     "* function address", "* function buffer", "* software double", "* function-address")
_replay_active = ContextVar("inert_spin_replay_active", default=False)


def marker_text(line):
    return re.sub(r"[ \t]+", " ", line.strip(" \t"))


def selected(report):
    lines = report.splitlines()
    markers = [line for line in lines if marker_text(line).startswith("* verification")]
    relevant = any(SCHEMA in line or marker_text(line).startswith("* inert spin") for line in lines)
    if not relevant:
        return False
    if markers != [f"* verification: `{SCHEMA}`"] or any(
            marker_text(line).startswith(FORBIDDEN_MARKERS) for line in lines):
        raise ValueError("mixed or malformed inert-spin profile selection")
    return True


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def compiler_text():
    from match import DEFAULT_CC, DEFAULT_FLAGS
    return f"{DEFAULT_CC} {DEFAULT_FLAGS}"


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def summary(manifest):
    if "loop" in manifest:
        return LOOP_SUMMARY
    return TAIL_SUMMARY if "tails" in manifest else SUMMARY


def control_flow(manifest):
    return LOOP_CONTROL_FLOW if "loop" in manifest else CONTROL_FLOW


def fingerprint(address, data, manifest, source_digest, mapping, index, data_mapping=None):
    digest = hashlib.sha256()
    payloads = [SCHEMA.encode("ascii"), address.to_bytes(4, "little"), data,
                manifest_text(manifest).encode("utf-8"), source_digest.encode("ascii"),
                hashlib.sha256(mapping).hexdigest().encode("ascii"),
                hashlib.sha256(index).hexdigest().encode("ascii"), compiler_text().encode("ascii")]
    if "data" in manifest:
        # Reports without typed data keep their original digest.
        if not isinstance(data_mapping, bytes):
            raise ValueError("inert-spin data fingerprint requires its exact data mapping")
        payloads += [DATA_POLICY, hashlib.sha256(data_mapping).hexdigest().encode("ascii")]
    for payload in payloads:
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("inert spins require the fixed approved toolchain configuration")


def validate_span(data, address, rom, mapping, index):
    from match import ROM_BASE
    if not isinstance(mapping, bytes) or not isinstance(index, bytes):
        raise ValueError("inert spins require both function-index snapshots")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("inert-spin function mapping must be a list")
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or len(callers) != 1 or int(callers[0]["rom"], 16) != address or \
            callers[0].get("mode") != "thumb" or int(callers[0]["end"], 16) != address + len(data) or \
            not data or len(data) % 2 or not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom) or \
            any(entry is not callers[0] and int(entry["rom"], 16) < address + len(data) and
                int(entry["end"], 16) > address for entry in entries):
        raise ValueError("inert spins require an exact unique nonoverlapping Thumb span")
    rows = [line.split() for line in index.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    selected_rows = [row for row in rows if int(row[0], 16) & ~1 == address & ~1]
    if len(selected_rows) != 1 or len(selected_rows[0]) < 3 or \
            int(selected_rows[0][0], 16) != address or \
            int(selected_rows[0][1], 16) != address + len(data) or \
            int(selected_rows[0][2]) != len(data) or \
            any(row is not selected_rows[0] and int(row[0], 16) < address + len(data) and
                int(row[1], 16) > address for row in rows):
        raise ValueError("inert-spin text index disagrees with the complete symbol")
    if data != rom[address - ROM_BASE:address - ROM_BASE + len(data)]:
        raise ValueError("inert-spin complete body differs from ROM")
    return entries


def call_records(calls, address):
    return [[site - address, f"func_{target:08X}"] for site, target in sorted(calls.items())]


def data_records(literals, data_mapping):
    from match import parse_data_symbols
    objects = parse_data_symbols(data_mapping)
    return [[offset, name, value - objects[name]] for offset, (name, value) in sorted(literals.items())]


def make_manifest(calls, address, instructions, context, literals=None, data_mapping=None):
    from match import uses_stack_frame
    manifest = {"calls": call_records(calls, address), "frame": uses_stack_frame(instructions),
                "spins": context["spins"]}
    # The records are optional, so reports without them keep their format and meaning.
    if context.get("tails"):
        manifest["tails"] = context["tails"]
    if context.get("loop") is not None:
        manifest["loop"] = context["loop"]
    if literals:
        manifest["data"] = data_records(literals, data_mapping)
    return manifest


def terminal_tails(instructions, edges, nonreturning):
    """Return the nonreturning nodes that are not narrow self-branches, once each is a tail.

    A tail instruction is straight-line: a two-byte instruction whose only
    successor is the next instruction, with no branch, call, interrupt,
    push/pop, SP or PC write. Every successor of a nonreturning node is
    nonreturning and a fallthrough strictly increases the address, so every
    tail chain is acyclic (the walk below also refuses any step that does not
    increase it); each must end at a `b .` encoding, which the caller verifies
    as an inert narrow self-branch.
    """
    from match import (CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, ARM_REG_PC, ARM_REG_SP,
                       thumb_stack_adjustment)
    tails = [current for current in nonreturning if bytes(instructions[current].bytes) != b"\xfe\xe7"]
    for current in tails:
        instruction = instructions[current]
        written = instruction.regs_access()[1]
        if instruction.size != 2 or tuple(edges[current]) != (current + 2,) or \
                any(group in instruction.groups for group in (CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP)) or \
                instruction.mnemonic in ("push", "pop") or thumb_stack_adjustment(instruction) is not None or \
                ARM_REG_PC in written or ARM_REG_SP in written:
            raise ValueError("terminal tails must be straight-line instructions without branches, calls "
                             "or stack-pointer changes")
    members = set(tails)
    for current in tails:
        while current in members:
            if edges[current][0] <= current:
                raise ValueError("terminal tail does not fall through towards a narrow self-branch")
            current = edges[current][0]
        if bytes(instructions[current].bytes) != b"\xfe\xe7":
            raise ValueError("terminal tail does not end in a narrow self-branch")
    return tails


def call_loop(instructions, edges, address, calls):
    """Return the loop record of a function that has no reachable return.

    The reachable instructions must be one contiguous run from the entry in
    which every instruction falls through to the next, except the last: a
    narrow unconditional `b` to a reachable instruction, the loop head, which
    can only be at or before it. That is exactly one cycle, with no exit. No instruction may
    branch, pop, interrupt or write PC other than through a typed call. Before
    the head, the prefix may also set up the frame (push, fixed SP adjustments)
    and make typed calls, all of which the walker has already checked. In the
    loop, every instruction other than the closing branch is a typed call or a
    straight-line instruction without a store, push or SP write, and at least
    one is a call, so a `b .` self-spin alone is not a call loop.
    """
    from match import (CS_AC_WRITE, CS_GRP_CALL, CS_GRP_INT, CS_GRP_JUMP, ARM_CC_AL, ARM_CC_INVALID,
                       ARM_INS_B, ARM_OP_IMM, ARM_OP_MEM, ARM_REG_PC, ARM_REG_SP)
    sites = sorted(instructions)
    branch = sites[-1]
    closing = instructions[branch]
    head = closing.operands[0].imm if len(closing.operands) == 1 and \
        closing.operands[0].type == ARM_OP_IMM else None
    if sites[0] != address or closing.id != ARM_INS_B or closing.size != 2 or \
            closing.cc not in (ARM_CC_AL, ARM_CC_INVALID) or head not in instructions or \
            tuple(edges[branch]) != (head,):
        raise ValueError("call loop must close with a narrow unconditional backward branch")
    for current, following in zip(sites, sites[1:]):
        instruction = instructions[current]
        call = current in calls
        written = instruction.regs_access()[1]
        # Capstone puts a BL in both the call and the jump group, and has it write PC.
        if following != current + instruction.size or tuple(edges[current]) != (following,) or \
                (CS_GRP_CALL in instruction.groups) != call or CS_GRP_INT in instruction.groups or \
                instruction.mnemonic == "pop" or not call and (CS_GRP_JUMP in instruction.groups or
                                                              ARM_REG_PC in written):
            raise ValueError("call loop code must fall straight through without branches, returns "
                             "or indirect transfers")
        if current >= head and not call and (
                instruction.mnemonic.startswith(("str", "stm", "push")) or ARM_REG_SP in written or
                any(operand.type == ARM_OP_MEM and operand.access & CS_AC_WRITE
                    for operand in instruction.operands)):
            raise ValueError("call loop excludes stores and stack-pointer changes")
    loop_calls = [site - address for site in sites if head <= site < branch and site in calls]
    if not loop_calls:
        raise ValueError("call loop requires a typed call inside the cycle")
    return {"branch": branch - address, "calls": loop_calls, "head": head - address}


def verify(data, address, rom, mapping, index, manifest, *, data_mapping=None):
    from match import (function_address_target, uses_stack_frame, verify_data_literals,
                       verify_leaf_instructions, parse_data_symbols, is_udivsi3_address, modsi3, divsi3,
                       umodsi3, ashldi3, software_double, software_float)
    entries = validate_span(data, address, rom, mapping, index)
    if not isinstance(manifest, dict) or not {"calls", "frame", "spins"} <= set(manifest) or \
            set(manifest) - {"calls", "frame", "spins", "data", "tails", "loop"} or \
            type(manifest["frame"]) is not bool or not isinstance(manifest["calls"], list) or \
            not isinstance(manifest["spins"], list) or not manifest["spins"] and "loop" not in manifest or \
            "tails" in manifest and (type(manifest["tails"]) is not list or not manifest["tails"]) or \
            "data" in manifest and (type(manifest["data"]) is not list or not manifest["data"] or
                                    not isinstance(data_mapping, bytes)):
        raise ValueError("invalid inert-spin manifest")
    loop = manifest.get("loop")
    if "loop" in manifest and (type(loop) is not dict or set(loop) != {"branch", "calls", "head"} or
                               type(loop["calls"]) is not list or
                               any(type(value) is not int for value in [loop["branch"], loop["head"]] +
                                   loop["calls"])):
        raise ValueError("invalid inert-spin call-loop record")
    calls = {}
    previous = -4
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid inert-spin call record")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or offset % 2 or \
                offset < previous + 4 or offset < 0 or offset + 4 > len(data):
            raise ValueError("inert-spin calls must be ordered nonoverlapping instructions")
        calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
        previous = offset
    for kind in ("spins", "tails"):
        previous = -1
        for offset in manifest.get(kind, []):
            if type(offset) is not int or offset <= previous or offset % 2 or \
                    offset < 0 or offset + 2 > len(data):
                raise ValueError("inert-spin offsets must be ordered complete instructions")
            previous = offset
    literals = {}
    if "data" in manifest:
        objects = parse_data_symbols(data_mapping)
        occupied = {byte for site in calls for byte in range(site - address, site - address + 4)}
        previous = -4
        for record in manifest["data"]:
            if type(record) is not list or len(record) != 3:
                raise ValueError("invalid inert-spin data binding")
            offset, name, addend = record
            if type(offset) is not int or type(name) is not str or name not in objects or \
                    type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or \
                    offset < previous + 4 or offset < 0 or offset + 4 > len(data) or (address + offset) % 4 or \
                    occupied & set(range(offset, offset + 4)):
                raise ValueError("inert-spin data bindings require ordered aligned mapped words")
            value = objects[name] + addend
            if not 0 <= value <= 0xFFFFFFFF or address <= rom_mirror.canonical(value) < address + len(data) or \
                    is_udivsi3_address(value) or modsi3.reserved(value) or divsi3.reserved(value) or \
                    umodsi3.reserved(value) or ashldi3.reserved(value) or software_double.reserved(value) or \
                    software_float.reserved(value) or struct.unpack_from("<I", data, offset)[0] != value:
                raise ValueError("inert-spin data literal differs, references its own function or a runtime")
            literals[offset] = (name, value)
            previous = offset
    context = {"tails": [], "loop": None}
    instructions = verify_leaf_instructions(data, address, True, calls, inert_spin_context=context)
    if context["spins"] != manifest["spins"] or context["tails"] != manifest.get("tails", []) or \
            context["loop"] != manifest.get("loop") or \
            uses_stack_frame(instructions) != manifest["frame"]:
        raise ValueError("inert-spin manifest disagrees with the converged CFG")
    verify_data_literals(instructions, address, literals)
    return instructions


def object_bytes(runner, workspace, args, original, address, mapping, rom, data_mapping=None, data_relocations=None):
    from match import (allocated_text_only, function_record, function_address_target, link_calls,
                       parse_data_symbols)
    fixed_configuration(args)
    if data_relocations is not None and (type(data_relocations) is not dict or data_relocations):
        raise ValueError("inert-spin data provenance requires an empty collection")
    objects = parse_data_symbols(data_mapping) if data_relocations is not None else {}
    if original["type"] != 1:
        raise ValueError("inert spins require a relocatable original ELF")
    allocated_text_only(original)
    symbol, offset = function_record(original, f"func_{address:08X}", address, True)
    definitions = [item for item in original["symbols"] if item["type"] == 2 and item["section"]]
    padding = original["text"][symbol["size"]:]
    if definitions != [symbol] or offset or len(padding) > 3 or \
            any(padding) and not (symbol["size"] % 4 == 2 and padding == b"\xc0\x46") or \
            any(item["type"] == 1 or re.fullmatch(r"\$a(?:\..*)?", item["name"])
                for item in original["symbols"]):
        raise ValueError("inert spins require sole-function Thumb text ownership")
    entries = json.loads(mapping)
    for section_index in original["relocations"]:
        section = original["sections"][section_index]
        if section[1] != 9 or section[7] != original["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("inert spins require ordinary Thumb call relocations only")
        symbols = original["symbol_tables"].get(section[6])
        for position in range(0, section[5], 8):
            _, info = struct.unpack_from("<II", original["section_data"][section_index], position)
            if info & 255 not in (2, 10) or info & 255 == 2 and data_relocations is None or \
                    symbols is None or info >> 8 >= len(symbols):
                raise ValueError("inert spins exclude non-call relocations")
            target = symbols[info >> 8]
            if info & 255 == 2:
                # Typed named data, bound and checked by the shared data linker below.
                if target["section"] or target["bind"] != 1 or target["type"] not in (0, 1) or \
                        target["value"] or target["name"] not in objects or \
                        sum(item["name"] == target["name"] for item in original["symbols"]) != 1:
                    raise ValueError("inert spins exclude function-address relocations"
                                     if target["name"].startswith("func_") else
                                     "inert-spin data requires one undefined mapped global object")
                continue
            function_address_target(target["name"], entries, address, symbol["size"], len(rom))
            if target["section"] or target["bind"] != 1 or target["type"] not in (0, 2) or \
                    target["value"] or sum(item["name"] == target["name"]
                                           for item in original["symbols"]) != 1:
                raise ValueError("inert-spin calls require unique undefined global functions")
    if original["relocations"]:
        data, calls, literals = link_calls(runner, workspace, args, original, address, mapping, len(rom), rom,
                                           data_mapping=data_mapping if data_relocations is not None else None)
        if literals:
            if data_relocations is None:
                raise ValueError("inert spins exclude data relocations")
            data_relocations.update(literals)
        return data, calls
    if any(item["name"] and not item["section"] for item in original["symbols"]):
        raise ValueError("inert-spin leaf retains undefined symbols")
    return original["text"][:symbol["size"]], {}


def verify_source(root, address, data, rom, mapping, index, source_digest, manifest, *, data_mapping=None):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object,
                       _run_replay_process, plausibility_result)
    from match_evidence import (source_paths, source_fingerprint, mapping_snapshot, report_rom_path,
                                data_snapshot)
    if _replay_active.get():
        raise ValueError("recursive inert-spin replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                "data" in manifest and data_snapshot(root) != data_mapping:
            raise ValueError("inert-spin replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("inert-spin replay ROM differs")
        validate_span(data, address, rom, mapping, index)
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_spin_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("inert-spin source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                literals = {}
                got, calls = object_bytes(runner, workspace, args, original, address, mapping, rom,
                                          data_mapping=data_mapping, data_relocations=literals)
                if got != data or call_records(calls, address) != manifest.get("calls") or \
                        (data_records(literals, data_mapping) if literals else None) != manifest.get("data"):
                    raise ValueError("inert-spin report lacks fresh original-ELF provenance")
                instructions = verify(got, address, rom, mapping, index, manifest, data_mapping=data_mapping)
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("inert-spin captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or report_rom_path(root) != selected_rom or \
                Path(selected_rom).read_bytes() != rom or \
                "data" in manifest and data_snapshot(root) != data_mapping:
            raise ValueError("inert-spin replay inputs changed")
        return instructions
    finally:
        _replay_active.reset(token)


def report_matches(report, root, address):
    from match_evidence import source_fingerprint, mapping_snapshot, report_rom_path, data_snapshot, STACK_SUMMARY
    lines = report.splitlines()

    def single(prefix):
        marker = prefix.split(":", 1)[0].rstrip()
        matches = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate inert-spin evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed quoted inert-spin evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate inert-spin manifest key")
            result[name] = value
        return result

    try:
        if not selected(report):
            return False
        spin_markers = {"* inert spins", "* inert spin manifest", "* inert spin proof SHA-256"}
        if any(marker_text(line).startswith("* inert spin") and
               line.split(":", 1)[0] not in spin_markers for line in lines):
            return False
        mapping, index = mapping_snapshot(root), index_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or unquote("* compiler: ") != compiler_text() or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
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
        encoded_manifest = unquote("* inert spin manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if not isinstance(manifest, dict) or manifest_text(manifest) != encoded_manifest or \
                single("* control flow: ") != control_flow(manifest) or \
                single("* inert spins: ") != summary(manifest):
            return False
        objects = data_snapshot(root) if "data" in manifest else None
        if "data" in manifest and objects is None or \
                [line for line in lines if marker_text(line).startswith("* data symbols")] != \
                ([f"* data symbols SHA-256: `{hashlib.sha256(objects).hexdigest()}`"] if objects is not None else []):
            return False
        frames = [line for line in lines if marker_text(line).startswith("* stack frame")]
        if frames != ([f"* stack frame: {STACK_SUMMARY}"] if manifest.get("frame") is True else []):
            return False
        verdicts = [line for line in lines if re.match(
            r"\*\*[ \t]*(?:MATCH|NOT|HAND|IMPLAUSIBLE)\b", marker_text(line))]
        if single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                verdicts != [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                unquote("* inert spin proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, data_mapping=objects):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        verify_source(root, address, data, rom, mapping, index, source_digest, manifest, data_mapping=objects)
        return report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
