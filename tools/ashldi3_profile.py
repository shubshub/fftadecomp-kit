"""Canonical agbcc split-word left shift, with target-machine call semantics."""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

SCHEMA = "elf-symbol-thumb-ashldi3-target-v1"
RUNTIME = "agbcc-thumb-ashldi3-v1"
ABI = "agbcc-thumb-di-r0-r1-shift-r2-v1"
SEMANTICS = "armv4t-register-shift-state-v1"
SUMMARY = "pinned returning Thumb split-word left shift; target-machine register-shift semantics"
ADDRESS, END, COUNT = 0x0814220C, 0x08142242, 27
DIGEST = "6a654c08094c50c91ace78cf2bf460ef7235fea0abafb0357b970163ff1faa52"
FORBIDDEN = ("* buffer", "* unsigned division", "* unsigned remainder", "* signed remainder",
             "* signed quotient", "* software double", "* inert spin", "* empty body",
             "* switches", "* switch manifest", "* switch proof", "* function address",
             "* function-address", "* function buffer")
_replay_active = ContextVar("ashldi3_replay_active", default=False)


def reserved(address):
    return ADDRESS <= address & ~1 < END


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("ashldi3 requires the fixed approved toolchain configuration")


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
    if not any(SCHEMA in line or marker_text(line).startswith("* ashldi3") for line in lines):
        return False
    profiles = [line for line in lines if marker_text(line).startswith("* verification")]
    if profiles != [f"* verification: `{SCHEMA}`"] or \
            any(marker_text(line).startswith(FORBIDDEN) for line in lines):
        raise ValueError("mixed or malformed ashldi3 profile selection")
    return True


def ownership(rom, mapping, index, start, end):
    # Reuse the strict JSON/text ownership parser and complete-span validator.
    from software_double_profile import indices, span_record
    if not isinstance(rom, bytes):
        raise ValueError("ashldi3 requires a ROM snapshot")
    try:
        entries, rows = indices(mapping, index)
        return entries, span_record(start, end, entries, rows, rom)
    except ValueError as error:
        raise ValueError(
            f"ashldi3 requires exact unique nonoverlapping Thumb spans/counts in both indexes: "
            f"[0x{start:08X}, 0x{end:08X})") from error


def verify_identity(rom, mapping, index):
    from match import verify_leaf_instructions
    _, entry = ownership(rom, mapping, index, ADDRESS, END)
    body = rom[ADDRESS - 0x08000000:END - 0x08000000]
    if entry["instrs"] != COUNT or hashlib.sha256(body).hexdigest() != DIGEST:
        raise ValueError("ashldi3 complete runtime identity differs")
    # All three shift cases return through the saved LR and restore r4-r6.
    # No arbitrary external ABI assumption is used for this pinned helper.
    instructions = verify_leaf_instructions(body, ADDRESS, True)
    if len(instructions) != COUNT:
        raise ValueError("ashldi3 runtime return/count proof differs")


def verify_context(data, address, calls, context):
    if type(context) is not tuple or len(context) != 4 or \
            type(context[3]) is not dict or not context[3]:
        raise ValueError("ashldi3 requires an isolated canonical runtime context")
    rom, mapping, index, bindings = context
    verify_identity(rom, mapping, index)
    ownership(rom, mapping, index, address, address + len(data))
    if reserved(address) or not data or address % 2 or len(data) % 2 or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("ashldi3 caller requires exact complete mapped ROM bytes")
    if any(target != ADDRESS for target in calls.values()) or \
            set(bindings.values()) != {"__ashldi3"} or \
            any(type(site) is not int or calls.get(site) != ADDRESS for site in bindings) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("ashldi3 call bindings are incomplete or mixed")


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
        raise ValueError("invalid ashldi3 manifest")
    _, entry = ownership(rom, mapping, index, address, address + len(data))
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls, bindings, literals, occupied = {}, {}, {}, set()
    for kind in ("calls", "data"):
        previous = -1
        for record in manifest[kind]:
            if type(record) is not list or len(record) != (2 if kind == "calls" else 3):
                raise ValueError("invalid ashldi3 binding")
            offset, name = record[:2]
            if type(offset) is not int or type(name) is not str or offset <= previous or \
                    offset < 0 or offset + 4 > len(data) or \
                    (address + offset) % (2 if kind == "calls" else 4):
                raise ValueError("ashldi3 bindings must be ordered aligned complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if occupied & positions:
                raise ValueError("ashldi3 bindings overlap")
            occupied.update(positions)
            if kind == "calls":
                if name == "__ashldi3":
                    calls[address + offset] = ADDRESS
                    bindings[address + offset] = name
                else:
                    raise ValueError("ashldi3 excludes other call targets")
            else:
                addend = record[2]
                if name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid ashldi3 mapped object")
                value = objects[name] + addend
                # parse_data_symbols rejects reserved bases; validate addends too.
                parse_data_symbols(json.dumps({name: f"0x{value:08X}"}).encode())
                if not modsi3.supported_data(objects[name], len(rom)) or \
                        not modsi3.supported_data(value, len(rom)) or \
                        address <= value < address + len(data) or \
                        struct.unpack_from("<I", data, offset)[0] != value:
                    raise ValueError("ashldi3 literal differs or uses a forbidden address")
                literals[offset] = (name, value)
    instructions = verify_leaf_instructions(
        data, address, True, calls, ashldi3_context=(rom, mapping, index, bindings))
    if uses_stack_frame(instructions) != manifest["frame"] or len(instructions) != entry["instrs"]:
        raise ValueError("ashldi3 frame/count differs from the verified CFG")
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
        raise ValueError("ashldi3 address-domain literals require exact mapped-data coverage")
    return instructions


def verify_source(root, address, data, rom, mapping, index, data_mapping, source_digest, manifest):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object, link_calls,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive ashldi3 replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                data_snapshot(root) != data_mapping:
            raise ValueError("ashldi3 replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("ashldi3 replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_ashldi3_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("ashldi3 source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=120)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                bindings = {}
                got, calls, literals = link_calls(
                    runner, workspace, args, original, address, mapping, len(rom), rom,
                    data_mapping=data_mapping, ashldi3_bindings=bindings, ashldi3_index=index)
                instructions = verify(got, address, rom, mapping, index, data_mapping, manifest)
                if got != data or make_manifest(calls, address, bindings, literals,
                                                data_mapping, instructions) != manifest:
                    raise ValueError("ashldi3 lacks fresh canonical ELF provenance")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, 120)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("ashldi3 captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
            raise ValueError("ashldi3 replay inputs changed")
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
        markers = {"* ashldi3", "* ashldi3 manifest", "* ashldi3 proof SHA-256"}
        if any(marker_text(line).startswith("* ashldi3") and
               line.split(":", 1)[0] not in markers for line in lines):
            return False

        def single(prefix):
            marker = prefix.split(":", 1)[0].rstrip()
            found = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
            if len(found) != 1 or not found[0].startswith(prefix):
                raise ValueError("missing, malformed or duplicate ashldi3 evidence")
            return found[0][len(prefix):]

        def unquote(prefix):
            value = single(prefix)
            if len(value) < 2 or value[0] != "`" or value[-1] != "`":
                raise ValueError("malformed ashldi3 evidence")
            return value[1:-1]

        mapping, index, objects = mapping_snapshot(root), index_snapshot(root), data_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                single("* control flow: ") != CALL_SUMMARY or single("* ashldi3: ") != SUMMARY or \
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
        encoded_manifest = unquote("* ashldi3 manifest: ")
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
                unquote("* ashldi3 proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, objects, rom):
            return False
        verify_source(root, address, data, rom, mapping, index, objects, source_digest, manifest)
        return True
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
