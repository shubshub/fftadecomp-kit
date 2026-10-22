"""Explicit mixed-return Thumb CFGs with only inert nonreturning self-branches."""

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


SCHEMA = "elf-symbol-thumb-mixed-return-inert-spin-v1"
SELECTOR = "mixed-return-inert-spin-v1"
CONTROL_FLOW = "mixed verified returns and closed inert Thumb self-spins; termination not proved"
SUMMARY = "every reachable node without a return path is a narrow unconditional self-branch"
REPLAY_TIMEOUT = 120
FORBIDDEN_MARKERS = ("* buffer", "* data symbols", "* unsigned division", "* signed remainder",
                     "* signed quotient", "* switches", "* switch manifest", "* switch proof",
                     "* function address", "* function buffer")
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


def fingerprint(address, data, manifest, source_digest, mapping, index):
    digest = hashlib.sha256()
    for payload in (SCHEMA.encode("ascii"), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode("utf-8"), source_digest.encode("ascii"),
                    hashlib.sha256(mapping).hexdigest().encode("ascii"),
                    hashlib.sha256(index).hexdigest().encode("ascii"), compiler_text().encode("ascii")):
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


def verify(data, address, rom, mapping, index, manifest):
    from match import function_address_target, uses_stack_frame, verify_leaf_instructions
    entries = validate_span(data, address, rom, mapping, index)
    if not isinstance(manifest, dict) or set(manifest) != {"calls", "frame", "spins"} or \
            type(manifest["frame"]) is not bool or not isinstance(manifest["calls"], list) or \
            not isinstance(manifest["spins"], list) or not manifest["spins"]:
        raise ValueError("invalid inert-spin manifest")
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
    previous = -1
    for offset in manifest["spins"]:
        if type(offset) is not int or offset <= previous or offset % 2 or \
                offset < 0 or offset + 2 > len(data):
            raise ValueError("inert-spin offsets must be ordered complete instructions")
        previous = offset
    context = {}
    instructions = verify_leaf_instructions(data, address, True, calls, inert_spin_context=context)
    if context["spins"] != manifest["spins"] or uses_stack_frame(instructions) != manifest["frame"]:
        raise ValueError("inert-spin manifest disagrees with the converged CFG")
    return instructions


def object_bytes(runner, workspace, args, original, address, mapping, rom):
    from match import allocated_text_only, function_record, function_address_target, link_calls
    fixed_configuration(args)
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
            if info & 255 != 10 or symbols is None or info >> 8 >= len(symbols):
                raise ValueError("inert spins exclude non-call relocations")
            target = symbols[info >> 8]
            function_address_target(target["name"], entries, address, symbol["size"], len(rom))
            if target["section"] or target["bind"] != 1 or target["type"] not in (0, 2) or \
                    target["value"] or sum(item["name"] == target["name"]
                                           for item in original["symbols"]) != 1:
                raise ValueError("inert-spin calls require unique undefined global functions")
    if original["relocations"]:
        data, calls, literals = link_calls(runner, workspace, args, original, address, mapping, len(rom), rom)
        if literals:
            raise ValueError("inert spins exclude data relocations")
        return data, calls
    if any(item["name"] and not item["section"] for item in original["symbols"]):
        raise ValueError("inert-spin leaf retains undefined symbols")
    return original["text"][:symbol["size"]], {}


def verify_source(root, address, data, rom, mapping, index, source_digest, manifest):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive inert-spin replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index:
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
                got, calls = object_bytes(runner, workspace, args, original, address, mapping, rom)
                if got != data or call_records(calls, address) != manifest.get("calls"):
                    raise ValueError("inert-spin report lacks fresh original-ELF provenance")
                instructions = verify(got, address, rom, mapping, index, manifest)
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("inert-spin captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or report_rom_path(root) != selected_rom or \
                Path(selected_rom).read_bytes() != rom:
            raise ValueError("inert-spin replay inputs changed")
        return instructions
    finally:
        _replay_active.reset(token)


def report_matches(report, root, address):
    from match_evidence import source_fingerprint, mapping_snapshot, report_rom_path, STACK_SUMMARY
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
        if mapping is None or single("* control flow: ") != CONTROL_FLOW or \
                single("* inert spins: ") != SUMMARY or \
                unquote("* compiler: ") != compiler_text() or \
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
        if manifest_text(manifest) != encoded_manifest:
            return False
        frames = [line for line in lines if marker_text(line).startswith("* stack frame")]
        if frames != ([f"* stack frame: {STACK_SUMMARY}"] if manifest.get("frame") is True else []):
            return False
        verdicts = [line for line in lines if re.match(
            r"\*\*[ \t]*(?:MATCH|NOT|HAND|IMPLAUSIBLE)\b", marker_text(line))]
        if single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                verdicts != [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                unquote("* inert spin proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        verify_source(root, address, data, rom, mapping, index, source_digest, manifest)
        return report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
