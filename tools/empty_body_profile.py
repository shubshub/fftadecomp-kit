"""Evidence-bound exception for one canonical empty C function."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import plausible
import software_double_profile as software_double
from inert_spin_profile import index_snapshot


SCHEMA = "elf-symbol-thumb-empty-v1"
SUMMARY = "canonical empty void function; exact complete Thumb bx lr"
BODY = bytes.fromhex("7047")


def source_path(root, address):
    candidates = list((Path(root) / "src").rglob(f"{address:08X}.c"))
    if len(candidates) != 1:
        raise ValueError("empty body requires one uniquely addressed source")
    source = candidates[0]
    text = source.read_text(encoding="utf-8")
    if any(re.search(pattern, text) for rule, _, pattern, _ in plausible.RULES if rule == "placeholder"):
        raise ValueError("empty body cannot contain placeholder markers, including comments")
    code = plausible.strip_comments_and_strings(text)
    if re.fullmatch(r"\s*void\s+func_" + f"{address:08X}" +
                    r"\s*\(\s*void\s*\)\s*\{\s*\}\s*", code) is None:
        raise ValueError("empty body requires only void func_ADDRESS(void) {}")
    return source


def check_findings(result, root, address):
    from match import plausibility_result

    findings, allowed = plausibility_result(result, address)
    source = source_path(root, address)
    records = json.loads(result.stdout)["findings"]
    expected = plausible.check_file(source)
    if result.returncode != 1 or allowed or len(findings) != 1 or len(records) != 1 or \
            len(expected) != 1 or expected[0][1:3] != ("empty-body", "error") or \
            records[0] != {"file": str(source), "line": expected[0][0],
                           "rule": "empty-body", "severity": "error", "message": expected[0][3]}:
        raise ValueError("only the addressed empty-body finding can be discharged")
    return source


def verify_span(address, rom, mapping, index):
    entries, rows = software_double.indices(mapping, index)
    entry = software_double.span_record(address, address + len(BODY), entries, rows, rom)
    if entry["instrs"] != 1 or rom[address - 0x08000000:address - 0x08000000 + len(BODY)] != BODY:
        raise ValueError("empty body requires an exact indexed two-byte Thumb bx lr")


def verify_object(object_data, text_data, address, thumb, rom, mapping, index):
    from match import (allocated_text_only, elf_image, function_bytes,
                       function_record, verify_leaf_instructions)

    if not thumb:
        raise ValueError("empty body supports only Thumb")
    verify_span(address, rom, mapping, index)
    image = elf_image(object_data)
    allocated_text_only(image)
    symbol, offset = function_record(image, f"func_{address:08X}", address, True)
    functions = [record for record in image["symbols"] if record["type"] == 2]
    if functions != [symbol] or symbol["bind"] != 1 or offset != 0:
        raise ValueError("empty body requires one ordinary global function")
    body = function_bytes(object_data, text_data, f"func_{address:08X}", address, True)
    if body != BODY:
        raise ValueError("empty body requires the complete two-byte return symbol")
    instructions = verify_leaf_instructions(body, address, True)
    if len(instructions) != 1 or instructions[0].mnemonic != "bx" or instructions[0].op_str != "lr":
        raise ValueError("empty body requires one verified return instruction")


def metadata(root, address, source_digest, mapping, index):
    from match import DEFAULT_CC, DEFAULT_FLAGS
    from match_evidence import mapping_fingerprint

    return {
        "source": f"`{source_path(root, address).relative_to(root).as_posix()}`",
        "verification": f"`{SCHEMA}`",
        "source SHA-256": f"`{source_digest}`",
        "mapping SHA-256": f"`{mapping_fingerprint(mapping)}`",
        "function index SHA-256": f"`{mapping_fingerprint(index)}`",
        "control flow": "closed leaf CFG",
        "empty body": SUMMARY,
        "compiler": f"`{DEFAULT_CC} {DEFAULT_FLAGS}`",
        "verified extent": "complete ELF function symbol, including literal pools",
        "relocations": "none",
        "ROM bytes": f"`{BODY.hex()}` (2 bytes)",
        "compiled ": f"`{BODY.hex()}`",
        "source plausibility": "plausible",
        "hand-asm allow list": "not listed",
    }


def verify_source(root, address, source_digest, mapping, index):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object,
                       _run_replay_process)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, report_rom_path

    root = Path(root)
    selected_rom = report_rom_path(root)
    rom = Path(selected_rom).read_bytes()
    source = source_path(root, address)
    if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index:
        raise ValueError("empty-body replay inputs differ")
    verify_span(address, rom, mapping, index)
    args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                              objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
    (root / "build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ffta_empty_replay_", dir=root / "build") as directory:
        captured = Path(directory)
        for path in source_paths(root, address):
            destination = captured / path.relative_to(root)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(path.read_bytes())
        if source_fingerprint(captured, address) != source_digest:
            raise ValueError("empty-body source capture differs")
        runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=120)
        with runner.workspace() as workspace:
            object_data, text_data, _ = compile_object(
                runner, workspace, args, captured, address, source.relative_to(root).as_posix())
            verify_object(object_data, text_data, address, True, rom, mapping, index)
        checker = Path(__file__).resolve().with_name("plausible.py")
        result = _run_replay_process(
            [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
            [str(path) for path in source_paths(captured, address)], captured, 120)
        check_findings(result, captured, address)
        if source_fingerprint(captured, address) != source_digest:
            raise ValueError("empty-body captured source changed")
    if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
            index_snapshot(root) != index or report_rom_path(root) != selected_rom or \
            Path(selected_rom).read_bytes() != rom:
        raise ValueError("empty-body replay inputs changed")


def has_empty_body(root, address):
    from match_evidence import source_paths

    return any(finding[1] == "empty-body" for path in source_paths(root, address)
               for finding in plausible.check_file(path))


def report_matches(report, root, address):
    from match_evidence import source_fingerprint, mapping_snapshot, valid_match_verdict

    try:
        root = Path(root)
        if not valid_match_verdict(report) or "IMPLAUSIBLE" in report or "HAND-ASM" in report:
            return False
        mapping, index = mapping_snapshot(root), index_snapshot(root)
        source_digest = source_fingerprint(root, address)
        expected = metadata(root, address, source_digest, mapping, index)
        lines = report.splitlines()
        records = [line for line in lines if line.lstrip().startswith("*") and
                   not line.startswith("**")]
        if sorted(records) != sorted(f"* {key}: {value}" for key, value in expected.items()) or \
                "**MATCH - byte identical** - 2/2 bytes" not in lines:
            return False
        verify_source(root, address, source_digest, mapping, index)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False
