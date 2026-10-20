"""Source-bound metadata for cached, offline match reports."""

import hashlib
from pathlib import Path
import re


SCHEMA = "elf-symbol-cfg-leaf-v2"
LINKED_SCHEMA = "elf-symbol-thumb-calls-v1"
CALL_SUMMARY = "direct Thumb BL with ordinary ARM ABI call summaries"
FRAMED_SCHEMA = "elf-symbol-thumb-frame-v1"
FRAMED_LINKED_SCHEMA = "elf-symbol-thumb-frame-calls-v1"
STACK_SUMMARY = "fixed Thumb frames and bounded stack aliases with return provenance"
DATA_SCHEMA = "elf-symbol-thumb-data-v1"
FRAMED_DATA_SCHEMA = "elf-symbol-thumb-frame-data-v1"
BUFFER_SCHEMA = "elf-symbol-thumb-frame-buffer-calls-v1"
BUFFER_SUMMARY = "ROM-checked bounded non-escaping register buffer arguments"
STACK_BUFFER_SCHEMA = "elf-symbol-thumb-frame-buffer-calls-v2"
STACK_BUFFER_SUMMARY = "ROM-checked bounded register and stack buffer arguments with returned alias provenance"


def mapping_snapshot(root):
    try:
        return (Path(root) / "config" / "functions.json").read_bytes()
    except FileNotFoundError:
        return None


def mapping_fingerprint(snapshot):
    return hashlib.sha256(snapshot).hexdigest() if snapshot is not None else None


def data_snapshot(root):
    try:
        return (Path(root) / "config" / "data_symbols.json").read_bytes()
    except FileNotFoundError:
        return None


def source_paths(root, address):
    root = Path(root)
    paths = {q for q in (root / "src").rglob(f"{address:08X}.c")}
    include = root / "include"
    if include.is_dir():
        paths.update(path for path in include.rglob("*") if path.is_file())
    paths.update((root / "src").rglob("*.h"))
    return sorted(paths)


def source_fingerprint(root, address):
    root = Path(root)
    digest = hashlib.sha256()
    for path in source_paths(root, address):
        name = path.relative_to(root).as_posix().encode("utf-8")
        data = path.read_bytes()
        digest.update(len(name).to_bytes(8, "little"))
        digest.update(name)
        digest.update(len(data).to_bytes(8, "little"))
        digest.update(data)
    return digest.hexdigest()


def verify_dependencies(preprocessed, root, address):
    allowed = {path.resolve() for path in source_paths(root, address)}
    observed = set()
    for name in re.findall(r'^#\s+\d+\s+"([^"\n]+)"', preprocessed, re.MULTILINE):
        if name.startswith("<") and name.endswith(">"):
            continue
        dependency = (Path(root) / name).resolve()
        if dependency not in allowed:
            raise ValueError(f"untracked include dependency: {name}; move shared inputs under include/")
        observed.add(dependency)
    observed = {Path(p).resolve() for p in observed}
    if not any(q.resolve() in observed
           for q in (Path(root) / "src").rglob(f"{address:08X}.c")):
        raise ValueError("preprocessor output lacks source dependency markers; do not use -P")


def buffer_report_matches(lines, root, address, mapping, stack_arguments=False):
    from match import BufferCallProof, verify_leaf_instructions

    compiled = [line for line in lines if line.startswith("* compiled :")]
    fingerprints = [line for line in lines if line.startswith("* buffer proof SHA-256:")]
    summaries = [line for line in lines if line.startswith("* buffer calls:")]
    summary = STACK_BUFFER_SUMMARY if stack_arguments else BUFFER_SUMMARY
    if len(compiled) != 1 or len(fingerprints) != 1 or \
            summaries != [f"* buffer calls: {summary}"]:
        return False
    encoded = re.fullmatch(r"\* compiled : `([0-9a-f]+)`", compiled[0])
    if encoded is None:
        return False
    try:
        rom = (Path(root) / "baserom.bin").read_bytes()
        data = bytes.fromhex(encoded[1])
        proof = BufferCallProof(rom, mapping, stack_arguments=stack_arguments)
        if proof.span(address) != data:
            return False
        verdict = f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"
        if verdict not in lines:
            return False
        verify_leaf_instructions(data, address, True, buffer_proof=proof,
                                 call_resolver=proof.target)
        return bool(proof.dependencies) and \
            fingerprints == [f"* buffer proof SHA-256: `{proof.fingerprint()}`"]
    except (OSError, ValueError, KeyError, TypeError, RecursionError):
        return False


def report_matches(report, root, address):
    lines = report.splitlines()
    profiles = [line for line in lines if line.startswith("* verification:")]
    profile_valid = profiles in ([f"* verification: `{SCHEMA}`"],
                                 [f"* verification: `{FRAMED_SCHEMA}`"])
    if profiles in ([f"* verification: `{LINKED_SCHEMA}`"],
                    [f"* verification: `{FRAMED_LINKED_SCHEMA}`"],
                    [f"* verification: `{BUFFER_SCHEMA}`"],
                    [f"* verification: `{STACK_BUFFER_SCHEMA}`"]):
        snapshot = mapping_snapshot(root)
        profile_valid = (snapshot is not None and
                         f"* mapping SHA-256: `{mapping_fingerprint(snapshot)}`" in lines and
                         f"* control flow: {CALL_SUMMARY}" in lines)
        if profiles in ([f"* verification: `{BUFFER_SCHEMA}`"],
                        [f"* verification: `{STACK_BUFFER_SCHEMA}`"]):
            profile_valid = profile_valid and buffer_report_matches(
                lines, root, address, snapshot,
                stack_arguments=profiles == [f"* verification: `{STACK_BUFFER_SCHEMA}`"])
    if profiles in ([f"* verification: `{DATA_SCHEMA}`"],
                    [f"* verification: `{FRAMED_DATA_SCHEMA}`"]):
        functions = mapping_snapshot(root)
        data = data_snapshot(root)
        summaries = [line for line in lines if line.startswith("* control flow:")]
        profile_valid = (functions is not None and data is not None and
                         f"* mapping SHA-256: `{mapping_fingerprint(functions)}`" in lines and
                         f"* data symbols SHA-256: `{mapping_fingerprint(data)}`" in lines and
                         summaries in ([f"* control flow: {CALL_SUMMARY}"],
                                       ["* control flow: closed leaf CFG"]))
    if profiles in ([f"* verification: `{FRAMED_SCHEMA}`"],
                    [f"* verification: `{FRAMED_LINKED_SCHEMA}`"],
                    [f"* verification: `{FRAMED_DATA_SCHEMA}`"],
                    [f"* verification: `{BUFFER_SCHEMA}`"],
                    [f"* verification: `{STACK_BUFFER_SCHEMA}`"]):
        profile_valid = profile_valid and f"* stack frame: {STACK_SUMMARY}" in lines
    verdict = re.search(r"^\*\*MATCH - byte identical\*\* - ([0-9]+)/([0-9]+) bytes$",
                        report, re.MULTILINE)
    return (profile_valid and
            f"* source SHA-256: `{source_fingerprint(root, address)}`" in lines and
            "* source plausibility: plausible" in lines and
            "* relocations: none" in lines and verdict is not None and
            int(verdict[1]) > 0 and verdict[1] == verdict[2])
