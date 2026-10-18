"""Source-bound metadata for cached, offline match reports."""

import hashlib
from pathlib import Path
import re


SCHEMA = "elf-symbol-cfg-leaf-v2"
LINKED_SCHEMA = "elf-symbol-thumb-calls-v1"
CALL_SUMMARY = "direct Thumb BL with ordinary ARM ABI call summaries"


def mapping_snapshot(root):
    try:
        return (Path(root) / "config" / "functions.json").read_bytes()
    except FileNotFoundError:
        return None


def mapping_fingerprint(snapshot):
    return hashlib.sha256(snapshot).hexdigest() if snapshot is not None else None


def source_paths(root, address):
    root = Path(root)
    paths = {root / "src" / f"{address:08X}.c"}
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
    if (Path(root) / "src" / f"{address:08X}.c").resolve() not in observed:
        raise ValueError("preprocessor output lacks source dependency markers; do not use -P")


def report_matches(report, root, address):
    lines = report.splitlines()
    profiles = [line for line in lines if line.startswith("* verification:")]
    profile_valid = profiles == [f"* verification: `{SCHEMA}`"]
    if profiles == [f"* verification: `{LINKED_SCHEMA}`"]:
        snapshot = mapping_snapshot(root)
        profile_valid = (snapshot is not None and
                         f"* mapping SHA-256: `{mapping_fingerprint(snapshot)}`" in lines and
                         f"* control flow: {CALL_SUMMARY}" in lines)
    verdict = re.search(r"^\*\*MATCH - byte identical\*\* - ([0-9]+)/([0-9]+) bytes$",
                        report, re.MULTILINE)
    return (profile_valid and
            f"* source SHA-256: `{source_fingerprint(root, address)}`" in lines and
            "* source plausibility: plausible" in lines and
            "* relocations: none" in lines and verdict is not None and
            int(verdict[1]) > 0 and verdict[1] == verdict[2])
