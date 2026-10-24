#!/usr/bin/env python3
"""
rebuild.py - prove the split is lossless, and check the assembled ROM.

  python tools/rebuild.py            concatenate files/*.bin in manifest order
                                     and compare SHA1 against baserom.bin
  python tools/rebuild.py --armips   assemble asm/*.s with armips first, then
                                     compare that output instead
  python tools/rebuild.py --compiled [--output build/mixed.gba]
                                    mix freshly compiled symbols with original gaps

Byte-exactness matters more than speed here: if the concatenation does not
reproduce the base ROM, the split is wrong and nothing downstream is safe.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
from rompath import rom_path
import re
import subprocess
import sys
import tempfile

from match_evidence import data_snapshot, mapping_snapshot, report_matches, source_fingerprint
import inert_spin_profile as inert_spin
import software_double_profile as software_double
import function_thunk_profile as function_thunk
import switch_constants_profile as switch_constants

ROM_BASE = 0x08000000


def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def sha1(data):
    return hashlib.sha1(data).hexdigest().upper()


def file_state(path):
    digest = hashlib.sha1()
    size = 0
    with open(path, "rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
            size += len(chunk)
    return size, digest.hexdigest().upper()


def source_inventory(root):
    source_dir = root / "src"
    inventory = {}
    for path in sorted(source_dir.rglob("*")):
        if path.suffix.lower() != ".c":
            continue
        if not path.is_file() or \
                not re.fullmatch(r"[0-9A-F]{8}\.c", path.name):
            raise ValueError(f"invalid addressed source: {path.relative_to(root)}")
        address = int(path.stem, 16)
        if address in inventory:
            raise ValueError(f"duplicate source address: 0x{address:08X}")
        inventory[address] = source_fingerprint(root, address)
    if not inventory:
        raise ValueError("compiled rebuild requires at least one addressed source")
    return dict(sorted(inventory.items()))


def output_path(root, requested):
    if requested is None:
        return None
    candidate = root / requested
    if candidate.exists() or candidate.is_symlink():
        raise ValueError("--output refuses to overwrite an existing file")
    output = candidate.resolve()
    build = (root / "build").resolve()
    if build not in output.parents or output == (root / "baserom.bin").resolve():
        raise ValueError("--output must name a new file under the decomp build/ directory")
    if output.exists() or output.is_symlink():
        raise ValueError("--output refuses to overwrite an existing file")
    return output


def saved_profile_arguments(report, root, address):
    arguments = []
    if switch_constants.selected(report):
        arguments += ["--switch-profile", switch_constants.SELECTOR]
    if function_thunk.selected(report):
        arguments += ["--function-address-profile", function_thunk.SELECTOR]
    if software_double.selected(report):
        arguments += ["--software-double-profile", software_double.SELECTOR]
    if inert_spin.selected(report):
        arguments += ["--control-flow-profile", inert_spin.SELECTOR]
    if arguments and not report_matches(report, root, address):
        raise ValueError(f"0x{address:08X}: invalid saved profile report")
    return arguments


def compiled_rebuild(root, requested_output=None):
    root = Path(root)
    output = output_path(root, requested_output)
    baseline = Path(rom_path(str(root), required=False) or
                    (root / "baserom.bin"))
    baseline_state = file_state(baseline)
    inventory = source_inventory(root)
    mapping = mapping_snapshot(root)
    data_mapping = data_snapshot(root)
    index_path = root / "symbols/functions.txt"
    function_index = index_path.read_bytes() if index_path.is_file() else None
    profile_reports = {}

    def profile_inputs_unchanged():
        return not profile_reports or (index_path.read_bytes() == function_index and
               all(path.read_bytes() == report for path, report in profile_reports.items()))

    matcher = Path(__file__).with_name("match.py")
    build = root / "build"
    build.mkdir(exist_ok=True)
    print(f"base ROM : {baseline.name}\n  size   : {baseline_state[0]:,}\n"
          f"  sha1   : {baseline_state[1]}")
    payloads = []
    previous_end = ROM_BASE
    with tempfile.TemporaryDirectory(prefix="ffta_rebuild_", dir=build) as directory:
        for address in inventory:
            emitted = Path(directory) / f"{address:08X}.bin"
            report_path = root / "docs/match" / f"{address:08X}.md"
            report = report_path.read_bytes() if report_path.is_file() else b""
            arguments = saved_profile_arguments(report.decode("utf-8"), root, address)
            if arguments:
                profile_reports[report_path] = report
            result = subprocess.run(
                [sys.executable, str(matcher), "--root", str(root),
                 f"{address:08X}", "--no-write", "--emit", str(emitted), *arguments],
                capture_output=True, text=True)
            if result.returncode:
                detail = (result.stderr or result.stdout).strip()
                raise ValueError(f"0x{address:08X}: matching failed\n{detail}")
            if not emitted.is_file() or emitted.is_symlink():
                raise ValueError(f"0x{address:08X}: matcher emitted no regular payload")
            size = emitted.stat().st_size
            if not size or address < ROM_BASE or address + size > ROM_BASE + baseline_state[0]:
                raise ValueError(f"0x{address:08X}: compiled extent is empty or outside the ROM")
            if address < previous_end:
                raise ValueError(f"0x{address:08X}: compiled extents overlap")
            payload = emitted.read_bytes()
            if len(payload) != size:
                raise ValueError(f"0x{address:08X}: emitted payload changed while reading")
            payloads.append((address, payload))
            previous_end = address + size
            emitted.unlink()
            print(f"verified  0x{address:08X}: {size} compiled bytes", flush=True)
    if source_inventory(root) != inventory or file_state(baseline) != baseline_state or \
            mapping_snapshot(root) != mapping or data_snapshot(root) != data_mapping or not profile_inputs_unchanged():
        raise ValueError("source inventory, dependencies, mapping, profile evidence, or base ROM changed during compilation")

    stream = None
    output_created = False
    complete = False
    digest = hashlib.sha1()
    reference_digest = hashlib.sha1()
    position = 0

    def emit(data):
        digest.update(data)
        if stream is not None:
            stream.write(data)

    try:
        if output is not None:
            output.parent.mkdir(parents=True, exist_ok=True)
            stream = output.open("xb")
            output_created = True
        with baseline.open("rb") as original:
            for address, payload in payloads:
                offset = address - ROM_BASE
                while position < offset:
                    gap = original.read(min(1024 * 1024, offset - position))
                    if not gap:
                        raise ValueError("base ROM ended before a compiled extent")
                    reference_digest.update(gap)
                    emit(gap)
                    position += len(gap)
                expected = original.read(len(payload))
                if len(expected) != len(payload):
                    raise ValueError("base ROM ended inside a compiled extent")
                if payload != expected:
                    first = next(index for index, pair in enumerate(zip(payload, expected))
                                 if pair[0] != pair[1])
                    raise ValueError(f"compiled byte mismatch at 0x{address + first:08X}")
                reference_digest.update(expected)
                emit(payload)
                position += len(payload)
            while gap := original.read(1024 * 1024):
                reference_digest.update(gap)
                emit(gap)
                position += len(gap)
        rebuilt_state = (position, digest.hexdigest().upper())
        if rebuilt_state != baseline_state or \
                reference_digest.hexdigest().upper() != baseline_state[1]:
            raise ValueError("mixed rebuild length or SHA1 differs from the initial base ROM")
        if stream is not None:
            stream.close()
            stream = None
            if file_state(output) != rebuilt_state:
                raise ValueError("written mixed rebuild failed its read-back check")
        if source_inventory(root) != inventory or file_state(baseline) != baseline_state or \
                mapping_snapshot(root) != mapping or data_snapshot(root) != data_mapping or not profile_inputs_unchanged():
            raise ValueError("source inventory, dependencies, mapping, profile evidence, or base ROM changed during rebuild")
        compiled_bytes = sum(len(payload) for _, payload in payloads)
        print(f"\nrebuilt  : {position:,} bytes (partial mixed C/ROM build)\n"
              f"  compiled functions : {len(payloads):,}\n"
              f"  compiled bytes     : {compiled_bytes:,}\n"
              f"  original bytes     : {position - compiled_bytes:,}\n"
              f"  sha1               : {rebuilt_state[1]}")
        if output is not None:
            print(f"  output             : {output}")
        print("\nOK - partial mixed C/ROM rebuild is byte-exact; unmatched bytes remain original")
        complete = True
        return 0
    finally:
        try:
            if stream is not None:
                stream.close()
        finally:
            if output_created and not complete:
                output.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--armips", action="store_true")
    mode.add_argument("--compiled", action="store_true")
    parser.add_argument("--output", help="new output file under decomp build/ (relative to decomp root)")
    args = parser.parse_args()
    if args.output and not args.compiled:
        parser.error("--output requires --compiled")
    here = repo_root(args.root)
    if args.compiled:
        try:
            return compiled_rebuild(here, args.output)
        except (OSError, ValueError) as error:
            print(f"compiled rebuild failed: {error}", file=sys.stderr)
            return 1
    base_file = rom_path(here)
    base = open(base_file, "rb").read()
    manifest = json.load(open(os.path.join(here, "asm", "manifest.json")))

    print(f"base ROM : {os.path.basename(base_file)}")
    print(f"  size   : {len(base):,}")
    print(f"  sha1   : {sha1(base)}")

    if args.armips:
        out = os.path.join(here, "build", "ffta.gba")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        script = os.path.join(here, "asm", "ffta.s")
        cmd = ["armips", script]
        print(f"\nassembling: {' '.join(cmd)}")
        try:
            subprocess.run(cmd, check=True, cwd=here)
        except FileNotFoundError:
            sys.exit("armips not found: install it first (see tools/bootstrap.sh)")
        built = open(out, "rb").read()
    else:
        built = bytearray()
        for part in manifest["parts"]:
            data = open(os.path.join(here, part["path"]), "rb").read()
            built += data
        built = bytes(built)

    print(f"\nrebuilt  : {len(built):,} bytes from {len(manifest['parts'])} parts")
    print(f"  sha1   : {sha1(built)}")

    if built == base:
        print("\nOK - the split reproduces the base ROM byte for byte")
        return 0

    print("\nMISMATCH")
    if len(built) != len(base):
        print(f"  size differs by {len(built) - len(base):+,}")
    n = min(len(built), len(base))
    first = next((i for i in range(n) if built[i] != base[i]), n)
    print(f"  first difference at 0x{ROM_BASE + first:08X} "
          f"(file offset 0x{first:X})")
    for i in range(max(0, first - 8), min(n, first + 8)):
        mark = "<<" if i == first else "  "
        print(f"    {ROM_BASE+i:08X}  base {base[i]:02X}  built {built[i]:02X} {mark}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
