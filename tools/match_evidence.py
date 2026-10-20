"""Source-bound metadata for cached, offline match reports."""

import hashlib
import json
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
FUNCTION_ADDRESS_SCHEMA = "elf-symbol-thumb-function-addresses-v1"
FUNCTION_ADDRESS_SUMMARY = "zero-addend mapped Thumb function literals; relocation fidelity, not callback ABI"
SWITCH_SCHEMA = "elf-symbol-thumb-switches-v1"
SWITCH_SUMMARY = "one unsigned-guarded local Thumb word table with verified predecessor edges"
SWITCH_DATA_SCHEMA = "elf-symbol-thumb-switch-data-v1"
SWITCH_DATA_SUMMARY = "one guarded local Thumb table with one reachable interposed mapped object word"
PRELOADED_SWITCH_SCHEMA = "elf-symbol-thumb-preloaded-switch-v1"
PRELOADED_SWITCH_SUMMARY = "one preloaded guarded local Thumb table; backward default loop; termination not proved"
PRELOADED_SWITCH_CONTROL_FLOW = "closed leaf CFG; termination not proved"
BUFFER_SCHEMA = "elf-symbol-thumb-frame-buffer-calls-v1"
BUFFER_SUMMARY = "ROM-checked bounded non-escaping register buffer arguments"
STACK_BUFFER_SCHEMA = "elf-symbol-thumb-frame-buffer-calls-v2"
STACK_BUFFER_SUMMARY = "ROM-checked bounded register and stack buffer arguments with returned alias provenance"
UDIVSI3_SCHEMA = "elf-symbol-thumb-udivsi3-v1"
UDIVSI3_SUMMARY = "pinned Thumb unsigned division runtime with CFG-proven nonzero constant divisors"
UDIVSI3_RUNTIME = "agbcc-thumb-udivsi3-v1"


def udivsi3_manifest(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def udivsi3_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (UDIVSI3_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, udivsi3_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def udivsi3_report_matches(lines, root, address):
    from match import verify_udivsi3

    def single(prefix):
        marker = prefix.rstrip(" :-")
        children = ("* unsigned division manifest", "* unsigned division proof SHA-256") \
            if marker == "* unsigned division" else ()
        matches = [line for line in lines if line.lstrip().startswith(marker) and
                   not line.lstrip().startswith(children)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate division evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed division evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate division manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        if single("* verification: ") != f"`{UDIVSI3_SCHEMA}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_fingerprint(root, address) or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* unsigned division: ") != UDIVSI3_SUMMARY or \
                single("* control flow: ") != CALL_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(("* stack frame", "* buffer calls", "* buffer proof SHA-256",
                                              "* data symbols SHA-256", "* switches", "* switch manifest",
                                              "* switch proof SHA-256", "* function addresses",
                                              "* function address manifest", "* function address proof SHA-256"))
                    for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* unsigned division manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if udivsi3_manifest(manifest) != encoded_manifest:
            return False
        rom = (Path(root) / "baserom.bin").read_bytes()
        verify_udivsi3(data, address, rom, mapping, manifest)
        return (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* unsigned division proof SHA-256: ") ==
                udivsi3_fingerprint(address, data, manifest))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


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


def function_address_manifest(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def function_address_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (FUNCTION_ADDRESS_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, function_address_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def function_address_report_matches(lines, root, address):
    from match import verify_function_addresses

    def single(prefix):
        matches = [line for line in lines if line.startswith(prefix)]
        if len(matches) != 1:
            raise ValueError("missing or duplicate function-address evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed function-address evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate function-address manifest key")
            result[name] = value
        return result

    try:
        functions = mapping_snapshot(root)
        objects = data_snapshot(root)
        if functions is None or \
                unquote("* source SHA-256: ") != source_fingerprint(root, address) or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(functions) or \
                single("* function addresses: ") != FUNCTION_ADDRESS_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.startswith(("* stack frame:", "* buffer calls:", "* buffer proof SHA-256:"))
                    for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* function address manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if function_address_manifest(manifest) != encoded_manifest:
            return False
        if manifest.get("data"):
            if objects is None or unquote("* data symbols SHA-256: ") != mapping_fingerprint(objects):
                return False
        elif any(line.startswith("* data symbols SHA-256:") for line in lines):
            return False
        rom = (Path(root) / "baserom.bin").read_bytes()
        _, control_flow = verify_function_addresses(data, address, rom, functions, objects, manifest)
        return (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* function address proof SHA-256: ") ==
                function_address_fingerprint(address, data, manifest))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def switch_manifest(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def switch_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SWITCH_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, switch_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def switch_data_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SWITCH_DATA_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, switch_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def preloaded_switch_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (PRELOADED_SWITCH_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, switch_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def preloaded_switch_report_matches(lines, root, address):
    from match import verify_preloaded_switches

    def single(prefix):
        marker = "**MATCH" if prefix.startswith("**MATCH") else prefix.rstrip(" :")
        matches = [line for line in lines if line.lstrip().startswith(marker)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate preloaded switch evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed preloaded switch evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate preloaded switch manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        objects = data_snapshot(root)
        excluded = ("* stack frame", "* buffer calls", "* buffer proof SHA-256",
                    "* function addresses", "* function address manifest",
                    "* function address proof SHA-256", "* unsigned division")
        if mapping is None or objects is None or \
                single("* verification: ") != f"`{PRELOADED_SWITCH_SCHEMA}`" or \
                unquote("* source SHA-256: ") != source_fingerprint(root, address) or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                unquote("* data symbols SHA-256: ") != mapping_fingerprint(objects) or \
                single("* switches: ") != PRELOADED_SWITCH_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(excluded) for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* switch manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if switch_manifest(manifest) != encoded_manifest:
            return False
        rom = (Path(root) / "baserom.bin").read_bytes()
        _, control_flow = verify_preloaded_switches(data, address, rom, mapping, objects, manifest)
        return (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* switch proof SHA-256: ") ==
                preloaded_switch_fingerprint(address, data, manifest))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def switch_report_matches(lines, root, address, *, data_profile=False):
    from match import verify_switches

    def single(prefix):
        marker = prefix.rstrip(" :") if data_profile else prefix
        matches = [line for line in lines
                   if (line.lstrip() if data_profile else line).startswith(marker)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate switch evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed switch evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate switch manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        objects = data_snapshot(root) if data_profile else None
        summary = SWITCH_DATA_SUMMARY if data_profile else SWITCH_SUMMARY
        excluded = ("* stack frame:", "* buffer calls:", "* buffer proof SHA-256:",
                    "* function addresses:", "* function address manifest:",
                    "* function address proof SHA-256:")
        if data_profile:
            if single("* verification: ") != f"`{SWITCH_DATA_SCHEMA}`":
                return False
            excluded = tuple(prefix.rstrip(":") for prefix in excluded)
        if mapping is None or \
                unquote("* source SHA-256: ") != source_fingerprint(root, address) or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* switches: ") != summary or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any((line.lstrip() if data_profile else line).startswith(excluded)
                    for line in lines):
            return False
        if data_profile:
            if objects is None or unquote("* data symbols SHA-256: ") != mapping_fingerprint(objects):
                return False
        elif any(line.startswith("* data symbols SHA-256:") for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* switch manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if switch_manifest(manifest) != encoded_manifest:
            return False
        rom = (Path(root) / "baserom.bin").read_bytes()
        _, control_flow = verify_switches(data, address, rom, mapping, manifest,
                                         data_mapping=objects)
        fingerprint = switch_data_fingerprint if data_profile else switch_fingerprint
        return (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* switch proof SHA-256: ") == fingerprint(address, data, manifest))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def legacy_report_control_flow(lines, root, address, profile):
    from match import (ROM_BASE, RUNTIME_HELPERS, function_address_target,
                       thunk_is_call_via, verify_leaf_instructions)

    def single(prefix):
        values = [line[len(prefix):] for line in lines if line.startswith(prefix)]
        if len(values) != 1:
            raise ValueError("missing or duplicate legacy body evidence")
        return values[0]

    try:
        encoded = single("* compiled : ")
        if re.fullmatch(r"`(?:[0-9a-f]{2})+`", encoded) is None:
            return False
        data = bytes.fromhex(encoded[1:-1])
        if single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                single("**MATCH - byte identical** - ") != f"{len(data)}/{len(data)} bytes" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or \
                single("* source plausibility: ") != "plausible" or \
                single("* source SHA-256: ") != f"`{source_fingerprint(root, address)}`":
            return False
        mapping = mapping_snapshot(root)
        if mapping is None:
            return False
        entries = json.loads(mapping)
        if not isinstance(entries, list):
            return False
        callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
        if len(callers) != 1 or int(callers[0]["rom"], 16) != address or \
                callers[0].get("mode") not in ("thumb", "arm"):
            return False
        thumb = callers[0]["mode"] == "thumb"
        if address % (2 if thumb else 4) or not thumb and profile != SCHEMA:
            return False
        rom = (Path(root) / "baserom.bin").read_bytes()
        if not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom) or \
                data != rom[address - ROM_BASE:address - ROM_BASE + len(data)]:
            return False
        if profile in (BUFFER_SCHEMA, STACK_BUFFER_SCHEMA):
            return True
        calls = profile in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA) or \
            profile in (DATA_SCHEMA, FRAMED_DATA_SCHEMA) and single("* control flow: ") == CALL_SUMMARY

        def resolve(target):
            if target in RUNTIME_HELPERS.values():
                register = (target - RUNTIME_HELPERS["_call_via_r0"]) // 4
                if not thunk_is_call_via(rom, target, register):
                    raise ValueError("legacy call target does not match its runtime thunk")
            else:
                function_address_target(f"func_{target:08X}", entries, address, len(data), len(rom))

        verify_leaf_instructions(data, address, thumb, call_resolver=resolve if calls else None)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def report_matches(report, root, address):
    lines = report.splitlines()
    profiles = [line for line in lines if line.startswith("* verification:")]
    if profiles == [f"* verification: `{PRELOADED_SWITCH_SCHEMA}`"]:
        return preloaded_switch_report_matches(lines, root, address)
    if profiles == [f"* verification: `{UDIVSI3_SCHEMA}`"]:
        return udivsi3_report_matches(lines, root, address)
    if any(line.startswith(("* unsigned division:", "* unsigned division manifest:",
                            "* unsigned division proof SHA-256:")) for line in lines):
        return False
    if profiles == [f"* verification: `{SWITCH_DATA_SCHEMA}`"]:
        return switch_report_matches(lines, root, address, data_profile=True)
    if profiles == [f"* verification: `{SWITCH_SCHEMA}`"]:
        return switch_report_matches(lines, root, address)
    if any(line.startswith(("* switches:", "* switch manifest:", "* switch proof SHA-256:"))
           for line in lines):
        return False
    if profiles == [f"* verification: `{FUNCTION_ADDRESS_SCHEMA}`"]:
        return function_address_report_matches(lines, root, address)
    if any(line.startswith(("* function addresses:", "* function address manifest:",
                            "* function address proof SHA-256:")) for line in lines):
        return False
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
    return (profile_valid and legacy_report_control_flow(
                lines, root, address, profiles[0].removeprefix("* verification: `").removesuffix("`")) and
            f"* source SHA-256: `{source_fingerprint(root, address)}`" in lines and
            "* source plausibility: plausible" in lines and
            "* relocations: none" in lines and verdict is not None and
            int(verdict[1]) > 0 and verdict[1] == verdict[2])
