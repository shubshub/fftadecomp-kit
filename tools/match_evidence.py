"""Source-bound metadata for cached, offline match reports."""

import hashlib
import json
import modsi3_profile as modsi3
import divsi3_profile as divsi3
import umodsi3_profile as umodsi3
import ashldi3_profile as ashldi3
import lshrdi3_profile as lshrdi3
import inert_spin_profile as inert_spin
import software_double_profile as software_double
import software_float_profile as software_float
import function_thunk_profile as function_thunk
import empty_body_profile as empty_body
import switch_constants_profile as switch_constants
import subprocess
from rompath import rom_path
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
FRAMED_FUNCTION_ADDRESS_SCHEMA = "elf-symbol-thumb-frame-function-addresses-v1"
FUNCTION_ADDRESS_SUMMARY = "zero-addend mapped Thumb function literals; relocation fidelity, not callback ABI"
FUNCTION_BUFFER_SCHEMA = "elf-symbol-thumb-function-buffer-calls-v1"
SWITCH_SCHEMA = "elf-symbol-thumb-switches-v1"
SWITCH_SUMMARY = "one unsigned-guarded local Thumb word table with verified predecessor edges"
SWITCH_DATA_SCHEMA = "elf-symbol-thumb-switch-data-v1"
SWITCH_DATA_SUMMARY = "one guarded local Thumb table with one reachable interposed mapped object word"
SWITCH_MULTIPLE_DATA_SCHEMA = "elf-symbol-thumb-switch-data-v2"
SWITCH_MULTIPLE_DATA_SUMMARY = "one guarded local Thumb table with complete reachable mapped object words"
SWITCH_MULTIPLE_DATA_POLICY = "complete-reachable-object-words-v1"
SWITCH_U16_SCALAR_SELECTOR = "u16-scalars-v1"
SWITCH_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-v1"
SWITCH_U16_SCALAR_SUMMARY = "one guarded local Thumb table with complete mapped object and u16 scalar words"
SWITCH_U16_SCALAR_POLICY = "complete-reachable-u16-scalar-words-v1"
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


def report_rom_path(root):
    try:
        return rom_path(root)
    except SystemExit as error:
        raise ValueError(str(error)) from error


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
        rom = Path(report_rom_path(root)).read_bytes()
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
        rom = Path(report_rom_path(root)).read_bytes()
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


def function_address_fingerprint(address, data, manifest, *, framed=False):
    digest = hashlib.sha256()
    schema = FRAMED_FUNCTION_ADDRESS_SCHEMA if framed else FUNCTION_ADDRESS_SCHEMA
    for payload in (schema.encode("ascii"), address.to_bytes(4, "little"),
                    data, function_address_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def function_buffer_fingerprint(address, data, manifest, source_digest, mapping, buffer_digest):
    digest = hashlib.sha256()
    for payload in (FUNCTION_BUFFER_SCHEMA.encode("ascii"), STACK_BUFFER_SCHEMA.encode("ascii"),
                    address.to_bytes(4, "little"), data,
                    function_address_manifest(manifest).encode("ascii"),
                    source_digest.encode("ascii"), mapping, buffer_digest.encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def function_address_report_matches(lines, root, address, buffer_profile=False):
    from match import verify_function_addresses, verify_function_buffers, uses_stack_frame

    def single(prefix):
        marker = "**MATCH" if prefix.startswith("**MATCH") else prefix.rstrip(" :")
        matches = [line for line in lines if
                   (line.lstrip().startswith(marker) if buffer_profile else line.startswith(prefix))]
        if len(matches) != 1 or not matches[0].startswith(prefix):
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
        source_digest = source_fingerprint(root, address)
        if functions is None or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(functions) or \
                single("* function addresses: ") != FUNCTION_ADDRESS_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                not buffer_profile and any(line.startswith(
                    ("* buffer calls:", "* buffer proof SHA-256:")) for line in lines):
            return False
        if buffer_profile and (
                single("* verification: ") != f"`{FUNCTION_BUFFER_SCHEMA}`" or
                any(line.lstrip().startswith(("* data symbols", "* switches", "* switch manifest",
                    "* switch proof", "* unsigned division", "* signed remainder")) for line in lines)):
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
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        if buffer_profile:
            instructions, proof = verify_function_buffers(data, address, rom, functions, manifest)
            if single("* buffer calls: ") != STACK_BUFFER_SUMMARY or \
                    unquote("* buffer proof SHA-256: ") != proof.fingerprint() or \
                    unquote("* function buffer proof SHA-256: ") != function_buffer_fingerprint(
                        address, data, manifest, source_digest, functions, proof.fingerprint()):
                return False
            control_flow = CALL_SUMMARY
        else:
            instructions, control_flow = verify_function_addresses(
                data, address, rom, functions, objects, manifest)
            schema = FRAMED_FUNCTION_ADDRESS_SCHEMA if uses_stack_frame(instructions) else FUNCTION_ADDRESS_SCHEMA
            if single("* verification: ") != f"`{schema}`":
                return False
        framed = uses_stack_frame(instructions)
        if framed:
            if single("* stack frame: ") != STACK_SUMMARY:
                return False
        elif any(line.lstrip().startswith("* stack frame") for line in lines):
            return False
        return (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* function address proof SHA-256: ") ==
                function_address_fingerprint(address, data, manifest,
                                             framed=framed and not buffer_profile) and
                (not buffer_profile or (source_fingerprint(root, address) == source_digest and
                 mapping_snapshot(root) == functions and report_rom_path(root) == selected_rom and
                 Path(selected_rom).read_bytes() == rom)))
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


def switch_multiple_data_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SWITCH_MULTIPLE_DATA_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, switch_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def switch_u16_scalar_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SWITCH_U16_SCALAR_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
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
        rom = Path(report_rom_path(root)).read_bytes()
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
        scalar_data = data_profile and \
            single("* verification: ") == f"`{SWITCH_U16_SCALAR_SCHEMA}`"
        multiple_data = scalar_data or data_profile and \
            single("* verification: ") == f"`{SWITCH_MULTIPLE_DATA_SCHEMA}`"
        summary = (SWITCH_U16_SCALAR_SUMMARY if scalar_data else
                   SWITCH_MULTIPLE_DATA_SUMMARY if multiple_data else
                   SWITCH_DATA_SUMMARY if data_profile else SWITCH_SUMMARY)
        excluded = ("* stack frame:", "* buffer calls:", "* buffer proof SHA-256:",
                    "* function addresses:", "* function address manifest:",
                    "* function address proof SHA-256:")
        if data_profile:
            schema = (SWITCH_U16_SCALAR_SCHEMA if scalar_data else
                      SWITCH_MULTIPLE_DATA_SCHEMA if multiple_data else SWITCH_DATA_SCHEMA)
            if single("* verification: ") != f"`{schema}`":
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
        if data_profile and multiple_data != (
                isinstance(manifest, dict) and
                manifest.get("data_policy") == SWITCH_MULTIPLE_DATA_POLICY):
            return False
        if scalar_data != (isinstance(manifest, dict) and
                           manifest.get("scalar_policy") == SWITCH_U16_SCALAR_POLICY):
            return False
        rom = Path(report_rom_path(root)).read_bytes()
        _, control_flow = verify_switches(data, address, rom, mapping, manifest,
                                         data_mapping=objects)
        fingerprint = (switch_u16_scalar_fingerprint if scalar_data else
                       switch_multiple_data_fingerprint if multiple_data else
                       switch_data_fingerprint if data_profile else switch_fingerprint)
        return (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* switch proof SHA-256: ") == fingerprint(address, data, manifest))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def modsi3_report_matches(lines, root, address):
    from match import verify_modsi3

    def single(prefix):
        marker = prefix.rstrip(" :-")
        children = ("* signed remainder manifest", "* signed remainder proof SHA-256") \
            if marker == "* signed remainder" else ()
        matches = [line for line in lines if line.lstrip().startswith(marker) and
                   not line.lstrip().startswith(children)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate signed remainder evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed signed remainder evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate signed remainder manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if single("* verification: ") != f"`{modsi3.SCHEMA}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* signed remainder: ") != modsi3.SUMMARY or \
                single("* control flow: ") != CALL_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(("* stack frame", "* buffer calls", "* buffer proof",
                                              "* unsigned division", "* switches", "* switch manifest",
                                              "* switch proof", "* function addresses",
                                              "* function address manifest", "* function address proof"))
                    for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* signed remainder manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if modsi3.manifest_text(manifest) != encoded_manifest:
            return False
        objects = data_snapshot(root) if manifest.get("data") else None
        if objects is not None:
            if unquote("* data symbols SHA-256: ") != mapping_fingerprint(objects):
                return False
        elif any(line.lstrip().startswith("* data symbols SHA-256") for line in lines):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        verify_modsi3(data, address, rom, mapping, objects, manifest)
        return (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* signed remainder proof SHA-256: ") ==
                modsi3.fingerprint(address, data, manifest) and
                source_fingerprint(root, address) == source_digest and
                mapping_snapshot(root) == mapping and
                (objects is None or data_snapshot(root) == objects) and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def umodsi3_report_matches(lines, root, address):
    from match import DEFAULT_CC, DEFAULT_FLAGS, verify_umodsi3_source, uses_stack_frame

    def single(prefix):
        marker = prefix.rstrip(" :-")
        children = ("* unsigned remainder manifest", "* unsigned remainder proof SHA-256") \
            if marker == "* unsigned remainder" else ()
        matches = [line for line in lines if line.lstrip().startswith(marker) and
                   not line.lstrip().startswith(children)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate unsigned remainder evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed unsigned remainder evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate unsigned remainder manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if single("* verification: ") != f"`{umodsi3.SCHEMA}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* unsigned remainder: ") != umodsi3.SUMMARY or \
                single("* control flow: ") != CALL_SUMMARY or \
                unquote("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(("* buffer calls", "* buffer proof", "* signed remainder", "* signed quotient",
                                              "* unsigned division", "* switches", "* switch manifest",
                                              "* switch proof", "* function addresses",
                                              "* function address manifest", "* function address proof"))
                    for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* unsigned remainder manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if umodsi3.manifest_text(manifest) != encoded_manifest:
            return False
        objects = data_snapshot(root) if manifest.get("data") else None
        if objects is not None:
            if unquote("* data symbols SHA-256: ") != mapping_fingerprint(objects):
                return False
        elif any(line.lstrip().startswith("* data symbols SHA-256") for line in lines):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        instructions = verify_umodsi3_source(root, address, data, rom, mapping,
                                             data_snapshot(root), source_digest, manifest)
        if uses_stack_frame(instructions):
            if single("* stack frame: ") != STACK_SUMMARY:
                return False
        elif any(line.lstrip().startswith("* stack frame") for line in lines):
            return False
        return (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* unsigned remainder proof SHA-256: ") ==
                umodsi3.fingerprint(address, data, manifest) and
                source_fingerprint(root, address) == source_digest and
                mapping_snapshot(root) == mapping and
                (objects is None or data_snapshot(root) == objects) and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def divsi3_report_matches(lines, root, address):
    from match import DEFAULT_CC, DEFAULT_FLAGS, verify_divsi3_source

    def single(prefix):
        marker = prefix.rstrip(" :-")
        children = ("* signed quotient manifest", "* signed quotient proof SHA-256") \
            if marker == "* signed quotient" else ()
        matches = [line for line in lines if line.lstrip().startswith(marker) and
                   not line.lstrip().startswith(children)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate signed quotient evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed signed quotient evidence")
        return value[1:-1]

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate signed quotient manifest key")
            result[name] = value
        return result

    try:
        mapping = mapping_snapshot(root)
        source_digest = source_fingerprint(root, address)
        verification = single("* verification: ")
        selector = divsi3.FRAMED_SELECTOR if verification == f"`{divsi3.FRAMED_SCHEMA}`" else None
        if verification != f"`{divsi3.schema(selector)}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* signed quotient: ") != (divsi3.FRAMED_SUMMARY if selector else divsi3.SUMMARY) or \
                single("* control flow: ") != CALL_SUMMARY or \
                unquote("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(("* buffer", "* data symbols",
                                              "* unsigned division", "* signed remainder", "* switches",
                                              "* switch manifest", "* switch proof", "* function address",
                                              "* function buffer")) for line in lines):
            return False
        if selector:
            if single("* stack frame: ") != STACK_SUMMARY:
                return False
        elif any(line.lstrip().startswith("* stack frame") for line in lines):
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* signed quotient manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if divsi3.manifest_text(manifest) != encoded_manifest or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                single("**MATCH - byte identical** - ") != f"{len(data)}/{len(data)} bytes" or \
                unquote("* signed quotient proof SHA-256: ") != divsi3.fingerprint(
                    address, data, manifest, selector=selector):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        verify_divsi3_source(root, address, data, rom, mapping, source_digest, manifest, selector=selector)
        return (source_fingerprint(root, address) == source_digest and mapping_snapshot(root) == mapping and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def legacy_report_control_flow(lines, root, address, profile):
    from match import (ROM_BASE, RUNTIME_HELPERS, function_address_target,
                       thunk_is_call_via, verify_leaf_instructions, verify_addressed_modsi3_source)

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
        rom = Path(report_rom_path(root)).read_bytes()
        if not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom) or \
                data != rom[address - ROM_BASE:address - ROM_BASE + len(data)]:
            return False
        if profile in (BUFFER_SCHEMA, STACK_BUFFER_SCHEMA):
            return function_thunk.legacy_absence(root, address, data, rom, mapping,
                                                buffer_stack_arguments=profile == STACK_BUFFER_SCHEMA)
        calls = profile in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA) or \
            profile in (DATA_SCHEMA, FRAMED_DATA_SCHEMA) and single("* control flow: ") == CALL_SUMMARY

        thunk_calls = set()
        def resolve(target):
            if target in RUNTIME_HELPERS.values():
                thunk_calls.add(target)
                register = (target - RUNTIME_HELPERS["_call_via_r0"]) // 4
                if not thunk_is_call_via(rom, target, register):
                    raise ValueError("legacy call target does not match its runtime thunk")
            else:
                function_address_target(f"func_{target:08X}", entries, address, len(data), len(rom))

        try:
            verify_leaf_instructions(data, address, thumb, call_resolver=resolve if calls else None)
        except modsi3.AddressedRemainderRequired:
            if profile not in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA):
                return False
            verify_addressed_modsi3_source(
                root, address, data, rom, mapping, single("* source SHA-256: ")[1:-1],
                profile == FRAMED_LINKED_SCHEMA)
        if thunk_calls:
            function_thunk.legacy_absence(root, address, data, rom, mapping)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def valid_match_verdict(report):
    records = [line for line in report.splitlines()
               if re.match(r"[ \t]*\*\*[ \t]*(?:MATCH\b|NOT[ \t]+MATCHING\b|HAND-ASM\b)", line)]
    return len(records) == 1 and re.fullmatch(
        r"\*\*MATCH - byte identical\*\* - ([1-9][0-9]*)/\1 bytes", records[0]) is not None


def report_matches(report, root, address):
    if not valid_match_verdict(report):
        return False
    try:
        import addressed_signed_runtime_profile
        if addressed_signed_runtime_profile.selected(report):
            return addressed_signed_runtime_profile.report_matches(report, root, address)
        import signed_divmod_profile
        if signed_divmod_profile.selected(report):
            return signed_divmod_profile.report_matches(report, root, address)
        import owner_admission_profile
        if owner_admission_profile.selected(report):
            return owner_admission_profile.report_matches(report, root, address)
        if software_float.selected(report):
            return software_float.report_matches(report, root, address)
        if lshrdi3.selected(report):
            return lshrdi3.report_matches(report, root, address)
        if ashldi3.selected(report):
            return ashldi3.report_matches(report, root, address)
        if switch_constants.selected_policy(report) is not None:
            return switch_constants.report_matches(report, root, address)
        if empty_body.SCHEMA in report or any(
                line.lstrip().startswith("* empty body") for line in report.splitlines()):
            return empty_body.report_matches(report, root, address)
        if empty_body.has_empty_body(root, address):
            return False
        if function_thunk.selected(report):
            return function_thunk.report_matches(report, root, address)
        if software_double.selected(report):
            return software_double.report_matches(report, root, address)
        if inert_spin.selected(report):
            return inert_spin.report_matches(report, root, address)
    except ValueError:
        return False
    lines = report.splitlines()
    profiles = [line for line in lines if line.startswith("* verification:")]
    if profiles == [f"* verification: `{umodsi3.SCHEMA}`"]:
        return umodsi3_report_matches(lines, root, address)
    if any(line.lstrip().startswith("* unsigned remainder") for line in lines):
        return False
    if profiles in ([f"* verification: `{divsi3.SCHEMA}`"],
                     [f"* verification: `{divsi3.FRAMED_SCHEMA}`"]):
        return divsi3_report_matches(lines, root, address)
    if any(line.lstrip().startswith("* signed quotient") for line in lines):
        return False
    if profiles == [f"* verification: `{FUNCTION_BUFFER_SCHEMA}`"]:
        return function_address_report_matches(lines, root, address, buffer_profile=True)
    if any(line.lstrip().startswith("* function buffer") for line in lines):
        return False
    if profiles == [f"* verification: `{modsi3.SCHEMA}`"]:
        return modsi3_report_matches(lines, root, address)
    if any(line.lstrip().startswith("* signed remainder") for line in lines):
        return False
    if profiles == [f"* verification: `{PRELOADED_SWITCH_SCHEMA}`"]:
        return preloaded_switch_report_matches(lines, root, address)
    if profiles == [f"* verification: `{UDIVSI3_SCHEMA}`"]:
        return udivsi3_report_matches(lines, root, address)
    if any(line.startswith(("* unsigned division:", "* unsigned division manifest:",
                            "* unsigned division proof SHA-256:")) for line in lines):
        return False
    if profiles in ([f"* verification: `{SWITCH_DATA_SCHEMA}`"],
                    [f"* verification: `{SWITCH_MULTIPLE_DATA_SCHEMA}`"],
                    [f"* verification: `{SWITCH_U16_SCALAR_SCHEMA}`"]):
        return switch_report_matches(lines, root, address, data_profile=True)
    if profiles == [f"* verification: `{SWITCH_SCHEMA}`"]:
        return switch_report_matches(lines, root, address)
    if any(line.startswith(("* switches:", "* switch manifest:", "* switch proof SHA-256:"))
           for line in lines):
        return False
    if profiles in ([f"* verification: `{FUNCTION_ADDRESS_SCHEMA}`"],
                    [f"* verification: `{FRAMED_FUNCTION_ADDRESS_SCHEMA}`"]):
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
