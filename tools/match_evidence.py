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
import plain_report_fields
import switch_constants_profile as switch_constants
import typed_switch_outgoing_frame as typed_switch_frame
import switch_pool_outgoing_frame as pool_switch_frame
import switch_wide_scalars as wide_scalars
import switch_data_thunks
import m4a_track_switch as music
import subprocess
from rompath import rom_path
from pathlib import Path
import re


SCHEMA = "elf-symbol-cfg-leaf-v2"
LINKED_SCHEMA = "elf-symbol-thumb-calls-v1"
CALL_SUMMARY = "direct Thumb BL with ordinary ARM ABI call summaries"
SELF_CALL_SUMMARY = ("exact-entry Thumb BL to this same verified complete ELF symbol under the ordinary ARM ABI "
                     "summary; partial correctness only, no termination or recursion-depth theorem")


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
SWITCH_POOL_U16_SCALAR_SELECTOR = "u16-scalars-v2"
SWITCH_POOL_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-v2"
SWITCH_POOL_U16_SCALAR_SUMMARY = ("one guarded local Thumb table found by its dispatch load, "
                                  "with complete mapped object and u16 scalar words")
SWITCH_POOL_POLICY = "dispatch-identified-table-pointer-v1"
SWITCH_FUNCTION_POLICY = "canonical-function-literals-v1"
SWITCH_FUNCTION_U16_SCALAR_SELECTOR = "u16-scalars-functions-v1"
SWITCH_FUNCTION_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-functions-v1"
SWITCH_FUNCTION_U16_SCALAR_SUMMARY = ("one guarded local Thumb table with complete mapped object, "
                                      "u16 scalar and canonical function words")
SWITCH_FUNCTION_POOL_U16_SCALAR_SELECTOR = "u16-scalars-functions-v2"
SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-functions-v2"
SWITCH_FUNCTION_POOL_U16_SCALAR_SUMMARY = ("one guarded local Thumb table found by its dispatch load, "
                                           "with complete mapped object, u16 scalar and canonical function words")
SWITCH_FUNCTION_FRAME_U16_SCALAR_SELECTOR = "u16-scalars-functions-frame-v1"
SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-functions-frame-v1"
SWITCH_FUNCTION_FRAME_U16_SCALAR_SUMMARY = (
    "one guarded local Thumb table with complete mapped object, u16 scalar and canonical function words "
    "and a fixed write-only outgoing-argument frame")
SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SELECTOR = "u16-scalars-functions-frame-v2"
SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA = "elf-symbol-thumb-switch-data-u16-scalars-functions-frame-v2"
SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SUMMARY = (
    "one guarded local Thumb table found by its dispatch load, with complete mapped object, u16 scalar "
    "and canonical function words and a fixed write-only outgoing-argument frame")
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
UDIVSI3_FRAMED_SELECTOR = "positive-constant-frame-v1"
UDIVSI3_FRAMED_SCHEMA = "elf-symbol-thumb-udivsi3-positive-constant-frame-v1"
UDIVSI3_FRAMED_SUMMARY = UDIVSI3_SUMMARY + " and a verified caller stack frame"


def self_call_sites_text(sites, address):
    """Canonical text of the self-call site offsets bound into a report."""
    return json.dumps(sorted(site - address for site in sites), separators=(",", ":"))


def udivsi3_schema(selector=None):
    if selector is not None and selector != UDIVSI3_FRAMED_SELECTOR:
        raise ValueError("unsupported unsigned quotient selector")
    return UDIVSI3_FRAMED_SCHEMA if selector is not None else UDIVSI3_SCHEMA


def report_rom_path(root):
    try:
        return rom_path(root)
    except SystemExit as error:
        raise ValueError(str(error)) from error


def udivsi3_manifest(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def udivsi3_fingerprint(address, data, manifest, *, selector=None):
    digest = hashlib.sha256()
    for payload in (udivsi3_schema(selector).encode("ascii"), address.to_bytes(4, "little"),
                    data, udivsi3_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def udivsi3_report_matches(lines, root, address, parts=None):
    from match import DEFAULT_CC, DEFAULT_FLAGS, verify_udivsi3, verify_udivsi3_source

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
        framed = single("* verification: ") == f"`{UDIVSI3_FRAMED_SCHEMA}`"
        selector = UDIVSI3_FRAMED_SELECTOR if framed else None
        mapping = mapping_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if single("* verification: ") != f"`{udivsi3_schema(selector)}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_fingerprint(root, address) or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* unsigned division: ") != (UDIVSI3_FRAMED_SUMMARY if framed else UDIVSI3_SUMMARY) or \
                single("* control flow: ") != CALL_SUMMARY or \
                single("* source plausibility: ") != "plausible" or \
                single("* relocations: ") != "none" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                any(line.lstrip().startswith(("* buffer calls", "* buffer proof SHA-256", "* buffer loop replay",
                                              "* buffer BIOS", "* buffer copy summary", "* buffer switch callee", "* buffer owner switch",
                                              "* data symbols SHA-256", "* switches", "* switch manifest",
                                              "* switch proof SHA-256", "* function addresses",
                                              "* function address manifest", "* function address proof SHA-256"))
                    for line in lines):
            return False
        if framed:
            if single("* stack frame: ") != STACK_SUMMARY or \
                    unquote("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                    any(line.lstrip().startswith(("* signed quotient", "* signed remainder",
                                                 "* unsigned remainder", "* inert spins",
                                                 "* software", "* owner")) for line in lines):
                return False
        elif any(line.lstrip().startswith("* stack frame") for line in lines):
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
        if framed:
            instructions = verify_udivsi3_source(root, address, data, rom, mapping, source_digest,
                                                 manifest, selector=selector)
        else:
            instructions = verify_udivsi3(data, address, rom, mapping, manifest)
        if not (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* unsigned division proof SHA-256: ") ==
                udivsi3_fingerprint(address, data, manifest, selector=selector)):
            return False
        if parts is not None:
            parts.update(schema=udivsi3_schema(selector), data=data, instructions=instructions, mapped=True,
                         control_flow=CALL_SUMMARY, udivsi3_bindings=True, division_evidence=manifest,
                         unsigned_quotient_profile=selector)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def saved_selectors(report):
    """The match.py selectors a saved report was issued under.

    status.py (`--verify`) and rebuild.py (`--compiled`) both re-run
    match.py for a source with a saved report, and both recover the selectors
    from that report here, so they re-issue every schema family the same
    way.  Returns a namespace of the recovered selectors, False or None when
    absent, and `arguments`, the match.py arguments in a fixed order.  A
    malformed or mixed profile report raises ValueError.

    The compiler flags are forwarded only when they differ from match.py's
    default; outside a library unit the replay admits only the default.
    """
    import types
    import addressed_signed_runtime_profile
    import libgcc_divdi3
    import library_units
    import owner_admission_profile
    import palette_source_admission_profile
    import private_float_pack_admission_profile
    import signed_divmod_profile
    import unsigned_divmod_profile
    from match import DEFAULT_FLAGS
    lines = report.splitlines()
    found = types.SimpleNamespace()
    found.unsigned_runtime = unsigned_divmod_profile.selector_for_report(report)
    found.palette_source = palette_source_admission_profile.selector_for_report(report)
    found.private_float = private_float_pack_admission_profile.selector_for_report(report)
    found.addressed_runtime = addressed_signed_runtime_profile.selector_for_report(report)
    found.signed_runtime = signed_divmod_profile.selector_for_report(report)
    found.owner = (owner_admission_profile.selector_for_report(report) if owner_admission_profile.selected(report)
                   else libgcc_divdi3.SELECTOR if f"* verification: `{libgcc_divdi3.SCHEMA}`" in lines else False)
    found.constants = switch_constants.selected_policy(report)
    found.typed_outgoing = typed_switch_frame.selector_for_report(report)
    u16 = {SWITCH_U16_SCALAR_SCHEMA: SWITCH_U16_SCALAR_SELECTOR,
           SWITCH_POOL_U16_SCALAR_SCHEMA: SWITCH_POOL_U16_SCALAR_SELECTOR,
           pool_switch_frame.SCHEMA: pool_switch_frame.SELECTOR,
           pool_switch_frame.FIXED_SCHEMA: pool_switch_frame.FIXED_SELECTOR,
           SWITCH_FUNCTION_U16_SCALAR_SCHEMA: SWITCH_FUNCTION_U16_SCALAR_SELECTOR,
           SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA: SWITCH_FUNCTION_POOL_U16_SCALAR_SELECTOR,
           SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA: SWITCH_FUNCTION_FRAME_U16_SCALAR_SELECTOR,
           SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA: SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SELECTOR}
    found.u16_switch = next((selector for schema, selector in u16.items()
                             if f"* verification: `{schema}`" in lines), None) or \
        switch_data_thunks.selector_for_report(report) or False
    found.double = software_double.selected(report)
    found.target_remainder = found.double and software_double.target_remainder_selected(report)
    found.thunk = function_thunk.selector_for_report(report)
    found.spin = inert_spin.selected(report)
    found.unsigned_quotient_frame = f"* verification: `{UDIVSI3_FRAMED_SCHEMA}`" in lines
    found.quotient_frame = any(f"* verification: `{schema}`" in lines
                               for schema in (divsi3.FRAMED_SCHEMA, divsi3.FRAMED_SWITCH_SCHEMA))
    found.flags = compiler_flags(report)
    found.unit_toolchain = library_units.report_toolchain(report)
    arguments = []
    if found.spin:
        arguments += ["--control-flow-profile", inert_spin.SELECTOR]
    if found.double:
        arguments += ["--software-double-profile", software_double.SELECTOR]
        if found.target_remainder:
            arguments += ["--software-double-remainder-profile", software_double.REMAINDER_TARGET_SELECTOR]
    if found.thunk:
        arguments += ["--function-address-profile", found.thunk]
    for owner in (found.owner, found.palette_source, found.private_float):
        if owner:
            arguments += ["--owner-runtime-profile", owner]
    if found.constants:
        arguments += ["--switch-profile", found.constants.selector]
    if found.typed_outgoing:
        arguments += ["--switch-data-profile", found.typed_outgoing]
    if found.u16_switch:
        arguments += ["--switch-data-profile", found.u16_switch]
    if found.unsigned_runtime:
        arguments += ["--unsigned-runtime-profile", found.unsigned_runtime]
    if found.signed_runtime:
        arguments += ["--signed-runtime-profile", found.signed_runtime]
    if found.addressed_runtime:
        arguments += ["--addressed-signed-runtime-profile", found.addressed_runtime]
    if found.unsigned_quotient_frame:
        arguments += ["--unsigned-quotient-profile", UDIVSI3_FRAMED_SELECTOR]
    if found.quotient_frame:
        arguments += ["--signed-quotient-profile", divsi3.FRAMED_SELECTOR]
    if found.unit_toolchain is not None:
        arguments += ["--unit-toolchain", found.unit_toolchain]
    elif found.flags is not None and found.flags != DEFAULT_FLAGS:
        arguments += ["--flags", found.flags]
    found.arguments = arguments
    return found


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


COMPILER_MARKER = "* compiler: "


def compiler_flags(report):
    """The optimisation flags a saved report was produced with.

    The report records the compiler and the flags it ran with.  A function
    that only reproduces at another optimisation level has to be re-verified
    with the level it was matched at, not with the default one, so the
    flags travel with the report.

    Returns the trailing run of option words, or None when the report names
    no flags.
    """
    for line in report.splitlines():
        if not line.startswith(COMPILER_MARKER):
            continue
        text = line[len(COMPILER_MARKER):].strip()
        if text.startswith("`") and text.endswith("`"):
            text = text[1:-1].strip()
        tokens = text.split()
        flags = []
        for token in reversed(tokens):
            if token.startswith("-"):
                flags.insert(0, token)
            else:
                break
        return " ".join(flags) if flags else None
    return None


def source_paths(root, address):
    import os

    root = Path(root)
    target = os.path.normcase(f"{address:08X}.c")
    paths = set()
    # Match directory entries too, as pathlib glob does, but do not descend
    # through directory symlinks. Each source directory is scanned only once.
    for directory, directories, files in os.walk(root / "src"):
        for name in directories + files:
            normalized = os.path.normcase(name)
            if normalized == target or normalized.endswith(".h"):
                paths.add(Path(directory) / name)
    for directory, _, files in os.walk(root / "include"):
        for name in files:
            path = Path(directory) / name
            if path.is_file():
                paths.add(path)
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


def report_source(root, address):
    """The source path match.py names in a report: src/<addr>.c, else the first folder copy."""
    import os

    root = Path(root)
    candidates = [root / "src" / f"{address:08X}.c", *sorted((root / "src").rglob(f"{address:08X}.c"))]
    chosen = next((path for path in candidates if os.path.exists(path)), None)
    if chosen is None:
        raise ValueError(f"no source for 0x{address:08X} under src/")
    return os.path.relpath(chosen, root).replace(os.sep, "/")


def report_unit(report, root, address):
    """(unit context, orphan constants, compiler) as match.py renders a saved report's unit lines.

    A report without unit lines is a default-toolchain report; one with them
    must name the unit that contains the address and its toolchain, which
    library_units.report_admitted has already held to the current row.  The
    orphan-constant exclusion is the report's own: match.py records it from
    the compile (see closed_report).
    """
    import library_units
    from match import DEFAULT_CC, DEFAULT_FLAGS
    bound = library_units.binding(report)
    if bound is None:
        return None, None, f"{DEFAULT_CC} {DEFAULT_FLAGS}"
    row, toolchain, _, orphan = bound
    unit = library_units.containing(library_units.load(root), address)
    if unit is None or unit.text != row or unit.toolchain != toolchain:
        raise ValueError("report unit lines do not name the containing library unit")
    tool = library_units.resolve(toolchain)
    return ({"unit": unit, "tool": tool}, None if orphan is None else json.loads(orphan),
            f"{tool['cc']} {tool['flags']}")


def closed_report(report, root, address, parts):
    """Whether `report` is exactly the report match.py writes for re-verified evidence.

    `parts` is what a cached replay re-verified: the compiled body (`data`),
    its verified instructions, the schema and the schema's evidence blocks,
    named as render_report names them.  Everything else is re-derived here -
    the source path and digest, the mapping and data-symbol digests, the
    stack-frame line, the unit and compiler lines, the ROM bytes, the
    hand-asm line and the listing - and the whole text is compared, so no
    line can be added, dropped, reordered or edited on its own.

    Two choices match.py makes from the compiled object are not visible to a
    replay that does not compile, so they come from the report: whether the
    function links a data relocation (the data schemas, the data-symbol line
    and the manifests' "data" entries) and a library unit's orphan-constant
    exclusion.  A consistent relabel of either still replays here; only a
    compile re-derives them, and status.py --verify requires the saved report
    to equal the one match.py writes (match.py --check-report).

    A MATCH report has plausible source, and plausible.py consults the
    hand-asm allow list only for implausible source, so its hand-asm line is
    always `not listed`; the replays that re-run the checker refuse an allow
    entry outright.
    """
    from match import ROM_BASE, render_report, report_listing, uses_stack_frame
    try:
        parts = dict(parts)
        data, instructions = parts.pop("data"), parts.pop("instructions")
        thumb = parts.pop("thumb", True)
        rom = Path(report_rom_path(root)).read_bytes()
        want = rom[address - ROM_BASE:address - ROM_BASE + len(data)]
        if not data or want != data:
            return False
        unit_context, unit_orphan, compiler = report_unit(report, root, address)
        listing, _, _ = report_listing(instructions, want, address, len(data), thumb)
        parts.setdefault("mapping", mapping_snapshot(root))
        parts.setdefault("data_mapping", data_snapshot(root))
        return render_report(
            addr=address, src_rel=report_source(root, address), fingerprint=source_fingerprint(root, address),
            compiler=compiler, want=want, span=len(data), got_body=data, verdict="MATCH - byte identical",
            same_bytes=len(data), listing=listing, framed_profile=thumb and uses_stack_frame(instructions),
            unit_context=unit_context, unit_orphan=unit_orphan, **parts) == report
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


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


def buffer_report_matches(lines, root, address, mapping, stack_arguments=False, parts=None):
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
        from inert_spin_profile import index_snapshot
        # Without a function index nothing is summarised or delegated, and the walk refuses as before.
        indexed = stack_arguments and (Path(root) / "symbols/functions.txt").is_file()
        proof = BufferCallProof(rom, mapping, stack_arguments=stack_arguments, loop_replay=True,
                                bios_wrappers=True,
                                copy_helper_index=index_snapshot(root) if indexed else None,
                                switch_callee_index=index_snapshot(root) if indexed else None)
        if proof.span(address) != data:
            return False
        verdict = f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"
        if verdict not in lines:
            return False
        instructions = verify_leaf_instructions(data, address, True, buffer_proof=proof,
                                                call_resolver=proof.target, incoming_narrow_reads=True)
        if stack_arguments:
            # match.py tries the version-1 proof first and writes version 2 only when it is refused.
            first = BufferCallProof(rom, mapping, loop_replay=True, bios_wrappers=True)
            try:
                verify_leaf_instructions(data, address, True, buffer_proof=first, call_resolver=first.target,
                                         incoming_narrow_reads=True)
            except ValueError:
                pass
            else:
                return False
        if not (bool(proof.dependencies) and
                fingerprints == [f"* buffer proof SHA-256: `{proof.fingerprint()}`"] and
                [line for line in lines if line.lstrip().startswith("* buffer")
                 and not line.startswith(("* buffer calls:", "* buffer proof SHA-256:"))] ==
                proof.loop_replay_lines() + proof.bios_summary_lines()):
            return False
        if parts is not None:
            parts.update(instructions=instructions, buffer_proof=proof)
        return True
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


def function_address_report_matches(lines, root, address, buffer_profile=False, parts=None):
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
                not buffer_profile and any(line.lstrip().startswith(
                    ("* buffer calls:", "* buffer proof SHA-256:", "* buffer loop replay", "* buffer BIOS",
                     "* buffer copy summary", "* buffer switch callee", "* buffer owner switch")) for line in lines):
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
                        address, data, manifest, source_digest, functions, proof.fingerprint()) or \
                    [line for line in lines if line.lstrip().startswith("* buffer loop replay") or
                     line.lstrip().startswith("* buffer copy summary") or
                     line.lstrip().startswith("* buffer switch callee") or
                     line.lstrip().startswith("* buffer owner switch")] != proof.loop_replay_lines() or \
                    [line for line in lines if line.lstrip().startswith("* buffer BIOS")] != proof.bios_summary_lines():
                return False
            control_flow = CALL_SUMMARY
            schema = FUNCTION_BUFFER_SCHEMA
        else:
            proof = None
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
        if not (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* function address proof SHA-256: ") ==
                function_address_fingerprint(address, data, manifest,
                                             framed=framed and not buffer_profile) and
                (not buffer_profile or (source_fingerprint(root, address) == source_digest and
                 mapping_snapshot(root) == functions and report_rom_path(root) == selected_rom and
                 Path(selected_rom).read_bytes() == rom))):
            return False
        if parts is not None:
            parts.update(schema=schema, data=data, instructions=instructions, buffer_proof=proof, mapped=True,
                         control_flow=control_flow, data_profile=bool(manifest.get("data")),
                         address_manifest=manifest)
        return True
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


def switch_pool_u16_scalar_fingerprint(address, data, manifest):
    digest = hashlib.sha256()
    for payload in (SWITCH_POOL_U16_SCALAR_SCHEMA.encode("ascii"), address.to_bytes(4, "little"),
                    data, switch_manifest(manifest).encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def switch_function_u16_scalar_fingerprint(address, data, manifest):
    """Domain-separated by the function-literal schema of the manifest's pool shape."""
    schema = ((SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA if "pool_policy" in manifest else
               SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA) if "stack_policy" in manifest else
              SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA if "pool_policy" in manifest else
              SWITCH_FUNCTION_U16_SCALAR_SCHEMA)
    digest = hashlib.sha256()
    for payload in (schema.encode("ascii"), address.to_bytes(4, "little"),
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


def preloaded_switch_report_matches(lines, root, address, parts=None):
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
        excluded = ("* stack frame", "* buffer calls", "* buffer proof SHA-256", "* buffer loop replay",
                    "* buffer BIOS", "* buffer copy summary", "* buffer switch callee", "* buffer owner switch", "* function addresses",
                    "* function address manifest",
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
        instructions, control_flow = verify_preloaded_switches(data, address, rom, mapping, objects, manifest)
        if not (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* switch proof SHA-256: ") ==
                preloaded_switch_fingerprint(address, data, manifest)):
            return False
        if parts is not None:
            parts.update(schema=PRELOADED_SWITCH_SCHEMA, data=data, instructions=instructions, mapped=True,
                         control_flow=control_flow, data_profile=True, switches=True, switch_evidence=manifest,
                         preloaded_profile=True)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def switch_report_matches(lines, root, address, *, data_profile=False, parts=None):
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
        outgoing_frame = data_profile and single("* verification: ") == f"`{typed_switch_frame.SCHEMA}`"
        function_frame = data_profile and single("* verification: ") in (
            f"`{SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA}`", f"`{SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA}`")
        thunk_selector = next((selector for selector, schema in switch_data_thunks.SCHEMAS.items()
                               if data_profile and single("* verification: ") == f"`{schema}`"), None)
        fixed_frame = data_profile and single("* verification: ") == f"`{pool_switch_frame.FIXED_SCHEMA}`"
        pool_frame = function_frame or fixed_frame or data_profile and \
            single("* verification: ") == f"`{pool_switch_frame.SCHEMA}`" or \
            thunk_selector is not None and switch_data_thunks.framed(thunk_selector)
        function_data = function_frame or data_profile and single("* verification: ") in (
            f"`{SWITCH_FUNCTION_U16_SCALAR_SCHEMA}`", f"`{SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA}`")
        pool_data = data_profile and single("* verification: ") in (
            f"`{SWITCH_POOL_U16_SCALAR_SCHEMA}`", f"`{pool_switch_frame.SCHEMA}`",
            f"`{SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA}`", f"`{SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA}`")
        scalar_data = pool_data or function_data or fixed_frame or data_profile and \
            single("* verification: ") == f"`{SWITCH_U16_SCALAR_SCHEMA}`"
        multiple_data = outgoing_frame or scalar_data or thunk_selector is not None or data_profile and \
            single("* verification: ") == f"`{SWITCH_MULTIPLE_DATA_SCHEMA}`"
        summary = (switch_data_thunks.SUMMARIES[thunk_selector] if thunk_selector is not None else
                   typed_switch_frame.SUMMARY if outgoing_frame else
                   SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SUMMARY if function_frame and pool_data else
                   SWITCH_FUNCTION_FRAME_U16_SCALAR_SUMMARY if function_frame else
                   pool_switch_frame.FIXED_SUMMARY if fixed_frame else
                   pool_switch_frame.SUMMARY if pool_frame else
                   SWITCH_FUNCTION_POOL_U16_SCALAR_SUMMARY if function_data and pool_data else
                   SWITCH_FUNCTION_U16_SCALAR_SUMMARY if function_data else
                   SWITCH_POOL_U16_SCALAR_SUMMARY if pool_data else
                   SWITCH_U16_SCALAR_SUMMARY if scalar_data else
                   SWITCH_MULTIPLE_DATA_SUMMARY if multiple_data else
                   SWITCH_DATA_SUMMARY if data_profile else SWITCH_SUMMARY)
        excluded = ("* stack frame:", "* buffer calls:", "* buffer proof SHA-256:",
                    "* buffer loop replay:", "* buffer BIOS", "* buffer copy summary:", "* buffer switch callee:", "* buffer owner switch:",
                    "* function addresses:",
                    "* function address manifest:",
                    "* function address proof SHA-256:")
        if outgoing_frame or pool_frame:
            if single("* stack frame: ") != STACK_SUMMARY:
                return False
            excluded = excluded[1:]
        if data_profile:
            schema = (switch_data_thunks.SCHEMAS[thunk_selector] if thunk_selector is not None else
                      typed_switch_frame.SCHEMA if outgoing_frame else
                      SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA if function_frame and pool_data else
                      SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA if function_frame else
                      pool_switch_frame.FIXED_SCHEMA if fixed_frame else
                      pool_switch_frame.SCHEMA if pool_frame else
                      SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA if function_data and pool_data else
                      SWITCH_FUNCTION_U16_SCALAR_SCHEMA if function_data else
                      SWITCH_POOL_U16_SCALAR_SCHEMA if pool_data else
                      SWITCH_U16_SCALAR_SCHEMA if scalar_data else
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
                any(line.lstrip().startswith(excluded)
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
        # Without a selector, match.py writes the version-2 data policy exactly
        # when the switch links more than one data relocation and is not preloaded.
        if data_profile and not (outgoing_frame or scalar_data or thunk_selector is not None) and \
                multiple_data != (len(manifest.get("data") or ()) > 1 and
                                  "preload" not in (manifest.get("switch") or {})):
            return False
        if outgoing_frame != (isinstance(manifest, dict) and
                              manifest.get("frame_policy") == typed_switch_frame.SELECTOR):
            return False
        if (thunk_selector is not None) != (isinstance(manifest, dict) and "thunk_policy" in manifest):
            return False
        if thunk_selector is None and scalar_data != (isinstance(manifest, dict) and
                           manifest.get("scalar_policy") == SWITCH_U16_SCALAR_POLICY):
            return False
        if pool_data != (isinstance(manifest, dict) and
                         manifest.get("pool_policy") == SWITCH_POOL_POLICY):
            return False
        if pool_frame != (isinstance(manifest, dict) and
                          manifest.get("stack_policy") == pool_switch_frame.STACK_POLICY):
            return False
        if function_data != (isinstance(manifest, dict) and
                             manifest.get("function_policy") == SWITCH_FUNCTION_POLICY):
            return False
        # The wide-scalar premise is printed in, and only in, a report that applies it.
        if [line for line in lines if line.lstrip().startswith(wide_scalars.REPORT_PREFIX.lstrip())] != (
                [wide_scalars.report_line()] if isinstance(manifest, dict) and
                "wide_scalar_policy" in manifest else []):
            return False
        rom = Path(report_rom_path(root)).read_bytes()
        instructions, control_flow = verify_switches(data, address, rom, mapping, manifest,
                                                    data_mapping=objects)
        if thunk_selector is not None and switch_data_thunks.selector_for_manifest(manifest) != thunk_selector:
            return False
        fingerprint = (switch_data_thunks.fingerprint if thunk_selector is not None else
                       typed_switch_frame.fingerprint if outgoing_frame else
                       switch_function_u16_scalar_fingerprint if function_data else
                       pool_switch_frame.fingerprint if pool_frame else
                       switch_pool_u16_scalar_fingerprint if pool_data else
                       switch_u16_scalar_fingerprint if scalar_data else
                       switch_multiple_data_fingerprint if multiple_data else
                       switch_data_fingerprint if data_profile else switch_fingerprint)
        if thunk_selector == music.SELECTOR and not music.replay(root, "\n".join(lines), data):
            return False
        # Each load-bearing thunk store premise (kit #393) is stated once, as the manifest derives it.
        if [line for line in lines if line.lstrip().startswith(f"* {switch_data_thunks.PREMISE}")] != \
                (switch_data_thunks.premise_lines(address, manifest) if thunk_selector is not None else []):
            return False
        if not (single("* control flow: ") == control_flow and
                single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* switch proof SHA-256: ") == fingerprint(address, data, manifest)):
            return False
        if parts is not None:
            parts.update(schema=schema if data_profile else SWITCH_SCHEMA, data=data, instructions=instructions,
                         mapped=True, control_flow=control_flow, data_profile=data_profile, switches=True,
                         switch_evidence=manifest, thunk_switch_selector=thunk_selector)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def modsi3_report_matches(lines, root, address, parts=None):
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
                                              "* buffer loop replay", "* buffer BIOS", "* buffer copy summary", "* buffer switch callee", "* buffer owner switch",
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
        instructions = verify_modsi3(data, address, rom, mapping, objects, manifest)
        if not (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* signed remainder proof SHA-256: ") ==
                modsi3.fingerprint(address, data, manifest) and
                source_fingerprint(root, address) == source_digest and
                mapping_snapshot(root) == mapping and
                (objects is None or data_snapshot(root) == objects) and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom):
            return False
        if parts is not None:
            parts.update(schema=modsi3.SCHEMA, data=data, instructions=instructions, mapped=True,
                         control_flow=CALL_SUMMARY, data_profile=objects is not None, remainder_evidence=manifest)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError):
        return False


def umodsi3_report_matches(lines, root, address, parts=None):
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
                any(line.lstrip().startswith(("* buffer calls", "* buffer proof", "* buffer loop replay",
                                              "* buffer BIOS", "* buffer copy summary", "* buffer switch callee", "* buffer owner switch", "* signed remainder",
                                              "* signed quotient",
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
        if not (single("* ROM bytes: ") == f"`{data.hex()}` ({len(data)} bytes)" and
                single("**MATCH - byte identical** - ") == f"{len(data)}/{len(data)} bytes" and
                unquote("* unsigned remainder proof SHA-256: ") ==
                umodsi3.fingerprint(address, data, manifest) and
                source_fingerprint(root, address) == source_digest and
                mapping_snapshot(root) == mapping and
                (objects is None or data_snapshot(root) == objects) and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom):
            return False
        if parts is not None:
            parts.update(schema=umodsi3.SCHEMA, data=data, instructions=instructions, mapped=True,
                         control_flow=CALL_SUMMARY, data_profile=objects is not None,
                         unsigned_remainder_evidence=manifest)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def divsi3_report_matches(lines, root, address, parts=None):
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
        selector = divsi3.FRAMED_SELECTOR if verification in (
            f"`{divsi3.FRAMED_SCHEMA}`", f"`{divsi3.FRAMED_SWITCH_SCHEMA}`") else None
        switched = verification in (f"`{divsi3.SWITCH_SCHEMA}`", f"`{divsi3.FRAMED_SWITCH_SCHEMA}`")
        if verification != f"`{divsi3.schema(selector, switched)}`" or mapping is None or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != mapping_fingerprint(mapping) or \
                single("* signed quotient: ") != divsi3.summary(selector, switched) or \
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
        if divsi3.manifest_text(manifest) != encoded_manifest or switched != ("switch" in manifest) or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                single("**MATCH - byte identical** - ") != f"{len(data)}/{len(data)} bytes" or \
                unquote("* signed quotient proof SHA-256: ") != divsi3.fingerprint(
                    address, data, manifest, selector=selector):
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        instructions = verify_divsi3_source(root, address, data, rom, mapping, source_digest, manifest,
                                            selector=selector)
        if not (source_fingerprint(root, address) == source_digest and mapping_snapshot(root) == mapping and
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom):
            return False
        if parts is not None:
            parts.update(schema=divsi3.schema(selector, switched), data=data, instructions=instructions, mapped=True,
                         control_flow=CALL_SUMMARY, quotient_evidence=manifest, signed_quotient_profile=selector)
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def legacy_report_control_flow(lines, root, address, profile, parts=None):
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
        if parts is not None:
            parts.update(data=data, thumb=thumb)
        if profile in (BUFFER_SCHEMA, STACK_BUFFER_SCHEMA):
            return function_thunk.legacy_absence(root, address, data, rom, mapping,
                                                buffer_stack_arguments=profile == STACK_BUFFER_SCHEMA)
        calls = profile in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA) or \
            profile in (DATA_SCHEMA, FRAMED_DATA_SCHEMA) and single("* control flow: ") == CALL_SUMMARY

        self_sites = None
        self_lines = [line for line in lines if line.startswith("* self call")]
        if self_lines:
            # a self-call claim needs the plain direct-call path and exactly
            # the two canonical lines, with sites that the bytes reproduce
            sites_text = [line for line in self_lines if line.startswith("* self call sites: ")]
            if not calls or len(self_lines) != 2 or "* self calls: " + SELF_CALL_SUMMARY not in self_lines or \
                    len(sites_text) != 1 or re.fullmatch(r"`\[[0-9]+(?:,[0-9]+)*\]`", sites_text[0][19:]) is None:
                return False
            offsets = json.loads(sites_text[0][20:-1])
            if self_call_sites_text([address + offset for offset in offsets], address) != sites_text[0][20:-1] or \
                    len(set(offsets)) != len(offsets) or any(offset % 2 or offset + 4 > len(data) for offset in offsets):
                return False
            self_sites = frozenset(address + offset for offset in offsets)

        thunk_calls = set()
        def resolve(target):
            if target == address and self_sites is not None:
                return
            if target in RUNTIME_HELPERS.values():
                thunk_calls.add(target)
                register = (target - RUNTIME_HELPERS["_call_via_r0"]) // 4
                if not thunk_is_call_via(rom, target, register):
                    raise ValueError("legacy call target does not match its runtime thunk")
            else:
                function_address_target(f"func_{target:08X}", entries, address, len(data), len(rom))

        try:
            reached = verify_leaf_instructions(data, address, thumb, call_resolver=resolve if calls else None,
                                               self_calls=self_sites,
                                               incoming_narrow_reads=thumb and self_sites is None)
            if self_sites is not None and {item.address for item in reached
                    if item.mnemonic == "bl" and item.operands and item.operands[0].imm == address} != self_sites:
                return False
            plain_report_fields.check_labels(profile, reached, address, data, thumb, calls)
        except modsi3.AddressedRemainderRequired:
            if profile not in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA) or self_sites is not None:
                return False
            reached = verify_addressed_modsi3_source(
                root, address, data, rom, mapping, single("* source SHA-256: ")[1:-1],
                profile == FRAMED_LINKED_SCHEMA)
        if parts is not None:
            parts.update(instructions=reached, self_sites=self_sites or frozenset())
        if thunk_calls:
            # a library unit report replays with its unit's toolchain
            import library_units
            function_thunk.legacy_absence(root, address, data, rom, mapping,
                                          unit_arguments=library_units.report_arguments("\n".join(lines)))
        return True
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False


def valid_match_verdict(report):
    records = [line for line in report.splitlines()
               if re.match(r"[ \t]*\*\*[ \t]*(?:MATCH\b|NOT[ \t]+MATCHING\b|HAND-ASM\b)", line)]
    return len(records) == 1 and re.fullmatch(
        r"\*\*MATCH - byte identical\*\* - ([1-9][0-9]*)/\1 bytes", records[0]) is not None


VOLATILE_RECORD_PREFIX = "* allowlisted volatile"
VOLATILE_RECORD_ANCHOR = "* source plausibility: plausible"


def volatile_record_lines(report):
    return [line for line in report.split("\n")
            if line.lstrip().startswith(VOLATILE_RECORD_PREFIX)]


def carry_volatile_records(report, records):
    """the report with the allowlisted volatile records in their one place.

    Every writer puts the records directly after its single
    `* source plausibility: plausible` line.  A report that already carries
    records, or lacks that line or has it twice, cannot carry them: ValueError.
    """
    if volatile_record_lines(report):
        raise ValueError("report already carries allowlisted volatile records")
    if not records:
        return report
    lines = report.split("\n")
    anchors = [index for index, line in enumerate(lines) if line == VOLATILE_RECORD_ANCHOR]
    if len(anchors) != 1:
        raise ValueError("report has no single plausible-source line to carry allowlisted volatile records")
    return "\n".join(lines[:anchors[0] + 1] + list(records) + lines[anchors[0] + 1:])


def strip_volatile_records(report, records):
    """the report without its allowlisted volatile records, once they equal `records`.

    The records must sit, contiguous and in order, directly after the single
    `* source plausibility: plausible` line, where every writer puts them.
    report_matches checks them here, centrally, and hands each profile
    validator the report as that profile's writer rendered it.
    """
    records = list(records)
    if volatile_record_lines(report) != records:
        raise ValueError("allowlisted volatile records differ from the recomputed records")
    if not records:
        return report
    lines = report.split("\n")
    anchors = [index for index, line in enumerate(lines) if line == VOLATILE_RECORD_ANCHOR]
    if len(anchors) != 1 or lines[anchors[0] + 1:anchors[0] + 1 + len(records)] != records:
        raise ValueError("allowlisted volatile records do not directly follow the plausible-source line")
    return "\n".join(lines[:anchors[0] + 1] + lines[anchors[0] + 1 + len(records):])


def report_matches(report, root, address):
    if not valid_match_verdict(report):
        return False
    import library_units
    if not library_units.report_admitted(report, root, address):
        # a unit report must bind its current row and compiler; any other
        # report must use the default toolchain, and inside a unit the unit's
        # toolchain must emit the same function
        return False
    if address == 0x08141B14 or '* verification: `elf-symbol-thumb-flash512-read-sector-v1`' in report.splitlines():
        import flash_read_sector
        try:
            return flash_read_sector.report_matches(report, root, address)
        except (OSError, RuntimeError, ValueError, TypeError, KeyError, IndexError, subprocess.SubprocessError):
            return False
    if address == 0x08141C78 or '* verification: `elf-symbol-thumb-flash512-verify-sector-n-bytes-v1`' in report.splitlines():
        import flash_sized_verify
        try:
            return flash_sized_verify.report_matches(report, root, address)
        except (OSError, RuntimeError, ValueError, TypeError, KeyError, IndexError, subprocess.SubprocessError):
            return False
    if address == 0x08141BE0 or '* verification: `elf-symbol-thumb-flash512-verify-sector-v1`' in report.splitlines():
        import flash_sector_verify
        try:
            return flash_sector_verify.report_matches(report, root, address)
        except (OSError, RuntimeError, ValueError, TypeError, KeyError, IndexError, subprocess.SubprocessError):
            return False
    if address == 0x08141AB0 or '* verification: `elf-symbol-thumb-flash512-set-read-flash1-v1`' in report.splitlines():
        import flash_reader_install
        try:
            return flash_reader_install.report_matches(report, root, address)
        except (OSError, RuntimeError, ValueError, TypeError, KeyError, IndexError, subprocess.SubprocessError):
            return False
    if address == 0x08142000 or '* verification: `elf-symbol-thumb-flash-retry-sector-programmer-v1`' in report.splitlines():
        import flash_retry_programmer
        return flash_retry_programmer.replay(report, root, address)
    if address == 0x08142160 or '* verification: `elf-symbol-thumb-flash-sector-programmer-v1`' in report.splitlines():
        import flash_sector_programmer
        return flash_sector_programmer.replay(report, root, address)
    if address == 0x081418C0 or '* verification: `elf-symbol-thumb-flash-read-id-v1`' in report.splitlines():
        import flash_read_id
        return flash_read_id.replay(report, root, address)
    if address == 0x08141EB8 or '* verification: `elf-symbol-thumb-flash-chip-reader-v1`' in report.splitlines():
        import flash_chip_erase
        return flash_chip_erase.replay(report, root, address)
    if address == 0x08141F2C or '* verification: `elf-symbol-thumb-flash-sector-reader-v1`' in report.splitlines():
        import flash_sector_erase
        return flash_sector_erase.replay(report, root, address)
    if address == 0x08142280 or "* verification: `elf-symbol-thumb-libgcc-divdi3-v1`" in report.splitlines():
        import libgcc_divdi3
        try:
            return libgcc_divdi3.report_matches(report, root, address)
        except (OSError, RuntimeError, ValueError, TypeError, KeyError, IndexError, subprocess.SubprocessError):
            return False
    if address == 0x08001244 or "* verification: `original-oam-list-context-v1`" in report.splitlines():
        import oam_list_context
        return oam_list_context.replay(report, root, address)
    if any(line.lstrip().startswith("* self call") for line in report.splitlines()):
        # self-call lines belong to the plain call profiles only; anything
        # else carrying them is a forged or misplaced claim
        stated = report.splitlines()
        plain = [f"* verification: `{schema}`" for schema in (LINKED_SCHEMA, FRAMED_LINKED_SCHEMA)]
        data = [f"* verification: `{schema}`" for schema in (DATA_SCHEMA, FRAMED_DATA_SCHEMA)]
        verdicts = [line for line in stated if line.startswith("* verification:")]
        if len(verdicts) != 1 or not (verdicts[0] in plain or
                verdicts[0] in data and f"* control flow: {CALL_SUMMARY}" in stated):
            return False
    import plausible
    try:
        records = plausible.allowlisted_volatile_uses(root, address)
        if records:
            from match import allowlisted_volatile_semantics
            from named_data_buffer_profile import (BIOS_FILL_SCHEMA, BIOS_FILL_SELECTOR,
                BIOS_LOCAL_FILL_SCHEMA, BIOS_LOCAL_FILL_SELECTOR, BIOS_OVERWRITE_SCHEMA, BIOS_OVERWRITE_SELECTOR)
            if f'* verification: `{BIOS_OVERWRITE_SCHEMA}`' in report.splitlines():
                records += allowlisted_volatile_semantics(root, address,
                    owner_runtime_profile=BIOS_OVERWRITE_SELECTOR)
            elif f'* verification: `{BIOS_LOCAL_FILL_SCHEMA}`' in report.splitlines():
                records += allowlisted_volatile_semantics(root, address,
                    owner_runtime_profile=BIOS_LOCAL_FILL_SELECTOR)
            elif f'* verification: `{BIOS_FILL_SCHEMA}`' in report.splitlines():
                records += allowlisted_volatile_semantics(root, address,
                    owner_runtime_profile=BIOS_FILL_SELECTOR)
            else:
                # a library unit report was compiled with its unit's toolchain
                unit_arguments = library_units.report_arguments(report)
                records += (allowlisted_volatile_semantics(root, address) if unit_arguments is None else
                            allowlisted_volatile_semantics(root, address, unit_arguments))
        if address == 0x08006720 and records:
            import blend_keyframe_loop
            blend_keyframe_loop.report_scope(report)
        if address == 0x0800C4B4:
            import scanline_dispatch
            if not records or not scanline_dispatch.report_body(report, root):
                return False
        if address == 0x080C62CC:
            import history_word_copy
            if not records or not history_word_copy.report_body(report, root):
                return False
        if address == 0x080EF484:
            import scroll_prefix_scene
            if not records or not scroll_prefix_scene.report_body(report, root):
                return False
        if address == 0x08000718:
            import boot_dma0_shadow
            if not boot_dma0_shadow.report_body(report, root):
                return False
        if address == 0x08000FC8:
            import affine_oam_slot
            if not affine_oam_slot.report_body(report, root):
                return False
        if address == 0x0804BF78:
            import tile_cpufill32
            if not tile_cpufill32.report_body(report, root):
                return False
        if address == 0x08141FC8:
            import flash_program_byte
            if not flash_program_byte.report_body(report, root):
                return False
        if address == 0x0814189C:
            import flash_bank_command
            if not flash_bank_command.report_body(report, root):
                return False
        if address == 0x0800DB0C:
            import blend_ramp
            if not blend_ramp.report_body(report, root):
                return False
        if address == 0x0800D3BC:
            import bg_affine_rows
            if not bg_affine_rows.report_body(report, root):
                return False
        if address == 0x0800DE70:
            import scanline_pair
            if not scanline_pair.report_body(report, root):
                return False
        if address == 0x0800C720:
            import scanline_wave
            if not scanline_wave.report_body(report, root):
                return False
        if address == 0x081457FC:
            import m4a_dma_counter
            if not m4a_dma_counter.report_body(report, root):
                return False
        if any(line.startswith("* allowlisted volatile scanline:") for line in records):
            import window_scanline
            if not window_scanline.report_body(report, root, address):
                return False
        report = strip_volatile_records(report, records)
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, subprocess.SubprocessError):
        return False
    try:
        import data_buffer_profile as data_buffer
        if data_buffer.selected(report):
            return data_buffer.report_matches(report, root, address)
        import compiler_orphan_constants_native_profile as orphan_constants
        if orphan_constants.selected(report):
            return orphan_constants.report_matches(report,root,address)
        import unsigned_divmod_profile
        if unsigned_divmod_profile.selected(report):
            return unsigned_divmod_profile.report_matches(report, root, address)
        import palette_source_admission_profile
        if palette_source_admission_profile.selected(report):
            return palette_source_admission_profile.report_matches(report, root, address)
        import private_float_pack_admission_profile
        if private_float_pack_admission_profile.selected(report):
            return private_float_pack_admission_profile.report_matches(report, root, address)
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
        import unit_double_multiply as double_mul
        if double_mul.SCHEMA in report:
            return double_mul.report_matches(report, root, address)
        import unit_double_add_parts as add_parts
        if add_parts.SCHEMA in report:
            return add_parts.report_matches(report, root, address)
        import unit_double_constructor as constructor
        if constructor.SCHEMA in report:
            return constructor.report_matches(report, root, address)
        import unit_float_multiply_profile as multiply
        if multiply.SCHEMA in report:
            return multiply.report_matches(report, root, address)
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
    # Each built-in replay re-verifies the evidence its schema binds and hands
    # it back in `parts`; closed_report then re-renders the whole report from
    # it and compares the text.
    parts = {}
    if profiles == [f"* verification: `{umodsi3.SCHEMA}`"]:
        return umodsi3_report_matches(lines, root, address, parts) and closed_report(report, root, address, parts)
    if any(line.lstrip().startswith("* unsigned remainder") for line in lines):
        return False
    if profiles in ([f"* verification: `{divsi3.SCHEMA}`"],
                     [f"* verification: `{divsi3.FRAMED_SCHEMA}`"],
                     [f"* verification: `{divsi3.SWITCH_SCHEMA}`"],
                     [f"* verification: `{divsi3.FRAMED_SWITCH_SCHEMA}`"]):
        return divsi3_report_matches(lines, root, address, parts) and closed_report(report, root, address, parts)
    if any(line.lstrip().startswith("* signed quotient") for line in lines):
        return False
    if profiles == [f"* verification: `{FUNCTION_BUFFER_SCHEMA}`"]:
        return function_address_report_matches(lines, root, address, buffer_profile=True, parts=parts) and \
            closed_report(report, root, address, parts)
    if any(line.lstrip().startswith("* function buffer") for line in lines):
        return False
    if profiles == [f"* verification: `{modsi3.SCHEMA}`"]:
        return modsi3_report_matches(lines, root, address, parts) and closed_report(report, root, address, parts)
    if any(line.lstrip().startswith("* signed remainder") for line in lines):
        return False
    if profiles == [f"* verification: `{PRELOADED_SWITCH_SCHEMA}`"]:
        return preloaded_switch_report_matches(lines, root, address, parts) and \
            closed_report(report, root, address, parts)
    if profiles in ([f"* verification: `{UDIVSI3_SCHEMA}`"],
                    [f"* verification: `{UDIVSI3_FRAMED_SCHEMA}`"]):
        return udivsi3_report_matches(lines, root, address, parts) and closed_report(report, root, address, parts)
    if any(line.startswith(("* unsigned division:", "* unsigned division manifest:",
                            "* unsigned division proof SHA-256:")) for line in lines):
        return False
    if profiles in ([f"* verification: `{SWITCH_DATA_SCHEMA}`"],
                    [f"* verification: `{SWITCH_MULTIPLE_DATA_SCHEMA}`"],
                    [f"* verification: `{SWITCH_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{SWITCH_POOL_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{pool_switch_frame.SCHEMA}`"],
                    [f"* verification: `{pool_switch_frame.FIXED_SCHEMA}`"],
                    [f"* verification: `{SWITCH_FUNCTION_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{SWITCH_FUNCTION_POOL_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA}`"],
                    [f"* verification: `{typed_switch_frame.SCHEMA}`"],
                    *([f"* verification: `{schema}`"] for schema in switch_data_thunks.SCHEMAS.values())):
        return switch_report_matches(lines, root, address, data_profile=True, parts=parts) and \
            closed_report(report, root, address, parts)
    if profiles == [f"* verification: `{SWITCH_SCHEMA}`"]:
        return switch_report_matches(lines, root, address, parts=parts) and closed_report(report, root, address, parts)
    if any(line.startswith(("* switches:", "* switch manifest:", "* switch proof SHA-256:"))
           for line in lines):
        return False
    if profiles in ([f"* verification: `{FUNCTION_ADDRESS_SCHEMA}`"],
                    [f"* verification: `{FRAMED_FUNCTION_ADDRESS_SCHEMA}`"]):
        return function_address_report_matches(lines, root, address, parts=parts) and \
            closed_report(report, root, address, parts)
    if any(line.startswith(("* function addresses:", "* function address manifest:",
                            "* function address proof SHA-256:")) for line in lines):
        return False
    claimed = re.fullmatch(r"\* verification: `([^`]*)`", profiles[0]) if len(profiles) == 1 else None
    if claimed is not None and plain_report_fields.layout(claimed[1]) is not None:
        try:
            plain_report_fields.check(lines, claimed[1], address, root)
        except ValueError:
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
                stack_arguments=profiles == [f"* verification: `{STACK_BUFFER_SCHEMA}`"], parts=parts)
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
    if not (profile_valid and legacy_report_control_flow(
                lines, root, address, profiles[0].removeprefix("* verification: `").removesuffix("`"), parts) and
            f"* source SHA-256: `{source_fingerprint(root, address)}`" in lines and
            "* source plausibility: plausible" in lines and
            "* relocations: none" in lines and verdict is not None and
            int(verdict[1]) > 0 and verdict[1] == verdict[2]):
        return False
    return legacy_report_closed(report, root, address, profiles[0][len("* verification: `"):-1], parts)


def legacy_report_closed(report, root, address, profile, parts):
    """closed_report for the plain, call, data and buffer profiles.

    The labels in the schema name are already held to the walk:
    plain_report_fields.check_labels (or, on the addressed-remainder path,
    verify_addressed_modsi3_source) holds the frame and call labels,
    buffer_report_matches the buffer version, in match.py's version-1-first
    order.  The mapping and control-flow lines follow from the walk the way
    match.py writes them: a call is a reached BL that leaves the function or
    re-enters its entry.  The data choice is the report's: whether the compiled
    object links a data relocation is known only to a compile (see
    closed_report).
    """
    try:
        instructions, data = parts["instructions"], parts["data"]
        called = any(item.mnemonic == "bl" and item.operands and
                     not address < item.operands[0].imm < address + len(data) for item in instructions)
    except (KeyError, TypeError, AttributeError):
        return False
    linked_data = profile in (DATA_SCHEMA, FRAMED_DATA_SCHEMA)
    return closed_report(report, root, address, dict(
        parts, schema=profile, mapped=called or linked_data,
        control_flow=CALL_SUMMARY if called else "closed leaf CFG", data_profile=linked_data))
