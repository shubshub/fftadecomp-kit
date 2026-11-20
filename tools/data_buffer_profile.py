"""Typed named-data literals beside the version-2 bounded buffer proof.

Schemas for matcher paths that reach a buffer call with named data:

* ``elf-symbol-thumb-data-buffer-calls-v1`` (plain direct-call path): the
  version-2 register and stack buffer proof with bounded loop replay
  (``BufferCallProof``), exactly as ``elf-symbol-thumb-frame-buffer-calls-v2``
  runs it, beside the typed object literals ``elf-symbol-thumb-data-v1`` binds.
* ``elf-symbol-thumb-function-data-buffer-calls-v1`` (function-literal path):
  the same proof with the function-buffer restrictions
  (``FunctionBufferCallProof``), beside typed object and function literals.
* The menu list callback adds a restoring-frame proof for its two far epilogue jumps.

Both require typed provenance for every reached RAM or ROM address-domain
literal word, as the complete-owner selectors do; untyped words in the fixed
hardware window are numbers, classified by the owner rule's
``reached-numeric-hardware-literals-v1`` class. A typed data literal is an
absolute address, never SP-derived, so the alias walk never tracks it; that
named objects do not overlap a live stack is a premise, not a check.
"""
import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import struct
import sys
import tempfile

import rom_mirror
from menu_list_frame import MenuListFrame, ADDRESS as MENU_LIST_ADDRESS

SCHEMA = "elf-symbol-thumb-data-buffer-calls-v1"
FUNCTION_SCHEMA = "elf-symbol-thumb-function-data-buffer-calls-v1"
MENU_LIST_SCHEMA = "elf-symbol-thumb-menu-list-long-branches-v1"
SCHEMAS = (SCHEMA, FUNCTION_SCHEMA, MENU_LIST_SCHEMA)
PREMISE = "premise, not checked: named objects do not overlap any live stack"
SUMMARIES = {
    SCHEMA: "typed ABS32 object literals beside the ROM-checked version-2 buffer proof; "
            "every reached RAM/ROM address word typed; " + PREMISE,
    MENU_LIST_SCHEMA: "typed object and function literals with two same-owner long BL jumps, restoring "
                      "frame and ROM-checked byte outputs; " + PREMISE,
    FUNCTION_SCHEMA: "typed ABS32 object and canonical function literals beside the ROM-checked "
                     "version-2 function-buffer proof; every reached RAM/ROM address word typed; " + PREMISE,
}
MARKER = "* data buffer"
CALLS_FIELD = "* data buffer calls: "
MANIFEST_FIELD = "* data buffer manifest: "
PROOF_FIELD = "* data buffer proof SHA-256: "
# Reached PC-loaded words in this window need typed provenance (the owner rule's
# RAM, I/O-to-OAM and ROM domains), apart from the numeric hardware class. A ROM
# wait-state mirror word is folded onto the ROM it names before the test.
ADDRESS_DOMAIN = rom_mirror.TYPED_DOMAIN
# owner_admission_profile.NUMERIC_HARDWARE: the I/O, palette, VRAM and OAM window.
HARDWARE_WINDOW = (0x04000000, 0x08000000)
REPLAY_TIMEOUT = 120
_replay_active = ContextVar("data_buffer_replay_active", default=False)


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def fingerprint(schema, address, data, manifest, source_digest, mapping, objects, buffer_digest):
    from match_evidence import STACK_BUFFER_SCHEMA
    if schema not in SCHEMAS:
        raise ValueError("unknown data-buffer schema")
    digest = hashlib.sha256()
    for payload in (schema.encode("ascii"), STACK_BUFFER_SCHEMA.encode("ascii"),
                    address.to_bytes(4, "little"), data, manifest_text(manifest).encode("ascii"),
                    source_digest.encode("ascii"), mapping, objects, buffer_digest.encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def report_lines(schema, address, data, manifest, source_digest, mapping, objects, buffer_digest):
    return [CALLS_FIELD + SUMMARIES[schema],
            f"{MANIFEST_FIELD}`{manifest_text(manifest)}`",
            f"{PROOF_FIELD}`{fingerprint(schema, address, data, manifest, source_digest, mapping, objects, buffer_digest)}`"]


def call_name(target):
    from match import RUNTIME_HELPERS
    names = [name for name, value in RUNTIME_HELPERS.items() if value == target]
    return names[0] if names else f"func_{target:08X}"


def reached_words(data, address, instructions):
    """{offset: (value, [load sites])} for every reached PC-relative word load."""
    from match import ARM_OP_MEM, ARM_REG_PC
    words = {}
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                if (address + offset) % 4 or not 0 <= offset <= len(data) - 4:
                    raise ValueError("reached literal is not a complete aligned caller word")
                value = struct.unpack_from("<I", data, offset)[0]
                words.setdefault(offset, (value, []))[1].append(instruction.address)
    return {offset: (value, sorted(sites)) for offset, (value, sites) in words.items()}


def numeric_hardware(data, address, mapping, instructions, calls, words, remaining, *, branches_expected=None):
    """The owner rule's numeric hardware class, over the exact complete owner graph."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    refinement = owner.refine(data, address, mapping)
    graph_instructions, edges, branches, _, table_words = graph.graph(data, address, refinement)
    if branches != (branches_expected or {}) or table_words or \
            set(graph_instructions) != {item.address for item in instructions}:
        raise ValueError("numeric hardware words require the exact complete owner graph")
    partition = {"words": [{"address": address + offset, "value": value, "load_sites": sites,
                            "switch_word": False} for offset, (value, sites) in sorted(words.items())]}
    return owner.numeric_hardware_words(graph_instructions, edges, calls, partition, address, remaining)


def prove(data, address, rom, mapping, objects, calls, data_relocations, function_relocations=None, *,
          index=None, switch_relocations=None, dma_fills=None):
    """The composed proof for linked bytes; returns (instructions, buffer proof, schema, manifest).

    calls maps each BL site to its target, data_relocations each typed object word
    offset to (name, value) and function_relocations each function word offset
    to (name, value), all from the exact link of the original ELF.  index is the
    function index snapshot that the plain path's default-walk summaries read
    (copy_helper_summary_profile, switch_callee_profile) and the restoring menu frame requires.
    switch_relocations, the owner's own jump table from the same link, is walked by
    owner_switch_buffer_profile on the plain path only; its table pointer is that
    proof's word, not an untyped literal.
    dma_fills, a fresh dma_fill_profile.Fills, goes to the plain path's walk; the
    function-literal path has no DMA fill rule, so a DMA source store there stays refused.
    """
    import match
    import function_thunk_profile as thunk
    function_relocations = function_relocations or {}
    schema = FUNCTION_SCHEMA if function_relocations else SCHEMA
    if not data_relocations:
        raise ValueError("data-buffer evidence requires typed named object relocations")
    symbols = match.parse_data_symbols(objects)
    if any(name not in symbols for name, _ in data_relocations.values()):
        raise ValueError("data-buffer object relocation is not in the data symbol map")
    manifest = {
        "calls": [[site - address, call_name(target)] for site, target in sorted(calls.items())],
        "data": [[offset, name, value - symbols[name]] for offset, (name, value) in sorted(data_relocations.items())],
        "functions": [[offset, name] for offset, (name, _) in sorted(function_relocations.items())]}
    entries = json.loads(mapping)
    if schema == FUNCTION_SCHEMA:
        # The function-literal path's own bindings: canonical function literals,
        # direct calls only (no runtime thunks), typed object words.
        bound, literals = match.function_address_bindings(data, address, rom, mapping, objects, manifest)
        if bound != calls:
            raise ValueError("data-buffer calls differ from their canonical bindings")
        if address == 0x0801A518:
            from map_record_loader import MapRecordProof
            proof = MapRecordProof(data, rom, mapping, index, calls)
        else:
            proof = match.FunctionBufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True)
    else:
        # The plain path's call rules: direct calls and the canonical _call_via_rN
        # thunks; the object words are bound like the function-literal path's.
        _, literals = match.function_address_bindings(
            data, address, rom, mapping, objects, dict(manifest, calls=[]), allow_empty_functions=True)
        occupied = {byte for offset in literals for byte in range(offset, offset + 4)}
        for site, target in sorted(calls.items()):
            offset = site - address
            if offset % 2 or not 0 <= offset <= len(data) - 4 or \
                    occupied & set(range(offset, offset + 4)):
                raise ValueError("data-buffer calls must be complete instructions outside literal words")
            if target in match.RUNTIME_HELPERS.values():
                if not match.thunk_is_call_via(rom, target, (target - match.RUNTIME_HELPERS["_call_via_r0"]) // 4):
                    raise ValueError("data-buffer call target does not match its runtime thunk")
            elif match.function_address_target(f"func_{target:08X}", entries, address, len(data), len(rom)) != target:
                raise ValueError("data-buffer call target is not its canonical function")
        thunk.verify_data_bindings(calls, literals, symbols, entries)
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True, loop_replay=True, bios_wrappers=True,
                                      copy_helper_index=index, switch_callee_index=index)
    if proof.span(address) != data:
        raise ValueError("data-buffer caller requires an exact complete mapped span")
    frame = None
    if address == MENU_LIST_ADDRESS and schema == FUNCTION_SCHEMA:
        if switch_relocations or dma_fills is not None:
            raise ValueError("menu list has no switch table or DMA fill proof")
        frame = MenuListFrame(data, rom, mapping, index, objects, data_relocations, function_relocations)
    if switch_relocations:
        # The owner's own jump table; only the plain proof takes it (owner_switch_buffer_profile).
        import owner_switch_buffer_profile as owner_switch
        instructions = owner_switch.walk(proof, data, address, calls, switch_relocations)
    elif schema == FUNCTION_SCHEMA:
        instructions = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof, menu_list_frame=frame)
        if frame is not None:
            schema = MENU_LIST_SCHEMA
            manifest["restoring_menu_frame"] = frame.evidence
    else:
        instructions = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof,
                                                      incoming_narrow_reads=True, dma_fills=dma_fills)
    if not proof.dependencies:
        raise ValueError("data-buffer evidence requires an inspected buffer call")
    match.verify_data_literals(instructions, address, literals)
    thunk.verify_literal_bindings(data, address, instructions, calls, mapping, function_relocations)
    if any(thunk.reserved(target) for target in calls.values()):
        thunk.verify_own_span_literals(data, address, instructions)
    # Every reached RAM/ROM address-domain word, a ROM mirror word included, is a
    # typed object or function literal, and every typed literal is a domain word
    # spelled at its canonical address; hardware-window words that are neither
    # are numbers (the owner rule's numeric hardware class).
    words = reached_words(data, address, instructions)
    domain = {offset for offset, (value, _) in words.items() if rom_mirror.typed_domain(value)}
    remaining = domain - set(literals)
    if proof.owner_switch is not None:
        # The owner switch's table pointer, read only by its dispatch, is that layout's word;
        # the case words are never loaded by PC.
        switch = proof.owner_switch.record["switch"]
        if words.get(switch["literal"], (None, []))[1] == [address + switch["dispatch"] + 2]:
            remaining.discard(switch["literal"])
    hardware = []
    if any(HARDWARE_WINDOW[0] <= words[offset][0] < HARDWARE_WINDOW[1] for offset in remaining):
        import owner_admission_profile as owner
        hardware = numeric_hardware(data, address, mapping, instructions, calls, words, remaining,
                                    branches_expected=frame.BRANCHES if frame is not None else None)
        if hardware:
            manifest["numeric_hardware_words"] = owner.numeric_hardware_record(hardware)
    untyped = sorted(remaining - {row[0] for row in hardware})
    outside = sorted(set(literals) - {offset for offset in domain if not rom_mirror.mirror(words[offset][0])})
    if untyped or outside:
        raise ValueError("data-buffer address literals require exact typed object/function coverage: " +
                         ", ".join([f"untyped word 0x{address + offset:08X} = 0x{words[offset][0]:08X}"
                                    for offset in untyped] +
                                   [f"typed word 0x{address + offset:08X} outside the address domain"
                                    for offset in outside]))
    if schema == FUNCTION_SCHEMA and address == 0x0801A518:
        manifest["record_loader"] = proof.finish()
    return instructions, proof, schema, manifest


def selected(report):
    lines = report.splitlines()
    return any(line.lstrip().startswith(MARKER) for line in lines) or any(
        f"* verification: `{schema}`" in (line.strip() for line in lines) for schema in SCHEMAS)


def verify_source(root, address, data, rom, mapping, objects, source_digest, dma_fills=None):
    """Recompile and relink the captured source, then rerun the composed proof."""
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS,
                       DEFAULT_WSL_PATH, Runner, compile_object, link_calls, _run_replay_process,
                       plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    from inert_spin_profile import index_snapshot
    if _replay_active.get():
        raise ValueError("recursive data-buffer replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        selected_rom = report_rom_path(root)
        index = index_snapshot(root) if (root / "symbols/functions.txt").is_file() else None

        def unchanged():
            return source_fingerprint(root, address) == source_digest and mapping_snapshot(root) == mapping and \
                data_snapshot(root) == objects and report_rom_path(root) == selected_rom and \
                Path(selected_rom).read_bytes() == rom
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or not unchanged():
            raise ValueError("data-buffer replay inputs differ")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_data_buffer_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("data-buffer source snapshot differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                candidates[0].relative_to(root).as_posix())
                functions, switches = {}, {}
                got, calls, literals = link_calls(runner, workspace, args, original, address, mapping,
                                                  len(rom), rom, objects, functions, switches,
                                                  allow_switch_data=True)
            if got != data:
                raise ValueError("data-buffer fresh complete bytes differ")
            result = prove(got, address, rom, mapping, objects, calls, literals, functions, index=index,
                           switch_relocations=switches, dma_fills=dma_fills)
            checker = Path(__file__).with_name("plausible.py")
            checked = _run_replay_process([sys.executable, str(checker), "--quiet", "--addr",
                                           f"0x{address:08X}", "--json"] +
                                          [str(path) for path in source_paths(captured, address)],
                                          captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(checked, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("data-buffer captured source changed or is implausible")
        if result[2] == MENU_LIST_SCHEMA and index_snapshot(root) != index:
            raise ValueError("menu list function index changed during replay")
        if not unchanged():
            raise ValueError("data-buffer replay inputs changed")
        return result
    finally:
        _replay_active.reset(token)


# Every unindented `* ` field a data-buffer report may carry; only the replay,
# copy-summary, switch-callee, BIOS premise and DMA fill premise lines may repeat. Anything else, or any
# indented field, refuses.
FIELDS = ("* source", "* verification", "* source SHA-256", "* stack frame", "* buffer calls",
          "* buffer proof SHA-256", "* buffer loop replay", "* buffer copy summary", "* buffer switch callee",
          "* buffer owner switch", "* mapping SHA-256", "* control flow",
          "* buffer BIOS summaries", "* buffer BIOS premise", "* buffer BIOS manifest",
          "* data symbols SHA-256", "* data buffer calls", "* data buffer manifest",
          "* data buffer proof SHA-256", "* compiler", "* verified extent", "* relocations",
          "* ROM bytes", "* compiled ", "* source plausibility", "* hand-asm allow list",
          "* DMA fills", "* DMA fill premise", "* DMA fill manifest")


def report_matches(report, root, address):
    from match import DEFAULT_CC, DEFAULT_FLAGS, uses_stack_frame
    from match_evidence import (CALL_SUMMARY, STACK_BUFFER_SUMMARY, STACK_SUMMARY, buffer_proof_lines, data_snapshot,
                                mapping_fingerprint, mapping_snapshot, report_rom_path, source_fingerprint)
    import dma_fill_profile as dma_fill
    lines = report.splitlines()

    def key(line):
        return line.split(":", 1)[0]

    def single(prefix):
        matches = [line for line in lines if key(line) == key(prefix)]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, duplicate or malformed data-buffer field")
        return matches[0][len(prefix):]

    def quoted(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed data-buffer quoted field")
        return value[1:-1]

    def unique(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate data-buffer manifest key")
            result[name] = value
        return result

    try:
        if any(line != line.lstrip() and line.lstrip().startswith("*") for line in lines) or any(
                line.startswith("* ") and key(line) not in FIELDS for line in lines) or any(
                key(line) == "* buffer loop replay" and not line.startswith("* buffer loop replay: ")
                for line in lines):
            return False
        schema = quoted("* verification: ")
        if schema not in SCHEMAS:
            return False
        functions, objects = mapping_snapshot(root), data_snapshot(root)
        source_digest = source_fingerprint(root, address)
        paths = list((Path(root) / "src").rglob(f"{address:08X}.c"))
        if functions is None or objects is None or len(paths) != 1 or \
                quoted("* source: ") != paths[0].relative_to(root).as_posix() or \
                quoted("* source SHA-256: ") != source_digest or \
                quoted("* mapping SHA-256: ") != mapping_fingerprint(functions) or \
                quoted("* data symbols SHA-256: ") != mapping_fingerprint(objects) or \
                single("* control flow: ") != CALL_SUMMARY or \
                single("* buffer calls: ") != STACK_BUFFER_SUMMARY or \
                single(CALLS_FIELD) != SUMMARIES[schema] or \
                quoted("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or single("* source plausibility: ") != "plausible" or \
                single("* hand-asm allow list: ") != "not listed":
            return False
        encoded = quoted("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        if single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes" not in lines:
            return False
        encoded_manifest = quoted(MANIFEST_FIELD)
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique)
        if manifest_text(manifest) != encoded_manifest:
            return False
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        # DMA fill lines (kit #239) replay with the same rule and must equal the recomputed lines.
        dma_lines = dma_fill.report_fields(lines)
        fills = dma_fill.Fills(rom) if dma_lines else None
        instructions, proof, proved_schema, proved = verify_source(
            root, address, data, rom, functions, objects, source_digest, fills)
        if fills is not None:
            dma_fill.check_report(fills, lines)
        framed = uses_stack_frame(instructions)
        stack_lines = [line for line in lines if key(line) == "* stack frame"]
        if not (proved_schema == schema and proved == manifest and
                stack_lines == ([f"* stack frame: {STACK_SUMMARY}"] if framed else []) and
                quoted("* buffer proof SHA-256: ") == proof.fingerprint() and
                buffer_proof_lines(lines) == proof.loop_replay_lines() + proof.bios_summary_lines() and
                quoted(PROOF_FIELD) == fingerprint(schema, address, data, manifest, source_digest,
                                                   functions, objects, proof.fingerprint()) and
                source_fingerprint(root, address) == source_digest and mapping_snapshot(root) == functions and
                data_snapshot(root) == objects and report_rom_path(root) == selected_rom and
                Path(selected_rom).read_bytes() == rom):
            return False
        from match_evidence import closed_report
        return closed_report(report, root, address, dict(
            schema=schema, data=data, instructions=instructions, buffer_proof=proof, mapped=True,
            control_flow=CALL_SUMMARY, data_profile=True, data_mapping=objects, data_buffer_evidence=manifest,
            dma_lines=fills.report_lines() if fills is not None else ()))
    except (OSError, ValueError, KeyError, TypeError, AttributeError, OverflowError, RecursionError,
            RuntimeError, json.JSONDecodeError):
        return False
