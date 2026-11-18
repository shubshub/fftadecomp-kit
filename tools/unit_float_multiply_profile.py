"""Fresh source replay of the old-agbcc fp-bit __mulsf3 library member."""
import argparse
import os
from pathlib import Path
import re
import shutil
import struct
import sys
import tempfile

import library_units as units
import private_float_inline_division_inventory as parts
import software_float_profile as runtime

SCHEMA = "elf-symbol-thumb-fp-bit-mulsf3-unit-v1"
ADDRESS, END = 0x08143CEC, 0x08143E54
UNIT_START, UNIT_END = 0x081439C8, 0x081443AE
TOOLCHAIN = "old-agbcc-O2-v1"
UNIT_DIGEST = "29f04fc63c3da5f6796be91008ee1c5537db51b98999a6886b3a7b47dd09c92c"
UNPACK, MULTIPLY, PACK = 0x08143A84, 0x08142A20, 0x081439C8
OBJECT = "data_03005E68"
TARGETS = {"func_08143A84": UNPACK, "__muldi3": MULTIPLY, "func_081439C8": PACK, OBJECT: 0x03005E68}
SITES = {0x12: "func_08143A84", 0x1c: "func_08143A84", 0x80: OBJECT,
         0xc8: "__muldi3", 0x152: "func_081439C8"}
CALLS = {ADDRESS + offset: TARGETS[name] for offset, name in SITES.items() if name != OBJECT}


def unit_owner(unit, address, orphan=None):
    return (unit is not None and address == ADDRESS and orphan is None and unit.toolchain == TOOLCHAIN and
            unit.name == "libgcc fp-bit, _cmpdi2, _lshrdi3" and
            (unit.start, unit.end, unit.proof) == (UNIT_START, UNIT_END, 0x0814435C) and
            unit.row["identity"] == [{"address": f"0x{UNIT_START:08X}", "size": UNIT_END - UNIT_START,
                                      "sha256": UNIT_DIGEST}])


def original_bindings(image):
    """All five nonoverlapping REL sites have fixed names, types and zero addends."""
    from addressed_signed_runtime_profile import original_function
    if original_function(image, ADDRESS)["size"] != END - ADDRESS or len(image["text"]) != END - ADDRESS:
        raise ValueError("fp-bit multiply requires the complete original function")
    undefined = [symbol["name"] for symbol in image["symbols"] if symbol["name"] and not symbol["section"]]
    if sorted(undefined) != sorted(TARGETS):
        raise ValueError("fp-bit multiply requires its exact undefined symbol namespace")
    seen = set()
    for idx in image["relocations"]:
        section = image["sections"][idx]
        if section[1] != 9 or section[7] != image["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("fp-bit multiply requires text REL relocations")
        symbols = image["symbol_tables"].get(section[6])
        for offset, info in struct.iter_unpack("<II", image["section_data"][idx]):
            if symbols is None or info >> 8 >= len(symbols):
                raise ValueError("fp-bit multiply REL has no matching symbol")
            symbol = symbols[info >> 8]
            name = SITES.get(offset)
            is_data = name == OBJECT
            if name is None or offset in seen or symbol["name"] != name or symbol["section"] or \
                    symbol["bind"] != 1 or symbol["type"] not in (0, 1 if is_data else 2) or \
                    symbol["value"] or symbol["size"] or info & 255 != (2 if is_data else 10) or \
                    sum(item["name"] == name for item in image["symbols"]) != 1 or \
                    image["text"][offset:offset+4] != (bytes(4) if is_data else bytes.fromhex("fff7feff")):
                raise ValueError("fp-bit multiply has an incorrect original relocation, symbol or addend")
            seen.add(offset)
    if seen != set(SITES):
        raise ValueError("fp-bit multiply lacks required original relocations")


def native_proof(data, rom, mapping, index, objects):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import indices, span_record
    if units.sha(rom) != runtime.ROM_SHA256 or match.parse_data_symbols(objects).get(OBJECT) != TARGETS[OBJECT]:
        raise ValueError("fp-bit multiply requires the approved ROM and named NaN record")
    entries, rows = indices(mapping, index)
    identities = {record[0]: record for record in runtime.IDENTITIES}
    dependencies = {}
    if data != rom[ADDRESS-match.ROM_BASE:END-match.ROM_BASE]:
        raise ValueError("fp-bit multiply differs from the complete pinned ROM caller")
    for start in (UNPACK, MULTIPLY, PACK, ADDRESS):
        _, end, count, digest = identities[start]
        record = span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record["instrs"] != count or units.sha(body) != digest:
            raise ValueError("fp-bit multiply helper or caller identity differs")
        if start != ADDRESS:
            bounds = next((bounds for _, identity, bounds in parts.HELPERS if identity[0] == start), parts.policy())
            dependencies[start] = runtime.prove_runtime(rom, entries, start, end, count, {}, call_edges=(),
                scalar_entries=(), argument_effect_policy=bounds)
    count = identities[ADDRESS][2]
    refinement = owner.refine(data, ADDRESS, mapping)
    ins, edges, branches, calls, words = graph.graph(data, ADDRESS, refinement)
    if calls != CALLS or branches or words or len(ins) != count:
        raise ValueError("fp-bit multiply has a different CFG or helper bindings")
    partition = graph.partition(data, ADDRESS, refinement, ins, words)
    if not any(word['address'] == ADDRESS + 0x80 and word['value'] == TARGETS[OBJECT] and
               word['load_sites'] and not word['switch_word'] for word in partition['words']):
        raise ValueError("fp-bit multiply requires its reached named data literal")
    caller = runtime.prove_runtime(rom, entries, ADDRESS, END, count, dependencies,
        call_edges=tuple(sorted(calls.items())), scalar_entries=(ADDRESS,), argument_effect_policy=parts.policy(),
        compose_pointer_returns=True, absolute_read_policy=parts.ABSOLUTE_POLICY)
    if caller['native_edges'] != [[site, list(succ)] for site, succ in sorted(edges.items())] or \
            caller['absolute_reads']['reads'] != parts.ABSOLUTE_POLICY['reads'] or \
            caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError("fp-bit multiply has unaccounted reachable effects")
    return {"instructions": count, "partition": partition, "returns": caller["returns"],
            "helper_calls": sorted(calls.items()), "conditional_reads": caller["absolute_reads"]["reads"],
            "caller_cfg_and_effects_sha256": units.sha(units.canonical(caller).encode()),
            "helper_proofs_sha256": units.sha(units.canonical(dependencies).encode())}


def build(root, address, args=None):
    import match
    from addressed_signed_runtime_profile import linked_bytes
    from match_evidence import source_fingerprint, source_paths, mapping_snapshot, data_snapshot, report_rom_path
    from plausible import strip_comments_and_strings
    root = Path(root).resolve()

    def inputs():
        rom_path = report_rom_path(root)
        return (source_fingerprint(root, address), mapping_snapshot(root), runtime.index_snapshot(root),
                data_snapshot(root), units.snapshot(root), rom_path, Path(rom_path).read_bytes())

    source, mapping, index, objects, table, _, rom = before = inputs()
    unit = units.containing(units.parse(table, rom, mapping), address, address + END - ADDRESS)
    if not unit_owner(unit, address):
        raise ValueError("fp-bit multiply requires the pinned full fp-bit library unit")
    tool = units.resolve(TOOLCHAIN)
    config = dict(cc=tool["cc"], flags=tool["flags"], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                  linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
    if args is not None and any(getattr(args, key) != value for key, value in config.items()):
        raise ValueError("fp-bit multiply requires the fixed old compiler configuration")
    args = argparse.Namespace(**config)

    def executables():
        path = os.path.expandvars(match.DEFAULT_WSL_PATH) + os.pathsep + os.environ["PATH"]
        names = (args.cc, args.cpp, args.assembler, args.linker, args.objcopy)
        return {name: units.sha(Path(shutil.which(os.path.expandvars(name), path=path)).read_bytes()) for name in names}

    binaries = executables()
    candidates = list((root/"src").rglob(f"{address:08X}.c"))
    if len(candidates) != 1:
        raise ValueError("fp-bit multiply requires exactly one source file")
    relative = candidates[0].relative_to(root)
    (root/"build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=root/"build", prefix="fp_bit_mulsf_") as directory:
        capture = Path(directory)
        for path in source_paths(root, address):
            dest = capture / path.relative_to(root)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(path.read_bytes())
        if source_fingerprint(capture, address) != source:
            raise ValueError("fp-bit multiply source capture differs")
        runner = match.Runner(args.cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=capture, timeout=120)
        with runner.workspace() as workspace:
            raw, _, original = match.compile_object(runner, workspace, args, capture, address, relative.as_posix())
            preprocessed = runner.read_binary(workspace + "/f.i").decode()
            if re.search(r"\b__muldi3\b", strip_comments_and_strings(preprocessed)):
                raise ValueError("fp-bit multiply requires compiler-generated wide multiplication")
            original_bindings(original)
            linked = match.link_typed_targets(runner, workspace, args, f"func_{address:08X}", address, TARGETS, {OBJECT})
            body = linked_bytes(original, linked, address, CALLS, TARGETS, data_relocations={0x80: (OBJECT, 0)})
            raw_linked = runner.read_binary(workspace + "/f.elf")
        checker = Path(__file__).with_name("plausible.py")
        process = match._run_replay_process([sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
            [str(path) for path in source_paths(capture, address)], capture, 120)
        findings, allowed = match.plausibility_result(process, address)
        if findings or allowed or source_fingerprint(capture, address) != source:
            raise ValueError("fp-bit multiply captured source changed or is implausible")
    proof = native_proof(body, rom, mapping, index, objects)
    if inputs() != before or units.resolve(TOOLCHAIN) != tool or executables() != binaries:
        raise ValueError("fp-bit multiply source, ROM, indexes, unit or tool changed during replay")
    evidence = dict(source=source, functions=units.sha(mapping), index=units.sha(index), objects=units.sha(objects),
                    rom=units.sha(rom), unit=unit.text, compiler=tool, tool_binaries=binaries, original_elf=units.sha(raw),
                    linked_elf=units.sha(raw_linked), cfg=proof)
    report = "\n".join([f"# match report - 0x{address:08X}", "", f"* source: `{relative.as_posix()}`",
        f"* verification: `{SCHEMA}`", f"* source SHA-256: `{source}`",
        *units.report_lines({"unit": unit, "tool": tool}, None), f"* compiler: `{args.cc} {args.flags}`",
        "* control flow: reached Thumb returns restore the frame and callee-saved registers; conditional reads of the NaN record",
        "* verified extent: complete ELF function symbol, including literal pools", "* relocations: none",
        "* source plausibility: plausible", "* hand-asm allow list: not listed",
        f"* fp-bit multiply evidence: `{units.canonical(evidence)}`",
        f"* compiled : `{body.hex()}`", f"* ROM bytes: `{body.hex()}` ({len(body)} bytes)", "",
        f"**MATCH - byte identical** - {len(body)}/{len(body)} bytes", ""])
    return body, report


def report_matches(report, root, address):
    return address == ADDRESS and report == build(root, address)[1]


def issue(root, address, args):
    if args.label:
        raise ValueError("fp-bit multiply requires the canonical report name")
    body, report = build(root, address, args)
    if args.emit:
        output = (Path(root) / args.emit).resolve()
        if (Path(root) / "build").resolve() not in output.parents:
            raise ValueError("--emit requires a new file beneath build/")
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("xb") as stream:
            stream.write(body)
    if not args.no_write:
        path = Path(root) / "docs/match" / f"{address:08X}.md"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(report, encoding="utf-8")
    print(f"extent    {len(body)} bytes (complete ELF symbol, 171 reachable instructions)")
    print("verdict MATCH - byte identical")
    return 0
