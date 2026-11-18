"""Fixed old-agbcc source capture, ELF replay and receipts for addressed fp-bit members."""
import argparse
import os
from pathlib import Path
import shutil
import struct
import sys
import tempfile

import library_units as units
import software_float_profile as runtime


DP_DIGEST = 'fd4260dbe23fa4058473ccd446851e3aa2a4e6a73ec65eebf4838bf401bcd7f0'


def dp_unit(unit):
    return (unit is not None and unit.name == 'libgcc dp-bit' and
            unit.toolchain == 'old-agbcc-O2-v1' and
            (unit.start, unit.end, unit.proof) == (0x08142BE8, 0x081439C8, 0x08142D34) and
            unit.row['identity'] == [dict(address='0x08142BE8', size=3552, sha256=DP_DIGEST)])


def reviewed_source(capture, relative, address, names, digest, *, headers=()):
    import plausible
    from sdk_cpuset_halfword import TOKEN, base_header
    path = capture / relative
    text = path.read_text()
    wanted = f'src/{address:08X}.c'
    includes = {wanted, 'include/ffta.h', *(name for name, _ in headers)}
    if any(units.sha((capture/name).read_bytes()) != checksum for name, checksum in headers):
        raise ValueError('dp-bit private type header differs from its reviewed definition')
    if relative.as_posix() != wanted or plausible.include_closure(capture, path) != (
            includes, []) or not base_header((capture/'include/ffta.h').read_bytes(), names):
        raise ValueError('dp-bit source requires the original public types and one addressed source')
    tokens = TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text))
    if any(marker in text for marker in ('\\', '??', '%:', '\0')) or units.sha(' '.join(tokens).encode()) != digest:
        raise ValueError('dp-bit source differs from the reviewed library signature or arithmetic')


def fixed_bindings(image, address, end, targets, sites, data_name):
    """Require the original complete symbol and every specified zero-addend REL site."""
    from addressed_signed_runtime_profile import original_function
    if original_function(image, address)["size"] != end - address or len(image["text"]) != end - address:
        raise ValueError("fp-bit member requires the complete original function")
    undefined = [symbol["name"] for symbol in image["symbols"] if symbol["name"] and not symbol["section"]]
    if sorted(undefined) != sorted(targets):
        raise ValueError("fp-bit member requires its exact undefined symbol namespace")
    seen = set()
    for idx in image["relocations"]:
        section = image["sections"][idx]
        if section[1] != 9 or section[7] != image["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("fp-bit member requires text REL relocations")
        symbols = image["symbol_tables"].get(section[6])
        for offset, info in struct.iter_unpack("<II", image["section_data"][idx]):
            if symbols is None or info >> 8 >= len(symbols):
                raise ValueError("fp-bit member REL has no matching symbol")
            symbol = symbols[info >> 8]
            name = sites.get(offset)
            is_data = name == data_name
            if name is None or offset in seen or symbol["name"] != name or symbol["section"] or \
                    symbol["bind"] != 1 or symbol["type"] not in (0, 1 if is_data else 2) or \
                    symbol["value"] or symbol["size"] or info & 255 != (2 if is_data else 10) or \
                    sum(item["name"] == name for item in image["symbols"]) != 1 or \
                    image["text"][offset:offset+4] != (bytes(4) if is_data else bytes.fromhex("fff7feff")):
                raise ValueError("fp-bit member has an incorrect original relocation, symbol or addend")
            seen.add(offset)
    if seen != set(sites):
        raise ValueError("fp-bit member lacks required original relocations")


def multiply_effects(data, rom, mapping, entries, dependencies, address, end, count, bindings,
                     literal, record, absolute_policy):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import private_float_argument_effects_inventory as parts
    refinement = owner.refine(data, address, mapping)
    ins, edges, branches, calls, words = graph.graph(data, address, refinement)
    if calls != bindings or branches or words or len(ins) != count:
        raise ValueError("fp-bit multiply has a different CFG or helper bindings")
    partition = graph.partition(data, address, refinement, ins, words)
    if not any(word['address'] == literal and word['value'] == record and
               word['load_sites'] and not word['switch_word'] for word in partition['words']):
        raise ValueError("fp-bit multiply requires its reached named data literal")
    caller = runtime.prove_runtime(rom, entries, address, end, count, dependencies,
        call_edges=tuple(sorted(calls.items())), scalar_entries=(address,), argument_effect_policy=parts.policy(),
        compose_pointer_returns=True, absolute_read_policy=absolute_policy)
    if caller['native_edges'] != [[site, list(succ)] for site, succ in sorted(edges.items())] or \
            caller['absolute_reads']['reads'] != absolute_policy['reads'] or \
            caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError("fp-bit multiply has unaccounted reachable effects")
    return {"instructions": count, "partition": partition, "returns": caller["returns"],
            "helper_calls": sorted(calls.items()), "conditional_reads": caller["absolute_reads"]["reads"],
            "caller_cfg_and_effects_sha256": units.sha(units.canonical(caller).encode()),
            "helper_proofs_sha256": units.sha(units.canonical(dependencies).encode())}


def build(member, root, address, args=None):
    import match
    from match_evidence import source_fingerprint, source_paths, mapping_snapshot, data_snapshot, report_rom_path
    root = Path(root).resolve()

    def inputs():
        rom_path = report_rom_path(root)
        return (source_fingerprint(root, address), mapping_snapshot(root), runtime.index_snapshot(root),
                data_snapshot(root), units.snapshot(root), rom_path, Path(rom_path).read_bytes())

    source, mapping, index, objects, table, _, rom = before = inputs()
    unit = units.containing(units.parse(table, rom, mapping), address, address + member.END - member.ADDRESS)
    if not member.unit_owner(unit, address):
        raise ValueError("fp-bit source requires the pinned complete library unit")
    tool = units.resolve(member.TOOLCHAIN)
    config = dict(cc=tool["cc"], flags=tool["flags"], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                  linker=match.DEFAULT_LD, objcopy=match.DEFAULT_OBJCOPY)
    if args is not None and any(getattr(args, key) != value for key, value in config.items()):
        raise ValueError("fp-bit source requires the fixed old compiler configuration")
    args = argparse.Namespace(**config)

    def executables():
        path = os.path.expandvars(match.DEFAULT_WSL_PATH) + os.pathsep + os.environ["PATH"]
        names = (args.cc, args.cpp, args.assembler, args.linker, args.objcopy)
        return {name: units.sha(Path(shutil.which(os.path.expandvars(name), path=path)).read_bytes()) for name in names}

    binaries = executables()
    candidates = list((root/"src").rglob(f"{address:08X}.c"))
    if len(candidates) != 1:
        raise ValueError("fp-bit source requires exactly one source file")
    relative = candidates[0].relative_to(root)
    (root/"build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=root/"build", prefix="fpbit_source_") as directory:
        capture = Path(directory)
        for path in source_paths(root, address):
            dest = capture / path.relative_to(root)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(path.read_bytes())
        if source_fingerprint(capture, address) != source:
            raise ValueError("fp-bit source capture differs")
        runner = match.Runner(args.cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=capture, timeout=120)
        with runner.workspace() as workspace:
            raw, _, original = match.compile_object(runner, workspace, args, capture, address, relative.as_posix())
            body = member.link_object(runner, workspace, args, original, capture, relative, rom, mapping, index)
            raw_linked = runner.read_binary(workspace + "/f.elf")
        checker = Path(__file__).with_name("plausible.py")
        process = match._run_replay_process([sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
            [str(path) for path in source_paths(capture, address)], capture, 120)
        findings, allowed = match.plausibility_result(process, address)
        if findings or allowed or source_fingerprint(capture, address) != source:
            raise ValueError("captured fp-bit source changed or is implausible")
    proof = member.native_proof(body, rom, mapping, index, objects)
    if inputs() != before or units.resolve(member.TOOLCHAIN) != tool or executables() != binaries:
        raise ValueError("fp-bit source, ROM, indexes, unit or tool changed during replay")
    evidence = dict(source=source, functions=units.sha(mapping), index=units.sha(index), objects=units.sha(objects),
                    rom=units.sha(rom), unit=unit.text, compiler=tool, tool_binaries=binaries, original_elf=units.sha(raw),
                    linked_elf=units.sha(raw_linked), cfg=proof)
    report = "\n".join([f"# match report - 0x{address:08X}", "", f"* source: `{relative.as_posix()}`",
        f"* verification: `{member.SCHEMA}`", f"* source SHA-256: `{source}`",
        *units.report_lines({"unit": unit, "tool": tool}, None), f"* compiler: `{args.cc} {args.flags}`",
        member.CONTROL,
        "* verified extent: complete ELF function symbol, including literal pools", "* relocations: none",
        "* source plausibility: plausible", "* hand-asm allow list: not listed",
        f"* {member.LABEL} evidence: `{units.canonical(evidence)}`",
        f"* compiled : `{body.hex()}`", f"* ROM bytes: `{body.hex()}` ({len(body)} bytes)", "",
        f"**MATCH - byte identical** - {len(body)}/{len(body)} bytes", ""])
    return body, report


def issue(member, root, address, args):
    if args.label:
        raise ValueError("fp-bit source requires the canonical report name")
    body, report = build(member, root, address, args)
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
    print(f"extent    {len(body)} bytes (complete ELF symbol; {member.COUNT} reachable instructions; no relocations)")
    print("verdict MATCH - byte identical")
    return 0
