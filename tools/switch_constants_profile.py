"""Fresh-source provenance for one guarded Thumb switch with two constant words."""

import argparse
from contextvars import ContextVar
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import stat
import struct
import subprocess
import sys
import tempfile
import switch_placement as placement


SCHEMA = "elf-symbol-thumb-switch-two-constants-v2"
SELECTOR = "two-constants-v2"
CONTROL_FLOW = "one unsigned-guarded local Thumb table with two reached unrelocated constants"
ROM_SHA1 = "4ac05441f4de70a4ec3dd932116346c61b8783d9"
ROM_SIZE = 16 * 1024 * 1024
REPLAY_TIMEOUT = 120
_active = ContextVar("switch_constants_replay_active", default=False)
_compile_object = placement.compile_object


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def configuration():
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    return (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS)


def check_opt_in(enabled, relocations, *incompatible):
    if type(enabled) is not bool:
        raise ValueError("switch-constants opt-in must be Boolean")
    if enabled and (type(relocations) is not dict or
                    any(value is not None and value is not False for value in incompatible)):
        raise ValueError("switch constants require isolated local-switch bindings")


def layout(data, address, relocations):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC
    if type(address) is not int or address % 2 or type(relocations) is not dict or \
            not 2 <= len(relocations) <= 257:
        raise ValueError("switch constants require one bounded Thumb table")
    for offset, addend in relocations.items():
        if type(offset) is not int or type(addend) is not int or offset < 0 or \
                (address + offset) % 4 or offset + 4 > len(data) or addend < 0 or \
                addend % 2 or addend + 2 > len(data) or \
                struct.unpack_from("<I", data, offset)[0] != address + addend:
            raise ValueError("invalid switch-constants local relocation")
    literal = min(relocations)
    table = literal + 4
    count = len(relocations) - 1
    table_end = table + count * 4
    if sorted(relocations) != list(range(literal, table_end, 4)) or \
            relocations[literal] != table or any(relocations[slot] < table_end
                                                for slot in range(table, table_end, 4)):
        raise ValueError("switch constants require adjacent forward pointer/table words")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True

    def instruction(offset):
        if offset < 0 or offset % 2 or offset + 2 > len(data):
            return None
        decoded = next(decoder.disasm(data[offset:offset + 4], address + offset, count=1), None)
        return decoded if decoded is not None and decoded.size == 2 else None

    def target(decoded, mnemonic):
        if decoded is None or decoded.mnemonic != mnemonic or len(decoded.operands) != 1 or \
                decoded.operands[0].type != ARM_OP_IMM:
            return None
        return decoded.operands[0].imm - address

    candidates = []
    for dispatch in (literal - 18, literal - 20):
        gap = literal - 8
        if dispatch < 0 or ((address + dispatch + 13) & ~3) != address + gap or \
                gap - dispatch - 10 not in (0, 2) or any(data[dispatch + 10:gap]):
            continue
        sequence = [instruction(dispatch + distance) for distance in range(0, 10, 2)]
        if any(item is None or item.cc not in (ARM_CC_AL, ARM_CC_INVALID) for item in sequence) or \
                tuple(item.mnemonic for item in sequence) != ("lsls", "ldr", "adds", "ldr", "mov"):
            continue
        shift, load_base, addition, load_target, transfer = (item.operands for item in sequence)
        if len(shift) != 3 or shift[0].type != ARM_OP_REG or shift[1].type != ARM_OP_REG or \
                shift[2].type != ARM_OP_IMM or shift[2].imm != 2:
            continue
        accumulator, selector = shift[0].reg, shift[1].reg
        if len(load_base) != 2 or load_base[0].type != ARM_OP_REG or \
                load_base[0].reg == accumulator or load_base[1].type != ARM_OP_MEM or \
                load_base[1].mem.base != ARM_REG_PC or load_base[1].mem.index or \
                ((address + dispatch + 6) & ~3) + load_base[1].mem.disp != address + literal:
            continue
        if len(addition) != 3 or any(operand.type != ARM_OP_REG for operand in addition) or \
                tuple(operand.reg for operand in addition) != (accumulator, accumulator, load_base[0].reg):
            continue
        if len(load_target) != 2 or load_target[0].type != ARM_OP_REG or \
                load_target[0].reg != accumulator or load_target[1].type != ARM_OP_MEM or \
                load_target[1].mem.base != accumulator or load_target[1].mem.index or load_target[1].mem.disp:
            continue
        if len(transfer) != 2 or any(operand.type != ARM_OP_REG for operand in transfer) or \
                tuple(operand.reg for operand in transfer) != (ARM_REG_PC, accumulator):
            continue
        for guard_size in (4, 6):
            comparison = dispatch - guard_size
            guard = comparison + 2
            compare = instruction(comparison)
            if compare is None or compare.mnemonic != "cmp" or len(compare.operands) != 2 or \
                    compare.operands[0].type != ARM_OP_REG or compare.operands[0].reg != selector or \
                    compare.operands[1].type != ARM_OP_IMM or compare.operands[1].imm != count - 1:
                continue
            if guard_size == 4:
                default = target(instruction(guard), "bhi")
            else:
                if target(instruction(guard), "bls") != dispatch:
                    continue
                default = target(instruction(guard + 2), "b")
            if default is not None and not default % 2 and table_end <= default <= len(data) - 2:
                candidates.append({"comparison": comparison, "guard": guard, "dispatch": dispatch,
                                   "default": default, "literal": literal, "table": table,
                                   "bound": count - 1,
                                   "relocations": [[offset, addend] for offset, addend in sorted(relocations.items())]})
    if len(candidates) != 1:
        raise ValueError("switch constants require an exact two-word gap and unsigned guarded dispatch")
    return candidates[0]


def _envelope(image, address, linked=False):
    from match import allocated_text_only, function_record
    base, prefix = placement.origin(address)
    if image["type"] != (2 if linked else 1):
        raise ValueError("unexpected placement ELF type")
    allocated_text_only(image)
    section = image["sections"][image["text_index"]]
    symbol, offset = function_record(image, f"func_{address:08X}", address, True)
    end = prefix + symbol["size"]
    suffix = image["text"][end:]
    if symbol["bind"] != 1 or offset != prefix or symbol["size"] % 2 or \
            section[2] != 6 or section[3] != (base if linked else 0) or section[8] != 4 or \
            len(image["text"]) != ((end + 3) & ~3) or image["text"][:prefix] != bytes(prefix) or \
            suffix not in (b"", b"\0\0", bytes.fromhex("c046")) or \
            suffix and end % 4 != 2 or \
            any(item["type"] == 1 or re.fullmatch(r"\$a(?:\..*)?", item["name"])
                for item in image["symbols"]):
        raise ValueError("unsupported placed function envelope")
    if not linked and [item for item in image["symbols"] if item["type"] == 2 and item["section"]] != [symbol]:
        raise ValueError("switch constants require sole Thumb function ownership")
    return symbol, prefix


def _original_records(original, address, mapping, rom_size):
    from match import function_address_target
    symbol, offset = _envelope(original, address)
    entries = json.loads(mapping)
    records = []
    occupied = set()
    for section_index in original["relocations"]:
        section = original["sections"][section_index]
        symbols = original["symbol_tables"].get(section[6])
        if section[1] != 9 or section[7] != original["text_index"] or section[9] != 8 or \
                section[5] % 8 or symbols is None:
            raise ValueError("unsupported raw relocation section")
        for position in range(0, section[5], 8):
            site, info = struct.unpack_from("<II", original["section_data"][section_index], position)
            kind = info & 255
            if kind not in (2, 10) or info >> 8 >= len(symbols) or site < offset or \
                    site + 4 > offset + symbol["size"]:
                raise ValueError("unsupported or out-of-bounds raw relocation")
            extent = set(range(site, site + 4))
            if occupied & extent:
                raise ValueError("overlapping raw relocation extents")
            occupied.update(extent)
            target = symbols[info >> 8]
            if kind == 2:
                if target["type"] != 3 or target["bind"] != 0 or target["name"] or \
                        target["value"] or target["section"] != original["text_index"] or \
                        sum(item["type"] == 3 and item["section"] == original["text_index"]
                            for item in original["symbols"]) != 1:
                    raise ValueError("switch words require the unique unnamed zero-valued text section")
                addend = struct.unpack_from("<I", original["text"], site)[0]
                if site % 4 or addend % 2 or not offset <= addend <= offset + symbol["size"] - 2:
                    raise ValueError("switch addend leaves function ownership")
            else:
                destination = function_address_target(target["name"], entries, address, symbol["size"], rom_size)
                if target["section"] or target["bind"] != 1 or target["type"] not in (0, 2) or \
                        target["value"] or sum(item["name"] == target["name"]
                                               for item in original["symbols"]) != 1 or \
                        site % 2 or address - offset <= destination < address or \
                        original["text"][site:site + 4] != bytes.fromhex("fff7feff"):
                    raise ValueError("switch calls require canonical zero-addend undefined functions")
            records.append((site, kind))
    return records


def _manifest(data, address, calls, relocations):
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC
    from match import verify_leaf_instructions
    descriptor = layout(data, address, relocations)
    instructions = verify_leaf_instructions(data, address, True, calls,
                                            switch_relocations=relocations, allow_switch_constants=True)
    owned = set(range(descriptor["dispatch"] + 10,
                      descriptor["table"] + 4 * (descriptor["bound"] + 1)))
    loads = {}
    starts = {instruction.address - address for instruction in instructions}
    for instruction in instructions:
        owned.update(range(instruction.address - address, instruction.address - address + instruction.size))
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                literal = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                loads.setdefault(literal, []).append(instruction.address - address)
                owned.update(range(literal, literal + 4))
    constants = []
    for offset in (descriptor["literal"] - 8, descriptor["literal"] - 4):
        if not loads.get(offset):
            raise ValueError("each interposed constant requires a reached word load")
        constants.append([offset, struct.unpack_from("<I", data, offset)[0], sorted(set(loads[offset]))])
    if any(addend not in starts for offset, addend in relocations.items() if offset != descriptor["literal"]):
        raise ValueError("switch cases must be reached instruction starts")
    missing = set(range(len(data))) - owned
    for offset in sorted(missing):
        if offset % 2 or offset + 1 not in missing or offset + 2 not in loads or \
                (address + offset) % 4 != 2 or data[offset:offset + 2] != b"\0\0":
            if offset - 1 in missing and offset % 2:
                continue
            raise ValueError("unowned complete-symbol bytes")
    return {"calls": [[site - address, f"func_{target:08X}"] for site, target in sorted(calls.items())],
            "switch": descriptor, "constants": constants}, len(instructions)


def _linked_bytes(original, linked, address, records, calls, targets, relocations):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from capstone.arm import ARM_INS_BL, ARM_OP_IMM
    before, prefix = _envelope(original, address)
    after, _ = _envelope(linked, address, True)
    base = address - prefix
    if linked["relocations"] or after["size"] != before["size"] or len(linked["text"]) != len(original["text"]):
        raise ValueError("linked placement extent or relocations changed")
    expected = {f"func_{address:08X}", *targets}
    functions = [item["name"] for item in linked["symbols"] if item["type"] == 2]
    sections = [item for item in linked["symbols"] if item["type"] == 3 and item["section"] == linked["text_index"]]
    if len(functions) != len(expected) or set(functions) != expected or len(sections) != 1 or \
            sections[0]["name"] or sections[0]["bind"] or sections[0]["value"] != base or \
            any(item["name"] and not item["section"] for item in linked["symbols"]):
        raise ValueError("linked placement symbols differ")
    for name, target in targets.items():
        definitions = [item for item in linked["symbols"] if item["name"] == name]
        if len(definitions) != 1 or definitions[0]["type"] != 2 or definitions[0]["bind"] != 1 or \
                definitions[0]["section"] != 0xFFF1 or definitions[0]["value"] != target | 1:
            raise ValueError("linked typed target differs")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    for site, target in calls.items():
        raw_site = site - base
        instruction = next(decoder.disasm(linked["text"][raw_site:raw_site + 4], site, count=1), None)
        if instruction is None or instruction.id != ARM_INS_BL or instruction.size != 4 or \
                len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM or \
                instruction.operands[0].imm != target:
            raise ValueError("linked Thumb call target differs")
    for relative, addend in relocations.items():
        raw_site = relative + prefix
        if struct.unpack_from("<I", original["text"], raw_site)[0] != addend + prefix or \
                struct.unpack_from("<I", linked["text"], raw_site)[0] != address + addend:
            raise ValueError("linked section-relative switch word differs")
    permitted = {position for site, _ in records for position in range(site, site + 4)}
    if any(left != right and position not in permitted for position, (left, right) in
           enumerate(zip(original["text"], linked["text"]))):
        raise ValueError("linker changed bytes outside permitted relocations")
    return linked["text"][prefix:prefix + before["size"]]


def _artifact_snapshot(path):
    def identity(info):
        return (info.st_dev, info.st_ino, info.st_mode, info.st_size, info.st_mtime_ns, info.st_ctime_ns)

    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ValueError("linked artifact is not a regular file")
        with os.fdopen(descriptor, "rb", closefd=False) as stream:
            data = stream.read()
        if identity(os.fstat(descriptor)) != identity(before):
            raise ValueError("linked artifact changed during capture")
        if identity(os.stat(path, follow_symlinks=False)) != identity(before):
            raise ValueError("linked artifact changed during capture")
        return data, identity(before)
    finally:
        os.close(descriptor)


def _object_bytes(runner, workspace, args, original, address, mapping, rom):
    from match import elf_image
    records = _original_records(original, address, mapping, len(rom))
    base, prefix = placement.origin(address)
    relocations = {}
    calls, targets = {}, {}
    for section_index in original["relocations"]:
        section = original["sections"][section_index]
        symbols = original["symbol_tables"][section[6]]
        for position in range(0, section[5], 8):
            site, info = struct.unpack_from("<II", original["section_data"][section_index], position)
            if info & 255 == 2:
                relocations[site - prefix] = struct.unpack_from("<I", original["text"], site)[0] - prefix
            else:
                name = symbols[info >> 8]["name"]
                targets[name] = int(name[5:], 16)
                calls[base + site] = targets[name]
    if any(item["name"] and not item["section"] and item["name"] not in targets for item in original["symbols"]):
        raise ValueError("unresolved symbols outside permitted calls")
    definitions = [".syntax unified", ".thumb"]
    for name, target in sorted(targets.items()):
        definitions.extend((f".global {name}", f".type {name}, %function", f".thumb_set {name}, 0x{target | 1:08X}"))
    runner.write_text(f"{workspace}/f.known.s", "\n".join(definitions) + "\n")
    script = (f"SECTIONS {{ .text 0x{base:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} "
              ".data 0 : { *(.data) } .bss 0 : { *(.bss) } "
              ".ARM.attributes 0 : { *(.ARM.attributes) } "
              ".unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } "
              ".rel.iplt 0 : { *(.rel.iplt) } "
              "ASSERT(SIZEOF(.unexpected) == 0, \"unexpected linker stubs\") "
              "ASSERT(SIZEOF(.rel.iplt) == 0, \"unexpected dynamic relocations\") "
              "/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }")
    runner.write_text(f"{workspace}/f.ld", script)
    quoted = shlex.quote(workspace)
    runner.sh(f"export TMPDIR={quoted}; {args.assembler} -mthumb-interwork {quoted}/f.known.s -o {quoted}/f.known.o")
    runner.sh(f"export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined --no-relax "
              f"--orphan-handling=error -T {quoted}/f.ld -e func_{address:08X} "
              f"{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf")
    runner.sh(f"{args.objcopy} -O binary --only-section=.text {quoted}/f.elf {quoted}/f.linked.bin")
    captured = {name: _artifact_snapshot(f"{workspace}/{name}") for name in ("f.elf", "f.linked.bin")}
    linked = elf_image(captured["f.elf"][0])
    if captured["f.linked.bin"][0] != linked["text"]:
        raise ValueError("objcopy output does not equal linked ELF text")
    data = _linked_bytes(original, linked, address, records, calls, targets, relocations)
    manifest, count = _manifest(data, address, calls, relocations)
    descriptor = manifest["switch"]
    gap = set(range(descriptor["dispatch"] + 10, descriptor["literal"]))
    if any(gap.intersection(range(site - prefix, site - prefix + 4)) for site, _ in records):
        raise ValueError("interposed constants and alignment must have no raw relocation")
    return data, manifest, count, captured


@dataclass(frozen=True)
class VerifiedSwitch:
    body: bytes
    manifest_json: str
    instruction_count: int
    source_path: str
    source_digest: str
    mapping_digest: str
    index_digest: str
    rom_digest: str


def _source_snapshot(root, address):
    from match_evidence import source_paths
    candidates = list((root / "src").rglob(f"{address:08X}.c"))
    if len(candidates) != 1:
        raise ValueError("switch constants require one uniquely addressed source")
    result = {}
    for path in source_paths(root, address):
        if root not in path.resolve().parents or any(parent.is_symlink() for parent in (path, *path.parents)
                                                    if parent != root):
            raise ValueError("captured inputs must be ordinary files inside the source root")
        result[path.relative_to(root).as_posix()] = path.read_bytes()
    return candidates[0].relative_to(root).as_posix(), result


def _resolve_tools():
    if os.name != "posix":
        raise ValueError("switch source replay requires bounded POSIX execution")
    result = []
    for spelling in configuration()[:5]:
        executable = shutil.which(os.path.expandvars(spelling))
        if executable is None:
            raise ValueError("missing fixed switch-profile tool")
        path = Path(executable).resolve(strict=True)
        result.append((spelling, str(path), digest(path.read_bytes())))
    return tuple(result)


def _checker_snapshot():
    import plausible
    directory = Path(__file__).resolve().parent
    paths = sorted(directory.glob("*.py"))
    allowance = Path(plausible.asm_allow_path()).resolve()
    return (str(allowance), {str(path): path.read_bytes() for path in paths},
            allowance.read_bytes() if allowance.exists() else None)


def _build_from_source(root, address):
    from match import Runner, elf_image, _run_replay_process, plausibility_result
    from match_evidence import source_fingerprint, report_rom_path
    from inert_spin_profile import validate_span
    if _active.get():
        raise ValueError("recursive switch source replay")
    token = _active.set(True)
    try:
        root = Path(root).resolve(strict=True)
        source, captured_sources = _source_snapshot(root, address)
        source_digest = source_fingerprint(root, address)
        mapping = (root / "config/functions.json").read_bytes()
        index = (root / "symbols/functions.txt").read_bytes()
        selected_rom = str(Path(report_rom_path(root)).resolve(strict=True))
        rom = Path(selected_rom).read_bytes()
        if len(rom) != ROM_SIZE or hashlib.sha1(rom).hexdigest() != ROM_SHA1:
            raise ValueError("switch replay requires the approved ROM identity")
        entries = json.loads(mapping)
        spans = [entry for entry in entries if int(entry["rom"], 16) == address]
        if len(spans) != 1:
            raise ValueError("switch caller index is ambiguous")
        end = int(spans[0]["end"], 16)
        validate_span(rom[address - 0x08000000:end - 0x08000000], address, rom, mapping, index)
        tools = _resolve_tools()
        checker = _checker_snapshot()
        allowance = json.loads(checker[2]) if checker[2] is not None else {"entries": []}
        if any(str(entry.get("address", "")).lower() == f"0x{address:08x}"
               for entry in allowance.get("entries", [])):
            raise ValueError("switch constants exclude hand-asm allowances")

        def unchanged():
            if _source_snapshot(root, address) != (source, captured_sources) or \
                    source_fingerprint(root, address) != source_digest or \
                    (root / "config/functions.json").read_bytes() != mapping or \
                    (root / "symbols/functions.txt").read_bytes() != index or \
                    str(Path(report_rom_path(root)).resolve(strict=True)) != selected_rom or \
                    Path(selected_rom).read_bytes() != rom or _resolve_tools() != tools or \
                    _checker_snapshot() != checker:
                raise ValueError("switch replay inputs changed")

        unchanged()
        build = root / "build"
        build.mkdir(exist_ok=True)
        if build.is_symlink() or root not in build.resolve().parents:
            raise ValueError("switch replay workspace leaves the source root")
        with tempfile.TemporaryDirectory(prefix="ffta_switch_constants_", dir=build) as directory:
            captured = Path(directory)
            for name, contents in captured_sources.items():
                destination = captured / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(contents)
            if _source_snapshot(captured, address) != (source, captured_sources) or \
                    source_fingerprint(captured, address) != source_digest:
                raise ValueError("switch source capture differs")
            args = argparse.Namespace(**dict(zip(("cc", "cpp", "assembler", "objcopy", "linker"),
                                                  (shlex.quote(item[1]) for item in tools))),
                                      flags=configuration()[5])
            runner = Runner(tools[0][1], root=captured, timeout=REPLAY_TIMEOUT)
            with placement.workspace(runner) as workspace:
                object_data, _, original = _compile_object(runner, workspace, args, captured, address, source)
                stage = {name: runner.read_binary(f"{workspace}/{name}") for name in ("f.raw.s", "f.s", "f.o")}
                placed, _ = placement.place(stage["f.raw.s"], address)
                if stage["f.s"] != placed or stage["f.o"] != object_data or elf_image(object_data) != original:
                    raise ValueError("fresh placement capture differs")
                body, manifest, count, linked_capture = _object_bytes(runner, workspace, args, original, address, mapping, rom)
                base, prefix = placement.origin(address)
                manifest["placement"] = {"rule": placement.RULE, "section_base": base,
                    "function_offset": prefix, "prefix_size": prefix,
                    "raw_assembly_sha256": digest(stage["f.raw.s"]), "placed_assembly_sha256": digest(placed),
                    "original_elf_sha256": digest(object_data),
                    "linked_elf_sha256": digest(linked_capture["f.elf"][0])}
                validate_span(body, address, rom, mapping, index)
                if any(runner.read_binary(f"{workspace}/{name}") != contents for name, contents in stage.items()):
                    raise ValueError("placement inputs changed during link")
                if any(_artifact_snapshot(f"{workspace}/{name}") != captured for name, captured in linked_capture.items()):
                    raise ValueError("linked artifacts changed after validation")
            checker_path = Path(__file__).resolve().with_name("plausible.py")
            command = [sys.executable, str(checker_path), "--quiet", "--addr", f"0x{address:08X}", "--json"]
            command += [str(captured / name) for name in sorted(captured_sources)]
            checker_command = f"export TMPDIR={shlex.quote(str(captured))}; exec " + shlex.join(command)
            result = _run_replay_process(checker_command, captured, REPLAY_TIMEOUT, shell=True)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or _source_snapshot(captured, address) != (source, captured_sources) or \
                    source_fingerprint(captured, address) != source_digest:
                raise ValueError("switch captured source changed or is implausible")
            unchanged()
            verified = VerifiedSwitch(body, canonical(manifest), count, source, source_digest,
                                      digest(mapping), digest(index), digest(rom))
        unchanged()
        return verified
    finally:
        _active.reset(token)


def verify_source(root, address, *, expected_bytes, expected_manifest, expected_source_path,
                  expected_source_digest, expected_mapping_digest, expected_index_digest, expected_rom_digest):
    manifest_json = canonical(expected_manifest)
    _parse_manifest(manifest_json, len(expected_bytes))
    result = _build_from_source(root, address)
    if (result.body, result.manifest_json, result.source_path, result.source_digest,
        result.mapping_digest, result.index_digest, result.rom_digest) != \
            (expected_bytes, manifest_json, expected_source_path, expected_source_digest,
             expected_mapping_digest, expected_index_digest, expected_rom_digest):
        raise ValueError("fresh switch source evidence differs from the report")
    return result


def fingerprint(address, result):
    proof = hashlib.sha256()
    for payload in (SCHEMA.encode(), address.to_bytes(4, "little"), result.body,
                    result.manifest_json.encode(), result.source_path.encode(),
                    result.source_digest.encode(), result.mapping_digest.encode(),
                    result.index_digest.encode(), result.rom_digest.encode(), canonical(configuration()).encode()):
        proof.update(len(payload).to_bytes(8, "little"))
        proof.update(payload)
    return proof.hexdigest()


def selected(report):
    normalized = [re.sub(r"[ \t]+", " ", line.strip()).lower() for line in report.splitlines()]
    if not any("switch-two-constants" in line or line.startswith("* switch constants") for line in normalized):
        return False
    verification = [line for line in report.splitlines()
                    if re.sub(r"[ \t]+", " ", line.strip()).startswith("* verification")]
    if verification != [f"* verification: `{SCHEMA}`"]:
        raise ValueError("mixed or malformed switch-constants selection")
    fields = [line for line in report.splitlines()
              if re.sub(r"[ \t]+", " ", line.strip()).startswith("* switch constants:")]
    if fields != [f"* switch constants: {SELECTOR}"]:
        raise ValueError("missing or malformed switch-constants selector")
    family = [line for line in report.splitlines()
              if re.sub(r"[ \t]+", " ", line.strip()).lower().startswith("* switch constants")]
    prefixes = ("* switch constants: ", "* switch constants manifest: ",
                "* switch constants proof SHA-256: ")
    if len(family) != 3 or any(sum(line.startswith(prefix) for line in family) != 1 for prefix in prefixes) or \
            any(not line.endswith("`") or "`" not in line for line in family if not line.startswith(prefixes[0])):
        raise ValueError("missing, duplicate or malformed switch-constants family field")
    forbidden = ("* switches", "* switch manifest", "* switch proof", "* buffer", "* stack", "* data",
                 "* function address", "* function-address", "* function buffer", "* unsigned division",
                 "* signed", "* software double", "* inert", "* empty")
    if any(line.startswith(forbidden) for line in normalized):
        raise ValueError("mixed switch-constants profiles")
    return True


def _parse_manifest(encoded, size):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate switch manifest key")
            result[key] = value
        return result

    def integer(value, maximum=size - 2):
        if type(value) is not int or not 0 <= value <= maximum:
            raise ValueError("invalid switch manifest integer")

    def pairs(records, names=False):
        if type(records) is not list:
            raise ValueError("invalid switch records")
        previous = -1
        for record in records:
            if type(record) is not list or len(record) != 2:
                raise ValueError("invalid switch record")
            integer(record[0], size - 4)
            if record[0] % 2 or record[0] <= previous:
                raise ValueError("unordered switch records")
            previous = record[0]
            if names:
                if type(record[1]) is not str or re.fullmatch(r"func_[0-9A-F]{8}", record[1]) is None:
                    raise ValueError("invalid switch call name")
            else:
                integer(record[1])

    manifest = json.loads(encoded, object_pairs_hook=unique)
    if canonical(manifest) != encoded or type(manifest) is not dict or \
            set(manifest) != {"calls", "switch", "constants", "placement"}:
        raise ValueError("noncanonical switch manifest")
    context = manifest["placement"]
    if type(context) is not dict or set(context) != {"rule", "section_base", "function_offset", "prefix_size",
            "raw_assembly_sha256", "placed_assembly_sha256", "original_elf_sha256", "linked_elf_sha256"} or \
            context["rule"] != placement.RULE:
        raise ValueError("invalid placement manifest")
    for key in ("section_base", "function_offset", "prefix_size"):
        integer(context[key], 0xFFFFFFFF)
    if context["function_offset"] not in (0, 2) or context["prefix_size"] != context["function_offset"] or \
            context["section_base"] % 4 or not 0x08000000 <= context["section_base"] < 0x09000000:
        raise ValueError("invalid placement origin")
    for key in ("raw_assembly_sha256", "placed_assembly_sha256", "original_elf_sha256", "linked_elf_sha256"):
        if type(context[key]) is not str or re.fullmatch(r"[0-9a-f]{64}", context[key]) is None:
            raise ValueError("invalid placement digest")
    pairs(manifest["calls"], True)
    switch = manifest["switch"]
    fields = {"comparison", "guard", "dispatch", "default", "literal", "table", "bound", "relocations"}
    if type(switch) is not dict or set(switch) != fields:
        raise ValueError("invalid switch descriptor")
    for field in fields - {"relocations"}:
        integer(switch[field], 255 if field == "bound" else size - 2)
    pairs(switch["relocations"])
    constants = manifest["constants"]
    if type(constants) is not list or len(constants) != 2:
        raise ValueError("exactly two constant records required")
    previous = -1
    for record in constants:
        if type(record) is not list or len(record) != 3:
            raise ValueError("invalid constant record")
        integer(record[0], size - 4)
        integer(record[1], 0xFFFFFFFF)
        if record[0] <= previous or type(record[2]) is not list or not record[2]:
            raise ValueError("unordered or unreferenced constant")
        previous = record[0]
        prior_load = -1
        for load in record[2]:
            integer(load)
            if load % 2 or load <= prior_load:
                raise ValueError("unordered constant loads")
            prior_load = load
    return manifest


def render_report(address, result):
    size = len(result.body)
    return "\n".join((f"# 0x{address:08X}", "", f"* verification: `{SCHEMA}`",
        f"* switch constants: {SELECTOR}", f"* compiler: `{configuration()[0]} {configuration()[5]}`",
        f"* source: `{result.source_path}`", f"* source SHA-256: `{result.source_digest}`",
        f"* mapping SHA-256: `{result.mapping_digest}`", f"* function index SHA-256: `{result.index_digest}`",
        f"* ROM SHA-256: `{result.rom_digest}`", f"* control flow: {CONTROL_FLOW}",
        f"* reached instructions: {result.instruction_count}",
        "* verified extent: complete ELF function symbol, including literal pools", "* relocations: none",
        "* source plausibility: plausible", "* hand-asm allow list: not listed",
        f"* switch constants manifest: `{result.manifest_json}`",
        f"* switch constants proof SHA-256: `{fingerprint(address, result)}`",
        f"* ROM bytes: `{result.body.hex()}` ({size} bytes)", f"* compiled : `{result.body.hex()}`", "",
        f"**MATCH - byte identical** - {size}/{size} bytes", ""))


def report_matches(report, root, address):
    try:
        if not selected(report):
            return False
        fields = {}
        for line in report.splitlines():
            if line.startswith("* "):
                key, value = line.split(": ", 1)
                if key in fields:
                    raise ValueError("duplicate switch report field")
                fields[key] = value

        def quoted(key):
            value = fields[key]
            if not value.startswith("`") or not value.endswith("`"):
                raise ValueError("unquoted switch report field")
            return value[1:-1]

        required = {"* verification", "* switch constants", "* compiler", "* source", "* source SHA-256",
                    "* mapping SHA-256", "* function index SHA-256", "* ROM SHA-256", "* control flow",
                    "* reached instructions", "* verified extent", "* relocations", "* source plausibility",
                    "* hand-asm allow list", "* switch constants manifest", "* switch constants proof SHA-256",
                    "* ROM bytes", "* compiled "}
        if set(fields) != required or quoted("* compiler") != f"{configuration()[0]} {configuration()[5]}" or \
                fields["* control flow"] != CONTROL_FLOW or fields["* relocations"] != "none" or \
                fields["* source plausibility"] != "plausible" or fields["* hand-asm allow list"] != "not listed" or \
                fields["* verified extent"] != "complete ELF function symbol, including literal pools" or \
                re.fullmatch(r"[1-9][0-9]*", fields["* reached instructions"]) is None:
            raise ValueError("noncanonical switch report fields")
        for key in ("* source SHA-256", "* mapping SHA-256", "* function index SHA-256", "* ROM SHA-256",
                    "* switch constants proof SHA-256"):
            if re.fullmatch(r"[0-9a-f]{64}", quoted(key)) is None:
                raise ValueError("noncanonical switch report digest")

        encoded = quoted("* compiled ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            raise ValueError("invalid compiled bytes")
        body = bytes.fromhex(encoded)
        manifest = _parse_manifest(quoted("* switch constants manifest"), len(body))
        result = verify_source(root, address, expected_bytes=body, expected_manifest=manifest,
            expected_source_path=quoted("* source"), expected_source_digest=quoted("* source SHA-256"),
            expected_mapping_digest=quoted("* mapping SHA-256"),
            expected_index_digest=quoted("* function index SHA-256"), expected_rom_digest=quoted("* ROM SHA-256"))
        return report == render_report(address, result)
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, struct.error, UnicodeError, subprocess.SubprocessError):
        return False


def issue(root, address, args):
    from match import DEFAULT_WSL_PATH
    try:
        if tuple(getattr(args, name) for name in ("cc", "cpp", "assembler", "objcopy", "linker", "flags")) != \
                configuration() or args.mode != "thumb" or args.control_flow_profile != "ordinary" or \
                args.software_double_profile is not None or args.function_address_profile is not None or \
                args.wsl != "Ubuntu" or args.wsl_path != DEFAULT_WSL_PATH or args.label:
            raise ValueError("switch constants require the fixed isolated default toolchain")
        output = None
        if args.emit:
            output = (root / args.emit).resolve()
            if (root / "build").resolve() not in output.parents or output.exists():
                raise ValueError("--emit must name a new file under build/")
        result = _build_from_source(root, address)
        report = render_report(address, result)
        if output is not None:
            output.parent.mkdir(parents=True, exist_ok=True)
            with output.open("xb") as stream:
                stream.write(result.body)
        if not args.no_write:
            destination = root / "docs/match" / f"{address:08X}.md"
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(report, encoding="utf-8")
        print(f"function  0x{address:08X}   {len(result.body)} bytes (Thumb)")
        print(f"extent    {len(result.body)} bytes (complete ELF symbol; {CONTROL_FLOW}; no relocations)")
        print("verdict MATCH - byte identical")
        return 0
    except (OSError, ValueError, KeyError, IndexError, TypeError, RuntimeError,
            struct.error, UnicodeError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error)) from error
