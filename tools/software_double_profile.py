"""Canonical target-state binary64 conversions, truncation, subtraction and division."""

import argparse
from contextvars import ContextVar
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile


SCHEMA = "elf-symbol-thumb-df-convert-sub-div-target-v1"
SELECTOR = "convert-sub-div-target-v1"
RUNTIME = "agbcc-thumb-df-convert-sub-div-trunc-closure-v2"
ABI = "agbcc-thumb-df-sf-mixed-integer-v2"
SEMANTICS = "target-machine-state-v1"
SUMMARY = ("pinned target binary64 conversion/sub/div/trunc runtime; entry RAM and stack are state inputs; "
           "unrestricted IEEE semantics not proved")
OPERATIONS = {"__floatdidf": 0x081428E4, "__floatsidf": 0x0814383C,
              "__subdf3": 0x081430B4, "__divdf3": 0x0814339C,
              "__truncdfsf2": 0x08143980}
IDENTITIES = (
    (0x081428E4, 0x08142950, 40,
     "a6d6bb1e52f8722074d02e2636c989190539cb12779065909bc2bb61093fe399"),
    (0x08142A20, 0x08142A94, 56,
     "f642a6a21668da428cbb8304f9710064aca75ff16130add649b86ff4b9e73be3"),
    (0x08142A94, 0x08142AAE, 13,
     "6a893c98dc95046692905bc7c4609ee1326b78480597733620dcea235536e4b2"),
    (0x08142BE8, 0x08142D34, 139,
     "38aa6a8e47b81d402a011d733156fc99229f9fdf028aee34f5920b3464a5bb00"),
    (0x08142D34, 0x08142E10, 97,
     "8fb09220b22c69e18dc39f19c8645de020c1d658f48894a5dfe3d68e79f0fb25"),
    (0x08142E10, 0x08143080, 302,
     "22a070699b52b1cb7cf2ab493553e6dab53d87cf3dfe25e3ef10c1968d369537"),
    (0x08143080, 0x081430B4, 22,
     "1b07d08a039cd8e27f726529b9e9456e67856a101882c398cd09d53a8f90a45f"),
    (0x081430B4, 0x081430F0, 26,
     "1d51a3ac118474f7f67a1a4e3654c10efd2c28694da8f9d8e5b50a40e6436bfb"),
    (0x081430F0, 0x0814339C, 323,
     "751f3196c6c084a8d79554ff85b18083f8e0b7e483c36c8dbe2eff90c14bf27d"),
    (0x0814339C, 0x08143528, 188,
     "724ac20cf05719a0fbe4d032862cdc3ba94f1085aa6fbf1d6bc01e598e23adbf"),
    (0x0814383C, 0x081438BC, 56,
     "99b0db82e85f6860b32c8ae93795730b88afaec7134f3ab439db123a7a9f9c0a"),
    (0x08143980, 0x081439C8, 32,
     "acb4499634230b81e5a935184b68ddda30d9c6eb08041a49ceccab21d05f4223"),
    (0x081439C8, 0x08143A84, 86,
     "765c352080a3d1f6c0da8210a214648596a5486760b3cedf7d6648fef32cae32"),
    (0x08144314, 0x0814432C, 11,
     "1c637e4a2eff2aeb108768d7234baa47f3b4a9cfed810ce28603b3bc29cc5d7f"),
    (0x08144378, 0x081443AE, 27,
     "a2d91a60b907f40dd3bafc448e79c2c4630ba7000195bb54f0f4b26e4e9d9faa"),
)
EDGES = (
    (0x81428EE, 0x814383C),
    (0x81428FA, 0x81430F0),
    (0x8142906, 0x81430F0),
    (0x8142910, 0x814383C),
    (0x8142920, 0x8143080),
    (0x8142930, 0x8143080),
    (0x8142C64, 0x8144378),
    (0x8142F84, 0x8142A94),
    (0x8142FC6, 0x8142A94),
    (0x8143090, 0x8142D34),
    (0x814309A, 0x8142D34),
    (0x81430A4, 0x8142E10),
    (0x81430A8, 0x8142BE8),
    (0x81430C4, 0x8142D34),
    (0x81430CE, 0x8142D34),
    (0x81430E0, 0x8142E10),
    (0x81430E4, 0x8142BE8),
    (0x8143108, 0x8142D34),
    (0x8143112, 0x8142D34),
    (0x81431E0, 0x8142A20),
    (0x81431F0, 0x8142A20),
    (0x8143200, 0x8142A20),
    (0x8143210, 0x8142A20),
    (0x8143376, 0x8142BE8),
    (0x81433AC, 0x8142D34),
    (0x81433B6, 0x8142D34),
    (0x8143512, 0x8142BE8),
    (0x81438AC, 0x8142BE8),
    (0x814398C, 0x8142D34),
    (0x81439B8, 0x8144314),
    (0x8144322, 0x81439C8),
)
# The new conversion reuses the double unpacker and single packer. Only the
# public conversion is a caller operation; the other three bodies stay private.
TRUNCATION_CLOSURE = (0x08142D34, 0x08143980, 0x081439C8, 0x08144314)
REPLAY_TIMEOUT = 120
FORBIDDEN_MARKERS = ("* buffer", "* unsigned division", "* signed remainder",
                     "* signed quotient", "* switches", "* switch manifest", "* switch proof",
                     "* function address", "* function buffer", "* inert spin", "* function-address")
_replay_active = ContextVar("software_double_replay_active", default=False)


def reserved(address):
    return any(start <= address & ~1 < end for start, end, _, _ in IDENTITIES)


def dependency_records():
    return [[start, end, digest] for start, end, _, digest in IDENTITIES]


def marker_text(line):
    return re.sub(r"[ \t]+", " ", line.strip(" \t"))


def selected(report):
    lines = report.splitlines()
    markers = [line for line in lines if marker_text(line).startswith("* verification")]
    relevant = any(SCHEMA in line or marker_text(line).startswith("* software double") for line in lines)
    if not relevant:
        return False
    if markers != [f"* verification: `{SCHEMA}`"] or any(
            marker_text(line).startswith(FORBIDDEN_MARKERS) for line in lines):
        raise ValueError("mixed or malformed software-double profile selection")
    return True


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def compiler_text():
    from match import DEFAULT_CC, DEFAULT_FLAGS
    return f"{DEFAULT_CC} {DEFAULT_FLAGS}"


def index_snapshot(root):
    return (Path(root) / "symbols/functions.txt").read_bytes()


def fingerprint(address, data, manifest, source_digest, mapping, index, rom, *, data_mapping=None):
    from match import DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD
    digest = hashlib.sha256()
    configuration = compiler_text() + repr((DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD))
    for payload in (SCHEMA.encode("ascii"), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode("utf-8"), source_digest.encode("ascii"),
                    hashlib.sha256(mapping).digest(), hashlib.sha256(index).digest(),
                    hashlib.sha256(rom).digest(), configuration.encode("ascii")):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    if "data" in manifest:
        if not isinstance(data_mapping, bytes):
            raise ValueError("software-double data fingerprint requires its exact mapping")
        for payload in (b"software-double-typed-data-v1", data_mapping):
            digest.update(len(payload).to_bytes(8, "little"))
            digest.update(payload)
    return digest.hexdigest()


def fixed_configuration(args):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
            (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
        raise ValueError("software double requires the fixed approved toolchain configuration")


def unique_members(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError("duplicate software-double JSON member")
        result[name] = value
    return result


def indices(mapping, index):
    if not isinstance(mapping, bytes) or not isinstance(index, bytes):
        raise ValueError("software double requires both index snapshots")
    entries = json.loads(mapping, object_pairs_hook=unique_members)
    if not isinstance(entries, list):
        raise ValueError("software-double mapping must be a list")
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("rom"), str) or \
                not isinstance(entry.get("end"), str) or \
                not re.fullmatch(r"0x[0-9A-Fa-f]{8}", entry["rom"]) or \
                not re.fullmatch(r"0x[0-9A-Fa-f]{8}", entry["end"]) or \
                int(entry["end"], 16) <= int(entry["rom"], 16):
            raise ValueError("malformed software-double function ownership row")
    rows = [line.split() for line in index.decode("utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")]
    for row in rows:
        if len(row) < 4 or not re.fullmatch(r"[0-9A-Fa-f]{8}", row[0]) or \
                not re.fullmatch(r"[0-9A-Fa-f]{8}", row[1]) or \
                int(row[1], 16) <= int(row[0], 16) or int(row[2]) <= 0 or int(row[3]) < 0:
            raise ValueError("malformed software-double text ownership row")
    return entries, rows


def span_record(start, end, entries, rows, rom):
    selected_entries = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
    selected_rows = [row for row in rows if int(row[0], 16) & ~1 == start]
    if start % 2 or len(selected_entries) != 1 or len(selected_rows) != 1 or \
            int(selected_entries[0]["rom"], 16) != start or \
            int(selected_entries[0]["end"], 16) != end or selected_entries[0].get("mode") != "thumb" or \
            type(selected_entries[0].get("instrs")) is not int or \
            int(selected_rows[0][0], 16) != start or int(selected_rows[0][1], 16) != end or \
            int(selected_rows[0][2]) != end - start or \
            int(selected_rows[0][3]) != selected_entries[0]["instrs"] or \
            not 0x08000000 <= start < end <= 0x08000000 + len(rom) or \
            any(entry is not selected_entries[0] and int(entry["rom"], 16) < end and
                int(entry["end"], 16) > start for entry in entries) or \
            any(row is not selected_rows[0] and int(row[0], 16) < end and
                int(row[1], 16) > start for row in rows):
        raise ValueError("software double requires exact unique nonoverlapping Thumb spans/counts")
    return selected_entries[0]


def verify_identity(rom, mapping, index):
    if not isinstance(rom, bytes):
        raise ValueError("software double requires a ROM snapshot")
    entries, rows = indices(mapping, index)
    for start, end, count, digest in IDENTITIES:
        entry = span_record(start, end, entries, rows, rom)
        if entry["instrs"] != count or \
                hashlib.sha256(rom[start - 0x08000000:end - 0x08000000]).hexdigest() != digest:
            raise ValueError("software-double complete runtime identity differs")
    for site, target in EDGES:
        first, second = struct.unpack_from("<HH", rom, site - 0x08000000)
        displacement = ((first & 0x7FF) << 12) | ((second & 0x7FF) << 1)
        if displacement & 0x400000:
            displacement -= 0x800000
        if first & 0xF800 != 0xF000 or second & 0xF800 != 0xF800 or site + 4 + displacement != target:
            raise ValueError("software-double dependency edge differs")
    prove_truncation_closure(rom, entries)
    return entries, rows


def prove_truncation_closure(rom, entries):
    """Prove the conversion's complete CFG, bounded writes and restoring ABI.

    Numeric loads remain target-state inputs. The unpacker may write only its
    five-word formal output record; transitive writes must fit each caller's
    real local frame. No unrestricted IEEE conversion semantics are asserted.
    """
    from software_float_profile import prove_runtime
    identities = {start: (end, count) for start, end, count, _ in IDENTITIES
                  if start in TRUNCATION_CLOSURE}
    pending, proofs = set(TRUNCATION_CLOSURE), {}
    while pending:
        ready = [start for start in sorted(pending)
                 if all(target in proofs for site, target in EDGES
                        if start <= site < identities[start][0])]
        if not ready:
            raise ValueError("software-double truncation closure is recursive or incomplete")
        for start in ready:
            end, count = identities[start]
            writes = tuple((1, offset, 4) for offset in range(0, 20, 4)) \
                if start == 0x08142D34 else ()
            proofs[start] = prove_runtime(
                rom, entries, start, end, count, proofs, call_edges=EDGES,
                scalar_entries=(OPERATIONS["__truncdfsf2"],), allowed_writes=writes,
                stack_load_widths=(1, 2, 4))
            pending.remove(start)
    return proofs


def validate_span(data, address, rom, mapping, index):
    entries, rows = verify_identity(rom, mapping, index)
    entry = span_record(address, address + len(data), entries, rows, rom)
    if reserved(address) or not data or len(data) % 2 or \
            data != rom[address - 0x08000000:address - 0x08000000 + len(data)]:
        raise ValueError("software-double complete caller differs from mapped ROM")
    return entries, entry


def call_records(calls, address, bindings):
    return [[site - address, bindings.get(site, f"func_{target:08X}")]
            for site, target in sorted(calls.items())]


def verify_context(data, address, calls, context):
    if not isinstance(context, tuple) or len(context) != 4 or \
            not isinstance(context[3], dict) or not context[3]:
        raise ValueError("software double requires an isolated canonical runtime context")
    rom, mapping, index, bindings = context
    validate_span(data, address, rom, mapping, index)
    if any(type(site) is not int or name not in OPERATIONS or calls.get(site) != OPERATIONS[name]
           for site, name in bindings.items()) or \
            set(bindings) != {site for site, target in calls.items() if reserved(target)}:
        raise ValueError("software-double runtime call bindings are incomplete or mixed")


def verify(data, address, rom, mapping, index, manifest, *, data_mapping=None):
    from match import (function_address_target, uses_stack_frame, verify_leaf_instructions,
                       parse_data_symbols, verify_data_literals, modsi3, ARM_OP_MEM, ARM_REG_PC)
    entries, entry = validate_span(data, address, rom, mapping, index)
    if not isinstance(manifest, dict) or \
            set(manifest) not in ({"runtime", "abi", "semantics", "dependencies", "frame", "calls"},
                                 {"runtime", "abi", "semantics", "dependencies", "frame", "calls", "data"}) or \
            manifest["runtime"] != RUNTIME or manifest["abi"] != ABI or manifest["semantics"] != SEMANTICS or \
            type(manifest["dependencies"]) is not list or \
            any(type(record) is not list or len(record) != 3 or \
                type(record[0]) is not int or type(record[1]) is not int or type(record[2]) is not str
                for record in manifest["dependencies"]) or \
            manifest["dependencies"] != dependency_records() or type(manifest["frame"]) is not bool or \
            not isinstance(manifest["calls"], list) or \
            "data" in manifest and (type(manifest["data"]) is not list or not manifest["data"]):
        raise ValueError("invalid software-double manifest")
    calls, bindings = {}, {}
    previous = -4
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid software-double call record")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or offset % 2 or \
                offset < previous + 4 or offset < 0 or offset + 4 > len(data):
            raise ValueError("software-double calls must be ordered nonoverlapping instructions")
        if name in OPERATIONS:
            calls[address + offset] = OPERATIONS[name]
            bindings[address + offset] = name
        else:
            calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
        previous = offset
    literals, occupied = {}, {byte - address for site in calls for byte in range(site, site + 4)}
    objects = parse_data_symbols(data_mapping) if "data" in manifest else {}
    previous = -1
    for record in manifest.get("data", []):
        if type(record) is not list or len(record) != 3:
            raise ValueError("invalid software-double data binding")
        offset, name, addend = record
        if type(offset) is not int or type(name) is not str or offset <= previous or \
                offset < 0 or offset + 4 > len(data) or (address + offset) % 4 or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF or name not in objects:
            raise ValueError("software-double data bindings require ordered aligned mapped words")
        previous = offset
        positions = set(range(offset, offset + 4))
        if occupied & positions:
            raise ValueError("software-double call/data bindings overlap")
        occupied.update(positions)
        value = objects[name] + addend
        parse_data_symbols(json.dumps({name: f"0x{value:08X}"}).encode())
        if not modsi3.supported_data(objects[name], len(rom)) or \
                not modsi3.supported_data(value, len(rom)) or \
                any(int(owner["rom"], 16) <= (pointer & ~1) < int(owner["end"], 16)
                    for owner in entries for pointer in (objects[name], value)) or \
                struct.unpack_from("<I", data, offset)[0] != value:
            raise ValueError("software-double data literal differs or aliases indexed code/forbidden memory")
        literals[offset] = (name, value)
    instructions = verify_leaf_instructions(data, address, True, calls,
                                            double_context=(rom, mapping, index, bindings))
    if uses_stack_frame(instructions) != manifest["frame"] or len(instructions) != entry["instrs"]:
        raise ValueError("software-double frame/count disagrees with the converged CFG")
    verify_data_literals(instructions, address, literals)
    address_literals = set()
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                if modsi3.address_literal(struct.unpack_from("<I", data, offset)[0]):
                    address_literals.add(offset)
    if address_literals != set(literals):
        raise ValueError("software-double address-domain literals require exact mapped-data coverage")
    return instructions


def make_manifest(calls, address, bindings, instructions, *, literals=None, data_mapping=None):
    from match import uses_stack_frame, parse_data_symbols
    manifest = {"runtime": RUNTIME, "abi": ABI, "semantics": SEMANTICS,
            "dependencies": dependency_records(), "frame": uses_stack_frame(instructions),
            "calls": call_records(calls, address, bindings)}
    if literals:
        objects = parse_data_symbols(data_mapping)
        manifest["data"] = [[offset, name, value - objects[name]]
                            for offset, (name, value) in sorted(literals.items())]
    return manifest


def object_bytes(runner, workspace, args, original, address, mapping, rom, index, *,
                 data_mapping=None, data_relocations=None):
    from match import (allocated_text_only, function_record, function_address_target,
                       link_calls, parse_data_symbols)
    fixed_configuration(args)
    if original["type"] != 1:
        raise ValueError("software double requires a relocatable original ELF")
    allocated_text_only(original)
    symbol, offset = function_record(original, f"func_{address:08X}", address, True)
    definitions = [item for item in original["symbols"] if item["type"] == 2 and item["section"]]
    padding = original["text"][symbol["size"]:]
    if definitions != [symbol] or offset or len(padding) > 3 or \
            any(padding) and not (symbol["size"] % 4 == 2 and padding == b"\xc0\x46") or \
            any(item["type"] == 1 and item["section"] or re.fullmatch(r"\$a(?:\..*)?", item["name"])
                for item in original["symbols"]):
        raise ValueError("software double requires sole-function Thumb text ownership")
    entries, _ = verify_identity(rom, mapping, index)
    if data_relocations is not None and (type(data_relocations) is not dict or data_relocations):
        raise ValueError("software-double data provenance requires an empty collection")
    objects, has_data = None, False
    for section_index in original["relocations"]:
        section = original["sections"][section_index]
        if section[1] != 9 or section[7] != original["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("software double requires ordinary Thumb call or mapped data relocations")
        symbols = original["symbol_tables"].get(section[6])
        for position in range(0, section[5], 8):
            _, info = struct.unpack_from("<II", original["section_data"][section_index], position)
            if info & 255 not in (2, 10) or symbols is None or info >> 8 >= len(symbols):
                raise ValueError("software double excludes unsupported relocations")
            target = symbols[info >> 8]
            if info & 255 == 2:
                if data_relocations is None:
                    raise ValueError("software-double data relocation requires explicit provenance capture")
                if objects is None:
                    objects = parse_data_symbols(data_mapping)
                if target["name"] not in objects or target["section"] or target["bind"] != 1 or \
                        target["type"] not in (0, 1) or target["value"] or \
                        sum(item["name"] == target["name"] for item in original["symbols"]) != 1:
                    raise ValueError("software-double data requires one undefined mapped global object")
                has_data = True
                continue
            if target["name"] not in OPERATIONS:
                function_address_target(target["name"], entries, address, symbol["size"], len(rom))
            if target["section"] or target["bind"] != 1 or target["type"] not in (0, 2) or \
                    target["value"] or sum(item["name"] == target["name"]
                                           for item in original["symbols"]) != 1:
                raise ValueError("software-double calls require unique undefined global functions")
    if original["relocations"]:
        bindings = {}
        data, calls, literals = link_calls(runner, workspace, args, original, address, mapping, len(rom), rom,
                                          data_mapping=data_mapping if has_data else None,
                                          double_bindings=bindings, double_index=index,
                                          allow_double_data=has_data)
        if not bindings:
            raise ValueError("software double requires at least one canonical runtime call")
        if data_relocations is not None:
            data_relocations.update(literals)
        return data, calls, bindings
    if any(item["name"] and not item["section"] for item in original["symbols"]):
        raise ValueError("software-double leaf retains undefined symbols")
    raise ValueError("software double requires at least one canonical runtime call")


def verify_source(root, address, data, rom, mapping, index, source_digest, manifest, *, data_mapping=None):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object,
                       _run_replay_process, plausibility_result)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive software-double replay is unsupported")
    token = _replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or index_snapshot(root) != index or \
                "data" in manifest and data_snapshot(root) != data_mapping:
            raise ValueError("software-double replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("software-double replay ROM differs")
        validate_span(data, address, rom, mapping, index)
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_double_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("software-double source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                literals = {}
                got, calls, bindings = object_bytes(runner, workspace, args, original, address, mapping, rom, index,
                                                    data_mapping=data_mapping, data_relocations=literals)
                instructions = verify(got, address, rom, mapping, index, manifest, data_mapping=data_mapping)
                if got != data or make_manifest(calls, address, bindings, instructions,
                        literals=literals, data_mapping=data_mapping) != manifest:
                    raise ValueError("software-double report lacks fresh original-ELF provenance")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("software-double captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                index_snapshot(root) != index or \
                "data" in manifest and data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or \
                Path(selected_rom).read_bytes() != rom:
            raise ValueError("software-double replay inputs changed")
        return instructions
    finally:
        _replay_active.reset(token)


def report_matches(report, root, address):
    from match_evidence import (source_fingerprint, mapping_snapshot, data_snapshot,
                                report_rom_path, STACK_SUMMARY, CALL_SUMMARY)
    lines = report.splitlines()

    def single(prefix):
        marker = prefix.split(":", 1)[0].rstrip()
        matches = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == marker]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, malformed or duplicate software-double evidence")
        return matches[0][len(prefix):]

    def unquote(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed quoted software-double evidence")
        return value[1:-1]

    try:
        if not selected(report):
            return False
        profile_markers = {"* software double", "* software double manifest", "* software double proof SHA-256",
                        "* software double ABI", "* software double runtime", "* software double semantics"}
        if any(marker_text(line).startswith("* software double") and
               line.split(":", 1)[0] not in profile_markers for line in lines):
            return False
        mapping, index = mapping_snapshot(root), index_snapshot(root)
        source_digest = source_fingerprint(root, address)
        if mapping is None or single("* control flow: ") != CALL_SUMMARY or \
                single("* software double: ") != SUMMARY or \
                unquote("* software double ABI: ") != ABI or \
                unquote("* software double runtime: ") != RUNTIME or \
                unquote("* software double semantics: ") != SEMANTICS or \
                unquote("* compiler: ") != compiler_text() or \
                unquote("* source SHA-256: ") != source_digest or \
                unquote("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                unquote("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or single("* source plausibility: ") != "plausible" or \
                single("* hand-asm allow list: ") != "not listed":
            return False
        candidates = list((Path(root) / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or unquote("* source: ") != candidates[0].relative_to(root).as_posix():
            return False
        encoded = unquote("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = unquote("* software double manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique_members)
        if manifest_text(manifest) != encoded_manifest:
            return False
        objects = data_snapshot(root) if "data" in manifest else None
        object_lines = [line for line in lines if marker_text(line).startswith("* data symbols")]
        if object_lines != ([f"* data symbols SHA-256: `{hashlib.sha256(objects).hexdigest()}`"]
                            if manifest.get("data") and objects is not None else []):
            return False
        frames = [line for line in lines if marker_text(line).startswith("* stack frame")]
        if frames != ([f"* stack frame: {STACK_SUMMARY}"] if manifest.get("frame") is True else []):
            return False
        verdicts = [line for line in lines if re.match(
            r"\*\*[ \t]*(?:MATCH|NOT|HAND|IMPLAUSIBLE)\b", marker_text(line))]
        selected_rom = report_rom_path(root)
        rom = Path(selected_rom).read_bytes()
        if unquote("* ROM SHA-256: ") != hashlib.sha256(rom).hexdigest() or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                verdicts != [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                unquote("* software double proof SHA-256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, rom, data_mapping=objects):
            return False
        verify_source(root, address, data, rom, mapping, index, source_digest, manifest, data_mapping=objects)
        return report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
