"""Explicit typed function literals with conditional canonical indirect calls."""

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

from inert_spin_profile import fixed_configuration, index_snapshot, marker_text, validate_span


SCHEMA = "elf-symbol-thumb-function-address-thunks-v1"
SELECTOR = "canonical-thunks-v1"
ZERO_SELECTOR = "canonical-thunks-zero-word-pool-v1"
ZERO_SCHEMA = "elf-symbol-thumb-function-address-thunks-zero-pool-v1"
INTERPOSED_SELECTOR = "canonical-thunks-interposed-pool-v1"
INTERPOSED_SCHEMA = "elf-symbol-thumb-function-address-thunks-interposed-pool-v1"
from umod_r1_thunk_profile import SELECTOR as UMOD_R1_SELECTOR, SCHEMA as UMOD_R1_SCHEMA
from thunk_pool_switch import INTERPOSED
from unsigned_thunk_profile import SELECTOR as UNSIGNED_SELECTOR, SCHEMA as UNSIGNED_SCHEMA

SELECTORS = (SELECTOR, ZERO_SELECTOR, UMOD_R1_SELECTOR, INTERPOSED_SELECTOR, UNSIGNED_SELECTOR)
# Selectors whose manifests carry their selector and producer-source digests.
VERSIONED_POOLS = {ZERO_SELECTOR: 0, INTERPOSED_SELECTOR: INTERPOSED}


def pool_words(selector):
    if type(selector) is not str or selector not in SELECTORS:
        raise ValueError("unsupported canonical-thunk selector")
    return VERSIONED_POOLS.get(selector, 5)


def is_versioned(words):
    """True for a pool policy whose selector is versioned (zero or dispatch-identified)."""
    return any(type(words) is type(value) and words == value for value in VERSIONED_POOLS.values())


def policy_name(words):
    return INTERPOSED_SELECTOR if type(words) is str and words == INTERPOSED else \
        ZERO_SELECTOR if type(words) is int and words == 0 else SELECTOR


def schema_for(selector):
    pool_words(selector)
    return {UMOD_R1_SELECTOR: UMOD_R1_SCHEMA, ZERO_SELECTOR: ZERO_SCHEMA,
            INTERPOSED_SELECTOR: INTERPOSED_SCHEMA, UNSIGNED_SELECTOR: UNSIGNED_SCHEMA}.get(selector, SCHEMA)


def selector_from_manifest(manifest):
    selector = manifest.get("selector", SELECTOR)
    pool_words(selector)
    if "selector" in manifest and selector not in (ZERO_SELECTOR, UMOD_R1_SELECTOR, INTERPOSED_SELECTOR,
                                                   UNSIGNED_SELECTOR):
        raise ValueError("legacy thunk evidence cannot carry an alternate pool policy")
    return selector


def producer_sources():
    return {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ("match.py", "function_thunk_profile.py", "thunk_pool_switch.py")}


def context_words(context):
    if context is not None and "interposed_words" in context:
        words = context["interposed_words"]
        if not (type(words) is int and words == 0 or type(words) is str and words == INTERPOSED):
            raise ValueError("explicit pool context requires the exact integer zero or the interposed policy")
        return words
    return 5


def check_pool_opt_in(words, function_thunks):
    if not (type(words) is int and words in (0, 5) or type(words) is str and words == INTERPOSED) or \
            is_versioned(words) and function_thunks is not True:
        raise ValueError("versioned pool selector linking requires its explicit canonical-thunk context")


def verify_pool_calls(calls, words):
    if not (type(words) is int and words in (0, 5) or type(words) is str and words == INTERPOSED):
        raise ValueError("unsupported canonical-thunk pool policy")
    if words == 0 and {target for target in calls.values() if reserved(target)} != {ALIASES["_call_via_r3"]}:
        raise ValueError("zero-pool selector requires only canonical R3 thunks and ordinary calls")

RUNTIME = "agbcc-call-via-r0-r12-v1"
ABI = "conditional-indirect-caller-abi-v1"
CONTROL_FLOW = "typed function literals and canonical thunks; conditional returning indirect ARM ABI"
REPLAY_TIMEOUT = 120
START, END = 0x08142244, 0x08142280
ALIASES = {f"_call_via_r{register}": START + 4 * register for register in range(13)}
FORBIDDEN = ("* buffer", "* unsigned division", "* signed remainder", "* signed quotient",
             "* switches", "* switch ", "* function address", "* function buffer",
             "* software double", "* inert spin")
_replay_active = ContextVar("function_thunk_replay_active", default=False)


def reserved(value):
    return START <= value & ~1 < END


def verify_data_bindings(calls, literals, objects, entries):
    if not literals or not any(reserved(target) for target in calls.values()):
        return
    code_entries = {int(entry["rom"], 16) & ~1 for entry in entries}
    for name, value in literals.values():
        if any(reserved(target) or target & ~1 in code_entries for target in (objects[name], value)):
            raise ValueError("thunk callers cannot bind indexed function entries as data")


def verify_literal_bindings(data, address, instructions, calls, mapping, functions):
    from match import ARM_OP_MEM, ARM_REG_PC
    if not any(reserved(target) for target in calls.values()):
        return
    code_entries = {int(entry["rom"], 16) & ~1 for entry in json.loads(mapping)}
    offsets = {((instruction.address + 4) & ~3) + operand.mem.disp - address
               for instruction in instructions for operand in instruction.operands
               if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and
               operand.mem.base == ARM_REG_PC and not operand.mem.index}
    for offset in offsets:
        if offset < 0 or offset + 4 > len(data) or (address + offset) % 4:
            raise ValueError("thunk literal is not a complete aligned caller word")
        value = struct.unpack_from("<I", data, offset)[0]
        if reserved(value) or value & ~1 in code_entries and (
                offset not in functions or functions[offset][1] != value):
            raise ValueError("code-entry thunk literals require canonical function provenance")


def verify_own_span_literals(data, address, instructions, table_pointer=None):
    """No reached literal may name the caller's own bytes (Thumb bit set or not),
    its own entry included. The one exception is the switch table pointer word at
    offset table_pointer, whose only reader the pool-switch record pins to the
    dispatch; the table's case words are never exempt."""
    from match import ARM_OP_MEM, ARM_REG_PC
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic != "ldr" or operand.type != ARM_OP_MEM or \
                    operand.mem.base != ARM_REG_PC or operand.mem.index:
                continue
            offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
            if offset < 0 or offset + 4 > len(data) or (address + offset) % 4:
                raise ValueError("thunk literal is not a complete aligned caller word")
            value = struct.unpack_from("<I", data, offset)[0]
            if offset != table_pointer and address <= value & ~1 < address + len(data):
                raise ValueError("thunk literals cannot name the caller's own bytes")


def selector_for_report(report):
    lines = report.splitlines()
    if not any("elf-symbol-thumb-function-address-thunks-" in line or
               marker_text(line).startswith("* function-address") for line in lines):
        return None
    fields = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == "* function-address thunks"]
    if len(fields) != 1 or not fields[0].startswith("* function-address thunks: "):
        raise ValueError("missing or duplicate canonical-thunk selector")
    selector = fields[0][len("* function-address thunks: "):]
    if [line for line in lines if marker_text(line).startswith("* verification")] != \
            [f"* verification: `{schema_for(selector)}`"] or any(marker_text(line).startswith(FORBIDDEN) for line in lines):
        raise ValueError("mixed or malformed function-thunk selection")
    return selector


def selected(report):
    return selector_for_report(report) is not None


def manifest_text(manifest):
    return json.dumps(manifest, sort_keys=True, separators=(",", ":"))


def fingerprint(address, data, manifest, source_digest, mapping, index, objects, rom):
    from match import DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS
    digest = hashlib.sha256()
    for payload in (schema_for(selector_from_manifest(manifest)).encode(), address.to_bytes(4, "little"), data,
                    manifest_text(manifest).encode(), source_digest.encode(), mapping, index,
                    b"absent" if objects is None else b"present:" + objects,
                    hashlib.sha256(rom).digest(),
                    json.dumps([DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY,
                                DEFAULT_LD, DEFAULT_FLAGS]).encode()):
        digest.update(len(payload).to_bytes(8, "little"))
        digest.update(payload)
    return digest.hexdigest()


def dependencies(names, rom):
    from match import ROM_BASE, thunk_is_call_via
    result = []
    for name in sorted(set(names)):
        if name not in ALIASES:
            raise ValueError("unsupported canonical call thunk")
        address = ALIASES[name]
        if not thunk_is_call_via(rom, address, (address - START) // 4):
            raise ValueError("call thunk identity differs")
        result.append([name, address, address + 4,
                       hashlib.sha256(rom[address - ROM_BASE:address - ROM_BASE + 4]).hexdigest()])
    return result


def namespace(preprocessed):
    from plausible import strip_comments_and_strings
    if re.search(r"\b_call_via_\w*", strip_comments_and_strings(preprocessed)):
        raise ValueError("call-via identifiers are reserved for compiler emission")


def original_bindings(image, address, mapping, rom, objects, *, switch_relocations=None, selector=SELECTOR):
    from match import (allocated_text_only, function_record, call_bindings, ARM_INS_BL,
                       ARM_OP_IMM, Cs, CS_ARCH_ARM, CS_MODE_THUMB)
    words = pool_words(selector)
    if image["type"] != 1:
        raise ValueError("function thunks require original relocatable ELF")
    allocated_text_only(image)
    symbol, offset = function_record(image, f"func_{address:08X}", address, True)
    if offset or any(item["type"] == 1 and item["section"] or re.fullmatch(r"\$a(?:\..*)?", item["name"])
                     for item in image["symbols"]):
        raise ValueError("function thunks require sole Thumb function ownership")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    for section_index in image["relocations"]:
        section = image["sections"][section_index]
        if section[1] != 9 or section[7] != image["text_index"] or section[9] != 8 or section[5] % 8:
            raise ValueError("invalid function-thunk relocation section")
        symbols = image["symbol_tables"].get(section[6])
        for position in range(0, section[5], 8):
            site, info = struct.unpack_from("<II", image["section_data"][section_index], position)
            if info & 255 not in (2, 10) or symbols is None or info >> 8 >= len(symbols):
                raise ValueError("unsupported function-thunk relocation")
            target = symbols[info >> 8]
            if info & 255 == 2 and target["section"]:
                # call_bindings validates the sole zero-valued local .text
                # symbol, word bounds/addends and exact guarded table roles.
                continue
            callable_symbol = info & 255 == 10 or target["name"].startswith("func_")
            if target["section"] or target["bind"] != 1 or target["value"] or \
                    target["type"] not in ((0, 2) if callable_symbol else (0, 1)) or \
                    sum(item["name"] == target["name"] for item in image["symbols"]) != 1:
                raise ValueError("function-thunk symbols require unique undefined global types")
            if info & 255 == 10:
                instruction = next(decoder.disasm(image["text"][site:site + 4], address + site), None)
                if instruction is None or instruction.id != ARM_INS_BL or instruction.size != 4 or \
                        len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM or \
                        instruction.operands[0].imm != address + site:
                    raise ValueError("function-thunk BL requires a canonical zero addend")
    functions = {}
    unsigned = {} if selector in (UMOD_R1_SELECTOR, UNSIGNED_SELECTOR) else None
    quotient = {} if selector == UNSIGNED_SELECTOR else None
    switch_relocations = {} if switch_relocations is None else switch_relocations
    calls, targets, literals = call_bindings(image, f"func_{address:08X}", address, mapping,
                                            len(rom), rom, objects, functions, switch_relocations,
                                            udivsi3_bindings=quotient,
                                            function_thunks=True, thunk_pool_words=words, umodsi3_bindings=unsigned,
                                            umod_r1_profile=selector if selector == UMOD_R1_SELECTOR else None,
                                            unsigned_thunk_profile=selector if selector == UNSIGNED_SELECTOR else None)
    verify_pool_calls(calls, words)
    if is_versioned(words) and not switch_relocations:
        raise ValueError(f"{policy_name(words)} requires a complete local switch")
    if not any(name in ALIASES for name in targets):
        raise ValueError("function thunks require canonical calls")
    for name, value in targets.items():
        if reserved(value) and name not in ALIASES:
            raise ValueError("reserved thunk requires its canonical call alias")
    if any(reserved(value) for _, value in literals.values()):
        raise ValueError("thunk table cannot be bound as data")
    dependencies([name for name in targets if name.startswith("_call_via_")], rom)
    return calls, functions, literals


def object_bytes(runner, workspace, args, original, address, mapping, rom, objects, *, selector=SELECTOR):
    from match import link_calls
    fixed_configuration(args)
    preprocessed = runner.read_binary(f"{workspace}/f.i").decode("utf-8")
    namespace(preprocessed)
    if selector == UNSIGNED_SELECTOR:
        from unsigned_thunk_profile import namespace as unsigned_namespace
        unsigned_namespace(preprocessed)
    expected_switch = {}
    expected_calls, expected_functions, expected_literals = original_bindings(
        original, address, mapping, rom, objects, switch_relocations=expected_switch, selector=selector)
    functions, switches = {}, {}
    unsigned = {} if selector in (UMOD_R1_SELECTOR, UNSIGNED_SELECTOR) else None
    quotient = {} if selector == UNSIGNED_SELECTOR else None
    data, calls, literals = link_calls(runner, workspace, args, original, address, mapping,
                                       len(rom), rom, objects, functions, switches, udivsi3_bindings=quotient,
                                       function_thunks=True,
                                       thunk_pool_words=pool_words(selector), umodsi3_bindings=unsigned,
                                       umod_r1_profile=selector if selector == UMOD_R1_SELECTOR else None,
                                       unsigned_thunk_profile=selector if selector == UNSIGNED_SELECTOR else None)
    if (calls, functions, literals, switches) != \
            (expected_calls, expected_functions, expected_literals, expected_switch):
        raise ValueError("function-thunk original bindings changed during linking")
    return data, calls, functions, literals


def make_manifest(calls, functions, literals, address, rom, objects, instructions, *, pool_switch=None, selector=SELECTOR):
    from match import parse_data_symbols, uses_stack_frame, ARM_OP_REG, ARM_REG_PC
    if selector == UMOD_R1_SELECTOR:
        from umod_r1_thunk_profile import make_manifest as composed_manifest
        if pool_switch is not None:
            raise ValueError("UMOD/r1 source admission excludes switches")
        return composed_manifest(calls, functions, literals, address, rom, objects, instructions)
    if selector == UNSIGNED_SELECTOR:
        from unsigned_thunk_profile import make_manifest as unsigned_manifest
        if pool_switch is not None:
            raise ValueError("unsigned thunk source admission excludes switches")
        return unsigned_manifest(calls, functions, literals, address, rom, objects, instructions)
    words = pool_words(selector)
    verify_pool_calls(calls, words)
    reverse = {target: name for name, target in ALIASES.items()}
    names = parse_data_symbols(objects)
    thunks = [[site - address, reverse[target]] for site, target in sorted(calls.items()) if target in reverse]
    manifest = {"runtime": RUNTIME, "abi": ABI, "frame": uses_stack_frame(instructions),
            "calls": [[site - address, f"func_{target:08X}"] for site, target in sorted(calls.items()) if target not in reverse],
            "thunks": thunks, "functions": [[offset, name] for offset, (name, _) in sorted(functions.items())],
            "data": [[offset, name, value - names[name]] for offset, (name, value) in sorted(literals.items())],
            "dependencies": dependencies([record[1] for record in thunks], rom)}
    if pool_switch is not None or any(item.mnemonic == 'mov' and item.operands and
            item.operands[0].type == ARM_OP_REG and item.operands[0].reg == ARM_REG_PC
            for item in instructions):
        from thunk_pool_switch import discover, record
        # Complete body size is supplied by the exact indexed caller span in verify.
        end = max(item.address + item.size for item in instructions)
        for item in instructions:
            from match import ARM_OP_MEM, ARM_REG_PC
            for operand in item.operands:
                if item.mnemonic == 'ldr' and operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC:
                    end = max(end, ((item.address + 4) & ~3) + operand.mem.disp + 4)
        body = rom[address - 0x08000000:end - 0x08000000]
        if pool_switch is None:
            pool_switch = discover(body, address, instructions, interposed_words=words)
        manifest['pool_switch'] = record(body, address, pool_switch, instructions, interposed_words=words)
    if is_versioned(words):
        if 'pool_switch' not in manifest:
            raise ValueError(f"{policy_name(words)} requires a complete local switch")
        manifest["selector"] = selector
        manifest["producer_source_sha256"] = producer_sources()
    return manifest


def verify(data, address, rom, mapping, index, objects, manifest):
    from match import function_address_bindings, verify_leaf_instructions, verify_data_literals, uses_stack_frame
    validate_span(data, address, rom, mapping, index)
    keys = {"runtime", "abi", "frame", "calls", "thunks", "functions", "data", "dependencies"}
    if type(manifest) is not dict:
        raise ValueError("invalid function-thunk manifest")
    selector = selector_from_manifest(manifest)
    if selector == UMOD_R1_SELECTOR:
        from umod_r1_thunk_profile import verify as composed_verify
        instructions = composed_verify(data, address, rom, mapping, index, objects, manifest)
        verify_own_span_literals(data, address, instructions)
        return instructions
    if selector == UNSIGNED_SELECTOR:
        from unsigned_thunk_profile import verify as unsigned_verify
        instructions = unsigned_verify(data, address, rom, mapping, index, objects, manifest)
        verify_own_span_literals(data, address, instructions)
        return instructions
    words = pool_words(selector)
    allowed = (keys | {"pool_switch", "selector", "producer_source_sha256"},) if is_versioned(words) else (keys, keys | {'pool_switch'})
    if set(manifest) not in allowed or manifest["runtime"] != RUNTIME or \
            manifest["abi"] != ABI or type(manifest["frame"]) is not bool or \
            any(type(manifest[name]) is not list for name in keys - {"runtime", "abi", "frame"}) or \
            not manifest["thunks"]:
        raise ValueError("invalid function-thunk manifest")
    if is_versioned(words) and manifest["producer_source_sha256"] != producer_sources():
        raise ValueError(f"{selector} producer source bytes differ")
    ordinary = {name: manifest[name] for name in ("calls", "functions", "data")}
    calls, literals = function_address_bindings(
        data, address, rom, mapping, objects, ordinary, allow_empty_functions=True)
    if any(reserved(target) for target in calls.values()) or any(reserved(value) for _, value in literals.values()):
        raise ValueError("reserved thunk binding outside canonical calls")
    occupied = {position for records in ordinary.values() for record in records
                for position in range(record[0], record[0] + 4)}
    previous = -1
    for record in manifest["thunks"]:
        if type(record) is not list or len(record) != 2:
            raise ValueError("invalid function-thunk call record")
        offset, name = record
        if type(offset) is not int or type(name) is not str or name not in ALIASES or \
                offset <= previous or offset < 0 or offset % 2 or offset + 4 > len(data) or \
                occupied.intersection(range(offset, offset + 4)):
            raise ValueError("invalid or overlapping function-thunk call")
        occupied.update(range(offset, offset + 4))
        calls[address + offset] = ALIASES[name]
        previous = offset
    verify_pool_calls(calls, words)
    for record in manifest["dependencies"]:
        if type(record) is not list or len(record) != 4 or type(record[0]) is not str or \
                type(record[1]) is not int or type(record[2]) is not int or type(record[3]) is not str:
            raise ValueError("invalid function-thunk dependency types")
    if manifest["dependencies"] != dependencies([record[1] for record in manifest["thunks"]], rom):
        raise ValueError("function-thunk dependencies differ")
    from match import parse_data_symbols
    verify_data_bindings(calls, {record[0]: literals[record[0]] for record in manifest["data"]},
                         parse_data_symbols(objects), json.loads(mapping))
    context = {}
    if 'pool_switch' in manifest:
        from thunk_pool_switch import discover, record
        from match import Cs, CS_ARCH_ARM, CS_MODE_THUMB
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        relocations = discover(data, address, list(decoder.disasm(data, address)), interposed_words=words)
        context['pool_switch'] = relocations
        if is_versioned(words):
            context['interposed_words'] = words
    instructions = verify_leaf_instructions(data, address, True, calls, function_thunk_context=context)
    if not context:
        from match import ARM_OP_REG, ARM_REG_PC
        if any(item.mnemonic == 'mov' and item.operands and
               item.operands[0].type == ARM_OP_REG and item.operands[0].reg == ARM_REG_PC
               for item in instructions):
            raise ValueError('canonical pool switch requires its versioned manifest')
    table_pointer = None
    if context:
        recorded = record(data, address, context['pool_switch'], instructions, interposed_words=words)
        if type(manifest['pool_switch']) is not dict or \
                manifest_text(manifest['pool_switch']) != manifest_text(recorded):
            raise ValueError('canonical pool-switch manifest differs')
        table_pointer = recorded['layout']['literal']
    functions = {offset: (name, struct.unpack_from("<I", data, offset)[0])
                 for offset, name in manifest["functions"]}
    verify_literal_bindings(data, address, instructions, calls, mapping, functions)
    verify_own_span_literals(data, address, instructions, table_pointer)
    verify_data_literals(instructions, address, literals)
    if uses_stack_frame(instructions) != manifest["frame"]:
        raise ValueError("function-thunk frame differs")
    return instructions


def verify_source(root, address, data, rom, mapping, index, objects, source_digest, manifest=None,
                  buffer_stack_arguments=None):
    from match import (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD,
                       DEFAULT_FLAGS, DEFAULT_WSL_PATH, Runner, compile_object, link_calls,
                       _run_replay_process, plausibility_result, verify_leaf_instructions, BufferCallProof)
    from match_evidence import source_paths, source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path
    if _replay_active.get():
        raise ValueError("recursive function-thunk replay is unsupported")
    selector = SELECTOR if manifest is None else selector_from_manifest(manifest)
    token = _replay_active.set(True)
    try:
        root = Path(root)
        selected_rom = report_rom_path(root)
        def unchanged():
            return source_fingerprint(root, address) == source_digest and mapping_snapshot(root) == mapping and \
                index_snapshot(root) == index and data_snapshot(root) == objects and \
                report_rom_path(root) == selected_rom and Path(selected_rom).read_bytes() == rom
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or not unchanged():
            raise ValueError("function-thunk replay inputs differ")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_thunk_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("function-thunk capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured, timeout=REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                if manifest is None:
                    functions = {}
                    got, calls, literals = link_calls(runner, workspace, args, original, address, mapping,
                                            len(rom), rom, objects, functions)
                    if functions:
                        raise ValueError("legacy thunk evidence cannot carry function literals")
                    if buffer_stack_arguments is not None or any(reserved(target) for target in calls.values()):
                        proof = BufferCallProof(rom, mapping, stack_arguments=buffer_stack_arguments,
                                                loop_replay=True) \
                            if buffer_stack_arguments is not None else None
                        instructions = verify_leaf_instructions(got, address, True, calls, buffer_proof=proof)
                        if proof is not None and (not proof.dependencies or literals or proof.span(address) != got):
                            raise ValueError("legacy thunk buffer replay requires its complete buffer-only proof")
                        verify_literal_bindings(got, address, instructions, calls, mapping, functions)
                        if any(reserved(target) for target in calls.values()):
                            verify_own_span_literals(got, address, instructions)
                else:
                    got, calls, functions, literals = object_bytes(runner, workspace, args, original,
                                                                  address, mapping, rom, objects, selector=selector)
                    if "pool_switch" in manifest:
                        switches = {}
                        original_bindings(original, address, mapping, rom, objects,
                                          switch_relocations=switches, selector=selector)
                        if [[offset, addend] for offset, addend in sorted(switches.items())] != \
                                manifest["pool_switch"]["layout"]["relocations"]:
                            raise ValueError("pool switch lacks exact original local relocations")
                    instructions = verify(got, address, rom, mapping, index, objects, manifest)
                    if make_manifest(calls, functions, literals, address, rom, objects, instructions, selector=selector) != manifest:
                        raise ValueError("function-thunk manifest lacks original-ELF provenance")
                if got != data:
                    raise ValueError("function-thunk fresh complete bytes differ")
            checker = Path(__file__).with_name("plausible.py")
            result = _run_replay_process([sys.executable, str(checker), "--quiet", "--addr",
                                         f"0x{address:08X}", "--json"] +
                                        [str(path) for path in source_paths(captured, address)], captured, REPLAY_TIMEOUT)
            findings, allowed = plausibility_result(result, address)
            if findings or allowed or source_fingerprint(captured, address) != source_digest:
                raise ValueError("function-thunk captured source changed or is implausible")
        if not unchanged():
            raise ValueError("function-thunk replay inputs changed")
        return True
    finally:
        _replay_active.reset(token)


def legacy_absence(root, address, data, rom, mapping, buffer_stack_arguments=None):
    from match_evidence import data_snapshot, source_fingerprint
    return verify_source(root, address, data, rom, mapping, index_snapshot(root),
                         data_snapshot(root), source_fingerprint(root, address),
                         buffer_stack_arguments=buffer_stack_arguments)


def report_matches(report, root, address):
    from match import DEFAULT_CC, DEFAULT_FLAGS
    from match_evidence import source_fingerprint, mapping_snapshot, data_snapshot, report_rom_path, STACK_SUMMARY
    lines = report.splitlines()
    def single(prefix):
        key = prefix.split(":", 1)[0].rstrip()
        matches = [line for line in lines if marker_text(line).split(":", 1)[0].rstrip() == key]
        if len(matches) != 1 or not matches[0].startswith(prefix):
            raise ValueError("missing, duplicate or malformed function-thunk field")
        return matches[0][len(prefix):]
    def quoted(prefix):
        value = single(prefix)
        if len(value) < 2 or value[0] != "`" or value[-1] != "`":
            raise ValueError("malformed function-thunk quoted field")
        return value[1:-1]
    def unique(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate function-thunk manifest key")
            result[name] = value
        return result
    try:
        selector = selector_for_report(report)
        if selector is None:
            return False
        markers = {"* function-address thunks", "* function-address-thunk manifest", "* function-address-thunk sha256"}
        if any(marker_text(line).startswith("* function-address") and line.split(":", 1)[0] not in markers for line in lines):
            return False
        mapping, index, objects = mapping_snapshot(root), index_snapshot(root), data_snapshot(root)
        source_digest = source_fingerprint(root, address)
        rom_path = report_rom_path(root)
        rom = Path(rom_path).read_bytes()
        if single("* function-address thunks: ") != selector or single("* control flow: ") != CONTROL_FLOW or \
                quoted("* compiler: ") != f"{DEFAULT_CC} {DEFAULT_FLAGS}" or \
                quoted("* source SHA-256: ") != source_digest or \
                quoted("* mapping SHA-256: ") != hashlib.sha256(mapping).hexdigest() or \
                quoted("* function index SHA-256: ") != hashlib.sha256(index).hexdigest() or \
                quoted("* ROM SHA-256: ") != hashlib.sha256(rom).hexdigest() or \
                single("* verified extent: ") != "complete ELF function symbol, including literal pools" or \
                single("* relocations: ") != "none" or single("* source plausibility: ") != "plausible" or \
                single("* hand-asm allow list: ") != "not listed":
            return False
        paths = list((Path(root) / "src").rglob(f"{address:08X}.c"))
        if len(paths) != 1 or quoted("* source: ") != paths[0].relative_to(root).as_posix():
            return False
        encoded = quoted("* compiled : ")
        if re.fullmatch(r"(?:[0-9a-f]{2})+", encoded) is None:
            return False
        data = bytes.fromhex(encoded)
        encoded_manifest = quoted("* function-address-thunk manifest: ")
        manifest = json.loads(encoded_manifest, object_pairs_hook=unique)
        if manifest_text(manifest) != encoded_manifest:
            return False
        if selector_from_manifest(manifest) != selector:
            return False
        verify(data, address, rom, mapping, index, objects, manifest)
        expected_objects = [f"* data symbols SHA-256: `{hashlib.sha256(objects).hexdigest()}`"] if manifest["data"] else []
        if [line for line in lines if marker_text(line).startswith("* data symbols")] != expected_objects or \
                [line for line in lines if marker_text(line).startswith("* stack frame")] != \
                ([f"* stack frame: {STACK_SUMMARY}"] if manifest["frame"] else []):
            return False
        verdicts = [line for line in lines if re.match(r"\*\*[ \t]*(?:MATCH|NOT|HAND|IMPLAUSIBLE)\b", marker_text(line))]
        if verdicts != [f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"] or \
                single("* ROM bytes: ") != f"`{data.hex()}` ({len(data)} bytes)" or \
                quoted("* function-address-thunk sha256: ") != \
                fingerprint(address, data, manifest, source_digest, mapping, index, objects, rom):
            return False
        verify_source(root, address, data, rom, mapping, index, objects, source_digest, manifest)
        return report_rom_path(root) == rom_path and Path(rom_path).read_bytes() == rom
    except (OSError, ValueError, KeyError, IndexError, TypeError, AttributeError, OverflowError,
            RecursionError, RuntimeError, subprocess.SubprocessError):
        return False
