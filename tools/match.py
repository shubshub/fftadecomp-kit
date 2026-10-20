#!/usr/bin/env python3
"""
match.py - compile src/<addr>.c and diff it against the ROM bytes.

    python tools/match.py 0x08017514
    python tools/match.py --flags "-mthumb-interwork -O1" 0x080112D4
    python tools/match.py --cc clang --flags "--target=arm-none-eabi -mthumb -O2" 0x...

Toolchain: agbcc (gcc 2.9-arm-000512 for Thumb/elf) is the compiler that
built the ROM.  It is a cc1, so it emits assembly and the file has to be
assembled and stripped before the bytes can be compared:

    agbcc <flags> src.c -o out.s
    arm-none-eabi-as -mthumb-interwork out.s -o out.o
    arm-none-eabi-objcopy -O binary --only-section=.text out.o out.bin

On Windows with WSL the whole chain runs inside the distro and the bytes are
read back over.  The verdict is byte-exact or it is not; the report shows which
instruction the compiler decided differently.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import shlex
import shutil
import struct
import subprocess
import sys
from rompath import rom_path
from contextlib import contextmanager
from pathlib import Path
from match_evidence import (BUFFER_SCHEMA, BUFFER_SUMMARY, CALL_SUMMARY, DATA_SCHEMA,
                            FRAMED_DATA_SCHEMA,
                            FUNCTION_ADDRESS_SCHEMA, FUNCTION_ADDRESS_SUMMARY,
                            FRAMED_LINKED_SCHEMA, FRAMED_SCHEMA, LINKED_SCHEMA,
                            SCHEMA, STACK_BUFFER_SCHEMA, STACK_BUFFER_SUMMARY,
                            SWITCH_SCHEMA, SWITCH_SUMMARY, switch_fingerprint, switch_manifest,
                            SWITCH_DATA_SCHEMA, SWITCH_DATA_SUMMARY, switch_data_fingerprint,
                            UDIVSI3_SCHEMA, UDIVSI3_SUMMARY, UDIVSI3_RUNTIME,
                            udivsi3_fingerprint, udivsi3_manifest,
                            STACK_SUMMARY, data_snapshot, mapping_fingerprint,
                            function_address_fingerprint, function_address_manifest,
                            mapping_snapshot, source_fingerprint, source_paths,
                            verify_dependencies)

try:
    from capstone import (Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB,
                          CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_INT)
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_ADR, ARM_INS_B,
                                    ARM_INS_BL, ARM_INS_CMP, ARM_INS_IT, ARM_OP_IMM, ARM_OP_MEM,
                                    ARM_OP_REG, ARM_REG_CPSR, ARM_REG_LR, ARM_REG_PC, ARM_REG_SP,
                                    ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3,
                                    ARM_REG_R12)
except ImportError:
    sys.exit("match.py needs capstone:  python -m pip install capstone")

def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


ROOT = repo_root()
ROM_BASE = 0x08000000

# agbcc's indirect-call helpers are a table of 'bx rN' thunks at 0x08142250,
# not addressed functions, so call_bindings cannot find them in the index.
# They are real code with a checkable shape, so recognise them by name and
# verify the thunk against the ROM rather than trusting the name.
RUNTIME_HELPERS = {f"_call_via_r{n}": 0x08142244 + n * 4
                   for n in range(0, 15)}
UDIVSI3_ADDRESS = 0x08142AB0
UDIVSI3_IDENTITIES = (
    (UDIVSI3_ADDRESS, 0x08142B28,
     "b01be100af59274950038e7cfbf7d5a68defe1a607369f88634aeb3c9453e408"),
    (0x0814274C, 0x0814274E,
     "abd49ec8111be1f55319f91a44d26daaf5abd7567c169a61abf6c0b031d4b31c"),
)


def is_udivsi3_address(address):
    return any(start <= address & ~1 < end for start, end, _ in UDIVSI3_IDENTITIES)


def verify_udivsi3_identity(rom, mapping):
    if not isinstance(rom, bytes) or not isinstance(mapping, bytes):
        raise ValueError("division identity requires ROM and mapping snapshots")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("division identity requires a function mapping")
    for start, end, digest in UDIVSI3_IDENTITIES:
        candidates = [entry for entry in entries if int(entry["rom"], 16) & ~1 == start]
        if len(candidates) != 1 or int(candidates[0]["rom"], 16) != start or \
                int(candidates[0]["end"], 16) != end or candidates[0].get("mode") != "thumb" or \
                not ROM_BASE <= start < end <= ROM_BASE + len(rom):
            raise ValueError("division runtime requires exact unique mapped Thumb spans")
        if any(entry is not candidates[0] and int(entry["rom"], 16) < end and
               int(entry["end"], 16) > start for entry in entries):
            raise ValueError("division runtime mapping overlaps another function")
        if hashlib.sha256(rom[start - ROM_BASE:end - ROM_BASE]).hexdigest() != digest:
            raise ValueError("division runtime or zero-path dependency identity differs")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    dependency = next(decoder.disasm(
        rom[UDIVSI3_ADDRESS + 0x70 - ROM_BASE:UDIVSI3_ADDRESS + 0x74 - ROM_BASE],
        UDIVSI3_ADDRESS + 0x70, count=1), None)
    if dependency is None or dependency.id != ARM_INS_BL or dependency.size != 4 or \
            len(dependency.operands) != 1 or dependency.operands[0].type != ARM_OP_IMM or \
            dependency.operands[0].imm != 0x0814274C:
        raise ValueError("division runtime has an unexpected zero-path dependency")


def thunk_is_call_via(rom, address, register):
    """the thunk must really be 'bx r<register>' followed by 'mov r8,r8'"""
    off = address - ROM_BASE
    if off < 0 or off + 4 > len(rom):
        return False
    hw0, hw1 = struct.unpack_from("<HH", rom, off)
    return hw0 == 0x4700 + (register << 3) and hw1 == 0x46C0

DEFAULT_CC = "$HOME/agbcc/gcc/agbcc"
DEFAULT_CPP = "cpp"
DEFAULT_AS = "arm-none-eabi-as"
DEFAULT_OBJCOPY = "arm-none-eabi-objcopy"
DEFAULT_LD = "arm-none-eabi-ld"
DEFAULT_FLAGS = "-mthumb-interwork -O2"
DEFAULT_WSL_PATH = "$HOME/armtc/root/usr/bin"


class Runner:
    """Runs shell commands, transparently through WSL on Windows."""

    def __init__(self, cc, wsl_distro="Ubuntu", wsl_path=""):
        self.wsl = None
        self.prefix = f"export PATH={wsl_path}:$PATH; " if wsl_path else ""
        if platform.system() == "Windows" and not shutil.which(cc.split("/")[-1]):
            wsl = shutil.which("wsl")
            if wsl:
                self.wsl = [wsl, "-d", wsl_distro, "-e", "bash", "-lc"]

    def sh(self, cmd):
        if self.wsl:
            here = "/mnt/c/" + "/".join(ROOT[3:].split(os.sep))
            cmd = f"{self.prefix}cd {here} && {cmd}"
            r = subprocess.run(self.wsl + [cmd], capture_output=True, text=True)
        else:
            r = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                               cwd=ROOT)
        if r.returncode != 0:
            raise RuntimeError((r.stderr or r.stdout or "command failed").strip())
        return r.stdout

    def read_binary(self, path):
        if self.wsl:
            out = self.sh(f"xxd -p {shlex.quote(path)}")
            return bytes.fromhex("".join(out.split()))
        with open(path, "rb") as f:
            return f.read()

    def write_text(self, path, text):
        self.sh(f"printf %s {shlex.quote(text)} > {shlex.quote(path)}")

    @contextmanager
    def workspace(self):
        path = self.sh('mkdir -p build && mktemp -d "$PWD/build/ffta_match_XXXXXXXX"').strip()
        if not path:
            raise RuntimeError("could not create compilation workspace")
        try:
            yield path
        finally:
            outputs = " ".join(shlex.quote(f"{path}/f.{suffix}")
                               for suffix in ("i", "s", "o", "bin", "known.s", "known.o",
                                              "ld", "elf", "linked.bin"))
            self.sh(f"rm -f -- {outputs} && rmdir -- {shlex.quote(path)}")


def elf_image(object_data):
    """Read ARM ELF32 sections, symbols, and relocation-section metadata."""
    if object_data[:7] != b"\x7fELF\x01\x01\x01":
        raise ValueError("expected a little-endian ELF32 object")
    header = struct.unpack_from("<HHIIIIIHHHHHH", object_data, 16)
    object_type, machine = header[:2]
    section_offset, section_size, section_count, names_index = (
        header[5], header[10], header[11], header[12])
    if object_type not in (1, 2) or machine != 40 or section_size != 40:
        raise ValueError("expected an ARM relocatable or executable ELF32 object")
    sections = [struct.unpack_from("<IIIIIIIIII", object_data,
                                  section_offset + index * section_size)
                for index in range(section_count)]

    def section_data(section):
        if section[1] == 8:
            return b""
        start, size = section[4:6]
        result = object_data[start:start + size]
        if len(result) != size:
            raise ValueError("truncated ELF section")
        return result

    def string_at(strings, offset):
        if not 0 <= offset < len(strings):
            raise ValueError("invalid ELF string offset")
        return strings[offset:strings.index(b"\0", offset)].decode("ascii")

    section_names = section_data(sections[names_index])
    text_sections = [index for index, section in enumerate(sections)
                     if string_at(section_names, section[0]) == ".text"]
    if len(text_sections) != 1:
        raise ValueError("expected exactly one .text section")
    text_index = text_sections[0]
    symbol_tables = {}
    for table_index, section in enumerate(sections):
        if section[1] != 2:
            continue
        if section[9] != 16 or section[5] % 16:
            raise ValueError("invalid ELF symbol table")
        strings = section_data(sections[section[6]])
        symbol_data = section_data(section)
        symbols = []
        for offset in range(0, len(symbol_data), 16):
            symbol_name, value, size, info, visibility, section_index = (
                struct.unpack_from("<IIIBBH", symbol_data, offset))
            symbols.append({"name": string_at(strings, symbol_name), "value": value,
                            "size": size, "type": info & 15, "bind": info >> 4,
                            "section": section_index})
        symbol_tables[table_index] = symbols
    return {"type": object_type, "sections": sections,
            "section_data": [section_data(section) for section in sections],
            "text_index": text_index, "text": section_data(sections[text_index]),
            "symbol_tables": symbol_tables,
            "symbols": [symbol for symbols in symbol_tables.values() for symbol in symbols],
            "relocations": [index for index, section in enumerate(sections)
                            if section[1] in (4, 9) and section[5]]}


def function_record(image, name, address, thumb):
    matches = [symbol for symbol in image["symbols"] if symbol["name"] == name]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one ELF function named {name}")
    symbol = matches[0]
    if symbol["type"] != 2 or symbol["section"] != image["text_index"] or not symbol["size"]:
        raise ValueError(f"{name} is not a sized .text function")
    start = symbol["value"] & ~1
    if bool(symbol["value"] & 1) != thumb:
        raise ValueError(f"{name} ELF instruction mode does not match requested mode")
    if start % 4 != address % 4 or address % (2 if thumb else 4):
        raise ValueError(f"{name} ELF and ROM alignment differ")
    base = image["sections"][image["text_index"]][3] if image["type"] == 2 else 0
    offset = start - base
    if offset < 0 or offset + symbol["size"] > len(image["text"]):
        raise ValueError(f"{name} extends beyond .text")
    return symbol, offset


def function_bytes(object_data, text_data, name, address, thumb):
    """Read the complete named function, including its pool, from ARM ELF32."""
    image = elf_image(object_data)
    if image["type"] != 1:
        raise ValueError("expected an ARM relocatable ELF32 object")
    if image["text"] != text_data:
        raise ValueError("objcopy output does not equal ELF .text")
    if image["relocations"]:
        raise ValueError("unresolved relocations: link the object before comparing ROM bytes")
    symbol, offset = function_record(image, name, address, thumb)
    return text_data[offset:offset + symbol["size"]]


def allocated_text_only(image):
    for index, section in enumerate(image["sections"]):
        if section[2] & 2 and section[5] and index != image["text_index"]:
            raise ValueError("unexpected nonempty allocated section")
    text_section = image["sections"][image["text_index"]]
    if text_section[1] != 1 or text_section[2] & 7 != 6:
        raise ValueError("expected read-only executable .text")


def parse_data_symbols(snapshot):
    if snapshot is None:
        return {}

    def unique_members(pairs):
        result = {}
        for name, value in pairs:
            if name in result:
                raise ValueError("duplicate data symbol name")
            result[name] = value
        return result

    document = json.loads(snapshot, object_pairs_hook=unique_members)
    if not isinstance(document, dict):
        raise ValueError("data symbol mapping must be an object")
    symbols = {}
    for name, value in document.items():
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name) or \
                name.startswith(("func_", "_call_via_")) or \
                name in ("__udivsi3", "__div0") or \
                not isinstance(value, str) or not re.fullmatch(r"0x[0-9A-Fa-f]{8}", value):
            raise ValueError("invalid data symbol name or absolute address")
        if is_udivsi3_address(int(value, 16)):
            raise ValueError("division runtime cannot be bound as data")
        symbols[name] = int(value, 16)
    return symbols


def function_address_target(name, entries, address, size, rom_size):
    match = re.fullmatch(r"func_([0-9A-F]{8})", name)
    if match is None:
        raise ValueError("function address requires a canonical addressed function")
    target = int(match[1], 16)
    if is_udivsi3_address(target):
        raise ValueError("division runtime requires its canonical versioned proof")
    if target in RUNTIME_HELPERS.values():
        raise ValueError("function-address evidence does not support runtime call thunks")
    candidates = [entry for entry in entries
                  if int(entry["rom"], 16) & ~1 == target & ~1]
    if target % 2 or len(candidates) != 1 or candidates[0].get("mode") != "thumb" or \
            int(candidates[0]["rom"], 16) != target or \
            not ROM_BASE <= target <= ROM_BASE + rom_size - 2:
        raise ValueError("function address is unknown, ambiguous, misaligned, or not Thumb ROM code")
    if address <= target < address + size:
        raise ValueError("self or intra-function addresses are unsupported")
    return target


def call_bindings(image, name, address, mapping, rom_size,
                   rom_image=b'', data_mapping=None, function_relocations=None,
                   switch_relocations=None, allow_switch_data=False, udivsi3_bindings=None):
    """Bind external Thumb calls and explicitly mapped absolute data words."""
    if image["type"] != 1 or mapping is None:
        raise ValueError("linked calls require a relocatable object and config/functions.json")
    if type(allow_switch_data) is not bool:
        raise ValueError("switch-data binding opt-in must be Boolean")
    if function_relocations is not None and \
            (not isinstance(function_relocations, dict) or function_relocations):
        raise ValueError("function-address bindings require an empty collection")
    if switch_relocations is not None and \
            (not isinstance(switch_relocations, dict) or switch_relocations):
        raise ValueError("switch bindings require an empty collection")
    if udivsi3_bindings is not None and \
            (not isinstance(udivsi3_bindings, dict) or udivsi3_bindings):
        raise ValueError("division bindings require an empty collection")
    allocated_text_only(image)
    symbol, offset = function_record(image, name, address, True)
    functions = [item for item in image["symbols"] if item["type"] == 2 and item["section"]]
    padding = image["text"][symbol["size"]:]
    thumb_padding = symbol["size"] % 4 == 2 and padding == b"\xc0\x46"
    if functions != [symbol] or offset or len(image["text"]) - symbol["size"] > 3 or \
            any(padding) and not thumb_padding:
        raise ValueError("linked calls require one complete function without helpers or extra text")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("function mapping must be a list")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    calls = {}
    targets = {}
    data_relocations = {}
    data_symbols = parse_data_symbols(data_mapping)
    occupied = set()
    for section_index in image["relocations"]:
        section = image["sections"][section_index]
        if section[1] != 9 or section[7] != image["text_index"] or \
                section[9] != 8 or section[5] % 8:
            raise ValueError("unsupported linked relocation section")
        symbols = image["symbol_tables"].get(section[6])
        if symbols is None:
            raise ValueError("relocation has no symbol table")
        for position in range(0, section[5], 8):
            relocation, info = struct.unpack_from("<II", image["section_data"][section_index], position)
            if info & 255 not in (2, 10) or info >> 8 >= len(symbols):
                raise ValueError("only R_ARM_THM_CALL and mapped R_ARM_ABS32 relocations are supported")
            target_symbol = symbols[info >> 8]
            if info & 255 == 2:
                target_name = target_symbol["name"]
                if target_symbol["section"] and switch_relocations is not None:
                    section_symbols = [item for item in image["symbols"]
                                       if item["type"] == 3 and
                                       item["section"] == image["text_index"]]
                    if target_symbol["type"] != 3 or target_symbol["bind"] != 0 or \
                            target_symbol["section"] != image["text_index"] or \
                            target_symbol["value"] or target_name or \
                            section_symbols != [target_symbol]:
                        raise ValueError("switch relocation requires one zero-valued local .text section symbol")
                    if relocation < 0 or (address + relocation) % 4 or \
                            relocation + 4 > symbol["size"]:
                        raise ValueError("switch relocation must cover an aligned complete word")
                    addend = struct.unpack_from("<I", image["text"], relocation)[0]
                    if addend % 2 or addend + 2 > symbol["size"]:
                        raise ValueError("switch relocation target is outside its function or odd")
                    positions = set(range(relocation, relocation + 4))
                    if positions & occupied:
                        raise ValueError("overlapping switch or call relocations")
                    occupied.update(positions)
                    switch_relocations[relocation] = addend
                    continue
                if target_name.startswith("func_"):
                    if function_relocations is None:
                        raise ValueError("function addresses require their versioned proof profile")
                    if target_symbol["section"] or target_symbol["bind"] != 1 or \
                            target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                            sum(item["name"] == target_name for item in image["symbols"]) != 1:
                        raise ValueError("function address must name an undefined global function")
                    target = function_address_target(target_name, entries, address,
                                                     symbol["size"], rom_size)
                    if (address + relocation) % 4 or relocation + 4 > symbol["size"]:
                        raise ValueError("function relocation must cover an aligned complete literal word")
                    if struct.unpack_from("<I", image["text"], relocation)[0]:
                        raise ValueError("function address addends must be zero")
                    positions = set(range(relocation, relocation + 4))
                    if positions & occupied:
                        raise ValueError("overlapping function, data or call relocations")
                    occupied.update(positions)
                    function_relocations[relocation] = (target_name, target | 1)
                    targets[target_name] = target
                    continue
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 1) or target_name not in data_symbols:
                    raise ValueError("data target must be an undefined mapped object")
                if (address + relocation) % 4 or relocation + 4 > symbol["size"]:
                    raise ValueError("data relocation must cover an aligned complete literal word")
                target = data_symbols[target_name]
                addend = struct.unpack_from("<i", image["text"], relocation)[0]
                value = target + addend
                if not 0 <= value <= 0xFFFFFFFF or address <= value < address + symbol["size"]:
                    raise ValueError("data relocation overflows or references its own function")
                if is_udivsi3_address(value):
                    raise ValueError("division runtime cannot be bound through a data addend")
                positions = set(range(relocation, relocation + 4))
                if positions & occupied:
                    raise ValueError("overlapping data or call relocations")
                occupied.update(positions)
                data_relocations[relocation] = (target_name, value)
                targets[target_name] = target
                continue
            match = re.fullmatch(r"func_([0-9A-F]{8})", target_symbol["name"])
            helper = RUNTIME_HELPERS.get(target_symbol["name"])
            division = target_symbol["name"] == "__udivsi3"
            if division:
                if udivsi3_bindings is None:
                    raise ValueError("division runtime requires its versioned proof profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == "__udivsi3" for item in image["symbols"]) != 1:
                    raise ValueError("division call requires one undefined global function symbol")
                verify_udivsi3_identity(rom_image, mapping)
                target = UDIVSI3_ADDRESS
                candidates = []
            elif helper is not None:
                # agbcc's _call_via_rN: a real call, through a thunk we verify
                if target_symbol["section"] or target_symbol["bind"] != 1:
                    raise ValueError("call helper must be an undefined symbol")
                target = helper
                if not thunk_is_call_via(rom_image, target,
                                         int(target_symbol["name"][len("_call_via_r"):])):
                    raise ValueError("call helper does not match its thunk in the ROM")
                candidates = []
                if not ROM_BASE <= target < ROM_BASE + len(rom_image):
                    raise ValueError("call target is outside the ROM")
            else:
                if not match or target_symbol["section"] or \
                        target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2):
                    raise ValueError("call target must be an undefined addressed function")
                target = int(match[1], 16)
                if is_udivsi3_address(target):
                    raise ValueError("division runtime requires its canonical compiler alias")
                candidates = []
            for entry in entries:
                try:
                    entry_address = int(entry["rom"], 16)
                except (KeyError, TypeError, ValueError):
                    continue
                if entry_address & ~1 == target & ~1:
                    candidates.append(entry)
            if helper is None and (target % 2 or len(candidates) != 1 or \
                    candidates[0].get("mode") != "thumb" or \
                    int(candidates[0]["rom"], 16) != target or \
                    not ROM_BASE <= target < ROM_BASE + rom_size):
                # No arbitrary region cap: config/functions.json already reaches
                # well past 0x08150000 (0x080D2E24 is indexed), so the old
                # min(rom_size, 0x150000) rejected legitimate call targets.
                # Uniqueness, exact address, Thumb mode and ROM bounds are the
                # real checks.
                raise ValueError("call target is unknown, ambiguous, misaligned, or not Thumb ROM code")
            if address <= target < address + symbol["size"]:
                raise ValueError("recursive or intra-function calls are unsupported")
            instruction = next(decoder.disasm(image["text"][relocation:relocation + 4],
                                             address + relocation, count=1), None)
            if relocation % 2 or relocation + 4 > symbol["size"] or instruction is None or \
                    instruction.id != ARM_INS_BL or instruction.size != 4:
                raise ValueError("call relocation does not cover a Thumb BL instruction")
            if division:
                if len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM or \
                        instruction.operands[0].imm != address + relocation:
                    raise ValueError("division call relocation has a noncanonical addend")
                udivsi3_bindings[address + relocation] = target_symbol["name"]
            positions = set(range(relocation, relocation + 4))
            if positions & occupied:
                raise ValueError("overlapping call relocations")
            occupied.update(positions)
            calls[address + relocation] = target
            targets[target_symbol["name"]] = target
    if udivsi3_bindings:
        if data_relocations or function_relocations or switch_relocations or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("division evidence excludes literal, switch and thunk combinations")
        for target_name in targets:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or \
                    definitions[0]["section"] or definitions[0]["bind"] != 1 or \
                    definitions[0]["type"] not in (0, 2):
                raise ValueError("division profile calls require unique undefined global functions")
    if function_relocations and any(target in RUNTIME_HELPERS for target in targets):
        raise ValueError("function-address evidence does not support runtime call thunks")
    if switch_relocations:
        if (data_relocations and not allow_switch_data) or function_relocations or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("switch evidence excludes object, callback and runtime-thunk bindings")
        data_names = {binding[0] for binding in data_relocations.values()}
        for target_name in targets:
            if target_name not in data_names:
                function_address_target(target_name, entries, address, symbol["size"], rom_size)
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"]:
                raise ValueError("switch calls require unique zero-valued undefined symbols")
        relocated = bytearray(image["text"][:symbol["size"]])
        for position, addend in switch_relocations.items():
            struct.pack_into("<I", relocated, position, address + addend)
        for position, (_, value) in data_relocations.items():
            struct.pack_into("<I", relocated, position, value)
        switch_layout(bytes(relocated), address, switch_relocations,
                      data_relocations if data_relocations else None)
    if not (calls or data_relocations or function_relocations or switch_relocations) or \
            any(item["name"] and not item["section"] and item["name"] not in targets
                for item in image["symbols"]):
        raise ValueError("unresolved symbols outside the permitted bindings")
    return calls, targets, data_relocations


def linked_function_bytes(original, linked, name, address, calls, targets, data_relocations=None,
                          function_relocations=None, switch_relocations=None,
                          allow_switch_data=False, udivsi3_bindings=None):
    """Validate exact placement and the linker's complete modification surface."""
    if linked["type"] != 2 or linked["relocations"]:
        raise ValueError("expected an executable ELF without remaining relocations")
    allocated_text_only(linked)
    before, _ = function_record(original, name, address, True)
    after, offset = function_record(linked, name, address, True)
    if after["value"] != address | 1 or offset or after["size"] != before["size"] or \
            linked["sections"][linked["text_index"]][3] != address:
        raise ValueError("linked function address, mode, or size changed")
    if len(linked["text"]) != len(original["text"]):
        raise ValueError("linker added text or veneers")
    data_relocations = data_relocations or {}
    function_relocations = function_relocations or {}
    switch_relocations = switch_relocations or {}
    if "__udivsi3" in targets:
        if not isinstance(udivsi3_bindings, dict) or not udivsi3_bindings or \
                targets["__udivsi3"] != UDIVSI3_ADDRESS or \
                any(alias != "__udivsi3" or calls.get(site) != UDIVSI3_ADDRESS
                    for site, alias in udivsi3_bindings.items()) or \
                set(udivsi3_bindings) != {site for site, target in calls.items()
                                          if target == UDIVSI3_ADDRESS} or \
                data_relocations or function_relocations or switch_relocations:
            raise ValueError("linked division call bindings are incomplete or mixed")
    elif udivsi3_bindings:
        raise ValueError("division bindings have no linked runtime")
    if any(is_udivsi3_address(target) and
           (target_name != "__udivsi3" or target != UDIVSI3_ADDRESS or not udivsi3_bindings)
           for target_name, target in targets.items()) or \
            udivsi3_bindings and any(target in RUNTIME_HELPERS.values() for target in targets.values()):
        raise ValueError("linked division aliases or thunk combinations are unsupported")
    if type(allow_switch_data) is not bool:
        raise ValueError("switch-data binding opt-in must be Boolean")
    if switch_relocations and ((data_relocations and not allow_switch_data) or function_relocations):
        raise ValueError("switch evidence cannot combine literal binding profiles")
    if switch_relocations:
        section_symbols = [item for item in linked["symbols"]
                           if item["type"] == 3 and item["section"] == linked["text_index"]]
        if len(section_symbols) != 1 or section_symbols[0]["value"] != address or \
                section_symbols[0]["bind"] != 0 or section_symbols[0]["name"]:
            raise ValueError("linked switch section lost its local .text identity")
    function_names = {binding[0] for binding in function_relocations.values()}
    data_names = {binding[0] for binding in data_relocations.values()}
    expected_functions = {name} | (set(targets) - data_names)
    actual_functions = [item["name"] for item in linked["symbols"] if item["type"] == 2]
    if len(actual_functions) != len(expected_functions) or set(actual_functions) != expected_functions:
        raise ValueError("unexpected linked function or veneer symbol")
    actual_objects = [item["name"] for item in linked["symbols"] if item["type"] == 1]
    if len(actual_objects) != len(data_names) or set(actual_objects) != data_names:
        raise ValueError("unexpected linked object symbol")
    for target_name, target in targets.items():
        definitions = [item for item in linked["symbols"] if item["name"] == target_name]
        expected_type = 1 if target_name in data_names else 2
        expected_value = target if target_name in data_names else target | 1
        if len(definitions) != 1 or definitions[0]["type"] != expected_type or \
                definitions[0]["section"] != 0xFFF1 or definitions[0]["value"] != expected_value or \
                (target_name in function_names or switch_relocations or udivsi3_bindings) and \
                definitions[0]["bind"] != 1:
            raise ValueError("linked target lost its absolute symbol type or address")
    if any(item["name"] and not item["section"] for item in linked["symbols"]):
        raise ValueError("linked ELF retains undefined symbols")
    if any(re.fullmatch(r"\$a(?:\..*)?", item["name"]) for item in linked["symbols"]):
        raise ValueError("linked text contains an ARM mode mapping")
    patched = {position for call in calls for position in range(call - address, call - address + 4)}
    for relocation, (_, value) in data_relocations.items():
        if struct.unpack_from("<I", linked["text"], relocation)[0] != value:
            raise ValueError("linked data word does not equal its mapped address and addend")
        patched.update(range(relocation, relocation + 4))
    for relocation, (target_name, value) in function_relocations.items():
        if value != targets[target_name] | 1 or \
                struct.unpack_from("<I", linked["text"], relocation)[0] != value:
            raise ValueError("linked function word does not equal its mapped Thumb address")
        patched.update(range(relocation, relocation + 4))
    for relocation, addend in switch_relocations.items():
        if struct.unpack_from("<I", original["text"], relocation)[0] != addend or \
                struct.unpack_from("<I", linked["text"], relocation)[0] != address + addend:
            raise ValueError("linked switch word does not equal its local section address")
        patched.update(range(relocation, relocation + 4))
    if switch_relocations:
        switch_layout(linked["text"][:after["size"]], address, switch_relocations,
                      data_relocations if data_relocations else None)
    if any(before_byte != after_byte and position not in patched
           for position, (before_byte, after_byte)
           in enumerate(zip(original["text"], linked["text"]))):
        raise ValueError("linker changed bytes outside permitted relocations")
    return linked["text"][:after["size"]]


def link_calls(runner, workspace, args, original, address, mapping, rom_size,
               rom_image=b'', data_mapping=None, function_relocations=None, switch_relocations=None,
               allow_switch_data=False, udivsi3_bindings=None):
    name = f"func_{address:08X}"
    calls, targets, data_relocations = call_bindings(original, name, address, mapping,
                                                    rom_size, rom_image, data_mapping,
                                                    function_relocations, switch_relocations,
                                                    allow_switch_data, udivsi3_bindings)
    data_names = {binding[0] for binding in data_relocations.values()}
    definitions = [".syntax unified", ".thumb"]
    for target_name, target in sorted(targets.items()):
        if target_name in data_names:
            definitions.extend((f".global {target_name}", f".type {target_name}, %object",
                                f".set {target_name}, 0x{target:08X}"))
        else:
            definitions.extend((f".global {target_name}", f".type {target_name}, %function",
                                f".thumb_set {target_name}, 0x{target | 1:08X}"))
    runner.write_text(f"{workspace}/f.known.s", "\n".join(definitions) + "\n")
    script = (f"SECTIONS {{ .text 0x{address:08X} : {{ *(.text) *(.glue_7) *(.glue_7t) }} "
              ".data 0 : { *(.data) } .bss 0 : { *(.bss) } "
              ".ARM.attributes 0 : { *(.ARM.attributes) } "
              ".unexpected 0 : { *(.vfp11_veneer) *(.v4_bx) *(.iplt) *(.igot.plt) } "
              ".rel.iplt 0 : { *(.rel.iplt) } "
              "ASSERT(SIZEOF(.unexpected) == 0, \"unexpected linker stubs\") "
              "ASSERT(SIZEOF(.rel.iplt) == 0, \"unexpected dynamic relocations\") "
              "/DISCARD/ : { *(.comment) *(.note.GNU-stack) } }")
    runner.write_text(f"{workspace}/f.ld", script)
    quoted = shlex.quote(workspace)
    runner.sh(f"export TMPDIR={quoted}; {args.assembler} -mthumb-interwork "
              f"{quoted}/f.known.s -o {quoted}/f.known.o")
    runner.sh(f"export TMPDIR={quoted}; {args.linker} --fatal-warnings --no-undefined "
              f"--no-relax --orphan-handling=error -T {quoted}/f.ld -e {name} "
              f"{quoted}/f.o {quoted}/f.known.o -o {quoted}/f.elf")
    runner.sh(f"{args.objcopy} -O binary --only-section=.text {quoted}/f.elf {quoted}/f.linked.bin")
    linked = elf_image(runner.read_binary(f"{workspace}/f.elf"))
    if runner.read_binary(f"{workspace}/f.linked.bin") != linked["text"]:
        raise ValueError("objcopy output does not equal linked ELF .text")
    return (linked_function_bytes(original, linked, name, address, calls, targets,
                                  data_relocations, function_relocations, switch_relocations,
                                  allow_switch_data, udivsi3_bindings),
            calls, data_relocations)


def verify_data_literals(instructions, address, data_relocations):
    literals = {((instruction.address + 4) & ~3) + operand.mem.disp
                for instruction in instructions for operand in instruction.operands
                if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and
                operand.mem.base == ARM_REG_PC and not operand.mem.index}
    if any(address + relocation not in literals for relocation in data_relocations):
        raise ValueError("data relocation is not a reachable trailing literal-pool load")


def verify_udivsi3(data, address, rom, mapping, manifest):
    if not isinstance(manifest, dict) or set(manifest) != {"calls", "runtime", "divisors"} or \
            manifest["runtime"] != UDIVSI3_RUNTIME or \
            not isinstance(manifest["calls"], list) or not isinstance(manifest["divisors"], list):
        raise ValueError("invalid division manifest")
    verify_udivsi3_identity(rom, mapping)
    entries = json.loads(mapping)
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or is_udivsi3_address(address) or len(callers) != 1 or \
            int(callers[0]["rom"], 16) != address or callers[0].get("mode") != "thumb" or \
            int(callers[0]["end"], 16) != address + len(data) or \
            not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom) or \
            any(entry is not callers[0] and int(entry["rom"], 16) < address + len(data) and
                int(entry["end"], 16) > address for entry in entries):
        raise ValueError("division caller requires an exact nonoverlapping mapped Thumb span")
    if data != rom[address - ROM_BASE:address - ROM_BASE + len(data)]:
        raise ValueError("division caller differs from the ROM")
    calls = {}
    runtime_sites = set()
    previous = -4
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid division call binding")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or offset % 2 or \
                offset < previous + 4 or offset < 0 or offset + 4 > len(data):
            raise ValueError("division calls must be ordered nonoverlapping complete instructions")
        previous = offset
        if name == "__udivsi3":
            calls[address + offset] = UDIVSI3_ADDRESS
            runtime_sites.add(offset)
        else:
            calls[address + offset] = function_address_target(
                name, entries, address, len(data), len(rom))
    expected = {}
    previous = -1
    for record in manifest["divisors"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid division constant binding")
        offset, divisor = record
        if type(offset) is not int or offset <= previous or offset not in runtime_sites or \
                type(divisor) is not int or not 1 <= divisor <= 0xFFFFFFFF:
            raise ValueError("division constants require ordered runtime sites and nonzero u32 values")
        previous = offset
        expected[address + offset] = divisor
    if not runtime_sites or {site - address for site in expected} != runtime_sites:
        raise ValueError("division constants must cover every runtime call exactly once")
    observed = {}
    instructions = verify_leaf_instructions(
        data, address, True, calls, udivsi3_context=(rom, mapping, observed))
    if observed != expected:
        raise ValueError("division constants disagree with verified incoming CFG state")
    return instructions


def verify_function_addresses(data, address, rom, mapping, data_mapping, manifest):
    if mapping is None or not isinstance(manifest, dict) or \
            set(manifest) != {"calls", "data", "functions"} or \
            any(not isinstance(records, list) for records in manifest.values()) or \
            not manifest["functions"]:
        raise ValueError("invalid function-address manifest")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("function mapping must be a list")
    caller = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or len(caller) != 1 or caller[0].get("mode") != "thumb" or \
            int(caller[0]["rom"], 16) != address or \
            int(caller[0]["end"], 16) != address + len(data) or \
            not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom):
        raise ValueError("function-address caller requires an exact mapped Thumb span")
    if rom[address - ROM_BASE:address - ROM_BASE + len(data)] != data:
        raise ValueError("function-address caller differs from the ROM")
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls = {}
    literals = {}
    occupied = set()
    for kind, records in manifest.items():
        previous = -1
        for record in records:
            if not isinstance(record, list) or len(record) != (3 if kind == "data" else 2):
                raise ValueError("invalid function-address binding")
            offset, name = record[:2]
            if type(offset) is not int or not isinstance(name, str) or offset <= previous or \
                    offset < 0 or offset + 4 > len(data):
                raise ValueError("function-address bindings must be ordered complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if positions & occupied:
                raise ValueError("overlapping function-address manifest bindings")
            occupied.update(positions)
            if kind == "calls":
                if offset % 2:
                    raise ValueError("function-address call is misaligned")
                calls[address + offset] = function_address_target(
                    name, entries, address, len(data), len(rom))
                continue
            if (address + offset) % 4:
                raise ValueError("function-address literal is misaligned")
            if kind == "functions":
                value = function_address_target(name, entries, address, len(data), len(rom)) | 1
            else:
                addend = record[2]
                if name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid function-address object binding")
                value = objects[name] + addend
                if not 0 <= value <= 0xFFFFFFFF or address <= value < address + len(data):
                    raise ValueError("function-address object binding overflows or references itself")
                if is_udivsi3_address(value):
                    raise ValueError("division runtime cannot be bound through an object addend")
            if struct.unpack_from("<I", data, offset)[0] != value:
                raise ValueError("function-address literal does not equal its binding")
            literals[offset] = (name, value)
    instructions = verify_leaf_instructions(data, address, True, calls)
    if uses_stack_frame(instructions):
        raise ValueError("function-address evidence supports only frameless callers")
    verify_data_literals(instructions, address, literals)
    return instructions, CALL_SUMMARY if calls else "closed leaf CFG"


def switch_layout(data, address, relocations, data_relocations=None):
    """Derive the single supported guarded dispatch from its complete local words."""
    if not isinstance(relocations, dict) or not 2 <= len(relocations) <= 257:
        raise ValueError("switch evidence requires one pointer and one bounded word table")
    for offset, addend in relocations.items():
        if type(offset) is not int or type(addend) is not int or \
                offset < 0 or (address + offset) % 4 or offset + 4 > len(data) or \
                addend < 0 or addend % 2 or addend + 2 > len(data) or \
                struct.unpack_from("<I", data, offset)[0] != address + addend:
            raise ValueError("invalid local switch word or section-relative target")
    literal = min(relocations)
    table = literal + 4
    count = len(relocations) - 1
    table_end = table + 4 * count
    if sorted(relocations) != list(range(literal, table_end, 4)) or \
            relocations[literal] != table or \
            any(relocations[offset] < table_end for offset in range(table, table_end, 4)):
        raise ValueError("switch words must describe an adjacent table and forward local cases")
    if data_relocations is not None:
        if not isinstance(data_relocations, dict) or len(data_relocations) != 1:
            raise ValueError("switch-data requires exactly one interposed object word")
        offset, binding = next(iter(data_relocations.items()))
        if type(offset) is not int or offset != literal - 4 or offset < 0 or \
                (address + offset) % 4 or not isinstance(binding, (tuple, list)) or \
                len(binding) != 2 or not isinstance(binding[0], str) or \
                type(binding[1]) is not int or not 0 <= binding[1] <= 0xFFFFFFFF or \
                address <= binding[1] < address + len(data) or \
                struct.unpack_from("<I", data, offset)[0] != binding[1]:
            raise ValueError("invalid interposed switch-data object word")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True

    def instruction(offset):
        if offset < 0 or offset % 2 or offset + 2 > len(data):
            return None
        decoded = next(decoder.disasm(data[offset:offset + 4], address + offset, count=1), None)
        return decoded if decoded is not None and decoded.size == 2 else None

    def branch_target(decoded, mnemonic):
        if decoded is None or decoded.mnemonic != mnemonic or len(decoded.operands) != 1 or \
                decoded.operands[0].type != ARM_OP_IMM:
            return None
        return decoded.operands[0].imm - address

    candidates = []
    for dispatch in ((literal - 14,) if data_relocations is not None
                     else (literal - 10, literal - 12)):
        if data_relocations is None:
            if (address + dispatch + 13) & ~3 != address + literal or \
                    any(data[dispatch + 10:literal]):
                continue
        elif (address + dispatch + 10) % 4:
            continue
        sequence = [instruction(dispatch + distance) for distance in range(0, 10, 2)]
        if any(item is None or item.cc not in (ARM_CC_AL, ARM_CC_INVALID) for item in sequence) or \
                tuple(item.mnemonic for item in sequence) != ("lsls", "ldr", "adds", "ldr", "mov"):
            continue
        shift, load_base, addition, load_target, transfer = (item.operands for item in sequence)
        if len(shift) != 3 or shift[0].type != ARM_OP_REG or shift[1].type != ARM_OP_REG or \
                shift[2].type != ARM_OP_IMM or shift[2].imm != 2:
            continue
        accumulator = shift[0].reg
        selector = shift[1].reg
        if len(load_base) != 2 or load_base[0].type != ARM_OP_REG or \
                load_base[0].reg == accumulator or load_base[1].type != ARM_OP_MEM or \
                load_base[1].mem.base != ARM_REG_PC or load_base[1].mem.index or \
                ((address + dispatch + 6) & ~3) + load_base[1].mem.disp != address + literal:
            continue
        if len(addition) != 3 or any(operand.type != ARM_OP_REG for operand in addition) or \
                tuple(operand.reg for operand in addition) != \
                (accumulator, accumulator, load_base[0].reg):
            continue
        if len(load_target) != 2 or load_target[0].type != ARM_OP_REG or \
                load_target[0].reg != accumulator or load_target[1].type != ARM_OP_MEM or \
                load_target[1].mem.base != accumulator or load_target[1].mem.index or \
                load_target[1].mem.disp:
            continue
        if len(transfer) != 2 or any(operand.type != ARM_OP_REG for operand in transfer) or \
                tuple(operand.reg for operand in transfer) != (ARM_REG_PC, accumulator):
            continue
        for guard_size in (4, 6):
            comparison = dispatch - guard_size
            guard = comparison + 2
            compare_instruction = instruction(comparison)
            if compare_instruction is None or compare_instruction.mnemonic != "cmp" or \
                    len(compare_instruction.operands) != 2 or \
                    compare_instruction.operands[0].type != ARM_OP_REG or \
                    compare_instruction.operands[0].reg != selector or \
                    compare_instruction.operands[1].type != ARM_OP_IMM or \
                    compare_instruction.operands[1].imm != count - 1:
                continue
            if guard_size == 4:
                default = branch_target(instruction(guard), "bhi")
            else:
                if branch_target(instruction(guard), "bls") != dispatch:
                    continue
                default = branch_target(instruction(guard + 2), "b")
            if default is None or default % 2 or not table_end <= default <= len(data) - 2:
                continue
            candidates.append({"comparison": comparison, "guard": guard, "dispatch": dispatch,
                               "default": default, "literal": literal, "table": table,
                               "bound": count - 1,
                               "relocations": [[offset, addend]
                                               for offset, addend in sorted(relocations.items())]})
    if len(candidates) != 1:
        raise ValueError("switch requires one exact adjacent unsigned guard and five-op dispatch")
    return candidates[0]


def verify_switches(data, address, rom, mapping, manifest, *, data_mapping=None):
    data_profile = data_mapping is not None
    fields = {"calls", "data", "switch"} if data_profile else {"calls", "switch"}
    if mapping is None or not isinstance(manifest, dict) or set(manifest) != fields or \
            not isinstance(manifest["calls"], list) or not isinstance(manifest["switch"], dict):
        raise ValueError("invalid switch manifest")
    data_relocations = None
    if data_profile:
        records = manifest["data"]
        if not isinstance(records, list) or len(records) != 1 or \
                not isinstance(records[0], list) or len(records[0]) != 3:
            raise ValueError("switch-data requires one canonical object binding")
        offset, name, addend = records[0]
        objects = parse_data_symbols(data_mapping)
        if type(offset) is not int or offset < 0 or offset + 4 > len(data) or \
                (address + offset) % 4 or not isinstance(name, str) or name not in objects or \
                type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF:
            raise ValueError("invalid switch-data object binding")
        value = objects[name] + addend
        data_relocations = {offset: (name, value)}
    descriptor = manifest["switch"]
    fields = {"comparison", "guard", "dispatch", "default", "literal", "table", "bound", "relocations"}
    if set(descriptor) != fields or \
            any(type(descriptor[field]) is not int for field in fields - {"relocations"}) or \
            not isinstance(descriptor["relocations"], list):
        raise ValueError("invalid switch descriptor")
    relocations = {}
    previous = -1
    for record in descriptor["relocations"]:
        if not isinstance(record, list) or len(record) != 2 or \
                any(type(value) is not int for value in record) or record[0] <= previous:
            raise ValueError("switch relocations must be unique ordered integer pairs")
        previous = record[0]
        relocations[record[0]] = record[1]
    if switch_layout(data, address, relocations, data_relocations) != descriptor:
        raise ValueError("switch descriptor does not match the guarded bytes")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("function mapping must be a list")
    caller = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if address % 2 or len(caller) != 1 or caller[0].get("mode") != "thumb" or \
            int(caller[0]["rom"], 16) != address or \
            int(caller[0]["end"], 16) != address + len(data) or \
            not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom):
        raise ValueError("switch caller requires an exact mapped Thumb span")
    if rom[address - ROM_BASE:address - ROM_BASE + len(data)] != data:
        raise ValueError("switch caller differs from the ROM")
    calls = {}
    previous = -1
    occupied = {position for offset in (*relocations, *(data_relocations or {}))
                for position in range(offset, offset + 4)}
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid switch call binding")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or \
                offset <= previous or offset % 2 or offset < 0 or offset + 4 > len(data):
            raise ValueError("switch call bindings must be unique ordered complete instructions")
        previous = offset
        positions = set(range(offset, offset + 4))
        if positions & occupied:
            raise ValueError("overlapping switch manifest bindings")
        occupied.update(positions)
        calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
    instructions = verify_leaf_instructions(data, address, True, calls,
                                            switch_relocations=relocations,
                                            switch_data_relocations=data_relocations)
    return instructions, CALL_SUMMARY if calls else "closed leaf CFG"


def thumb_stack_adjustment(instruction):
    if instruction.size != 2 or instruction.bytes[1] != 0xB0:
        return None
    words = instruction.bytes[0] & 0x7F
    return -words if instruction.bytes[0] & 0x80 else words


def uses_stack_frame(instructions):
    return any(thumb_stack_adjustment(instruction) is not None or
               any((operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_SP) or
                   (operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP)
                   for operand in instruction.operands)
               for instruction in instructions)


def register_alias_assignment(instruction, aliases):
    operands = instruction.operands
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            not operands or operands[0].type != ARM_OP_REG:
        return None
    source = None
    displacement = 0
    if instruction.mnemonic in ("mov", "movs") and len(operands) == 2 and \
            operands[1].type == ARM_OP_REG:
        source = operands[1].reg
    elif instruction.mnemonic in ("add", "adds", "sub", "subs") and \
            len(operands) in (2, 3) and operands[-1].type == ARM_OP_IMM:
        if len(operands) == 2:
            source = operands[0].reg
        elif operands[1].type == ARM_OP_REG:
            source = operands[1].reg
        displacement = operands[-1].imm
        if instruction.mnemonic.startswith("sub"):
            displacement = -displacement
    if source not in aliases:
        return None
    return operands[0].reg, aliases[source] + displacement, source


def stack_alias_assignment(instruction, aliases, depth, constants):
    assignment = register_alias_assignment(instruction, {**aliases, ARM_REG_SP: -4 * depth})
    operands = instruction.operands
    if assignment is None and instruction.size == 2 and instruction.mnemonic == "add" and \
            instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and len(operands) == 3 and \
            all(operand.type == ARM_OP_REG and not operand.shift.type and
                not operand.shift.value and not operand.subtracted for operand in operands):
        destination = operands[0].reg
        if ARM_REG_R0 <= destination <= ARM_REG_R0 + 7 and \
                instruction.bytes == bytes((0x68 + destination - ARM_REG_R0, 0x44)) and \
                operands[1].reg == ARM_REG_SP and operands[2].reg == destination and \
                destination in constants:
            assignment = (destination, constants[destination] - 4 * depth, ARM_REG_SP)
    if assignment is None:
        return None
    offset = assignment[1]
    if not -4 * depth <= offset <= 0:
        raise ValueError("stack alias arithmetic leaves the tracked frame")
    return assignment


CALLER_CLOBBERED = (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2,
                    ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)


def merge_possible_aliases(previous, incoming):
    merged = dict(previous)
    for register, offset in incoming:
        if register in merged and merged[register] != offset:
            raise ValueError("inconsistent possible pointer offsets at control-flow join")
        merged[register] = offset
    return tuple(sorted(merged.items()))


class BufferCallProof:
    """Check bounded buffer arguments and their aliases against the current ROM."""

    def __init__(self, rom, mapping, stack_arguments=False):
        self.rom = rom
        self.entries = json.loads(mapping) if mapping is not None else []
        if not isinstance(self.entries, list):
            raise ValueError("buffer calls require a function mapping")
        self.dependencies = {}
        self.active = set()
        self.stack_arguments = stack_arguments

    def target(self, address):
        if is_udivsi3_address(address):
            raise ValueError("division runtime is outside buffer-call proof profiles")
        candidates = [entry for entry in self.entries
                      if isinstance(entry, dict) and isinstance(entry.get("rom"), str)
                      and int(entry["rom"], 16) & ~1 == address & ~1]
        if address % 2 or len(candidates) != 1 or candidates[0].get("mode") != "thumb" or \
                int(candidates[0]["rom"], 16) != address or \
                not ROM_BASE <= address < ROM_BASE + len(self.rom):
            raise ValueError("buffer call target is not unique aligned Thumb ROM code")
        return candidates[0]

    def span(self, address):
        entry = self.target(address)
        end = int(entry["end"], 16)
        if end % 2 or not address < end <= ROM_BASE + len(self.rom):
            raise ValueError("buffer callee has no complete mapped span")
        for other in self.entries:
            if other is entry:
                continue
            if int(other["rom"], 16) < end and int(other["end"], 16) > address:
                raise ValueError("buffer callee mapping overlaps another span")
        return self.rom[address - ROM_BASE:end - ROM_BASE]

    @staticmethod
    def access(offset, width, stack):
        start = offset + 4 * len(stack)
        if offset % width or start < 0 or offset + width > 0 or \
                any(not stack[slot][2]
                    for slot in range(start // 4, (start + width - 1) // 4 + 1)):
            raise ValueError("buffer access is unaligned or outside allocated local words")

    def check_call(self, address, aliases, stack, slots=None):
        arguments = {register: offset for register, offset in aliases.items()
                     if register in CALLER_CLOBBERED}
        slots = slots or {}
        if slots and not self.stack_arguments:
            raise ValueError("stack-passed buffer pointers require versioned evidence")
        for offset in slots:
            self.access(offset, 4, stack)
        incoming = {offset + 4 * len(stack): target for offset, target in slots.items()}
        return self.check_arguments(address, arguments, stack, incoming, frozenset(slots))

    def check_arguments(self, address, arguments, stack, incoming, protected):
        if not arguments and not incoming:
            return {}
        if ARM_REG_LR in arguments:
            raise ValueError("buffer pointer cannot be passed through the link register")
        for offset in (*arguments.values(), *incoming.values()):
            self.access(offset, 1, stack)
        if address in self.active or len(self.active) >= 16:
            raise ValueError("recursive or excessively nested buffer calls are unsupported")
        self.active.add(address)
        try:
            data = self.span(address)
            instructions = verify_leaf_instructions(data, address, True,
                                                     buffer_proof=self if self.stack_arguments else None,
                                                     call_resolver=self.target)
            self.dependencies[address] = data
            by_address = {instruction.address: instruction for instruction in instructions}
            states = {address: (tuple(sorted(arguments.items())), 0)}
            pending = [address]
            returned = ()
            while pending:
                current = pending.pop()
                instruction = by_address[current]
                aliases = dict(states[current][0])
                depth = states[current][1]
                operands = instruction.operands
                registers = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
                read, written = instruction.regs_access()
                returning = (instruction.mnemonic == "bx" or
                             instruction.mnemonic == "pop" and ARM_REG_PC in registers or
                             instruction.mnemonic == "mov" and registers and registers[0] == ARM_REG_PC)
                if instruction.mnemonic == "push":
                    if set(registers) & aliases.keys():
                        raise ValueError("buffer pointers cannot be pushed or spilled")
                    depth += len(registers)
                elif instruction.mnemonic == "pop":
                    for register in registers:
                        aliases.pop(register, None)
                    depth -= len(registers)
                elif thumb_stack_adjustment(instruction) is not None:
                    depth -= thumb_stack_adjustment(instruction)
                elif CS_GRP_CALL in instruction.groups:
                    passed = {register: offset for register, offset in aliases.items()
                              if register in CALLER_CLOBBERED}
                    nested = {offset + depth * 4: target for offset, target in incoming.items()}
                    result = self.check_arguments(operands[0].imm, passed, stack, nested, protected)
                    for register in CALLER_CLOBBERED:
                        aliases.pop(register, None)
                    aliases.update(result)
                else:
                    assignment = register_alias_assignment(instruction, aliases)
                    allowed = {assignment[2]} if assignment is not None else set()
                    loaded = None
                    for operand in operands:
                        if operand.type != ARM_OP_MEM:
                            continue
                        if operand.mem.base == ARM_REG_SP and instruction.mnemonic == "ldr":
                            position = operand.mem.disp - 4 * depth
                            if position in incoming:
                                loaded = (registers[0], incoming[position])
                        if operand.mem.base not in aliases:
                            continue
                        widths = {"ldr": 4, "str": 4, "ldrh": 2, "strh": 2,
                                  "ldrb": 1, "strb": 1, "ldrsh": 2, "ldrsb": 1}
                        width = widths.get(instruction.mnemonic)
                        if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                                width is None or len(operands) != 2 or len(registers) != 1 or \
                                operands[0].type != ARM_OP_REG or operand.mem.index:
                            raise ValueError("unsupported buffer memory access")
                        offset = aliases[operand.mem.base] + operand.mem.disp
                        self.access(offset, width, stack)
                        if any(offset < slot + 4 and offset + width > slot for slot in protected):
                            raise ValueError("buffer access overlaps a pointer-bearing argument slot")
                        if instruction.mnemonic.startswith("str") and registers[0] in aliases:
                            raise ValueError("buffer pointers cannot be stored or spilled")
                        allowed.add(operand.mem.base)
                    if (set(read) & aliases.keys()) - allowed:
                        raise ValueError("unsupported buffer pointer use or escape")
                    for register in written:
                        aliases.pop(register, None)
                    if assignment is not None:
                        if assignment[0] in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR):
                            raise ValueError("buffer pointer cannot overwrite a control register")
                        aliases[assignment[0]] = assignment[1]
                    if loaded is not None:
                        aliases[loaded[0]] = loaded[1]
                if returning:
                    if aliases and not self.stack_arguments:
                        raise ValueError("buffer pointer escapes through a return register")
                    if any(register not in CALLER_CLOBBERED or register == ARM_REG_LR
                           for register in aliases):
                        raise ValueError("buffer pointer escapes through an unrestored register")
                    returned = merge_possible_aliases(returned, aliases.items())
                    successors = ()
                elif instruction.id == ARM_INS_B:
                    successors = (operands[0].imm,)
                    if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
                        successors += (current + instruction.size,)
                else:
                    successors = (current + instruction.size,)
                outgoing = (tuple(sorted(aliases.items())), depth)
                for successor in successors:
                    if successor not in states:
                        states[successor] = outgoing
                        pending.append(successor)
                    elif states[successor] != outgoing:
                        previous = states[successor]
                        if not self.stack_arguments or previous[1] != depth:
                            raise ValueError("inconsistent buffer aliases at control-flow join")
                        merged = (merge_possible_aliases(previous[0], outgoing[0]), depth)
                        if merged != previous:
                            states[successor] = merged
                            pending.append(successor)
            return dict(returned)
        except ValueError as error:
            raise ValueError(f"buffer callee 0x{address:08X}: {error}") from error
        finally:
            self.active.remove(address)

    def fingerprint(self):
        digest = hashlib.sha256()
        for address, data in sorted(self.dependencies.items()):
            digest.update(struct.pack("<II", address, len(data)))
            digest.update(data)
        return digest.hexdigest()


def verify_leaf_instructions(data, address, thumb, validated_calls=None,
                             buffer_proof=None, call_resolver=None, switch_relocations=None,
                             switch_data_relocations=None, udivsi3_context=None):
    """Verify a local CFG, optionally applying validated direct-call ABI summaries."""
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    decoder.detail = True
    switch = None
    reserved = set()
    division_constants = None
    if udivsi3_context is not None:
        if not isinstance(udivsi3_context, tuple) or len(udivsi3_context) != 3 or \
                not isinstance(udivsi3_context[2], dict) or udivsi3_context[2] or \
                not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None or switch_data_relocations is not None:
            raise ValueError("division verification requires an isolated fresh ROM context")
        verify_udivsi3_identity(udivsi3_context[0], udivsi3_context[1])
        division_constants = udivsi3_context[2]
    if switch_data_relocations is not None and switch_relocations is None:
        raise ValueError("switch-data requires a verified local switch")
    if switch_relocations is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None:
            raise ValueError("switch evidence cannot combine frame or buffer proof profiles")
        switch = switch_layout(data, address, switch_relocations, switch_data_relocations)
        reserved = {address + position
                    for offset in (*switch_relocations, *(switch_data_relocations or {}))
                    for position in range(offset, offset + 4)}
    end = address + len(data)
    alignment = 2 if thumb else 4
    states = {address: (frozenset({ARM_REG_LR}), (), (), (), ())}
    stack_arguments = buffer_proof is not None and buffer_proof.stack_arguments
    caller_clobbered = CALLER_CLOBBERED
    pending = [address]
    instructions = {}
    owners = {}
    edges = {}
    returns = set()
    literals = set()
    calls = dict(validated_calls or {})
    seen_calls = set()
    while pending:
        current = pending.pop()
        if current % alignment or not address <= current < end:
            raise ValueError("function has no verified return: non-leaf control flow leaves the symbol")
        if current not in instructions:
            instruction = next(decoder.disasm(data[current - address:current - address + 4],
                                             current, count=1), None)
            if instruction is None or current + instruction.size > end:
                raise ValueError("invalid or truncated reachable instruction")
            for position in range(current, current + instruction.size):
                if position in reserved:
                    raise ValueError("reachable code overlaps the switch pointer or table")
                if position in owners:
                    raise ValueError("control flow enters the middle of an instruction")
                owners[position] = current
            instructions[current] = instruction
        instruction = instructions[current]
        return_registers = set(states[current][0])
        stack = list(states[current][1])
        aliases = dict(states[current][2])
        constants = dict(states[current][3])
        pointer_slots = dict(states[current][4])
        operands = instruction.operands
        registers = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        stack_operation = instruction.mnemonic in ("push", "pop")
        adjustment = thumb_stack_adjustment(instruction) if thumb else None
        calling = CS_GRP_CALL in instruction.groups
        if CS_GRP_INT in instruction.groups or calling and not (calls or call_resolver):
            raise ValueError("non-leaf calls and interrupts require linked CFG verification")
        if calling:
            if not thumb or not unconditional or instruction.id != ARM_INS_BL or \
                    instruction.size != 4 or len(operands) != 1 or operands[0].type != ARM_OP_IMM or \
                    address <= operands[0].imm < end:
                raise ValueError("call is not a validated external direct Thumb BL")
            target = operands[0].imm
            if is_udivsi3_address(target):
                if division_constants is None or target != UDIVSI3_ADDRESS:
                    raise ValueError("division runtime requires its versioned nonzero-divisor proof")
                divisor = constants.get(ARM_REG_R1)
                if type(divisor) is not int or not 1 <= divisor <= 0xFFFFFFFF:
                    raise ValueError("division requires a CFG-proven nonzero constant in r1")
                division_constants[current] = divisor
            elif division_constants is not None and target in RUNTIME_HELPERS.values():
                raise ValueError("division evidence excludes runtime call thunks")
            if call_resolver is not None:
                call_resolver(operands[0].imm)
                calls[current] = operands[0].imm
            elif calls.get(current) != operands[0].imm:
                raise ValueError("call is not a validated external direct Thumb BL")
            seen_calls.add(current)
        if instruction.id == ARM_INS_IT:
            raise ValueError("unsupported conditional instruction block")
        if instruction.id == ARM_INS_ADR:
            raise ValueError("unsupported program-counter materialization")
        if stack_operation:
            if not unconditional or ARM_REG_SP in registers:
                raise ValueError("unsupported conditional or irregular stack operation")
            if instruction.mnemonic == "push":
                if ARM_REG_PC in registers:
                    raise ValueError("unsupported program-counter materialization")
                if any(register in aliases for register in registers):
                    raise ValueError("stack aliases cannot be pushed or spilled")
                stack[:0] = [(register in return_registers, True, False) for register in registers]
                for slot in range(len(registers)):
                    pointer_slots.pop(-4 * len(stack) + 4 * slot, None)
            else:
                if len(registers) > len(stack):
                    raise ValueError("pop reads outside the saved stack frame")
                if any(-4 * len(stack) + 4 * slot in pointer_slots
                       for slot in range(len(registers))):
                    raise ValueError("pointer-bearing local words cannot be popped")
                for register, saved_slot in zip(registers, stack):
                    aliases.pop(register, None)
                    constants.pop(register, None)
                    return_registers.discard(register)
                    if saved_slot[0]:
                        return_registers.add(register)
                del stack[:len(registers)]
        elif adjustment is not None:
            if not unconditional:
                raise ValueError("unsupported conditional stack-pointer adjustment")
            if adjustment < 0:
                stack[:0] = [(False, False, True)] * -adjustment
            elif adjustment > len(stack):
                raise ValueError("stack-pointer adjustment leaves the tracked frame")
            else:
                del stack[:adjustment]
        returning = unconditional and (
            (instruction.mnemonic == "bx" and len(registers) == 1 and
             registers[0] in return_registers) or
            (instruction.mnemonic == "pop" and ARM_REG_PC in return_registers) or
            (instruction.mnemonic == "mov" and registers == (ARM_REG_PC, ARM_REG_LR)
             and ARM_REG_LR in return_registers))
        if returning:
            if stack:
                raise ValueError("return does not balance the saved stack frame")
            if stack_arguments and aliases:
                raise ValueError("local stack pointer escapes through a return register")
            returns.add(current)
            successors = ()
        elif calling:
            returned_aliases = {}
            if pointer_slots or any(register in aliases for register in caller_clobbered):
                if buffer_proof is None:
                    raise ValueError("stack aliases cannot cross calls in caller-clobbered registers")
                returned_aliases = buffer_proof.check_call(operands[0].imm, aliases, stack,
                                                          pointer_slots)
            return_registers.difference_update(caller_clobbered)
            for register in caller_clobbered:
                constants.pop(register, None)
                aliases.pop(register, None)
            aliases.update(returned_aliases)
            stack = [(saved_return and saved_slot, saved_slot, local_word)
                     for saved_return, saved_slot, local_word in stack]
            successors = (current + instruction.size,)
        elif instruction.id == ARM_INS_B:
            if len(operands) != 1 or operands[0].type != ARM_OP_IMM:
                raise ValueError("unsupported non-leaf branch operand")
            successors = (operands[0].imm,)
            if not unconditional:
                successors += (current + instruction.size,)
        elif switch is not None and current == address + switch["dispatch"] + 8:
            successors = tuple(sorted({address + addend for offset, addend
                                       in switch_relocations.items() if offset != switch["literal"]}))
        else:
            if CS_GRP_JUMP in instruction.groups:
                raise ValueError("non-leaf indirect control flow requires linked CFG verification")
            if not stack_operation and adjustment is None:
                read, written = instruction.regs_access()
                assigned_return = None
                loaded_alias = None
                if ARM_REG_PC in written:
                    raise ValueError("unresolved program-counter write")
                if ARM_REG_SP in written:
                    raise ValueError("unsupported stack-pointer adjustment")
                assignment = stack_alias_assignment(instruction, aliases, len(stack), constants) if thumb else None
                if ARM_REG_SP in registers and assignment is None:
                    raise ValueError("unsupported stack-address materialization")
                if ARM_REG_PC in registers:
                    raise ValueError("unsupported program-counter materialization")
                allowed_aliases = {assignment[2]} if assignment is not None else set()
                if thumb and unconditional and instruction.id == ARM_INS_CMP and \
                        instruction.size == 2 and not instruction.writeback and \
                        len(operands) == 2 and operands[0].type == ARM_OP_REG and \
                        operands[1].type == ARM_OP_IMM and operands[1].imm == 0 and \
                        all(not operand.shift.type and not operand.shift.value and
                            not operand.subtracted for operand in operands):
                    compared = operands[0].reg
                    if ARM_REG_R0 <= compared <= ARM_REG_R0 + 7 and compared in aliases and \
                            instruction.bytes == bytes((0, 0x28 + compared - ARM_REG_R0)) and \
                            set(read) == {compared} and set(written) == {ARM_REG_CPSR}:
                        offset = aliases[compared]
                        if -4 * len(stack) <= offset < 0 and \
                                stack[(offset + 4 * len(stack)) // 4][2]:
                            allowed_aliases.add(compared)
                for operand in operands:
                    if operand.type != ARM_OP_MEM:
                        continue
                    if operand.mem.index == ARM_REG_SP:
                        raise ValueError("unsupported stack-address materialization")
                    if operand.mem.index == ARM_REG_PC:
                        raise ValueError("unsupported program-counter materialization")
                    if operand.mem.base in aliases:
                        widths = {"ldr": 4, "str": 4, "ldrh": 2, "strh": 2,
                                  "ldrb": 1, "strb": 1, "ldrsh": 2, "ldrsb": 1}
                        width = widths.get(instruction.mnemonic)
                        if not thumb or not unconditional or instruction.size != 2 or \
                                width is None or len(operands) != 2 or len(registers) != 1 or \
                                operands[0].type != ARM_OP_REG:
                            raise ValueError("unsupported stack-alias memory access")
                        offset = aliases[operand.mem.base] + operand.mem.disp
                        if operand.mem.index:
                            if operand.mem.index not in constants:
                                raise ValueError("stack-alias index is not a known constant")
                            offset += constants[operand.mem.index]
                        if offset % width or not -4 * len(stack) <= offset or offset + width > 0:
                            raise ValueError("stack-alias access is unaligned or outside the tracked frame")
                        allowed_aliases.add(operand.mem.base)
                        slot = (offset + 4 * len(stack)) // 4
                        pointer_word = offset - offset % 4
                        if pointer_word in pointer_slots:
                            if width != 4:
                                raise ValueError("partial access to a pointer-bearing local word")
                            if instruction.mnemonic.startswith("ldr"):
                                loaded_alias = (registers[0], pointer_slots[pointer_word])
                        if instruction.mnemonic.startswith("str"):
                            if registers[0] in aliases:
                                raise ValueError("stack aliases cannot be stored or spilled")
                            stack[slot] = (width == 4 and registers[0] in return_registers,
                                           stack[slot][1], stack[slot][2])
                            pointer_slots.pop(pointer_word, None)
                        elif width == 4 and stack[slot][0]:
                            assigned_return = registers[0]
                    if operand.mem.base == ARM_REG_PC:
                        if instruction.mnemonic != "ldr" or operand.mem.index:
                            raise ValueError("unsupported PC-relative memory access")
                        program_counter = ((current + 4) & ~3 if thumb else current + 8)
                        literals.add(program_counter + operand.mem.disp)
                    if operand.mem.base == ARM_REG_SP:
                        if thumb:
                            if not unconditional or instruction.size != 2 or \
                                    instruction.mnemonic not in ("ldr", "str") or \
                                    len(operands) != 2 or len(registers) != 1 or \
                                    operands[0].type != ARM_OP_REG or operand.mem.index or \
                                    operand.mem.disp < 0 or operand.mem.disp % 4:
                                raise ValueError("unsupported direct stack-frame access")
                            slot = operand.mem.disp // 4
                            offset = operand.mem.disp - 4 * len(stack)
                            if instruction.mnemonic == "str":
                                if slot >= len(stack):
                                    raise ValueError("stack-frame write is outside the tracked frame")
                                if registers[0] in aliases and stack_arguments:
                                    buffer_proof.access(offset, 4, stack)
                                    buffer_proof.access(aliases[registers[0]], 1, stack)
                                    pointer_slots[offset] = aliases[registers[0]]
                                    allowed_aliases.add(registers[0])
                                else:
                                    pointer_slots.pop(offset, None)
                                stack[slot] = (registers[0] in return_registers,
                                               stack[slot][1], stack[slot][2])
                            else:
                                if slot < len(stack) and stack[slot][0]:
                                    assigned_return = registers[0]
                                if offset in pointer_slots:
                                    loaded_alias = (registers[0], pointer_slots[offset])
                        elif not instruction.mnemonic.startswith("ldr"):
                            raise ValueError("unsupported stack-frame write")
                if (set(read) & aliases.keys()) - allowed_aliases:
                    raise ValueError("unsupported stack-alias use or escape")
                constant = None
                if thumb and unconditional and instruction.size == 2 and \
                        instruction.mnemonic in ("mov", "movs") and len(operands) == 2 and \
                        operands[0].type == ARM_OP_REG:
                    if operands[1].type == ARM_OP_IMM:
                        constant = operands[1].imm
                    elif operands[1].type == ARM_OP_REG:
                        constant = constants.get(operands[1].reg)
                        if operands[1].reg in return_registers:
                            assigned_return = operands[0].reg
                return_registers.difference_update(written)
                for register in written:
                    aliases.pop(register, None)
                    constants.pop(register, None)
                if constant is not None:
                    constants[operands[0].reg] = constant
                if assignment is not None:
                    aliases[assignment[0]] = assignment[1]
                if loaded_alias is not None:
                    aliases[loaded_alias[0]] = loaded_alias[1]
                if assigned_return is not None:
                    return_registers.add(assigned_return)
            elif ARM_REG_PC in registers:
                raise ValueError("unproven program-counter stack return")
            successors = (current + instruction.size,)
        edges[current] = successors
        outgoing = (frozenset(return_registers), tuple(stack), tuple(sorted(aliases.items())),
                    tuple(sorted(constants.items())), tuple(sorted(pointer_slots.items())))
        for successor in successors:
            previous = states.get(successor)
            if previous is None:
                merged = outgoing
            else:
                if len(previous[1]) != len(stack):
                    raise ValueError("inconsistent saved stack depth at control-flow join")
                if previous[2] != outgoing[2] and not stack_arguments:
                    raise ValueError("inconsistent stack aliases at control-flow join")
                merged_aliases = (merge_possible_aliases(previous[2], outgoing[2])
                                  if stack_arguments else outgoing[2])
                merged_slots = merge_possible_aliases(previous[4], outgoing[4])
                merged = (previous[0] & outgoing[0],
                          tuple((saved[0] and incoming[0], saved[1] and incoming[1],
                                 saved[2] and incoming[2])
                                for saved, incoming
                                in zip(previous[1], stack)), merged_aliases,
                          tuple((register, value) for register, value in previous[3]
                                if constants.get(register) == value), merged_slots)
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if seen_calls != calls.keys():
        raise ValueError("call relocations are not all reachable verified instructions")
    if division_constants is not None and \
            (not division_constants or uses_stack_frame(instructions.values())):
        raise ValueError("division evidence requires runtime calls and a frameless caller")
    if not returns:
        raise ValueError("function has no verified return")
    predecessors = {current: set() for current in instructions}
    for current, successors in edges.items():
        for successor in successors:
            predecessors[successor].add(current)
    if switch is not None:
        if uses_stack_frame(instructions.values()) or any(
                target in RUNTIME_HELPERS.values() for target in calls.values()):
            raise ValueError("switch evidence excludes fixed frames and runtime call thunks")
        comparison = address + switch["comparison"]
        guard = address + switch["guard"]
        dispatch = address + switch["dispatch"]
        expected = {guard: {comparison}, dispatch: {guard}}
        if dispatch - guard == 4:
            expected[guard + 2] = {guard}
        expected.update({dispatch + distance: {dispatch + distance - 2}
                         for distance in range(2, 10, 2)})
        if comparison not in instructions or any(
                current == address or predecessors.get(current) != incoming
                for current, incoming in expected.items()):
            raise ValueError("switch selector bound is bypassed by an unverified predecessor edge")
    reaching_return = set(returns)
    pending = list(returns)
    while pending:
        for predecessor in predecessors[pending.pop()]:
            if predecessor not in reaching_return:
                reaching_return.add(predecessor)
                pending.append(predecessor)
    if reaching_return != instructions.keys():
        raise ValueError("reachable control-flow region has no path to a verified return")
    code_end = max(instruction.address + instruction.size
                   for instruction in instructions.values())
    # A literal pool is usually trailing, but agbcc interleaves it when a
    # switch has enough arms: each 'ldr rX,=const' gets its own word between the
    # case bodies, and the ROM has it there too, so no source variation avoids
    # it.  'Literal must sit after the last instruction' is therefore the wrong
    # rule - it is the trailing-pool assumption, and an interior word always
    # fails it.
    #
    # The real test is whether a literal could be confused with code.  A pool
    # word is skipped by a branch or stepped over by a fallthrough, so it never
    # appears in the reachable instruction set; requiring alignment and
    # non-overlap with that set distinguishes it from a mis-decode.
    reachable = set()
    for instruction in instructions.values():
        reachable.update(range(instruction.address,
                               instruction.address + instruction.size))
    for literal in sorted(literals):
        if literal % 4 or literal < address or literal + 4 > end:
            raise ValueError("literal read is not an aligned word inside the "
                             "function")
        if any(a in reachable for a in range(literal, literal + 4)):
            raise ValueError("literal read overlaps reachable code")
    if switch_data_relocations is not None:
        verify_data_literals(instructions.values(), address, switch_data_relocations)
    return [instructions[current] for current in sorted(instructions)]


def verify_leaf(data, address, thumb):
    """Return the code extent of a verified local leaf CFG."""
    instructions = verify_leaf_instructions(data, address, thumb)
    return max(instruction.address + instruction.size for instruction in instructions) - address


def lcs_align(a, b):
    """align two sequences, reporting which elements are shared"""
    n, m = len(a), len(b)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            dp[i][j] = dp[i + 1][j + 1] + 1 if a[i] == b[j] \
                else max(dp[i + 1][j], dp[i][j + 1])
    i = j = 0
    rows = []
    while i < n and j < m:
        if a[i] == b[j]:
            rows.append(("same", a[i], b[j]))
            i += 1
            j += 1
        elif dp[i + 1][j] >= dp[i][j + 1]:
            rows.append(("got", a[i], None))
            i += 1
        else:
            rows.append(("want", None, b[j]))
            j += 1
    rows += [("got", x, None) for x in a[i:]]
    rows += [("want", None, x) for x in b[j:]]
    return rows


def disasm(data, base, thumb):
    cs = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    return [(i.address, i.size, f"{i.mnemonic} {i.op_str}".strip())
            for i in cs.disasm(data, base)]


def function_span(addr, symbols_file):
    """length of the ROM function at addr, from symbols/functions.txt"""
    with open(symbols_file, encoding="utf-8") as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            p = line.split()                    # addr end size instrs endby
            a = int(p[0], 16)
            if a == addr:
                return int(p[1], 16) - a
    return None


def plausibility_result(result, address):
    document = json.loads(result.stdout)
    required = {"findings", "total", "addr", "hand_asm_allowed", "allow_entry"}
    if not isinstance(document, dict) or not required <= document.keys():
        raise ValueError("missing plausibility JSON fields")
    records = document["findings"]
    if not isinstance(records, list) or type(document["total"]) is not int or \
            document["total"] != len(records) or document["addr"] != f"0x{address:08X}" or \
            type(document["hand_asm_allowed"]) is not bool:
        raise ValueError("invalid plausibility JSON fields")
    findings = []
    for record in records:
        if not isinstance(record, dict) or \
                any(not isinstance(record.get(field), str) or not record[field]
                    for field in ("file", "rule", "severity", "message")) or \
                type(record.get("line")) is not int or record["line"] < 0 or \
                record["severity"] not in ("error", "suspect"):
            raise ValueError("invalid plausibility finding")
        findings.append(f"{os.path.basename(record['file'])}:{record['line']}: "
                        f"{record['severity'].upper()}: {record['rule']}")
    allowed = document["allow_entry"]
    if allowed is not None and (not isinstance(allowed, dict) or
            not isinstance(allowed.get("address"), str) or
            allowed["address"].upper() != f"0x{address:08X}".upper() or
            not isinstance(allowed.get("reason", "no reason recorded"), str)):
        raise ValueError("invalid hand-asm allow entry")
    if document["hand_asm_allowed"] != (allowed is not None) or \
            allowed is not None and not findings:
        raise ValueError("inconsistent hand-asm allow entry")
    expected_exit = 1 if findings else 0
    if result.returncode != expected_exit:
        findings.append(f"plausibility checker failed with exit {result.returncode}; "
                        f"expected {expected_exit}")
        allowed = None
    return findings, allowed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("addr")
    ap.add_argument("--cc", default=DEFAULT_CC)
    ap.add_argument("--cpp", default=DEFAULT_CPP)
    ap.add_argument("--assembler", dest="assembler", default=DEFAULT_AS)
    ap.add_argument("--objcopy", default=DEFAULT_OBJCOPY)
    ap.add_argument("--linker", default=DEFAULT_LD)
    ap.add_argument("--flags", default=DEFAULT_FLAGS)
    ap.add_argument("--mode", default="thumb", choices=("thumb", "arm"))
    ap.add_argument("--wsl", default="Ubuntu")
    ap.add_argument("--wsl-path", default=os.environ.get("FFTA_WSL_PATH",
                                                         DEFAULT_WSL_PATH))
    ap.add_argument("--label", default="")
    ap.add_argument("--no-write", action="store_true")
    ap.add_argument("--emit", help="write verified symbol bytes to a new file under the decomp build/")
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT"),
                    help="decomp repo (default: current directory)")
    args = ap.parse_args()
    global ROOT
    ROOT = repo_root(args.root)

    addr = int(args.addr, 16)
    # one file per function, grouped into folders by module - the folder is
    # evidence, not decoration, so look for the source rather than assuming it
    # sits at the top of src/
    candidates = [os.path.join(ROOT, "src", f"{addr:08X}.c")]
    for path in sorted(Path(ROOT, "src").rglob(f"{addr:08X}.c")):
        candidates.append(str(path))
    src_abs = next((c for c in candidates if os.path.exists(c)), None)
    if not src_abs:
        sys.exit(f"no source for 0x{addr:08X} under src/")
    src_rel = os.path.relpath(src_abs, ROOT).replace(os.sep, "/")
    fingerprint = source_fingerprint(ROOT, addr)
    mapping = mapping_snapshot(ROOT)
    data_mapping = data_snapshot(ROOT)
    linked_profile = False
    emit = None
    if args.emit:
        emit = os.path.realpath(os.path.join(ROOT, args.emit))
        build = os.path.realpath(os.path.join(ROOT, "build"))
        if os.path.commonpath((emit, build)) != build or emit == build:
            sys.exit("--emit must name a new file under the decomp build/ directory")
        if os.path.lexists(emit):
            sys.exit("--emit refuses to overwrite an existing file")

    rom_file = rom_path(ROOT)
    with open(rom_file, "rb") as original:
        rom = original.read()
    span = function_span(addr, os.path.join(ROOT, "symbols", "functions.txt"))
    if span is None or span <= 0:
        sys.exit(f"no valid indexed span for 0x{addr:08X}")
    if not ROM_BASE <= addr < ROM_BASE + len(rom):
        sys.exit("function address is outside the ROM")
    thumb = args.mode == "thumb"

    print(f"function  0x{addr:08X}   {span} bytes ({'Thumb' if thumb else 'ARM'})")
    print(f"source    {src_rel}")
    print(f"compiler  {args.cc} {args.flags}")

    # the compile runs in a shell (possibly inside WSL), so give it a POSIX path
    runner = Runner(args.cc, args.wsl, args.wsl_path)
    try:
        with runner.workspace() as workspace:
            tmp = shlex.quote(workspace)
            environment = f"export TMPDIR={tmp}; "
            runner.sh(f"{environment}{args.cpp} -nostdinc -undef -I include {src_rel} -o {tmp}/f.i")
            verify_dependencies(runner.read_binary(f"{workspace}/f.i").decode("utf-8"), ROOT, addr)
            runner.sh(f"{environment}{args.cc} {args.flags} {tmp}/f.i -o {tmp}/f.s")
            assembler_flags = "-mthumb-interwork" if thumb else ""
            runner.sh(f"{environment}{args.assembler} {assembler_flags} {tmp}/f.s -o {tmp}/f.o")
            runner.sh(f"{args.objcopy} -O binary --only-section=.text "
                      f"{tmp}/f.o {tmp}/f.bin")
            object_data = runner.read_binary(f"{workspace}/f.o")
            original = elf_image(object_data)
            text_data = runner.read_binary(f"{workspace}/f.bin")
            if original["text"] != text_data:
                raise ValueError("objcopy output does not equal ELF .text")
            calls = {}
            data_relocations = {}
            function_relocations = {}
            switch_relocations = {}
            udivsi3_bindings = {}
            division_evidence = None
            address_manifest = None
            switch_evidence = None
            if original["relocations"]:
                if not thumb:
                    raise ValueError("linked profile supports only Thumb callers")
                got, calls, data_relocations = link_calls(runner, workspace, args, original,
                                                          addr, mapping, len(rom), rom, data_mapping,
                                                          function_relocations, switch_relocations,
                                                          allow_switch_data=True,
                                                          udivsi3_bindings=udivsi3_bindings)
                linked_profile = bool(calls)
            else:
                got = function_bytes(object_data, text_data, f"func_{addr:08X}", addr, thumb)
            buffer_proof = BufferCallProof(rom, mapping if calls else None)
            if udivsi3_bindings:
                divisors = {}
                verify_leaf_instructions(got, addr, True, calls,
                                         udivsi3_context=(rom, mapping, divisors))
                division_evidence = {
                    "calls": [[site - addr, udivsi3_bindings.get(site, f"func_{target:08X}")]
                              for site, target in sorted(calls.items())],
                    "runtime": UDIVSI3_RUNTIME,
                    "divisors": [[site - addr, divisor] for site, divisor in sorted(divisors.items())]}
                verified_instructions = verify_udivsi3(
                    got, addr, rom, mapping, division_evidence)
            elif switch_relocations:
                switch_evidence = {
                    "calls": [[site - addr, f"func_{target:08X}"]
                              for site, target in sorted(calls.items())],
                    "switch": switch_layout(got, addr, switch_relocations,
                                            data_relocations if data_relocations else None)}
                if data_relocations:
                    objects = parse_data_symbols(data_mapping)
                    switch_evidence["data"] = [
                        [offset, name, value - objects[name]]
                        for offset, (name, value) in sorted(data_relocations.items())]
                verified_instructions, _ = verify_switches(
                    got, addr, rom, mapping, switch_evidence,
                    data_mapping=data_mapping if data_relocations else None)
            elif function_relocations:
                objects = parse_data_symbols(data_mapping) if data_relocations else {}
                address_manifest = {
                    "calls": [[site - addr, f"func_{target:08X}"]
                              for site, target in sorted(calls.items())],
                    "data": [[offset, name, value - objects[name]]
                             for offset, (name, value) in sorted(data_relocations.items())],
                    "functions": [[offset, name] for offset, (name, value)
                                  in sorted(function_relocations.items())]}
                verified_instructions, _ = verify_function_addresses(
                    got, addr, rom, mapping, data_mapping, address_manifest)
            else:
                try:
                    verified_instructions = verify_leaf_instructions(got, addr, thumb, calls,
                                                                      buffer_proof=buffer_proof)
                except ValueError:
                    if not thumb or not calls:
                        raise
                    buffer_proof = BufferCallProof(rom, mapping, stack_arguments=True)
                    verified_instructions = verify_leaf_instructions(got, addr, thumb, calls,
                                                                      buffer_proof=buffer_proof)
            verify_data_literals(verified_instructions, addr, data_relocations)
            if buffer_proof.stack_arguments and not buffer_proof.dependencies:
                raise ValueError("stack-buffer evidence requires an inspected buffer call")
            if buffer_proof.dependencies and data_relocations:
                raise ValueError("buffer-call evidence does not support data relocations")
            if buffer_proof.dependencies and len(buffer_proof.span(addr)) != len(got):
                raise ValueError("buffer caller requires an exact complete mapped span")
    except Exception as e:                       # noqa: BLE001
        sys.exit(f"compile failed:\n{e}")

    if len(got) < span:
        sys.exit(f"compiled symbol is shorter than the indexed span: {len(got)} < {span}")
    span = len(got)
    framed_profile = thumb and uses_stack_frame(verified_instructions)
    data_profile = bool(data_relocations)
    schema = LINKED_SCHEMA if linked_profile else SCHEMA
    if data_profile:
        schema = FRAMED_DATA_SCHEMA if framed_profile else DATA_SCHEMA
    elif framed_profile:
        schema = FRAMED_LINKED_SCHEMA if linked_profile else FRAMED_SCHEMA
    if buffer_proof.dependencies:
        schema = STACK_BUFFER_SCHEMA if buffer_proof.stack_arguments else BUFFER_SCHEMA
    if function_relocations:
        schema = FUNCTION_ADDRESS_SCHEMA
    if switch_relocations:
        schema = SWITCH_DATA_SCHEMA if data_profile else SWITCH_SCHEMA
    if udivsi3_bindings:
        schema = UDIVSI3_SCHEMA
    control_flow = CALL_SUMMARY if linked_profile else "closed leaf CFG"
    print(f"extent    {span} bytes (complete ELF symbol; {control_flow}; no relocations)")
    want = rom[addr - ROM_BASE: addr - ROM_BASE + span]
    got_body = got
    identical = got_body == want

    # a byte-identical compile is only a match if the source is something a
    # developer could plausibly have written
    here = os.path.dirname(os.path.abspath(__file__))
    plaus_path = os.path.join(here, "plausible.py")
    findings = ["plausibility checker is missing"]
    hand_asm_allowed = None
    if os.path.exists(plaus_path):
        lint_targets = [str(path) for path in source_paths(ROOT, addr)]
        try:
            checker_result = subprocess.run(
                [sys.executable, plaus_path, "--quiet", "--addr", f"0x{addr:08X}",
                 "--json"] + lint_targets,
                capture_output=True, text=True)
            findings, hand_asm_allowed = plausibility_result(checker_result, addr)
        except (OSError, ValueError, TypeError, RecursionError) as error:
            findings = [f"plausibility checker failed: {error}"]

    plausible = not findings
    if source_fingerprint(ROOT, addr) != fingerprint:
        sys.exit("source or headers changed during verification; re-run match.py")
    if (linked_profile or data_profile or function_relocations or switch_relocations) and \
            mapping_snapshot(ROOT) != mapping:
        sys.exit("function mapping changed during verification; re-run match.py")
    if data_profile and data_snapshot(ROOT) != data_mapping:
        sys.exit("data symbol mapping changed during verification; re-run match.py")
    with open(rom_file, "rb") as original:
        if original.read() != rom:
            sys.exit("base ROM changed during verification; re-run match.py")
    exact = identical and plausible
    byte_rows = lcs_align(got_body, want)

    # Byte-identical output from source that no developer would write is not a
    # match.  It is only acceptable at an address the maintainer has explicitly
    # put on the hand-asm allow list, and then it is reported as HAND-ASM so it
    # never counts as a decompilation.
    if exact:
        verdict = "MATCH - byte identical"
    elif identical:
        verdict = ("HAND-ASM (sanctioned) - byte identical, but the source is "
                   "not code a developer would have written"
                   if hand_asm_allowed else
                   "HAND-ASM REQUIRED BUT NOT ALLOWED - byte identical, yet "
                   f"0x{addr:08X} is not on the hand-asm allow list; park it, "
                   "and only the maintainer may add it")
    else:
        verdict = "NOT MATCHING - bytes differ"

    print(f"\ntarget  {want.hex()}")
    print(f"got     {got_body.hex()}"
          + ("" if len(got_body) == span else f"   ({len(got_body)} bytes compiled)"))
    print(f"bytes   {'identical' if identical else 'DIFFER'}")
    print(f"source  {'plausible' if plausible else 'IMPLAUSIBLE'}"
          + ("" if plausible or hand_asm_allowed else " (not on the allow list)"))
    print(f"verdict {verdict}\n")
    if findings:
        print("plausibility findings:")
        for line in findings:
            print(f"  {line}")
    if hand_asm_allowed:
        print(f"\nhand-asm allow entry for 0x{addr:08X}: "
              f"{hand_asm_allowed.get('reason', 'no reason recorded')}")

    ga = [(instruction.address, instruction.size,
           f"{instruction.mnemonic} {instruction.op_str}".strip())
          for instruction in verified_instructions]
    wa = [row for address, size, _ in ga
          for row in disasm(want[address - addr:address - addr + size], address, thumb)]
    gbytes = [t for _, _, t in ga]
    wbytes = [t for _, _, t in wa]
    past_end = {i for i, (a, _, _) in enumerate(ga) if a >= addr + span}
    rows = lcs_align(gbytes, wbytes)

    width = 40
    lines, gi, wi = [], 0, 0
    for kind, _, _ in rows:
        g = gbytes[gi] if gi < len(gbytes) else ""
        w = wbytes[wi] if wi < len(wbytes) else ""
        if kind == "same":
            lines.append(f"{g:<{width}}{w}")
        elif kind == "got":
            over = "  (past the ROM function)" if gi in past_end else ""
            lines.append(f"{g:<{width}}{'':<{width}}  <- extra in compiled{over}")
        else:
            lines.append(f"{'':<{width}}{w:<{width}}  <- missing from compiled")
        gi += 1 if kind != "want" else 0
        wi += 1 if kind != "got" else 0

    print(f"{'compiled':<{width}}rom")
    print(f"{'-' * width}{'-' * 40}")
    for line in lines:
        print(line)

    same_bytes = sum(1 for k, _, _ in byte_rows if k == "same")
    same_instr = sum(1 for k, _, _ in rows if k == "same")
    print(f"\n{same_instr}/{len(wbytes)} instructions identical "
          f"({same_bytes}/{len(want)} bytes)")

    if not args.no_write:
        label = f".{args.label}" if args.label else ""
        out = os.path.join(ROOT, "docs", "match", f"{addr:08X}{label}.md")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "w", encoding="utf-8", newline="\n") as f:
            f.write(f"# match report - 0x{addr:08X}"
                    f"{' (' + args.label + ')' if args.label else ''}\n\n")
            f.write(f"* source: `{src_rel}`\n")
            f.write(f"* verification: `{schema}`\n")
            f.write(f"* source SHA-256: `{fingerprint}`\n")
            if framed_profile:
                f.write(f"* stack frame: {STACK_SUMMARY}\n")
            if buffer_proof.dependencies:
                summary = STACK_BUFFER_SUMMARY if buffer_proof.stack_arguments else BUFFER_SUMMARY
                f.write(f"* buffer calls: {summary}\n")
                f.write(f"* buffer proof SHA-256: `{buffer_proof.fingerprint()}`\n")
            if linked_profile or data_profile or function_relocations or switch_relocations:
                f.write(f"* mapping SHA-256: `{mapping_fingerprint(mapping)}`\n")
                f.write(f"* control flow: {control_flow}\n")
            if data_profile:
                f.write(f"* data symbols SHA-256: `{mapping_fingerprint(data_mapping)}`\n")
            if function_relocations:
                encoded_manifest = function_address_manifest(address_manifest)
                f.write(f"* function addresses: {FUNCTION_ADDRESS_SUMMARY}\n")
                f.write(f"* function address manifest: `{encoded_manifest}`\n")
                proof_digest = function_address_fingerprint(addr, got_body, address_manifest)
                f.write(f"* function address proof SHA-256: `{proof_digest}`\n")
            if switch_relocations:
                summary = SWITCH_DATA_SUMMARY if data_profile else SWITCH_SUMMARY
                f.write(f"* switches: {summary}\n")
                f.write(f"* switch manifest: `{switch_manifest(switch_evidence)}`\n")
                fingerprint_switch = switch_data_fingerprint if data_profile else switch_fingerprint
                proof_digest = fingerprint_switch(addr, got_body, switch_evidence)
                f.write(f"* switch proof SHA-256: `{proof_digest}`\n")
            if udivsi3_bindings:
                f.write(f"* unsigned division: {UDIVSI3_SUMMARY}\n")
                f.write(f"* unsigned division manifest: `{udivsi3_manifest(division_evidence)}`\n")
                proof_digest = udivsi3_fingerprint(addr, got_body, division_evidence)
                f.write(f"* unsigned division proof SHA-256: `{proof_digest}`\n")
            f.write(f"* compiler: `{args.cc} {args.flags}`\n")
            f.write(f"* verified extent: complete ELF function symbol, including literal pools\n")
            f.write(f"* relocations: none\n")
            f.write(f"* ROM bytes: `{want.hex()}` ({span} bytes)\n")
            f.write(f"* compiled : `{got_body.hex()}`\n")
            f.write(f"* source plausibility: "
                    f"{'plausible' if plausible else 'IMPLAUSIBLE'}\n")
            f.write(f"* hand-asm allow list: "
                    f"{'listed (' + str(hand_asm_allowed.get('reason', 'no reason recorded')) + ')' if hand_asm_allowed else 'not listed'}\n\n")
            f.write(f"**{verdict}** - {same_bytes}/{len(want)} bytes\n")
            if findings:
                f.write("\nplausibility findings:\n\n")
                for line in findings:
                    f.write(f"- {line.strip()}\n")
            f.write("\n```\n")
            f.write(f"{'compiled':<{width}}rom\n")
            for line in lines:
                f.write(line.rstrip() + "\n")
            f.write("```\n")
        print(f"\nwrote {os.path.relpath(out, ROOT)}")
    if exact and emit:
        os.makedirs(os.path.dirname(emit), exist_ok=True)
        created = False
        complete = False
        try:
            with open(emit, "xb") as output:
                created = True
                if output.write(got_body) != len(got_body):
                    raise OSError("incomplete verified symbol write")
            complete = True
        finally:
            if created and not complete:
                os.unlink(emit)
        print(f"emitted {span} verified bytes to {os.path.relpath(emit, ROOT)}")
    return 0 if exact else 1


if __name__ == "__main__":
    sys.exit(main())
