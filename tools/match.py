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
import tempfile
import modsi3_profile as modsi3
import divsi3_profile as divsi3
import signed_divmod_profile as signed_divmod
import umodsi3_profile as umodsi3
import ashldi3_profile as ashldi3
import inert_spin_profile as inert_spin
import software_double_profile as software_double
import software_float_profile as software_float
import function_thunk_profile as function_thunk
import empty_body_profile as empty_body
import stack_pointer_compare_profile as sp_compare
import signal
from contextvars import ContextVar
from rompath import rom_path
from contextlib import contextmanager
from pathlib import Path
from match_evidence import (BUFFER_SCHEMA, BUFFER_SUMMARY, CALL_SUMMARY, DATA_SCHEMA,
                            FRAMED_DATA_SCHEMA,
                            FUNCTION_ADDRESS_SCHEMA, FRAMED_FUNCTION_ADDRESS_SCHEMA,
                            FUNCTION_ADDRESS_SUMMARY,
                            FUNCTION_BUFFER_SCHEMA, function_buffer_fingerprint,
                            FRAMED_LINKED_SCHEMA, FRAMED_SCHEMA, LINKED_SCHEMA,
                            SCHEMA, STACK_BUFFER_SCHEMA, STACK_BUFFER_SUMMARY,
                            SWITCH_SCHEMA, SWITCH_SUMMARY, switch_fingerprint, switch_manifest,
                            SWITCH_DATA_SCHEMA, SWITCH_DATA_SUMMARY, switch_data_fingerprint,
                            PRELOADED_SWITCH_SCHEMA, PRELOADED_SWITCH_SUMMARY,
                            PRELOADED_SWITCH_CONTROL_FLOW, preloaded_switch_fingerprint,
                            UDIVSI3_SCHEMA, UDIVSI3_SUMMARY, UDIVSI3_RUNTIME,
                            udivsi3_fingerprint, udivsi3_manifest,
                            STACK_SUMMARY, data_snapshot, mapping_fingerprint,
                            function_address_fingerprint, function_address_manifest,
                            mapping_snapshot, source_fingerprint, source_paths, report_rom_path,
                            verify_dependencies)

try:
    from capstone import (Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB,
                          CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_INT, CS_AC_WRITE)
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


SIGNED_REPLAY_TIMEOUT = 120


def _run_replay_process(command, root, timeout, shell=False):
    if os.name != "posix":
        raise ValueError("bounded signed replay requires POSIX process-group cleanup")
    with subprocess.Popen(command, cwd=root, shell=shell, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, start_new_session=True) as process:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except BaseException:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.communicate()
            raise
        return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


class Runner:
    """Runs shell commands, transparently through WSL on Windows."""

    def __init__(self, cc, wsl_distro="Ubuntu", wsl_path="", root=None, timeout=None):
        self.wsl = None
        self.timeout = timeout
        self.root = ROOT if root is None else repo_root(root)
        self.prefix = f"export PATH={wsl_path}:$PATH; " if wsl_path else ""
        if platform.system() == "Windows" and not shutil.which(cc.split("/")[-1]):
            wsl = shutil.which("wsl")
            if wsl:
                self.wsl = [wsl, "-d", wsl_distro, "-e", "bash", "-lc"]

    def sh(self, cmd):
        if self.wsl:
            here = "/mnt/c/" + "/".join(self.root[3:].split(os.sep))
            cmd = f"{self.prefix}cd {here} && {cmd}"
            r = (_run_replay_process(self.wsl + [cmd], self.root, self.timeout)
                 if self.timeout is not None else
                 subprocess.run(self.wsl + [cmd], capture_output=True, text=True))
        else:
            r = (_run_replay_process(cmd, self.root, self.timeout, shell=True)
                 if self.timeout is not None else
                 subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=self.root))
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


def compile_object(runner, workspace, args, root, address, source, thumb=True):
    temporary = shlex.quote(workspace)
    environment = f"export TMPDIR={temporary}; "
    runner.sh(f"{environment}{args.cpp} -nostdinc -undef -I include {shlex.quote(source)} "
              f"-o {temporary}/f.i")
    verify_dependencies(runner.read_binary(f"{workspace}/f.i").decode("utf-8"), root, address)
    runner.sh(f"{environment}{args.cc} {args.flags} {temporary}/f.i -o {temporary}/f.s")
    assembler_flags = "-mthumb-interwork" if thumb else ""
    runner.sh(f"{environment}{args.assembler} {assembler_flags} {temporary}/f.s -o {temporary}/f.o")
    runner.sh(f"{args.objcopy} -O binary --only-section=.text {temporary}/f.o {temporary}/f.bin")
    object_data = runner.read_binary(f"{workspace}/f.o")
    image = elf_image(object_data)
    text_data = runner.read_binary(f"{workspace}/f.bin")
    if image["text"] != text_data:
        raise ValueError("objcopy output does not equal ELF .text")
    return object_data, text_data, image


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
                name in ("__udivsi3", "__modsi3", "__umodsi3", "__ashldi3", "__lshrdi3", "__divsi3", "__div0") or name in software_double.OPERATIONS or name in software_float.OPERATIONS or \
                not isinstance(value, str) or not re.fullmatch(r"0x[0-9A-Fa-f]{8}", value):
            raise ValueError("invalid data symbol name or absolute address")
        if is_udivsi3_address(int(value, 16)) or modsi3.reserved(int(value, 16)) or \
                divsi3.reserved(int(value, 16)) or umodsi3.reserved(int(value, 16)) or ashldi3.reserved(int(value, 16)) or software_double.reserved(int(value, 16)) or software_float.reserved(int(value, 16)):
            raise ValueError("division runtime cannot be bound as data")
        symbols[name] = int(value, 16)
    return symbols


def function_address_target(name, entries, address, size, rom_size):
    match = re.fullmatch(r"func_([0-9A-F]{8})", name)
    if match is None:
        raise ValueError("function address requires a canonical addressed function")
    target = int(match[1], 16)
    if is_udivsi3_address(target) or modsi3.reserved(target) or divsi3.reserved(target) or umodsi3.reserved(target) or ashldi3.reserved(target) or software_double.reserved(target) or software_float.reserved(target):
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
                   switch_relocations=None, allow_switch_data=False, udivsi3_bindings=None,
                   allow_preloaded_switch=False, modsi3_bindings=None, divsi3_bindings=None,
                   double_bindings=None, double_index=None, function_thunks=False, *,
                   allow_switch_constants=False, umodsi3_bindings=None,
                   ashldi3_bindings=None, ashldi3_index=None, float_bindings=None, float_index=None,
                   allow_double_data=False, signed_runtime_profile=None):
    """Bind external Thumb calls and explicitly mapped absolute data words."""
    from switch_constants_profile import check_opt_in
    check_opt_in(allow_switch_constants, switch_relocations, data_mapping,
                 function_relocations, allow_switch_data, udivsi3_bindings,
                 allow_preloaded_switch, modsi3_bindings, divsi3_bindings,
                 double_bindings, double_index, function_thunks, umodsi3_bindings,
                 ashldi3_bindings, ashldi3_index, float_bindings, float_index)
    if signed_runtime_profile is not None and (
            signed_runtime_profile not in signed_divmod.SCHEMAS or
            type(divsi3_bindings) is not dict or type(modsi3_bindings) is not dict or
            data_mapping is not None or function_relocations is not None or switch_relocations is not None or
            allow_switch_data or allow_preloaded_switch or allow_switch_constants or function_thunks or
            any(value is not None for value in (udivsi3_bindings, double_bindings, double_index,
                umodsi3_bindings, ashldi3_bindings, ashldi3_index, float_bindings, float_index)) or allow_double_data):
        raise ValueError('signed divmod linking requires its isolated canonical selector')
    if image["type"] != 1 or mapping is None:
        raise ValueError("linked calls require a relocatable object and config/functions.json")
    if type(function_thunks) is not bool or function_thunks and (
            function_relocations is None or allow_switch_data or
            allow_preloaded_switch or udivsi3_bindings is not None or modsi3_bindings is not None or
            divsi3_bindings is not None or double_bindings is not None or double_index is not None):
        raise ValueError("function thunks require isolated typed function bindings")
    if type(allow_switch_data) is not bool:
        raise ValueError("switch-data binding opt-in must be Boolean")
    if type(allow_preloaded_switch) is not bool:
        raise ValueError("preloaded-switch binding opt-in must be Boolean")
    if function_relocations is not None and \
            (not isinstance(function_relocations, dict) or function_relocations):
        raise ValueError("function-address bindings require an empty collection")
    if switch_relocations is not None and \
            (not isinstance(switch_relocations, dict) or switch_relocations):
        raise ValueError("switch bindings require an empty collection")
    if udivsi3_bindings is not None and \
            (not isinstance(udivsi3_bindings, dict) or udivsi3_bindings):
        raise ValueError("division bindings require an empty collection")
    if modsi3_bindings is not None and \
            (not isinstance(modsi3_bindings, dict) or modsi3_bindings):
        raise ValueError("signed remainder bindings require an empty collection")
    if divsi3_bindings is not None and (not isinstance(divsi3_bindings, dict) or divsi3_bindings):
        raise ValueError("signed quotient bindings require an empty collection")
    if umodsi3_bindings is not None and (type(umodsi3_bindings) is not dict or umodsi3_bindings):
        raise ValueError("unsigned remainder bindings require an empty collection")
    if ashldi3_bindings is not None and (type(ashldi3_bindings) is not dict or ashldi3_bindings):
        raise ValueError("ashldi3 bindings require an empty collection")
    if ashldi3_index is not None and ashldi3_bindings is None:
        raise ValueError("ashldi3 index requires its binding context")
    if float_bindings is not None and (type(float_bindings) is not dict or float_bindings):
        raise ValueError("software-float bindings require an empty collection")
    if float_index is not None and float_bindings is None:
        raise ValueError("software-float index requires its binding context")
    if type(allow_double_data) is not bool or allow_double_data and \
            (double_bindings is None or data_mapping is None):
        raise ValueError("software-double data requires isolated explicit call and object mappings")
    if double_bindings is not None:
        if not isinstance(double_bindings, dict) or double_bindings or \
                data_mapping is not None and not allow_double_data or \
                function_relocations is not None or allow_switch_data or \
                allow_preloaded_switch or udivsi3_bindings is not None or divsi3_bindings is not None or \
                float_bindings is not None:
            raise ValueError("software double requires isolated empty call bindings")
        software_double.verify_identity(rom_image, mapping, double_index)
    elif double_index is not None:
        raise ValueError("software-double index requires its binding context")
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
                if is_udivsi3_address(value) or modsi3.reserved(value) or divsi3.reserved(value) or umodsi3.reserved(value) or ashldi3.reserved(value) or software_double.reserved(value) or software_float.reserved(value):
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
            left_shift = target_symbol["name"] in ("__ashldi3", "__lshrdi3")
            unsigned_remainder = target_symbol["name"] == "__umodsi3"
            quotient = target_symbol["name"] == "__divsi3"
            remainder = target_symbol["name"] in ("__modsi3", modsi3.ADDRESSED_NAME)
            double_operation = target_symbol["name"] in software_double.OPERATIONS or (
                double_bindings is not None and
                software_double.shared_division_call(target_symbol["name"], divsi3.ADDRESS))
            float_operation = target_symbol["name"] in software_float.OPERATIONS and not (
                double_operation and double_bindings is not None)
            if float_operation:
                if float_bindings is None:
                    raise ValueError("software float requires its canonical target-machine profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == target_symbol["name"] for item in image["symbols"]) != 1:
                    raise ValueError("software float requires one undefined global function symbol")
                software_float.verify_identity(rom_image, mapping, float_index)
                target = software_float.OPERATIONS[target_symbol["name"]]
                candidates = []
            elif left_shift:
                if ashldi3_bindings is None:
                    raise ValueError("ashldi3 requires its canonical target-machine profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == target_symbol["name"] for item in image["symbols"]) != 1:
                    raise ValueError("ashldi3 requires one undefined global function symbol")
                shift = ashldi3.for_bindings({address + relocation: target_symbol["name"]})
                shift.verify_identity(rom_image, mapping, ashldi3_index)
                target = shift.ADDRESS
                candidates = []
            elif double_operation:
                if double_bindings is None:
                    raise ValueError("software double requires its explicit canonical profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == target_symbol["name"] for item in image["symbols"]) != 1:
                    raise ValueError("software double requires one undefined global function symbol")
                target = software_double.call_target(target_symbol["name"])
                candidates = []
            elif unsigned_remainder:
                if umodsi3_bindings is None:
                    raise ValueError("unsigned remainder requires its canonical constant-divisor profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == "__umodsi3" for item in image["symbols"]) != 1:
                    raise ValueError("unsigned remainder requires one undefined global function symbol")
                umodsi3.verify_identity(rom_image, mapping)
                target = umodsi3.ADDRESS
                candidates = []
            elif quotient:
                if divsi3_bindings is None:
                    raise ValueError("signed quotient requires its canonical positive-constant profile")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == "__divsi3" for item in image["symbols"]) != 1:
                    raise ValueError("signed quotient requires one undefined global function symbol")
                divsi3.verify_identity(rom_image, mapping)
                target = divsi3.ADDRESS
                candidates = []
            elif remainder:
                if modsi3_bindings is None:
                    raise ValueError("signed remainder requires its isolated binding profile")
                if double_bindings is not None and target_symbol["name"] != "__modsi3":
                    raise ValueError("software-double composition requires canonical __modsi3 provenance")
                if target_symbol["section"] or target_symbol["bind"] != 1 or \
                        target_symbol["type"] not in (0, 2) or target_symbol["value"] or \
                        sum(item["name"] == target_symbol["name"] for item in image["symbols"]) != 1:
                    raise ValueError("signed remainder requires one undefined global function symbol")
                modsi3.verify_identity(rom_image, mapping)
                target = modsi3.ADDRESS
                candidates = []
            elif division:
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
                if is_udivsi3_address(target) or modsi3.reserved(target) or divsi3.reserved(target) or umodsi3.reserved(target) or ashldi3.reserved(target) or software_double.reserved(target) or software_float.reserved(target):
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
            if division or remainder or quotient or double_operation or unsigned_remainder or left_shift or float_operation:
                if len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM or \
                        instruction.operands[0].imm != address + relocation:
                    raise ValueError("division call relocation has a noncanonical addend")
                bindings = (float_bindings if float_operation else ashldi3_bindings if left_shift else umodsi3_bindings if unsigned_remainder else
                            double_bindings if double_operation else divsi3_bindings if quotient else
                            modsi3_bindings if remainder else udivsi3_bindings)
                bindings[address + relocation] = target_symbol["name"]
            positions = set(range(relocation, relocation + 4))
            if positions & occupied:
                raise ValueError("overlapping call relocations")
            occupied.update(positions)
            calls[address + relocation] = target
            targets[target_symbol["name"]] = target
    if signed_runtime_profile is not None and (not divsi3_bindings or not modsi3_bindings or
            set(modsi3_bindings.values()) != {'__modsi3'}):
        raise ValueError('signed divmod requires both canonical original runtime relocations')
    if float_bindings:
        if udivsi3_bindings or modsi3_bindings or divsi3_bindings or umodsi3_bindings or ashldi3_bindings or \
                double_bindings is not None or function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("software float excludes other runtime, switch, function and thunk profiles")
        for target_name in set(targets) - {value[0] for value in data_relocations.values()}:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("software-float calls require unique undefined global functions")
    if ashldi3_bindings:
        shift = ashldi3.for_bindings(ashldi3_bindings)
        if any(target != shift.ADDRESS for target in calls.values()) or udivsi3_bindings or modsi3_bindings or divsi3_bindings or umodsi3_bindings or \
                double_bindings is not None or function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("ashldi3 excludes other runtime, switch, function and thunk profiles")
        for target_name in set(targets) - {value[0] for value in data_relocations.values()}:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("ashldi3 calls require unique undefined global functions")
    if umodsi3_bindings:
        if udivsi3_bindings or modsi3_bindings or divsi3_bindings or double_bindings is not None or \
                function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("unsigned remainder excludes other runtime, switch, function and thunk profiles")
        for target_name in set(targets) - {value[0] for value in data_relocations.values()}:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("unsigned remainder calls require unique undefined global functions")
    if double_bindings is not None:
        if not double_bindings or data_relocations and not allow_double_data or \
                modsi3_bindings is not None and not modsi3_bindings or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("software double requires canonical operations and isolated typed data without thunks")
        for target_name in set(targets) - {binding[0] for binding in data_relocations.values()}:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("software-double calls require unique undefined global functions")
    if divsi3_bindings:
        if udivsi3_bindings or modsi3_bindings and signed_runtime_profile is None or data_relocations or function_relocations or \
                switch_relocations or any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("signed quotient excludes other runtime, literal, switch and thunk profiles")
        for target_name in targets:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("signed quotient calls require unique undefined global functions")
    if modsi3_bindings:
        aliases = set(modsi3_bindings.values())
        if aliases not in ({"__modsi3"}, {modsi3.ADDRESSED_NAME}) or \
                double_bindings is not None and aliases != {"__modsi3"} or \
                udivsi3_bindings or function_relocations or switch_relocations and double_bindings is None or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()) or \
                aliases == {modsi3.ADDRESSED_NAME} and data_relocations:
            raise ValueError("signed remainder excludes mixed aliases, addressed calls with data, and other profiles")
        for target_name in set(targets) - {value[0] for value in data_relocations.values()}:
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"] or definitions[0]["section"] or \
                    definitions[0]["bind"] != 1 or definitions[0]["type"] not in (0, 2):
                raise ValueError("signed remainder calls require unique undefined globals")
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
    if not function_thunks and function_relocations and any(target in RUNTIME_HELPERS for target in targets):
        raise ValueError("function-address evidence does not support runtime call thunks")
    if switch_relocations:
        if not function_thunks and ((data_relocations and not (
                allow_switch_data or double_bindings is not None and allow_double_data)) or function_relocations or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values())):
            raise ValueError("switch evidence excludes object, callback and runtime-thunk bindings")
        data_names = {binding[0] for binding in data_relocations.values()}
        for target_name in targets:
            if target_name not in data_names and not (
                    function_thunks and target_name in function_thunk.ALIASES) and not (double_bindings is not None and
                    (software_double.call_target(target_name) is not None or target_name == "__modsi3")):
                function_address_target(target_name, entries, address, symbol["size"], rom_size)
            definitions = [item for item in image["symbols"] if item["name"] == target_name]
            if len(definitions) != 1 or definitions[0]["value"]:
                raise ValueError("switch calls require unique zero-valued undefined symbols")
        relocated = bytearray(image["text"][:symbol["size"]])
        for position, addend in switch_relocations.items():
            struct.pack_into("<I", relocated, position, address + addend)
        for position, (_, value) in data_relocations.items():
            struct.pack_into("<I", relocated, position, value)
        if function_thunks:
            from thunk_pool_switch import layout as pool_layout
            for position, (_, value) in function_relocations.items():
                struct.pack_into("<I", relocated, position, value)
            layout = pool_layout(bytes(relocated), address, switch_relocations)
        else:
            layout = (switch_layout(bytes(relocated), address, switch_relocations)
                      if double_bindings is not None else selected_switch_layout(
                          bytes(relocated), address, switch_relocations,
                          data_relocations if data_relocations else None, allow_preloaded_switch,
                          allow_switch_constants=allow_switch_constants))
        if "preload" in layout and calls:
            raise ValueError("preloaded switches do not support calls")
    if not (calls or data_relocations or function_relocations or switch_relocations) or \
            any(item["name"] and not item["section"] and item["name"] not in targets
                for item in image["symbols"]):
        raise ValueError("unresolved symbols outside the permitted bindings")
    function_thunk.verify_data_bindings(calls, data_relocations, data_symbols, entries)
    return calls, targets, data_relocations


def linked_function_bytes(original, linked, name, address, calls, targets, data_relocations=None,
                          function_relocations=None, switch_relocations=None,
                          allow_switch_data=False, udivsi3_bindings=None,
                          allow_preloaded_switch=False, modsi3_bindings=None, divsi3_bindings=None,
                          double_bindings=None, function_thunks=False, *,
                          allow_switch_constants=False, umodsi3_bindings=None, ashldi3_bindings=None, float_bindings=None,
                          allow_double_data=False, signed_runtime_profile=None):
    """Validate exact placement and the linker's complete modification surface."""
    if signed_runtime_profile is not None and (
            signed_runtime_profile not in signed_divmod.SCHEMAS or
            not divsi3_bindings or not modsi3_bindings or
            set(divsi3_bindings.values()) != {'__divsi3'} or
            set(modsi3_bindings.values()) != {'__modsi3'} or
            data_relocations or function_relocations or switch_relocations or
            allow_switch_data or allow_preloaded_switch or allow_switch_constants or function_thunks or
            any(value is not None for value in (udivsi3_bindings, double_bindings,
                umodsi3_bindings, ashldi3_bindings, float_bindings)) or allow_double_data):
        raise ValueError('linked signed divmod requires its isolated canonical selector')
    from switch_constants_profile import check_opt_in
    check_opt_in(allow_switch_constants, switch_relocations, data_relocations or None,
                 function_relocations, allow_switch_data, udivsi3_bindings,
                 allow_preloaded_switch, modsi3_bindings, divsi3_bindings,
                 double_bindings, function_thunks, umodsi3_bindings, ashldi3_bindings, float_bindings)
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
    if double_bindings is not None and float_bindings is not None:
        raise ValueError("linked software float and double require isolated contexts")
    if type(allow_double_data) is not bool or allow_double_data and double_bindings is None:
        raise ValueError("linked software-double data requires its explicit runtime context")
    function_relocations = function_relocations or {}
    if function_thunks:
        if type(function_thunks) is not bool or \
                not any(name in function_thunk.ALIASES for name in targets) or \
                allow_switch_data or allow_preloaded_switch or udivsi3_bindings is not None or \
                modsi3_bindings is not None or divsi3_bindings is not None or double_bindings is not None:
            raise ValueError("linked function-thunk bindings are incomplete or mixed")
    elif function_relocations and any(name in RUNTIME_HELPERS for name in targets):
        raise ValueError("linked function literals exclude call thunks without their profile")
    switch_relocations = switch_relocations or {}
    float_targets = {name: target for name, target in targets.items()
                     if software_float.reserved(target) and not (
                         double_bindings is not None and software_double.shared_float_call(name, target) or
                         ashldi3_bindings and target == ashldi3.for_bindings(ashldi3_bindings).ADDRESS)}
    if float_targets:
        if type(float_bindings) is not dict or not float_bindings or \
                any(alias not in software_float.OPERATIONS or calls.get(site) != software_float.OPERATIONS[alias]
                    for site, alias in float_bindings.items()) or \
                float_targets != {alias: software_float.OPERATIONS[alias] for alias in float_bindings.values()} or \
                set(float_bindings) != {site for site, target in calls.items() if software_float.reserved(target)} or \
                udivsi3_bindings or modsi3_bindings or divsi3_bindings or umodsi3_bindings or ashldi3_bindings or \
                double_bindings is not None or function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("linked software-float bindings are incomplete or mixed")
    elif float_bindings:
        raise ValueError("software-float bindings have no linked runtime")
    shift = ashldi3.for_bindings(ashldi3_bindings) if ashldi3_bindings else ashldi3
    shift_targets = {name: target for name, target in targets.items() if shift.reserved(target)}
    if shift_targets:
        if any(target != shift.ADDRESS for target in calls.values()) or \
                shift_targets != {"__" + shift.NAME: shift.ADDRESS} or \
                type(ashldi3_bindings) is not dict or not ashldi3_bindings or \
                any(calls.get(site) != shift.ADDRESS
                    for site, alias in ashldi3_bindings.items()) or \
                set(ashldi3_bindings) != {site for site, target in calls.items() if shift.reserved(target)} or \
                udivsi3_bindings or modsi3_bindings or divsi3_bindings or umodsi3_bindings or \
                double_bindings is not None or function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("linked ashldi3 bindings are incomplete or mixed")
    elif ashldi3_bindings:
        raise ValueError("ashldi3 bindings have no linked runtime")
    unsigned_remainder_targets = {name: target for name, target in targets.items()
                                  if umodsi3.reserved(target)}
    if unsigned_remainder_targets:
        if unsigned_remainder_targets != {"__umodsi3": umodsi3.ADDRESS} or \
                type(umodsi3_bindings) is not dict or not umodsi3_bindings or \
                any(alias != "__umodsi3" or calls.get(site) != umodsi3.ADDRESS
                    for site, alias in umodsi3_bindings.items()) or \
                set(umodsi3_bindings) != {site for site, target in calls.items() if umodsi3.reserved(target)} or \
                udivsi3_bindings or modsi3_bindings or divsi3_bindings or double_bindings is not None or \
                function_relocations or switch_relocations or function_thunks or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("linked unsigned remainder bindings are incomplete or mixed")
    elif umodsi3_bindings:
        raise ValueError("unsigned remainder bindings have no linked runtime")
    double_targets = {name: target for name, target in targets.items()
                      if (software_double.reserved(target) or
                          double_bindings is not None and software_double.shared_division_call(name, target)) and not (
                          float_bindings is not None and software_double.shared_float_call(name, target) or
                          ashldi3_bindings and target == ashldi3.for_bindings(ashldi3_bindings).ADDRESS)}
    if double_targets:
        if not isinstance(double_bindings, dict) or not double_bindings or \
                any(software_double.call_target(alias) is None or calls.get(site) != software_double.call_target(alias)
                    for site, alias in double_bindings.items()) or \
                double_targets != {alias: software_double.call_target(alias) for alias in double_bindings.values()} or \
                set(double_bindings) != {site for site, target in calls.items() if software_double.reserved(target) or
                                             target in software_double.DIVISION_OPERATION.values()} or \
                udivsi3_bindings or divsi3_bindings or \
                modsi3_bindings is not None and not modsi3_bindings or \
                data_relocations and not allow_double_data or \
                function_relocations or allow_switch_data or allow_preloaded_switch or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("linked software-double bindings are incomplete or mixed")
    elif double_bindings is not None:
        raise ValueError("software-double bindings have no linked runtime")
    quotient_targets = {name: target for name, target in targets.items()
                        if divsi3.reserved(target) and not (double_bindings is not None and
                            software_double.shared_division_call(name, target))}
    if quotient_targets:
        if quotient_targets != {"__divsi3": divsi3.ADDRESS} or \
                not isinstance(divsi3_bindings, dict) or not divsi3_bindings or \
                any(alias != "__divsi3" or calls.get(site) != divsi3.ADDRESS
                    for site, alias in divsi3_bindings.items()) or \
                set(divsi3_bindings) != {site for site, target in calls.items() if divsi3.reserved(target)} or \
                udivsi3_bindings or modsi3_bindings and signed_runtime_profile is None or data_relocations or function_relocations or \
                switch_relocations or any(target in RUNTIME_HELPERS.values() for target in targets.values()):
            raise ValueError("linked signed quotient bindings are incomplete or mixed")
    elif divsi3_bindings:
        raise ValueError("signed quotient bindings have no linked runtime")
    remainder_targets = {name: target for name, target in targets.items() if modsi3.reserved(target)}
    if remainder_targets:
        if not isinstance(modsi3_bindings, dict) or not modsi3_bindings or \
                set(modsi3_bindings.values()) not in ({"__modsi3"}, {modsi3.ADDRESSED_NAME}) or \
                double_bindings is not None and set(modsi3_bindings.values()) != {"__modsi3"} or \
                remainder_targets != {next(iter(modsi3_bindings.values())): modsi3.ADDRESS} or \
                any(calls.get(site) != modsi3.ADDRESS for site in modsi3_bindings) or \
                set(modsi3_bindings) != {site for site, target in calls.items()
                                         if modsi3.reserved(target)} or \
                udivsi3_bindings or function_relocations or switch_relocations and double_bindings is None or \
                any(target in RUNTIME_HELPERS.values() for target in targets.values()) or \
                modsi3.ADDRESSED_NAME in remainder_targets and data_relocations:
            raise ValueError("linked signed remainder bindings are incomplete or mixed")
    elif modsi3_bindings:
        raise ValueError("signed remainder bindings have no linked runtime")
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
    if type(allow_preloaded_switch) is not bool:
        raise ValueError("preloaded-switch binding opt-in must be Boolean")
    if switch_relocations and not function_thunks and ((data_relocations and not (
            allow_switch_data or double_bindings is not None and allow_double_data)) or function_relocations):
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
                (target_name in function_names or switch_relocations or udivsi3_bindings or
                 modsi3_bindings or divsi3_bindings or double_bindings or umodsi3_bindings or ashldi3_bindings or float_bindings) and \
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
        if function_thunks:
            from thunk_pool_switch import layout as pool_layout
            layout = pool_layout(linked["text"][:after["size"]], address, switch_relocations)
            # The original local section words grant only this finite table.
            # Prove all case/guard edges, literal roles and frame/return joins
            # against the fully linked complete symbol, not linear decoding.
            verify_leaf_instructions(linked["text"][:after["size"]], address, True, calls,
                                     function_thunk_context={"pool_switch": switch_relocations})
        else:
            layout = (switch_layout(linked["text"][:after["size"]], address, switch_relocations)
                      if double_bindings is not None else selected_switch_layout(
                          linked["text"][:after["size"]], address, switch_relocations,
                          data_relocations if data_relocations else None, allow_preloaded_switch,
                          allow_switch_constants=allow_switch_constants))
        if "preload" in layout and calls:
            raise ValueError("preloaded switches do not support calls")
    if any(before_byte != after_byte and position not in patched
           for position, (before_byte, after_byte)
           in enumerate(zip(original["text"], linked["text"]))):
        raise ValueError("linker changed bytes outside permitted relocations")
    return linked["text"][:after["size"]]


def link_calls(runner, workspace, args, original, address, mapping, rom_size,
               rom_image=b'', data_mapping=None, function_relocations=None, switch_relocations=None,
               allow_switch_data=False, udivsi3_bindings=None, allow_preloaded_switch=False,
               modsi3_bindings=None, divsi3_bindings=None, double_bindings=None, double_index=None,
               function_thunks=False, *, allow_switch_constants=False, umodsi3_bindings=None,
               ashldi3_bindings=None, ashldi3_index=None, float_bindings=None, float_index=None,
               allow_double_data=False, signed_runtime_profile=None):
    name = f"func_{address:08X}"
    calls, targets, data_relocations = call_bindings(original, name, address, mapping,
                                                    rom_size, rom_image, data_mapping,
                                                    function_relocations, switch_relocations,
                                                    allow_switch_data, udivsi3_bindings,
                                                    allow_preloaded_switch, modsi3_bindings, divsi3_bindings,
                                                    double_bindings, double_index, function_thunks,
                                                    allow_switch_constants=allow_switch_constants,
                                                    umodsi3_bindings=umodsi3_bindings,
                                                    ashldi3_bindings=ashldi3_bindings, ashldi3_index=ashldi3_index,
                                                    float_bindings=float_bindings, float_index=float_index,
                                                    allow_double_data=allow_double_data,
                                                    signed_runtime_profile=signed_runtime_profile)
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
                                  allow_switch_data, udivsi3_bindings, allow_preloaded_switch,
                                  modsi3_bindings, divsi3_bindings, double_bindings, function_thunks,
                                  allow_switch_constants=allow_switch_constants,
                                  umodsi3_bindings=umodsi3_bindings,
                                  ashldi3_bindings=ashldi3_bindings, float_bindings=float_bindings,
                                  allow_double_data=allow_double_data,
                                  signed_runtime_profile=signed_runtime_profile),
            calls, data_relocations)


def verify_data_literals(instructions, address, data_relocations):
    literals = {((instruction.address + 4) & ~3) + operand.mem.disp
                for instruction in instructions for operand in instruction.operands
                if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and
                operand.mem.base == ARM_REG_PC and not operand.mem.index}
    if any(address + relocation not in literals for relocation in data_relocations):
        raise ValueError("data relocation is not a reachable PC-relative literal-pool load")


_addressed_replay_active = ContextVar("addressed_remainder_replay_active", default=False)


def verify_addressed_modsi3_source(root, address, data, rom, mapping, source_digest, framed):
    if _addressed_replay_active.get():
        raise ValueError("recursive addressed-runtime replay is unsupported")
    token = _addressed_replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping:
            raise ValueError("addressed-runtime replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("addressed-runtime replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("addressed-runtime source snapshot differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured)
            with runner.workspace() as workspace:
                _, _, original = compile_object(
                    runner, workspace, args, captured, address,
                    candidates[0].relative_to(root).as_posix())
                bindings = {}
                got, calls, literals = link_calls(
                    runner, workspace, args, original, address, mapping, len(rom), rom,
                    modsi3_bindings=bindings)
                if not bindings or set(bindings.values()) != {modsi3.ADDRESSED_NAME} or \
                        literals or got != data:
                    raise ValueError("legacy remainder lacks fresh canonical addressed-call provenance")
                instructions = verify_leaf_instructions(
                    got, address, True, calls, modsi3_context=(rom, mapping, bindings))
                if uses_stack_frame(instructions) != framed:
                    raise ValueError("addressed-runtime replay frame profile differs")
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = subprocess.run([sys.executable, str(checker), "--quiet", "--addr",
                                     f"0x{address:08X}", "--json"] +
                                    [str(path) for path in source_paths(captured, address)],
                                    capture_output=True, text=True)
            findings, _ = plausibility_result(result, address)
            if findings or source_fingerprint(captured, address) != source_digest:
                raise ValueError("addressed-runtime snapshot changed or source is implausible")
        if source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or report_rom_path(root) != selected_rom or \
                Path(selected_rom).read_bytes() != rom:
            raise ValueError("addressed-runtime replay inputs changed")
        return instructions
    finally:
        _addressed_replay_active.reset(token)


def verify_divsi3(data, address, rom, mapping, manifest, *, selector=None):
    divsi3.schema(selector)
    framed = selector == divsi3.FRAMED_SELECTOR
    fields = {"runtime", "calls", "divisors"} | ({"frame"} if framed else set())
    if not isinstance(manifest, dict) or set(manifest) != fields or \
            framed and manifest.get("frame") is not True or \
            manifest["runtime"] != divsi3.RUNTIME or \
            not isinstance(manifest["calls"], list) or not isinstance(manifest["divisors"], list):
        raise ValueError("invalid signed quotient manifest")
    divsi3.verify_identity(rom, mapping)
    entries = json.loads(mapping)
    calls, bindings = {}, {}
    previous = -4
    for record in manifest["calls"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid signed quotient call binding")
        offset, name = record
        if type(offset) is not int or not isinstance(name, str) or offset % 2 or \
                offset < previous + 4 or offset < 0 or offset + 4 > len(data):
            raise ValueError("signed quotient calls must be ordered nonoverlapping instructions")
        previous = offset
        if name == "__divsi3":
            calls[address + offset] = divsi3.ADDRESS
            bindings[address + offset] = name
        else:
            calls[address + offset] = function_address_target(name, entries, address, len(data), len(rom))
    expected = {}
    previous = -1
    for record in manifest["divisors"]:
        if not isinstance(record, list) or len(record) != 2:
            raise ValueError("invalid signed quotient divisor binding")
        offset, divisor = record
        if type(offset) is not int or offset <= previous or address + offset not in bindings or \
                type(divisor) is not int or not 1 <= divisor <= 0x7FFFFFFF:
            raise ValueError("signed quotient divisors must be ordered positive signed32 constants")
        previous = offset
        expected[address + offset] = divisor
    if not bindings or set(expected) != set(bindings):
        raise ValueError("signed quotient divisors must cover every runtime call exactly once")
    observed = {}
    instructions = verify_leaf_instructions(
        data, address, True, calls, divsi3_context=(rom, mapping, bindings, observed),
        signed_quotient_profile=selector)
    if observed != expected:
        raise ValueError("signed quotient divisors disagree with final incoming CFG facts")
    return instructions


_signed_replay_active = ContextVar("signed_quotient_replay_active", default=False)


def verify_divsi3_source(root, address, data, rom, mapping, source_digest, manifest, *, selector=None):
    divsi3.schema(selector)
    if _signed_replay_active.get():
        raise ValueError("recursive signed quotient replay is unsupported")
    token = _signed_replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping:
            raise ValueError("signed quotient replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("signed quotient replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_signed_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("signed quotient source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured,
                            timeout=SIGNED_REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                bindings = {}
                got, calls, literals = link_calls(runner, workspace, args, original, address,
                                                  mapping, len(rom), rom, divsi3_bindings=bindings)
                fresh_calls = [[site - address, bindings.get(site, f"func_{target:08X}")]
                               for site, target in sorted(calls.items())]
                if not bindings or set(bindings.values()) != {"__divsi3"} or literals or \
                        got != data or fresh_calls != manifest.get("calls"):
                    raise ValueError("signed quotient lacks fresh canonical ELF provenance")
                instructions = verify_divsi3(got, address, rom, mapping, manifest, selector=selector)
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, SIGNED_REPLAY_TIMEOUT)
            findings, _ = plausibility_result(result, address)
            if findings or source_fingerprint(captured, address) != source_digest:
                raise ValueError("signed quotient captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
            raise ValueError("signed quotient replay inputs changed")
        return instructions
    finally:
        _signed_replay_active.reset(token)


_unsigned_remainder_replay_active = ContextVar("unsigned_remainder_replay_active", default=False)


def verify_umodsi3_source(root, address, data, rom, mapping, data_mapping, source_digest, manifest):
    if _unsigned_remainder_replay_active.get():
        raise ValueError("recursive unsigned remainder replay is unsupported")
    token = _unsigned_remainder_replay_active.set(True)
    try:
        root = Path(root)
        candidates = list((root / "src").rglob(f"{address:08X}.c"))
        if len(candidates) != 1 or source_fingerprint(root, address) != source_digest or \
                mapping_snapshot(root) != mapping or data_snapshot(root) != data_mapping:
            raise ValueError("unsigned remainder replay inputs differ")
        selected_rom = report_rom_path(root)
        if Path(selected_rom).read_bytes() != rom:
            raise ValueError("unsigned remainder replay ROM differs")
        args = argparse.Namespace(cc=DEFAULT_CC, cpp=DEFAULT_CPP, assembler=DEFAULT_AS,
                                  objcopy=DEFAULT_OBJCOPY, linker=DEFAULT_LD, flags=DEFAULT_FLAGS)
        (root / "build").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="ffta_unsigned_remainder_replay_", dir=root / "build") as directory:
            captured = Path(directory)
            for path in source_paths(root, address):
                destination = captured / path.relative_to(root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            if source_fingerprint(captured, address) != source_digest:
                raise ValueError("unsigned remainder source capture differs")
            runner = Runner(DEFAULT_CC, "Ubuntu", DEFAULT_WSL_PATH, root=captured,
                            timeout=SIGNED_REPLAY_TIMEOUT)
            with runner.workspace() as workspace:
                _, _, original = compile_object(runner, workspace, args, captured, address,
                                                 candidates[0].relative_to(root).as_posix())
                bindings = {}
                got, calls, literals = link_calls(runner, workspace, args, original, address,
                                                  mapping, len(rom), rom, data_mapping=data_mapping,
                                                  umodsi3_bindings=bindings)
                objects = parse_data_symbols(data_mapping) if literals else {}
                fresh_data = [[offset, name, value - objects[name]]
                              for offset, (name, value) in sorted(literals.items())]
                fresh_calls = [[site - address, bindings.get(site, f"func_{target:08X}")]
                               for site, target in sorted(calls.items())]
                if not bindings or set(bindings.values()) != {"__umodsi3"} or \
                        got != data or fresh_calls != manifest.get("calls") or fresh_data != manifest.get("data"):
                    raise ValueError("unsigned remainder lacks fresh canonical ELF provenance")
                instructions = umodsi3.verify(got, address, rom, mapping, data_mapping, manifest)
            checker = Path(__file__).resolve().with_name("plausible.py")
            result = _run_replay_process(
                [sys.executable, str(checker), "--quiet", "--addr", f"0x{address:08X}", "--json"] +
                [str(path) for path in source_paths(captured, address)], captured, SIGNED_REPLAY_TIMEOUT)
            findings, _ = plausibility_result(result, address)
            if findings or source_fingerprint(captured, address) != source_digest:
                raise ValueError("unsigned remainder captured source changed or is implausible")
        if source_fingerprint(root, address) != source_digest or mapping_snapshot(root) != mapping or \
                data_snapshot(root) != data_mapping or \
                report_rom_path(root) != selected_rom or Path(selected_rom).read_bytes() != rom:
            raise ValueError("unsigned remainder replay inputs changed")
        return instructions
    finally:
        _unsigned_remainder_replay_active.reset(token)


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


def verify_modsi3(data, address, rom, mapping, data_mapping, manifest):
    if not isinstance(manifest, dict) or set(manifest) != {"runtime", "calls", "operands", "data"} or \
            manifest["runtime"] != modsi3.RUNTIME or \
            any(not isinstance(manifest[key], list) for key in ("calls", "operands", "data")):
        raise ValueError("invalid signed remainder manifest")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("signed remainder requires a function mapping")
    objects = parse_data_symbols(data_mapping) if manifest["data"] else {}
    calls = {}
    bindings = {}
    literals = {}
    occupied = set()
    for kind in ("calls", "data"):
        previous = -1
        for record in manifest[kind]:
            if not isinstance(record, list) or len(record) != (2 if kind == "calls" else 3):
                raise ValueError("invalid signed remainder binding")
            offset, name = record[:2]
            if type(offset) is not int or not isinstance(name, str) or offset <= previous or \
                    offset < 0 or offset + 4 > len(data):
                raise ValueError("signed remainder bindings must be ordered complete words")
            previous = offset
            positions = set(range(offset, offset + 4))
            if occupied & positions:
                raise ValueError("signed remainder bindings overlap")
            occupied.update(positions)
            if kind == "calls":
                if offset % 2:
                    raise ValueError("signed remainder call is misaligned")
                if name == "__modsi3":
                    calls[address + offset] = modsi3.ADDRESS
                    bindings[address + offset] = name
                else:
                    calls[address + offset] = function_address_target(
                        name, entries, address, len(data), len(rom))
            else:
                addend = record[2]
                if (address + offset) % 4 or name not in objects or type(addend) is not int or \
                        not -0x80000000 <= addend <= 0x7FFFFFFF:
                    raise ValueError("invalid signed remainder object binding")
                value = objects[name] + addend
                if not 0 <= value <= 0xFFFFFFFF or address <= value < address + len(data) or \
                        not modsi3.supported_data(objects[name], len(rom)) or \
                        not modsi3.supported_data(value, len(rom)) or \
                        is_udivsi3_address(value) or modsi3.reserved(value) or divsi3.reserved(value) or umodsi3.reserved(value) or ashldi3.reserved(value) or software_double.reserved(value) or software_float.reserved(value) or \
                        struct.unpack_from("<I", data, offset)[0] != value:
                    raise ValueError("signed remainder literal differs or uses a forbidden address")
                literals[offset] = (name, value)
    expected = [[site - address, "signed16", "nonzero"] for site in sorted(bindings)]
    if not expected or manifest["operands"] != expected or any(
            not isinstance(record, list) or len(record) != 3 or type(record[0]) is not int
            for record in manifest["operands"]):
        raise ValueError("signed remainder operands must cover every runtime call exactly once")
    instructions = verify_leaf_instructions(
        data, address, True, calls, modsi3_context=(rom, mapping, bindings))
    verify_data_literals(instructions, address, literals)
    address_literals = set()
    for instruction in instructions:
        for operand in instruction.operands:
            if instruction.mnemonic == "ldr" and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((instruction.address + 4) & ~3) + operand.mem.disp - address
                value = struct.unpack_from("<I", data, offset)[0]
                if modsi3.address_literal(value):
                    address_literals.add(offset)
    if address_literals != set(literals):
        raise ValueError("signed remainder address-domain literals require exact mapped-data coverage")
    return instructions


def function_address_bindings(data, address, rom, mapping, data_mapping, manifest, *,
                              allow_empty_functions=False):
    if type(allow_empty_functions) is not bool or mapping is None or not isinstance(manifest, dict) or \
            set(manifest) != {"calls", "data", "functions"} or \
            any(not isinstance(records, list) for records in manifest.values()) or \
            not manifest["functions"] and not allow_empty_functions:
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
                if is_udivsi3_address(value) or modsi3.reserved(value) or divsi3.reserved(value) or umodsi3.reserved(value) or ashldi3.reserved(value) or software_double.reserved(value) or software_float.reserved(value):
                    raise ValueError("division runtime cannot be bound through an object addend")
            if struct.unpack_from("<I", data, offset)[0] != value:
                raise ValueError("function-address literal does not equal its binding")
            literals[offset] = (name, value)
    return calls, literals


def verify_function_addresses(data, address, rom, mapping, data_mapping, manifest):
    calls, literals = function_address_bindings(data, address, rom, mapping, data_mapping, manifest)
    instructions = verify_leaf_instructions(data, address, True, calls)
    verify_data_literals(instructions, address, literals)
    return instructions, CALL_SUMMARY if calls else "closed leaf CFG"


def verify_function_buffers(data, address, rom, mapping, manifest):
    calls, literals = function_address_bindings(data, address, rom, mapping, None, manifest)
    if manifest["data"] or not calls:
        raise ValueError("function-buffer evidence requires direct calls and excludes data bindings")
    proof = FunctionBufferCallProof(rom, mapping, stack_arguments=True)
    if proof.span(address) != data:
        raise ValueError("function-buffer caller requires an exact complete mapped span")
    instructions = verify_leaf_instructions(data, address, True, calls, buffer_proof=proof)
    if not proof.dependencies:
        raise ValueError("function-buffer evidence requires an inspected buffer call")
    verify_data_literals(instructions, address, literals)
    return instructions, proof


def preloaded_switch_encoding(data, address, literal):
    if type(literal) is not int or literal < 20 or literal + 4 > len(data):
        return None
    dispatch = literal - 14
    if (address + dispatch) % 4 != 2:
        return None
    words = struct.unpack_from("<7H", data, dispatch - 6)
    accumulator = words[3] & 7
    selector = (words[3] >> 3) & 7
    base = (words[0] >> 8) & 7
    bound = words[1] & 255
    expected = (0x4804 | base << 8, 0x2800 | selector << 8 | bound,
                0xD8FD, 0x0080 | selector << 3 | accumulator,
                0x1800 | base << 6 | accumulator << 3 | accumulator,
                0x6800 | accumulator << 3 | accumulator,
                0x4687 | accumulator << 3)
    if len({accumulator, selector, base}) != 3 or words != expected:
        return None
    return dispatch, accumulator, selector, base, bound


def selected_switch_layout(data, address, relocations, data_relocations=None,
                           allow_preloaded_switch=False, *, allow_switch_constants=False):
    from switch_constants_profile import check_opt_in, layout
    check_opt_in(allow_switch_constants, relocations, data_relocations, allow_preloaded_switch)
    if allow_switch_constants:
        return layout(data, address, relocations)
    if type(allow_preloaded_switch) is not bool:
        raise ValueError("preloaded-switch layout opt-in must be Boolean")
    if allow_preloaded_switch and isinstance(relocations, dict) and relocations and \
            all(type(offset) is int for offset in relocations) and \
            preloaded_switch_encoding(data, address, min(relocations)) is not None:
        return preloaded_switch_layout(data, address, relocations, data_relocations)
    return switch_layout(data, address, relocations, data_relocations)


def preloaded_switch_layout(data, address, relocations, data_relocations):
    if type(address) is not int or address % 2 or not isinstance(relocations, dict) or \
            not 2 <= len(relocations) <= 257:
        raise ValueError("preloaded switch requires one bounded local word table")
    for offset, addend in relocations.items():
        if type(offset) is not int or type(addend) is not int or offset < 0 or \
                (address + offset) % 4 or offset + 4 > len(data) or addend < 0 or \
                addend % 2 or addend + 2 > len(data) or \
                struct.unpack_from("<I", data, offset)[0] != address + addend:
            raise ValueError("invalid preloaded local word or section-relative target")
    literal = min(relocations)
    table = literal + 4
    table_end = table + 4 * (len(relocations) - 1)
    if sorted(relocations) != list(range(literal, table_end, 4)) or \
            relocations[literal] != table or \
            any(relocations[offset] < table_end for offset in range(table, table_end, 4)):
        raise ValueError("preloaded switch requires adjacent words and forward cases")
    encoding = preloaded_switch_encoding(data, address, literal)
    if encoding is None:
        raise ValueError("preloaded switch requires its exact backward guard and four-op dispatch")
    dispatch, accumulator, selector, base, bound = encoding
    if bound != len(relocations) - 2 or data[dispatch + 8:dispatch + 10] != b"\x00\x00":
        raise ValueError("preloaded switch bound or alignment does not match its table")
    if not isinstance(data_relocations, dict) or len(data_relocations) != 1:
        raise ValueError("preloaded switch requires exactly one mapped object word")
    offset, binding = next(iter(data_relocations.items()))
    if type(offset) is not int or offset != literal - 4 or \
            not isinstance(binding, (tuple, list)) or len(binding) != 2 or \
            not isinstance(binding[0], str) or not binding[0] or \
            type(binding[1]) is not int or not 0 <= binding[1] <= 0xFFFFFFFF or \
            address <= binding[1] < address + len(data) or \
            struct.unpack_from("<I", data, offset)[0] != binding[1]:
        raise ValueError("invalid preloaded switch object word")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    sequence = list(decoder.disasm(data[dispatch - 6:dispatch + 8], address + dispatch - 6))
    if len(sequence) != 7 or any(item.size != 2 for item in sequence) or \
            tuple(item.mnemonic for item in sequence) != \
            ("ldr", "cmp", "bhi", "lsls", "adds", "ldr", "mov") or \
            any(item.cc not in (ARM_CC_AL, ARM_CC_INVALID)
                for position, item in enumerate(sequence) if position != 2):
        raise ValueError("preloaded dispatch decoding disagrees with its encodings")

    def register(operand, name):
        return operand.type == ARM_OP_REG and decoder.reg_name(operand.reg) == name

    def immediate(operand, value):
        return operand.type == ARM_OP_IMM and operand.imm == value

    def memory(operand, name, displacement):
        return operand.type == ARM_OP_MEM and decoder.reg_name(operand.mem.base) == name and \
            not operand.mem.index and operand.mem.disp == displacement

    operands = [item.operands for item in sequence]
    accumulator_name, selector_name, base_name = (f"r{value}" for value in (accumulator, selector, base))
    if tuple(map(len, operands)) != (2, 2, 1, 3, 3, 2, 2) or \
            not register(operands[0][0], base_name) or not memory(operands[0][1], "pc", 16) or \
            not register(operands[1][0], selector_name) or not immediate(operands[1][1], bound) or \
            not immediate(operands[2][0], address + dispatch - 4) or \
            not register(operands[3][0], accumulator_name) or \
            not register(operands[3][1], selector_name) or not immediate(operands[3][2], 2) or \
            not all(register(operand, name) for operand, name in
                    zip(operands[4], (accumulator_name, accumulator_name, base_name))) or \
            not register(operands[5][0], accumulator_name) or \
            not memory(operands[5][1], accumulator_name, 0) or \
            not register(operands[6][0], "pc") or not register(operands[6][1], accumulator_name):
        raise ValueError("preloaded dispatch operands disagree with its encodings")
    return {"preload": dispatch - 6, "comparison": dispatch - 4, "guard": dispatch - 2,
            "dispatch": dispatch, "transfer": dispatch + 6, "default": dispatch - 4,
            "literal": literal, "table": table, "bound": bound,
            "relocations": [[offset, addend] for offset, addend in sorted(relocations.items())]}


def verify_preloaded_switch_cfg(data, address, instructions, edges, predecessors, switch):
    preload = address + switch["preload"]
    comparison = address + switch["comparison"]
    guard = address + switch["guard"]
    dispatch = address + switch["dispatch"]
    transfer = address + switch["transfer"]
    expected = {preload: {preload - 2}, guard: {comparison}, dispatch: {guard}}
    expected.update({current: {current - 2} for current in range(dispatch + 2, transfer + 2, 2)})
    if comparison not in instructions or any(
            current == address or predecessors.get(current) != incoming
            for current, incoming in expected.items()):
        raise ValueError("preloaded switch has an unverified predecessor edge")
    preceding = instructions[preload - 2]
    if preceding.group(CS_GRP_JUMP) or preceding.group(CS_GRP_CALL) or \
            ARM_REG_PC in preceding.regs_access()[1] or edges[preload - 2] != (preload,):
        raise ValueError("preloaded switch requires fallthrough into its table load")
    incoming = predecessors[comparison]
    if not {preload, guard} <= incoming:
        raise ValueError("preloaded switch comparison is missing its initial or loop edge")
    for predecessor in incoming - {preload, guard}:
        instruction = instructions[predecessor]
        if instruction.id != ARM_INS_B or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                edges[predecessor] != (comparison,):
            raise ValueError("preloaded switch comparison requires direct unconditional backedges")
    pending = [address]
    without_preload = set()
    while pending:
        current = pending.pop()
        if current == preload or current in without_preload:
            continue
        without_preload.add(current)
        pending.extend(edges[current])
    if comparison in without_preload:
        raise ValueError("preloaded table load does not dominate its comparison")
    reaching_guard = {comparison}
    pending = [comparison]
    while pending:
        for predecessor in predecessors[pending.pop()]:
            if predecessor not in reaching_guard:
                reaching_guard.add(predecessor)
                pending.append(predecessor)
    base = instructions[preload].operands[0].reg
    literal_loads = []
    owned = set()
    for current, instruction in instructions.items():
        if instruction.size != 2 or instruction.writeback and instruction.mnemonic not in ("push", "pop") or \
                instruction.mnemonic.startswith(("str", "stm")) or \
                any(operand.type == ARM_OP_MEM and operand.access & CS_AC_WRITE
                    for operand in instruction.operands):
            raise ValueError("preloaded switch requires read-only narrow Thumb instructions")
        if current != preload and current in reaching_guard and base in instruction.regs_access()[1]:
            raise ValueError("preloaded table base is clobbered on a path to its guard")
        owned.update(range(current, current + instruction.size))
        for operand in instruction.operands:
            if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC:
                literal_loads.append(((current + 4) & ~3) + operand.mem.disp)
    literal = address + switch["literal"]
    if sorted(literal_loads) != [literal - 4, literal]:
        raise ValueError("preloaded switch requires exactly its two reachable literal loads")
    word_bytes = {address + offset + position for offset, _ in switch["relocations"]
                  for position in range(4)} | set(range(literal - 4, literal))
    alignment = set(range(dispatch + 8, dispatch + 10))
    if owned & (word_bytes | alignment) or \
            owned | word_bytes | alignment != set(range(address, address + len(data))):
        raise ValueError("preloaded switch does not classify every function byte")


def verify_preloaded_switches(data, address, rom, mapping, data_mapping, manifest):
    if mapping is None or not isinstance(manifest, dict) or set(manifest) != {"calls", "data", "switch"} or \
            manifest["calls"] != [] or not isinstance(manifest["data"], list) or \
            len(manifest["data"]) != 1 or not isinstance(manifest["data"][0], list) or \
            len(manifest["data"][0]) != 3:
        raise ValueError("invalid preloaded switch manifest or excluded calls")
    offset, name, addend = manifest["data"][0]
    objects = parse_data_symbols(data_mapping)
    if type(offset) is not int or not isinstance(name, str) or name not in objects or \
            type(addend) is not int or not -0x80000000 <= addend <= 0x7FFFFFFF:
        raise ValueError("invalid preloaded object binding")
    data_relocations = {offset: (name, objects[name] + addend)}
    descriptor = manifest["switch"]
    fields = {"preload", "comparison", "guard", "dispatch", "transfer", "default",
              "literal", "table", "bound", "relocations"}
    if not isinstance(descriptor, dict) or set(descriptor) != fields or \
            any(type(descriptor[field]) is not int for field in fields - {"relocations"}) or \
            not isinstance(descriptor["relocations"], list):
        raise ValueError("invalid preloaded switch descriptor")
    relocations = {}
    previous = -1
    for record in descriptor["relocations"]:
        if not isinstance(record, list) or len(record) != 2 or \
                any(type(value) is not int for value in record) or record[0] <= previous:
            raise ValueError("preloaded relocations require unique ordered integer pairs")
        previous = record[0]
        relocations[record[0]] = record[1]
    if preloaded_switch_layout(data, address, relocations, data_relocations) != descriptor:
        raise ValueError("preloaded switch descriptor does not match its bytes")
    entries = json.loads(mapping)
    if not isinstance(entries, list):
        raise ValueError("preloaded switch requires a function mapping list")
    callers = [entry for entry in entries if int(entry["rom"], 16) & ~1 == address & ~1]
    if len(callers) != 1 or callers[0].get("mode") != "thumb" or \
            int(callers[0]["rom"], 16) != address or \
            int(callers[0]["end"], 16) != address + len(data) or \
            not ROM_BASE <= address < address + len(data) <= ROM_BASE + len(rom) or \
            rom[address - ROM_BASE:address - ROM_BASE + len(data)] != data:
        raise ValueError("preloaded switch requires its exact mapped full ROM span")
    instructions = verify_leaf_instructions(data, address, True,
                                            switch_relocations=relocations,
                                            switch_data_relocations=data_relocations,
                                            preloaded_switch=True)
    return instructions, PRELOADED_SWITCH_CONTROL_FLOW


def switch_layout(data, address, relocations, data_relocations=None, *, interposed_words=0):
    """Derive a guarded dispatch; the five-word pool needs separate reached-load proof."""
    if type(interposed_words) is not int or interposed_words not in (0, 5) or \
            interposed_words and data_relocations is not None:
        raise ValueError("unsupported interposed switch pool")
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

    def instruction(offset, size=2):
        if offset < 0 or offset % 2 or offset + 2 > len(data):
            return None
        decoded = next(decoder.disasm(data[offset:offset + 4], address + offset, count=1), None)
        return decoded if decoded is not None and decoded.size == size else None

    def branch_target(decoded, mnemonic):
        if decoded is None or decoded.mnemonic != mnemonic or len(decoded.operands) != 1 or \
                decoded.operands[0].type != ARM_OP_IMM:
            return None
        return decoded.operands[0].imm - address

    candidates = []
    for dispatch in ((literal - 14, literal - 16) if data_relocations is not None
                     else (literal - 10 - interposed_words * 4,
                           literal - 12 - interposed_words * 4)):
        if data_relocations is None:
            pool_start = literal - interposed_words * 4
            if dispatch < 0 or (address + dispatch + 13) & ~3 != address + pool_start or \
                    any(data[dispatch + 10:pool_start]):
                continue
        elif (address + dispatch + 13) & ~3 != address + literal - 4 or \
                any(data[dispatch + 10:literal - 4]):
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
        for guard_size in (4, 6, 8):
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
                if guard_size == 6:
                    default = branch_target(instruction(guard + 2), "b")
                else:
                    # agbcc uses a local BL when the shared default block
                    # is beyond a narrow branch. Shape recognition grants
                    # no call permission: its enclosing CFG must separately
                    # prove sole ownership, LR overwrite and frame restoration.
                    jump = instruction(guard + 2, size=4)
                    if jump is None:
                        continue
                    from local_long_branch_profile import target as local_target
                    try:
                        default = local_target(jump, address, address + len(data)) - address
                    except ValueError:
                        continue
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


def thumb_literal_stack_adjustment(instruction, data, address):
    """Recognize only an adjacent literal LDR / ADD SP, low-register pair.

    The caller must also prove that the LDR is the ADD's sole CFG predecessor.
    Literal ownership is checked with every other reachable PC-relative load.
    No scalar constant or pointer/index fact is introduced by this rule.
    """
    offset = instruction.address - address
    if instruction.size != 2 or offset < 2 or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
        return None
    addition = int.from_bytes(instruction.bytes, "little")
    if (addition & 0xFFC7) != 0x4485:
        return None
    load = struct.unpack_from("<H", data, offset - 2)[0]
    if (load & 0xF800) != 0x4800 or ((load >> 8) & 7) != ((addition >> 3) & 7):
        return None
    literal = ((instruction.address + 2) & ~3) + 4 * (load & 0xFF)
    if not address <= literal or literal + 4 > address + len(data):
        raise ValueError("stack adjustment literal is outside the function")
    displacement = struct.unpack_from("<i", data, literal - address)[0]
    if not displacement or displacement % 4 or abs(displacement) > 4096:
        raise ValueError("stack adjustment literal is not a bounded aligned displacement")
    return displacement // 4


def thumb_shifted_stack_constant(instruction, data, address):
    """Recognize MOVS Rd,#N; LSLS Rd,Rd,#S; ADD Rd,SP,Rd only.

    Both intermediate edges must be proved unique by the CFG verifier. This
    value is solely an input to bounded stack-alias formation, not an index fact.
    """
    offset = instruction.address - address
    if instruction.size != 2 or offset < 4 or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            instruction.bytes[1] != 0x44 or not 0x68 <= instruction.bytes[0] <= 0x6F:
        return None
    register = instruction.bytes[0] - 0x68
    moved, shifted = struct.unpack_from("<HH", data, offset - 4)
    if (moved & 0xFF00) != (0x2000 | (register << 8)) or (shifted & 0xF800) or \
            (shifted & 7) != register or ((shifted >> 3) & 7) != register:
        return None
    shift = (shifted >> 6) & 31
    if not shift:
        return None
    value = (moved & 255) << shift
    if value > 0xFFFFFFFF:
        raise ValueError("shifted stack offset overflows a 32-bit scalar")
    return ARM_REG_R0 + register, value


def thumb_literal_stack_constant(instruction, data, address):
    """Recognize adjacent literal LDR Rd / ADD Rd,SP,Rd only.

    The load must be the addition's sole CFG predecessor, and the literal must
    remain outside reachable code. This value forms only a bounded stack alias.
    """
    offset = instruction.address - address
    if instruction.size != 2 or offset < 2 or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            instruction.bytes[1] != 0x44 or not 0x68 <= instruction.bytes[0] <= 0x6F:
        return None
    register = instruction.bytes[0] - 0x68
    load = struct.unpack_from("<H", data, offset - 2)[0]
    if (load & 0xF800) != 0x4800 or ((load >> 8) & 7) != register:
        return None
    literal = ((instruction.address + 2) & ~3) + 4 * (load & 255)
    if not address <= literal or literal + 4 > address + len(data):
        raise ValueError("stack alias literal is outside the function")
    value = struct.unpack_from("<I", data, literal - address)[0]
    if value % 4 or value > 4096:
        raise ValueError("stack alias literal is not a bounded aligned offset")
    return ARM_REG_R0 + register, value


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


def stack_alias_store(stack, pointer_slots, aliases, return_registers,
                      offset, width, register):
    """Apply an existing scalar store's bounded stack/provenance effects."""
    if width not in (1, 2, 4) or offset % width or \
            not -4 * len(stack) <= offset or offset + width > 0:
        raise ValueError("stack-alias access is unaligned or outside the tracked frame")
    pointer_word = offset - offset % 4
    if pointer_word in pointer_slots and width != 4:
        raise ValueError("partial access to a pointer-bearing local word")
    if register in aliases:
        raise ValueError("stack aliases cannot be stored or spilled")
    slot = (offset + 4 * len(stack)) // 4
    stack[slot] = (width == 4 and register in return_registers,
                   stack[slot][1], stack[slot][2])
    pointer_slots.pop(pointer_word, None)


def thumb_stack_alias_stm(instruction, aliases, depth):
    """Recognize exact Thumb-1 STMIA writeback through a known stack alias.

    Base-in-list forms are deliberately excluded. All source registers must be
    low scalar registers; callers apply the ordinary store effects to each word
    and retain the exact one-past writeback alias for later uses and CFG joins.
    """
    operands = instruction.operands
    if not instruction.mnemonic.startswith("stm") or not operands or \
            operands[0].type != ARM_OP_REG or operands[0].reg not in aliases:
        return None
    encoded = int.from_bytes(instruction.bytes, "little")
    base = ARM_REG_R0 + ((encoded >> 8) & 7)
    registers = tuple(ARM_REG_R0 + bit for bit in range(8) if encoded & (1 << bit))
    read, written = instruction.regs_access()
    if instruction.size != 2 or len(instruction.bytes) != 2 or \
            encoded & 0xF800 != 0xC000 or \
            instruction.mnemonic != "stm" or not instruction.writeback or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
            not registers or base in registers or \
            tuple(operand.reg for operand in operands) != (base, *registers) or \
            any(operand.type != ARM_OP_REG or operand.shift.type or
                operand.shift.value or operand.subtracted for operand in operands) or \
            set(read) != {base, *registers} or set(written) != {base}:
        raise ValueError("unsupported stack-alias STM encoding or register list")
    offset = aliases[base]
    if offset % 4 or not -4 * depth <= offset or offset + 4 * len(registers) > 0:
        raise ValueError("stack-alias STM is unaligned or outside the tracked frame")
    if any(register in aliases for register in registers):
        raise ValueError("stack aliases cannot be stored or spilled")
    return base, offset, registers


CALLER_CLOBBERED = (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2,
                    ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)


def merge_possible_aliases(previous, incoming):
    merged = dict(previous)
    for register, offset in incoming:
        if register in merged and merged[register] != offset:
            raise ValueError("inconsistent possible pointer offsets at control-flow join")
        merged[register] = offset
    return tuple(sorted(merged.items()))


def stack_alias_overwritten_before_use(data, address, successor, register, decoder):
    """Prove a differing Thumb join alias is killed on every path before observation."""
    if not ARM_REG_R0 <= register <= ARM_REG_R12:
        return False
    end = address + len(data)
    pending, edges, safe = [successor], {}, set()
    while pending:
        current = pending.pop()
        if current in edges:
            continue
        if current % 2 or not address <= current < end:
            return False
        instruction = next(decoder.disasm(data[current - address:current - address + 4],
                                         current, count=1), None)
        if instruction is None or current + instruction.size > end or \
                instruction.id == ARM_INS_IT or any(group in instruction.groups
                    for group in (CS_GRP_CALL, CS_GRP_INT)):
            return False
        read, written = instruction.regs_access()
        if register in read:
            return False
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        if register in written and unconditional:
            edges[current] = ()
            safe.add(current)
            continue
        if instruction.id == ARM_INS_B:
            if len(instruction.operands) != 1 or instruction.operands[0].type != ARM_OP_IMM:
                return False
            targets = (instruction.operands[0].imm,)
            if not unconditional:
                targets += (current + instruction.size,)
        elif CS_GRP_JUMP in instruction.groups or ARM_REG_PC in written:
            # This includes returns: no result/scratch alias is discarded at exit.
            return False
        else:
            targets = (current + instruction.size,)
        edges[current] = targets
        pending.extend(targets)
    # Cycles with an un-killed alias are deliberately not a proof of lifetime end.
    while True:
        newly_safe = {current for current, targets in edges.items()
                      if current not in safe and targets and all(target in safe for target in targets)}
        if not newly_safe:
            return successor in safe
        safe.update(newly_safe)


class BufferCallProof:
    word_provenance = False
    callee_frames = False
    single_word_stores = False
    exact_alias_state_budget = None

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
        if is_udivsi3_address(address) or modsi3.reserved(address) or divsi3.reserved(address) or umodsi3.reserved(address) or ashldi3.reserved(address) or software_double.reserved(address) or software_float.reserved(address):
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

    def validate_pointer_value(self, offset, stack):
        self.access(offset, 1, stack)

    def argument_constants(self, constants):
        return {}

    def extra_constant(self, instruction, data, address, constants):
        return None

    def clear_extra_call_constants(self, constants):
        pass

    def finish_call_constants(self, constants, result, *, site=None, target=None):
        self.clear_extra_call_constants(constants)

    def word_context(self, words, frame_base, root_frame, watched=()):
        return {}

    def word_result(self, aliases, words):
        return dict(aliases)

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        arguments = {register: offset for register, offset in aliases.items()
                     if register in CALLER_CLOBBERED}
        slots = slots or {}
        if slots and not self.stack_arguments:
            raise ValueError("stack-passed buffer pointers require versioned evidence")
        for offset in slots:
            self.access(offset, 4, stack)
        incoming = {offset + 4 * len(stack): target for offset, target in slots.items()}
        return self.check_arguments(address, arguments, stack, incoming, frozenset(slots),
                                    constants=self.argument_constants(constants or {}), site=site,
                                    **self.word_context(words or {}, -4*len(stack), site,
                                        tuple(register for register in aliases if register not in CALLER_CLOBBERED)))

    def inspect(self, address, data):
        instructions = verify_leaf_instructions(data, address, True,
                                                buffer_proof=self if self.stack_arguments else None,
                                                call_resolver=self.target)
        return instructions, {}

    def check_arguments(self, address, arguments, stack, incoming, protected, *, constants=None, site=None,
                        words=None, frame_base=None, root_frame=None, watched=()):
        if not arguments and not incoming and not words and not watched:
            return self.word_result({}, {})
        if ARM_REG_LR in arguments:
            raise ValueError("buffer pointer cannot be passed through the link register")
        for offset in (*arguments.values(), *incoming.values()):
            self.validate_pointer_value(offset, stack)
        if address in self.active or len(self.active) >= 16:
            raise ValueError("recursive or excessively nested buffer calls are unsupported")
        self.active.add(address)
        try:
            if self.callee_frames and frame_base != -4 * len(stack):
                raise ValueError("callee frame origin differs from the exact incoming live stack")
            data = self.span(address)
            instructions, finite_transfers = self.inspect(address, data)
            self.dependencies[address] = data
            by_address = {instruction.address: instruction for instruction in instructions}
            states = {address: (tuple(sorted(arguments.items())), 0,
                                tuple(sorted((constants or {}).items())),
                                tuple(sorted((words or {}).items())))}
            if self.callee_frames:
                states[address] += (tuple(stack),)
            exact_budget = self.exact_alias_state_budget
            if exact_budget is not None and (type(exact_budget) is not int or
                    not 1 <= exact_budget <= 4096 or not self.callee_frames):
                raise ValueError("exact buffer alternatives require bounded callee frame states")
            path_states = {address: {states[address]}} if exact_budget is not None else None
            pending = [(address, states[address])] if path_states is not None else [address]
            path_state_count = 1
            path_context = None
            if path_states is not None:
                path_context = self.alias_path_context(address, arguments, stack, incoming,
                    protected, constants or {}, words or {}, frame_base, root_frame, watched, site)
                self.observe_alias_state(path_context, address, states[address])
            returned = ()
            exact_returns = {}
            returned_words = None
            while pending:
                if path_states is None:
                    current = pending.pop()
                else:
                    current, incoming_state = pending.pop()
                    states[current] = incoming_state
                instruction = by_address[current]
                aliases = dict(states[current][0])
                depth = states[current][1]
                constants = dict(states[current][2])
                words = dict(states[current][3])
                if self.callee_frames:
                    stack = list(states[current][4])
                call_alternatives = None
                operands = instruction.operands
                registers = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
                read, written = instruction.regs_access()
                if set(written) & set(watched):
                    raise ValueError("descriptor call does not prove preservation of a live alias register")
                returning = current not in finite_transfers and (instruction.mnemonic == "bx" or
                             instruction.mnemonic == "pop" and ARM_REG_PC in registers or
                             instruction.mnemonic == "mov" and registers and registers[0] == ARM_REG_PC)
                if instruction.mnemonic == "push":
                    if set(registers) & aliases.keys():
                        raise ValueError("buffer pointers cannot be pushed or spilled")
                    depth += len(registers)
                    if self.callee_frames:
                        stack[:0] = [(False, True, False)] * len(registers)
                elif instruction.mnemonic == "pop":
                    for register in registers:
                        aliases.pop(register, None)
                        constants.pop(register, None)
                    depth -= len(registers)
                    if self.callee_frames:
                        del stack[:len(registers)]
                elif (adjustment := thumb_stack_adjustment(instruction)) is not None or \
                        (adjustment := thumb_literal_stack_adjustment(instruction, data, address)) is not None:
                    depth -= adjustment
                    if self.callee_frames:
                        if adjustment < 0:
                            stack[:0] = [(False, False, True)] * -adjustment
                        else:
                            del stack[:adjustment]
                elif CS_GRP_CALL in instruction.groups:
                    passed = {register: offset for register, offset in aliases.items()
                              if register in CALLER_CLOBBERED}
                    nested = {offset + depth * 4: target for offset, target in incoming.items()}
                    result = self.check_arguments(operands[0].imm, passed, stack, nested, protected,
                        constants=self.argument_constants(constants), site=current,
                        **self.word_context(words, frame_base-4*depth if frame_base is not None else None, root_frame,
                            tuple(sorted(set(watched) | {register for register in aliases if register not in CALLER_CLOBBERED}))))
                    call_alternatives = getattr(result, 'alternatives', None)
                    if self.word_provenance:
                        words = dict(result.words)
                    for register in CALLER_CLOBBERED:
                        aliases.pop(register, None)
                        constants.pop(register, None)
                    self.finish_call_constants(constants, result, site=current, target=operands[0].imm)
                    aliases.update(result)
                elif self.single_word_stores and self.apply_single_store(
                        instruction, aliases, constants, stack, words, root_frame=root_frame,
                        context={'address':address, 'call_site':site, 'frame_base':frame_base,
                            'arguments':sorted(arguments.items()), 'incoming':sorted(incoming.items()),
                            'protected':sorted(protected), 'watched':sorted(watched)}):
                    pass
                else:
                    assignment = register_alias_assignment(instruction, aliases)
                    if self.callee_frames:
                        assignment = stack_alias_assignment(instruction, aliases, len(stack), constants)
                        if assignment is not None and assignment[2] == ARM_REG_SP:
                            self.access(assignment[1], 1, stack)
                            self.observe_frame_alias(address, instruction.address, assignment, stack, words,
                                frame_base, root_frame, watched, arguments, incoming, protected, constants)
                    allowed = {assignment[2]} if assignment is not None else set()
                    loaded = None
                    word_constant = None
                    word_load = pointer_store = False
                    if self.word_provenance:
                        loaded, word_constant, word_load, pointer_store = self.word_memory(
                            instruction, aliases, constants, stack, words,
                            frame_base-4*depth, protected, root_frame=root_frame)
                    if self.callee_frames and pointer_store:
                        allowed.add(operands[0].reg)
                    for operand in operands:
                        if operand.type != ARM_OP_MEM:
                            continue
                        if not self.word_provenance and operand.mem.base == ARM_REG_SP and instruction.mnemonic == "ldr":
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
                                operands[0].type != ARM_OP_REG or \
                                operand.mem.index and not self.stack_arguments:
                            raise ValueError("unsupported buffer memory access")
                        offset = aliases[operand.mem.base] + operand.mem.disp
                        if operand.mem.index:
                            if instruction.writeback or operand.shift.type or operand.shift.value or \
                                    operand.subtracted or operand.mem.scale != 1 or operand.mem.disp:
                                raise ValueError("unsupported indexed buffer memory access")
                            if operand.mem.index not in constants or operand.mem.index in aliases:
                                raise ValueError("buffer index is not a known scalar constant")
                            offset += constants[operand.mem.index]
                        self.access(offset, width, stack)
                        if any(offset < slot + 4 and offset + width > slot for slot in protected) and not word_load:
                            raise ValueError("buffer access overlaps a pointer-bearing argument slot")
                        if instruction.mnemonic.startswith("str") and registers[0] in aliases and not pointer_store:
                            raise ValueError("buffer pointers cannot be stored or spilled")
                        if pointer_store:
                            allowed.add(registers[0])
                        allowed.add(operand.mem.base)
                    if self.stack_arguments and instruction.size == 2 and \
                            instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and \
                            instruction.mnemonic == "cmp" and len(operands) == 2 and \
                            operands[0].type == ARM_OP_REG and operands[0].reg in aliases and \
                            operands[1].type == ARM_OP_IMM and operands[1].imm == 0:
                        # A null test observes the pointer without moving or escaping it.
                        # Both successors still retain the alias and all access bounds.
                        allowed.add(operands[0].reg)
                    if (set(read) & aliases.keys()) - allowed:
                        raise ValueError("unsupported buffer pointer use or escape")
                    constant = None
                    if self.stack_arguments and instruction.size == 2 and \
                            instruction.cc in (ARM_CC_AL, ARM_CC_INVALID) and \
                            instruction.mnemonic in ("mov", "movs") and len(operands) == 2 and \
                            operands[0].type == ARM_OP_REG:
                        if operands[1].type == ARM_OP_IMM:
                            constant = operands[1].imm
                        elif operands[1].type == ARM_OP_REG:
                            constant = constants.get(operands[1].reg)
                    extra = self.extra_constant(instruction, data, address, constants)
                    if extra is not None:
                        constant = extra
                    if word_constant is not None:
                        constant = word_constant
                    for register in written:
                        aliases.pop(register, None)
                        constants.pop(register, None)
                    if constant is not None:
                        constants[operands[0].reg] = constant
                    if assignment is not None:
                        if assignment[0] in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR):
                            raise ValueError("buffer pointer cannot overwrite a control register")
                        aliases[assignment[0]] = assignment[1]
                    if loaded is not None:
                        aliases[loaded[0]] = loaded[1]
                if current in finite_transfers:
                    successors = finite_transfers[current]
                elif returning:
                    if self.callee_frames:
                        for offset in aliases.values():
                            self.validate_pointer_value(offset, stack)
                    if aliases and not self.stack_arguments:
                        raise ValueError("buffer pointer escapes through a return register")
                    if any(register not in CALLER_CLOBBERED or register == ARM_REG_LR
                           for register in aliases):
                        raise ValueError("buffer pointer escapes through an unrestored register")
                    if path_states is not None:
                        result_state = (tuple(sorted(aliases.items())), tuple(sorted(words.items())))
                        exact_returns[result_state] = self.word_result(aliases, words)
                        self.observe_alias_return(path_context, current, incoming_state, result_state)
                    else:
                        returned = merge_possible_aliases(returned, aliases.items())
                        returned_words = words if returned_words is None else {slot:value for slot,value in returned_words.items() if words.get(slot)==value}
                    successors = ()
                elif instruction.id == ARM_INS_B:
                    successors = (operands[0].imm,)
                    if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
                        successors += (current + instruction.size,)
                else:
                    successors = (current + instruction.size,)
                if self.callee_frames:
                    if len(stack) * 4 > 4096 or frame_base - 4 * depth != -4 * len(stack):
                        raise ValueError("callee live stack exceeds its exact bounded frame")
                    self.prune_words(words, stack)
                outgoing = (tuple(sorted(aliases.items())), depth, tuple(sorted(constants.items())), tuple(sorted(words.items())))
                if self.callee_frames:
                    outgoing += (tuple(stack),)
                if call_alternatives is not None:
                    if path_states is None:
                        raise ValueError("disjunctive call results require exact caller alternatives")
                    outgoings = []
                    for result in call_alternatives:
                        result_aliases = dict(aliases)
                        result_aliases.update(result)
                        result_words = dict(result.words)
                        self.prune_words(result_words, stack)
                        outgoings.append((tuple(sorted(result_aliases.items())), depth,
                            tuple(sorted(constants.items())), tuple(sorted(result_words.items())), tuple(stack)))
                else:
                    outgoings = [outgoing]
                for successor, outgoing in ((target, state) for target in successors for state in outgoings):
                    if path_states is not None:
                        previous_paths = path_states.get(successor, set())
                        if previous_paths and any(state[1] != depth or state[4] != outgoing[4]
                                                  for state in previous_paths):
                            raise ValueError("inconsistent live callee frame at exact alternative join")
                        self.observe_alias_state(path_context, successor, outgoing,
                                                 current, incoming_state)
                        if outgoing not in previous_paths:
                            if path_state_count >= exact_budget:
                                raise ValueError("exact buffer alternative state budget exhausted")
                            path_states.setdefault(successor, set()).add(outgoing)
                            path_state_count += 1
                            pending.append((successor, outgoing))
                        continue
                    if successor not in states:
                        states[successor] = outgoing
                        pending.append(successor)
                    elif states[successor] != outgoing:
                        previous = states[successor]
                        if not self.stack_arguments or previous[1] != depth:
                            raise ValueError("inconsistent buffer aliases at control-flow join")
                        if self.callee_frames and previous[4] != outgoing[4]:
                            raise ValueError("inconsistent live callee frame at control-flow join")
                        merged = (merge_possible_aliases(previous[0], outgoing[0]), depth,
                                  tuple((register, value) for register, value in previous[2]
                                        if constants.get(register) == value),
                                  tuple((slot,value) for slot,value in previous[3] if words.get(slot)==value))
                        if self.callee_frames:
                            merged += (previous[4],)
                        if merged != previous:
                            states[successor] = merged
                            pending.append(successor)
            if self.callee_frames:
                self.complete_frame(address, data, instructions)
            if path_states is not None:
                return self.alternative_result([exact_returns[key] for key in sorted(exact_returns)])
            return self.word_result(returned, returned_words or {})
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


class FunctionBufferCallProof(BufferCallProof):
    def target(self, address):
        if address in RUNTIME_HELPERS.values():
            raise ValueError("function-buffer evidence excludes runtime call thunks in inspected dependencies")
        return super().target(address)


def verify_leaf_instructions(data, address, thumb, validated_calls=None,
                             buffer_proof=None, call_resolver=None, switch_relocations=None,
                             switch_data_relocations=None, udivsi3_context=None,
                             preloaded_switch=False, modsi3_context=None, divsi3_context=None,
                             inert_spin_context=None, double_context=None, function_thunk_context=None, *,
                             allow_switch_constants=False, allow_switch_scalar_frame=False,
                             umodsi3_context=None, ashldi3_context=None, float_context=None,
                             acyclic_state_budget=None, ignored_leaf_alias_proof=None,
                             signed_quotient_profile=None, stack_pointer_compare_profile=None,
                             signed_runtime_context=None, remainder_inventory_context=None):
    """Verify a local CFG, optionally applying validated direct-call ABI summaries."""
    if remainder_inventory_context is not None:
        import zero_aware_remainder_inventory as remainder_inventory
        if not thumb or buffer_proof is not None or call_resolver is not None or preloaded_switch or \
                allow_switch_constants or allow_switch_scalar_frame or any(value is not None for value in (
                    switch_relocations, switch_data_relocations, udivsi3_context, modsi3_context,
                    divsi3_context, inert_spin_context, double_context, function_thunk_context,
                    umodsi3_context, ashldi3_context, float_context, acyclic_state_budget,
                    ignored_leaf_alias_proof, signed_quotient_profile, stack_pointer_compare_profile,
                    signed_runtime_context)):
            raise ValueError('zero-aware remainder requires its isolated inventory context')
        remainder_inventory.prepare(data, address, validated_calls or {}, remainder_inventory_context)
        modsi3_context = (remainder_inventory_context[0], remainder_inventory_context[1],
                         remainder_inventory_context[3])
    if signed_runtime_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or preloaded_switch or \
                allow_switch_constants or allow_switch_scalar_frame or any(value is not None for value in (
                    switch_relocations, switch_data_relocations, udivsi3_context, modsi3_context,
                    divsi3_context, inert_spin_context, double_context, function_thunk_context,
                    umodsi3_context, ashldi3_context, float_context, acyclic_state_budget,
                    ignored_leaf_alias_proof, signed_quotient_profile, stack_pointer_compare_profile)):
            raise ValueError('signed divmod requires its isolated canonical Thumb context')
        div_bindings, mod_bindings = signed_divmod.prepare(
            data, address, validated_calls or {}, signed_runtime_context)
        divsi3_context = (signed_runtime_context[0], signed_runtime_context[1], div_bindings, {})
        modsi3_context = (signed_runtime_context[0], signed_runtime_context[1], mod_bindings)
    if stack_pointer_compare_profile is not None:
        if type(stack_pointer_compare_profile) is not str or \
                stack_pointer_compare_profile != sp_compare.SELECTOR or not thumb or \
                buffer_proof is not None or call_resolver is not None or preloaded_switch or \
                allow_switch_constants or allow_switch_scalar_frame or any(context is not None for context in (
                    switch_relocations, switch_data_relocations, udivsi3_context, modsi3_context,
                    divsi3_context, inert_spin_context, double_context, function_thunk_context,
                    umodsi3_context, ashldi3_context, float_context, acyclic_state_budget,
                    ignored_leaf_alias_proof, signed_quotient_profile)):
            raise ValueError('SP comparison requires its isolated inventory-only Thumb selector')
        if any(target in RUNTIME_HELPERS.values() or function_thunk.reserved(target) or
               is_udivsi3_address(target) or modsi3.reserved(target) or divsi3.reserved(target) or
               umodsi3.reserved(target) or ashldi3.reserved(target) or software_double.reserved(target) or
               software_float.reserved(target) for target in (validated_calls or {}).values()):
            raise ValueError('SP comparison inventory excludes runtime and thunk calls')
    divsi3.schema(signed_quotient_profile)
    if signed_quotient_profile is not None and (
            not thumb or divsi3_context is None or buffer_proof is not None or
            call_resolver is not None or preloaded_switch or allow_switch_constants or
            allow_switch_scalar_frame or acyclic_state_budget is not None or
            ignored_leaf_alias_proof is not None or any(context is not None for context in (
                switch_relocations, switch_data_relocations, udivsi3_context, modsi3_context,
                inert_spin_context, double_context, function_thunk_context, umodsi3_context,
                ashldi3_context, float_context))):
        raise ValueError("framed signed quotient requires its isolated canonical Thumb context")
    if ignored_leaf_alias_proof is not None:
        from ignored_leaf_alias_profile import IgnoredLeafAliasProof
        if type(ignored_leaf_alias_proof) is not IgnoredLeafAliasProof or \
                acyclic_state_budget is None or ignored_leaf_alias_proof.caller != address or \
                ignored_leaf_alias_proof.size != len(data) or \
                ignored_leaf_alias_proof.calls != dict(validated_calls or {}):
            raise ValueError("ignored leaf aliases require their isolated exact acyclic caller context")
    if acyclic_state_budget is not None:
        if type(acyclic_state_budget) is not int or not 1 <= acyclic_state_budget <= 4096:
            raise ValueError("acyclic path-state budget must be an integer in 1..4096")
        if not thumb or buffer_proof is not None or call_resolver is not None or any(
                context is not None for context in (switch_relocations, switch_data_relocations,
                    udivsi3_context, modsi3_context, divsi3_context, inert_spin_context,
                    double_context, function_thunk_context, umodsi3_context,
                    ashldi3_context, float_context)) or preloaded_switch or \
                allow_switch_constants or allow_switch_scalar_frame:
            raise ValueError("acyclic path states require an ordinary isolated Thumb CFG")
    from switch_constants_profile import check_opt_in, layout as constants_layout
    check_opt_in(allow_switch_constants, switch_relocations, buffer_proof, call_resolver,
                 switch_data_relocations, udivsi3_context, preloaded_switch, modsi3_context,
                 divsi3_context, inert_spin_context, double_context, function_thunk_context,
                 umodsi3_context, ashldi3_context, float_context)
    if allow_switch_constants and not thumb:
        raise ValueError("switch constants require Thumb mode")
    if type(allow_switch_scalar_frame) is not bool or \
            allow_switch_scalar_frame and not (allow_switch_constants and thumb):
        raise ValueError("scalar switch frames require explicit Boolean two-constant Thumb policy")
    exact_alias_budget = (buffer_proof.exact_alias_state_budget
                          if buffer_proof is not None else None)
    if exact_alias_budget is not None:
        if type(exact_alias_budget) is not int or not 1 <= exact_alias_budget <= 4096 or \
                not thumb or acyclic_state_budget is not None or not buffer_proof.callee_frames or \
                any(context is not None for context in (switch_relocations, switch_data_relocations,
                    udivsi3_context, modsi3_context, divsi3_context, inert_spin_context,
                    double_context, function_thunk_context, umodsi3_context, ashldi3_context,
                    float_context)) or preloaded_switch or allow_switch_constants or allow_switch_scalar_frame:
            raise ValueError("exact alias frame states require their isolated bounded Thumb buffer context")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    decoder.detail = True
    switch = None
    reserved = set()
    division_constants = None
    signed_numeric = False
    if float_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None or switch_data_relocations is not None or \
                udivsi3_context is not None or modsi3_context is not None or divsi3_context is not None or \
                umodsi3_context is not None or ashldi3_context is not None or inert_spin_context is not None or \
                double_context is not None or function_thunk_context is not None or preloaded_switch:
            raise ValueError("software float requires an isolated ordinary direct-call context")
        software_float.verify_context(data, address, validated_calls or {}, float_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               modsi3.reserved(target) or divsi3.reserved(target) or umodsi3.reserved(target) or
               ashldi3.reserved(target) or software_double.reserved(target) and not
               software_double.shared_float_call(float_context[3].get(site), target)
               for site, target in (validated_calls or {}).items()):
            raise ValueError("software float excludes other runtimes and thunks")
    if ashldi3_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None or switch_data_relocations is not None or \
                udivsi3_context is not None or modsi3_context is not None or divsi3_context is not None or \
                umodsi3_context is not None or inert_spin_context is not None or double_context is not None or \
                function_thunk_context is not None or preloaded_switch:
            raise ValueError("ashldi3 requires an isolated ordinary direct-call context")
        if type(ashldi3_context) is not tuple or len(ashldi3_context) != 4:
            raise ValueError("shift requires an isolated canonical runtime context")
        shift = ashldi3.for_bindings(ashldi3_context[3])
        shift.verify_context(data, address, validated_calls or {}, ashldi3_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               modsi3.reserved(target) or divsi3.reserved(target) or umodsi3.reserved(target) or
               (software_double.reserved(target) or software_float.reserved(target)) and
               target != shift.ADDRESS
               for target in (validated_calls or {}).values()):
            raise ValueError("ashldi3 excludes other runtimes and thunks")
    if umodsi3_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None or switch_data_relocations is not None or \
                udivsi3_context is not None or modsi3_context is not None or divsi3_context is not None or \
                inert_spin_context is not None or double_context is not None or \
                function_thunk_context is not None or preloaded_switch:
            raise ValueError("unsigned remainder requires an isolated ordinary direct-call context")
        umodsi3.verify_context(data, address, validated_calls or {}, umodsi3_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               modsi3.reserved(target) or divsi3.reserved(target) or ashldi3.reserved(target) or software_double.reserved(target) or software_float.reserved(target)
               for target in (validated_calls or {}).values()):
            raise ValueError("unsigned remainder excludes other runtimes and thunks")
    if function_thunk_context is not None:
        if type(function_thunk_context) is not dict or set(function_thunk_context) not in (set(), {'pool_switch'}) or not thumb or \
                buffer_proof is not None or call_resolver is not None or switch_relocations is not None or \
                switch_data_relocations is not None or udivsi3_context is not None or modsi3_context is not None or \
                divsi3_context is not None or inert_spin_context is not None or double_context is not None or preloaded_switch:
            raise ValueError("function thunks require an isolated ordinary caller context")
        if not any(target in function_thunk.ALIASES.values() for target in (validated_calls or {}).values()) or \
                any(is_udivsi3_address(target) or modsi3.reserved(target) or divsi3.reserved(target) or
                    ashldi3.reserved(target) or software_double.reserved(target) or software_float.reserved(target) or function_thunk.reserved(target) and
                    target not in function_thunk.ALIASES.values() for target in (validated_calls or {}).values()):
            raise ValueError("function thunks require supported canonical calls without other runtimes")
    if double_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_data_relocations is not None or udivsi3_context is not None or modsi3_context is not None or \
                divsi3_context is not None or preloaded_switch:
            raise ValueError("software double requires an isolated direct-call context")
        remainder_bindings = software_double.verify_context(data, address, validated_calls or {}, double_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               (modsi3.reserved(target) and target != modsi3.ADDRESS) or
               (divsi3.reserved(target) and target != software_double.DIVISION_OPERATION["__divsi3"])
               for target in (validated_calls or {}).values()):
            raise ValueError("software double excludes other runtimes and call thunks")
        if remainder_bindings and not software_double.target_remainder_context(double_context):
            modsi3_context = (double_context[0], double_context[1], remainder_bindings)
    if inert_spin_context is not None:
        if type(inert_spin_context) is not dict or inert_spin_context or not thumb or \
                buffer_proof is not None or call_resolver is not None or switch_relocations is not None or \
                switch_data_relocations is not None or udivsi3_context is not None or \
                modsi3_context is not None or divsi3_context is not None or preloaded_switch:
            raise ValueError("inert spins require a fresh isolated Thumb direct-call context")
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               modsi3.reserved(target) or divsi3.reserved(target) or ashldi3.reserved(target) or
               (software_double.reserved(target) or software_float.reserved(target)) and not
               (double_context is not None and target in software_double.OPERATIONS.values())
               for target in (validated_calls or {}).values()):
            raise ValueError("inert spins exclude unproved arithmetic runtimes and call thunks")
    if divsi3_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None or switch_data_relocations is not None or \
                udivsi3_context is not None or modsi3_context is not None and signed_runtime_context is None or preloaded_switch:
            raise ValueError("signed quotient requires an isolated direct-call profile")
        divsi3.verify_context(data, address, validated_calls or {}, divsi3_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target) or
               modsi3.reserved(target) and not (signed_runtime_context is not None and target == modsi3.ADDRESS)
               for target in (validated_calls or {}).values()):
            raise ValueError("signed quotient excludes other runtimes and thunks")
    if modsi3_context is not None:
        if not thumb or buffer_proof is not None or call_resolver is not None or \
                switch_relocations is not None and double_context is None or switch_data_relocations is not None or \
                udivsi3_context is not None or preloaded_switch:
            raise ValueError("signed remainder requires an isolated direct-call profile")
        signed_numeric = modsi3.verify_context(data, address, validated_calls or {}, modsi3_context)
        if any(target in RUNTIME_HELPERS.values() or is_udivsi3_address(target)
               for target in (validated_calls or {}).values()):
            raise ValueError("signed remainder excludes other runtimes and thunks")
    if type(preloaded_switch) is not bool:
        raise ValueError("preloaded-switch CFG opt-in must be Boolean")
    if preloaded_switch and (not thumb or validated_calls or buffer_proof is not None or
                             call_resolver is not None or udivsi3_context is not None or
                             switch_relocations is None or switch_data_relocations is None):
        raise ValueError("preloaded switches require isolated leaf and object evidence")
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
        if allow_switch_constants:
            switch = constants_layout(data, address, switch_relocations)
            reserved.update(range(address + switch["dispatch"] + 10,
                                  address + switch["literal"]))
        else:
            layout = preloaded_switch_layout if preloaded_switch else switch_layout
            switch = layout(data, address, switch_relocations, switch_data_relocations)
        reserved.update({address + position
                    for offset in (*switch_relocations, *(switch_data_relocations or {}))
                    for position in range(offset, offset + 4)})
    if function_thunk_context == {}:
        # This is already an explicit canonical-thunk profile. Discover only the
        # exact finite five-word shape; failure grants no indirect-jump edge.
        from thunk_pool_switch import discover as pool_discover
        try:
            pool_relocations = pool_discover(data, address, list(decoder.disasm(data, address)))
        except ValueError:
            pass
        else:
            function_thunk_context = {'pool_switch': pool_relocations}
    if function_thunk_context is not None and 'pool_switch' in function_thunk_context:
        from thunk_pool_switch import layout as pool_layout
        switch_relocations = function_thunk_context['pool_switch']
        switch = pool_layout(data, address, switch_relocations)
        reserved.update(range(address + switch['dispatch'] + 10,
                              address + switch['literal']))
        reserved.update(address + offset + byte for offset in switch_relocations for byte in range(4))
    end = address + len(data)
    alignment = 2 if thumb else 4
    states = {address: (frozenset({ARM_REG_LR}), (), (), (), (), ())}
    stack_arguments = buffer_proof is not None and buffer_proof.stack_arguments
    caller_clobbered = CALLER_CLOBBERED
    pending = [address]
    path_states = None
    state_budget = acyclic_state_budget if acyclic_state_budget is not None else exact_alias_budget
    if state_budget is not None:
        path_states = {address: {states[address]}}
        pending = [(address, states[address])]
        path_state_count = 1
    instructions = {}
    owners = {}
    edges = {}
    returns = set()
    literals = set()
    calls = dict(validated_calls or {})
    seen_calls = set()
    local_branches = {}
    literal_adjustments = set()
    shifted_stack_constants = set()
    literal_stack_constants = set()
    while pending:
        if path_states is None:
            current = pending.pop()
        else:
            current, incoming_state = pending.pop()
            states[current] = incoming_state
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
        words = dict(states[current][5])
        word_mode = buffer_proof is not None and buffer_proof.word_provenance
        call_alternatives = None
        operands = instruction.operands
        registers = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        stack_operation = instruction.mnemonic in ("push", "pop")
        adjustment = thumb_stack_adjustment(instruction) if thumb else None
        if thumb and adjustment is None:
            adjustment = thumb_literal_stack_adjustment(instruction, data, address)
            if adjustment is not None:
                literal_adjustments.add(current)
        if allow_switch_scalar_frame:
            if instruction.mnemonic.startswith(("ldm", "stm")):
                raise ValueError("scalar switch frames exclude block transfers")
            if not stack_operation and adjustment is None and ARM_REG_SP in registers:
                raise ValueError("scalar switch frames exclude stack-address materialization")
        calling = CS_GRP_CALL in instruction.groups
        local_branch = (calling and double_context is not None and
                        len(operands) == 1 and operands[0].type == ARM_OP_IMM and
                        address <= operands[0].imm < end)
        if local_branch:
            from local_long_branch_profile import target as local_target
            local_branches[current] = local_target(instruction, address, end)
            calling = False
        if CS_GRP_INT in instruction.groups or calling and not (calls or call_resolver):
            raise ValueError("non-leaf calls and interrupts require linked CFG verification")
        if calling:
            if not thumb or not unconditional or instruction.id != ARM_INS_BL or \
                    instruction.size != 4 or len(operands) != 1 or operands[0].type != ARM_OP_IMM or \
                    address <= operands[0].imm < end:
                raise ValueError("call is not a validated external direct Thumb BL")
            target = operands[0].imm
            if software_float.reserved(target) and not (
                    double_context is not None and
                    software_double.shared_float_call(double_context[3].get(current), target) or
                    ashldi3_context is not None and
                    target == ashldi3.for_bindings(ashldi3_context[3]).ADDRESS):
                if float_context is None or current not in float_context[3] or \
                        software_float.OPERATIONS.get(float_context[3][current]) != target:
                    raise ValueError("software float requires its canonical runtime proof")
            if ashldi3.reserved(target):
                if ashldi3_context is None or target != ashldi3.ADDRESS or current not in ashldi3_context[3]:
                    raise ValueError("ashldi3 requires its canonical target-machine proof")
            if umodsi3.reserved(target):
                if umodsi3_context is None or target != umodsi3.ADDRESS or \
                        current not in umodsi3_context[2]:
                    raise ValueError("unsigned remainder requires its canonical constant-divisor proof")
            if software_double.reserved(target) and not (
                    float_context is not None and
                    software_double.shared_float_call(float_context[3].get(current), target) or
                    ashldi3_context is not None and
                    target == ashldi3.for_bindings(ashldi3_context[3]).ADDRESS):
                if double_context is None or current not in double_context[3] or \
                        software_double.OPERATIONS.get(double_context[3][current]) != target:
                    raise ValueError("software double requires its canonical runtime proof")
            if divsi3.reserved(target) and target != 0x0814274C and not (
                    double_context is not None and
                    software_double.shared_division_call(double_context[3].get(current), target)):
                if divsi3_context is None or target != divsi3.ADDRESS or current not in divsi3_context[2]:
                    raise ValueError("signed quotient requires its canonical positive-constant proof")
            if modsi3.reserved(target) and target != 0x0814274C and not (
                    double_context is not None and software_double.target_remainder_context(double_context) and
                    target == modsi3.ADDRESS and double_context[3].get(current) == "__modsi3"):
                if modsi3_context is None:
                    if target == modsi3.ADDRESS:
                        raise modsi3.AddressedRemainderRequired(
                            "signed remainder requires numeric proof or fresh addressed-call provenance")
                    raise ValueError("signed remainder interior targets are unsupported")
                if target != modsi3.ADDRESS or current not in modsi3_context[2]:
                    raise ValueError("signed remainder call lacks a canonical binding")
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
                if current in literal_adjustments and 4 * (len(stack) - adjustment) > 4096:
                    raise ValueError("literal stack allocation exceeds the bounded tracked frame")
                stack[:0] = [(False, False, True)] * -adjustment
            elif adjustment > len(stack):
                raise ValueError("stack-pointer adjustment leaves the tracked frame")
            else:
                del stack[:adjustment]
        if word_mode and (stack_operation or adjustment is not None):
            buffer_proof.prune_words(words, stack)
        returning = unconditional and (
            (instruction.mnemonic == "bx" and len(registers) == 1 and
             registers[0] in return_registers) or
            (instruction.mnemonic == "pop" and ARM_REG_PC in return_registers) or
            (instruction.mnemonic == "mov" and registers == (ARM_REG_PC, ARM_REG_LR)
             and ARM_REG_LR in return_registers))
        if returning:
            if stack:
                raise ValueError("return does not balance the saved stack frame")
            # IP is ABI scratch, not a result register. Keep its alias tracked
            # through calls and later uses, but an unobserved value at return
            # does not return a pointer. All other escape checks still apply.
            if stack_arguments and aliases.keys() - {ARM_REG_R12}:
                raise ValueError("local stack pointer escapes through a return register")
            returns.add(current)
            successors = ()
        elif local_branch:
            # A compiler long jump updates LR but has no call ABI clobbers
            # or continuation edge. The complete restoring-frame proof below
            # must recover the entry return independently of this new LR.
            return_registers.discard(ARM_REG_LR)
            constants.pop(ARM_REG_LR, None)
            aliases.pop(ARM_REG_LR, None)
            successors = (local_branches[current],)
        elif calling:
            if function_thunk_context is not None and operands[0].imm in function_thunk.ALIASES.values():
                target_number = (operands[0].imm - function_thunk.START) // 4
                target_register = ARM_REG_R0 + target_number
                if target_register in aliases or target_register in return_registers:
                    raise ValueError("indirect target carries tracked stack or return provenance")
            returned_aliases = {}
            if pointer_slots or words or word_mode and aliases or any(register in aliases for register in caller_clobbered):
                if ignored_leaf_alias_proof is not None:
                    returned_aliases = ignored_leaf_alias_proof.check_call(
                        current, operands[0].imm, aliases, pointer_slots)
                elif buffer_proof is None:
                    raise ValueError("stack aliases cannot cross calls in caller-clobbered registers")
                else:
                    returned_aliases = buffer_proof.check_call(operands[0].imm, aliases, stack,
                                                              pointer_slots, constants=constants,
                                                              site=current, words=words)
                    call_alternatives = getattr(returned_aliases, 'alternatives', None)
                    if word_mode:
                        words = dict(returned_aliases.words)
            return_registers.difference_update(caller_clobbered)
            for register in caller_clobbered:
                constants.pop(register, None)
                aliases.pop(register, None)
            if buffer_proof is not None:
                buffer_proof.finish_call_constants(constants, returned_aliases,
                                                   site=current, target=operands[0].imm)
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
        elif switch is not None and current == address + (
                switch["transfer"] if preloaded_switch else switch["dispatch"] + 8):
            successors = tuple(sorted({address + addend for offset, addend
                                       in switch_relocations.items() if offset != switch["literal"]}))
        elif buffer_proof is not None and buffer_proof.single_word_stores and \
                buffer_proof.apply_single_store(instruction, aliases, constants, stack, words,
                pointer_slots=pointer_slots, root_frame=address,
                context={'address':address, 'frame_base':-4*len(stack),
                    'protected':sorted(pointer_slots), 'return_registers':sorted(return_registers)}):
            return_registers.difference_update(instruction.regs_access()[1])
            successors = (current + instruction.size,)
        else:
            if CS_GRP_JUMP in instruction.groups:
                raise ValueError("non-leaf indirect control flow requires linked CFG verification")
            if not stack_operation and adjustment is None:
                read, written = instruction.regs_access()
                assigned_return = None
                loaded_alias = None
                word_constant = None
                if word_mode:
                    loaded_alias, word_constant, _, _ = buffer_proof.word_memory(
                        instruction, aliases, constants, stack, words, -4*len(stack), frozenset(pointer_slots), root_frame=address)
                if ARM_REG_PC in written:
                    raise ValueError("unresolved program-counter write")
                if ARM_REG_SP in written:
                    raise ValueError("unsupported stack-pointer adjustment")
                alias_constants = constants
                if thumb:
                    shifted = thumb_shifted_stack_constant(instruction, data, address)
                    if shifted is not None:
                        shifted_stack_constants.add(current)
                        alias_constants = {**constants, shifted[0]: shifted[1]}
                    literal = thumb_literal_stack_constant(instruction, data, address)
                    if literal is not None:
                        literal_stack_constants.add(current)
                        alias_constants = {**constants, literal[0]: literal[1]}
                assignment = stack_alias_assignment(instruction, aliases, len(stack), alias_constants) if thumb else None
                if ARM_REG_SP in registers and assignment is None:
                    if stack_pointer_compare_profile is None:
                        raise ValueError("unsupported stack-address materialization")
                    sp_compare.verify_instruction(instruction)
                if ARM_REG_PC in registers:
                    raise ValueError("unsupported program-counter materialization")
                allowed_aliases = {assignment[2]} if assignment is not None else set()
                stm = thumb_stack_alias_stm(instruction, aliases, len(stack)) if thumb else None
                if stm is not None:
                    base, offset, stored_registers = stm
                    for index, register in enumerate(stored_registers):
                        stack_alias_store(stack, pointer_slots, aliases, return_registers,
                                          offset + 4 * index, 4, register)
                    allowed_aliases.add(base)
                    assignment = (base, offset + 4 * len(stored_registers), base)
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
                        if pointer_word in pointer_slots and not word_mode:
                            if width != 4:
                                raise ValueError("partial access to a pointer-bearing local word")
                            if instruction.mnemonic.startswith("ldr"):
                                loaded_alias = (registers[0], pointer_slots[pointer_word])
                        if instruction.mnemonic.startswith("str"):
                            stack_alias_store(stack, pointer_slots, aliases, return_registers,
                                              offset, width, registers[0])
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
                                    buffer_proof.validate_pointer_value(aliases[registers[0]], stack)
                                    pointer_slots[offset] = aliases[registers[0]]
                                    allowed_aliases.add(registers[0])
                                else:
                                    pointer_slots.pop(offset, None)
                                stack[slot] = (registers[0] in return_registers,
                                               stack[slot][1], stack[slot][2])
                            else:
                                if slot < len(stack) and stack[slot][0]:
                                    assigned_return = registers[0]
                                if offset in pointer_slots and not word_mode:
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
                if buffer_proof is not None:
                    extra = buffer_proof.extra_constant(instruction, data, address, constants)
                    if extra is not None:
                        constant = extra
                if word_constant is not None:
                    constant = word_constant
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
                    tuple(sorted(constants.items())), tuple(sorted(pointer_slots.items())), tuple(sorted(words.items())))
        if call_alternatives is not None:
            if exact_alias_budget is None:
                raise ValueError("disjunctive call results require exact native frame alternatives")
            outgoings = []
            for result in call_alternatives:
                result_aliases = dict(aliases)
                result_aliases.update(result)
                result_words = dict(result.words)
                buffer_proof.prune_words(result_words, stack)
                outgoings.append((frozenset(return_registers), tuple(stack), tuple(sorted(result_aliases.items())),
                    tuple(sorted(constants.items())), tuple(sorted(pointer_slots.items())), tuple(sorted(result_words.items()))))
        else:
            outgoings = [outgoing]
        for successor, outgoing in ((target, state) for target in successors for state in outgoings):
            if path_states is not None:
                previous_paths = path_states.get(successor, set())
                if previous_paths and any(len(state[1]) != len(stack) for state in previous_paths):
                    raise ValueError("inconsistent saved stack depth at control-flow join")
                if outgoing not in previous_paths:
                    if path_state_count >= state_budget:
                        raise ValueError("acyclic path-state budget exhausted" if acyclic_state_budget is not None
                                         else "exact alias frame state budget exhausted")
                    path_states.setdefault(successor, set()).add(outgoing)
                    path_state_count += 1
                    pending.append((successor, outgoing))
                continue
            previous = states.get(successor)
            if previous is None:
                merged = outgoing
            else:
                if len(previous[1]) != len(stack):
                    raise ValueError("inconsistent saved stack depth at control-flow join")
                incoming_aliases = outgoing[2]
                if previous[2] != incoming_aliases and not stack_arguments:
                    previous_aliases = dict(previous[2])
                    incoming = dict(incoming_aliases)
                    differing = {register for register in previous_aliases.keys() | incoming.keys()
                                 if previous_aliases.get(register) != incoming.get(register)}
                    if not thumb or not all(stack_alias_overwritten_before_use(
                            data, address, successor, register, decoder) for register in differing):
                        raise ValueError("inconsistent stack aliases at control-flow join")
                    incoming_aliases = tuple((register, offset) for register, offset in incoming_aliases
                                             if register not in differing)
                merged_aliases = (merge_possible_aliases(previous[2], outgoing[2])
                                  if stack_arguments else incoming_aliases)
                merged_slots = merge_possible_aliases(previous[4], outgoing[4])
                merged = (previous[0] & outgoing[0],
                          tuple((saved[0] and incoming[0], saved[1] and incoming[1],
                                 saved[2] and incoming[2])
                                for saved, incoming
                                in zip(previous[1], stack)), merged_aliases,
                          tuple((register, value) for register, value in previous[3]
                                if constants.get(register) == value), merged_slots,
                          tuple((slot,value) for slot,value in previous[5] if words.get(slot)==value))
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if acyclic_state_budget is not None:
        # Exact states never merge. The complete reached graph must also be a
        # DAG, including cycles whose repeated states needed no new work item.
        incoming_edges = {site: 0 for site in instructions}
        for successors in edges.values():
            for successor in successors:
                incoming_edges[successor] += 1
        ready = [site for site, count in incoming_edges.items() if count == 0]
        removed = 0
        while ready:
            site = ready.pop()
            removed += 1
            for successor in edges[site]:
                incoming_edges[successor] -= 1
                if incoming_edges[successor] == 0:
                    ready.append(successor)
        if removed != len(instructions):
            raise ValueError("acyclic path states reject reachable CFG cycles")
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
    if any(current == address or predecessors[current] != {current - 2}
           for current in literal_adjustments):
        raise ValueError("stack adjustment literal load is bypassed by a control-flow edge")
    if any(predecessors.get(current) != {current - 2} or
           predecessors.get(current - 2) != {current - 4}
           for current in shifted_stack_constants):
        raise ValueError("shifted stack constant is bypassed by a control-flow edge")
    if any(predecessors.get(current) != {current - 2} for current in literal_stack_constants):
        raise ValueError("stack alias literal load is bypassed by a control-flow edge")
    if switch is not None:
        pool_switch = function_thunk_context is not None and 'pool_switch' in function_thunk_context
        if (not allow_switch_scalar_frame and double_context is None and not pool_switch and
                uses_stack_frame(instructions.values())) or any(
                target in RUNTIME_HELPERS.values() and not (pool_switch and target in function_thunk.ALIASES.values())
                for target in calls.values()):
            raise ValueError("switch evidence excludes fixed frames and runtime call thunks")
        if allow_switch_scalar_frame and not any(
                (thumb_stack_adjustment(instruction) or 0) < 0 for instruction in instructions.values()):
            raise ValueError("scalar switch frames require a reached nonzero fixed allocation")
        if preloaded_switch:
            verify_preloaded_switch_cfg(data, address, instructions, edges, predecessors, switch)
        else:
            comparison = address + switch["comparison"]
            guard = address + switch["guard"]
            dispatch = address + switch["dispatch"]
            expected = {guard: {comparison}, dispatch: {guard}}
            if dispatch - guard in (4, 6):
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
    if inert_spin_context is not None:
        spins = sorted(instructions.keys() - reaching_return)
        if not spins:
            raise ValueError("inert-spin profile requires a reachable nonreturning self-branch")
        for current in spins:
            instruction = instructions[current]
            if instruction.id != ARM_INS_B or instruction.size != 2 or \
                    instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                    bytes(instruction.bytes) != b"\xfe\xe7" or len(instruction.operands) != 1 or \
                    instruction.operands[0].type != ARM_OP_IMM or \
                    instruction.operands[0].imm != current or set(edges[current]) != {current}:
                raise ValueError("every non-return-reaching node must itself be an inert narrow self-branch")
    elif reaching_return != instructions.keys():
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
        if divsi3.reserved(struct.unpack_from("<I", data, literal - address)[0]):
            raise ValueError("signed quotient runtime cannot be materialized as a literal")
        if ashldi3.reserved(struct.unpack_from("<I", data, literal - address)[0]):
            raise ValueError("ashldi3 runtime cannot be materialized as a literal")
        if umodsi3.reserved(struct.unpack_from("<I", data, literal - address)[0]):
            raise ValueError("unsigned remainder runtime cannot be materialized as a literal")
        if software_float.reserved(struct.unpack_from("<I", data, literal - address)[0]):
            raise ValueError("software-float runtime cannot be materialized as a literal")
        if software_double.reserved(struct.unpack_from("<I", data, literal - address)[0]):
            raise ValueError("software-double runtime cannot be materialized as a literal")
    if switch_data_relocations is not None:
        verify_data_literals(instructions.values(), address, switch_data_relocations)
    if divsi3_context is not None:
        if signed_quotient_profile == divsi3.FRAMED_SELECTOR:
            # Reached only after the complete CFG, stack/save/return, alias and
            # literal checks above. Positive divisor facts stay register-only;
            # stack loads and caller-clobbered registers introduce no constants.
            if not any((thumb_stack_adjustment(item) or
                        thumb_literal_stack_adjustment(item, data, address) or 0) < 0
                       for item in instructions.values()):
                raise ValueError("framed signed quotient requires an allocated caller stack frame")
            from local_long_branch_profile import prove_frame
            prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
        elif uses_stack_frame(instructions.values()):
            raise ValueError("signed quotient requires a frameless caller")
        divsi3_context[3].update(divsi3.prove_divisors(instructions, edges, address, divsi3_context[2]))
    if umodsi3_context is not None:
        umodsi3_context[3].update(umodsi3.prove_divisors(instructions, edges, address, umodsi3_context[2]))
    if ashldi3_context is not None:
        shift = ashldi3.for_bindings(ashldi3_context[3])
        if hasattr(shift, "prove_counts"):
            shift.prove_counts(instructions, edges, address, ashldi3_context[3], data)
    if signed_numeric:
        # Only the canonical double composition may reuse the complete local
        # stack/save/restore proof above. The operand proof remains register-only:
        # frame adjustments kill SP facts and unknown local loads yield no facts.
        # Standalone remainder retains its existing frameless boundary.
        if uses_stack_frame(instructions.values()) and double_context is None:
            raise ValueError("signed remainder numeric proof requires a frameless caller")
        if remainder_inventory_context is not None:
            remainder_inventory.prove_operands(data, address, instructions, edges,
                modsi3_context[2], remainder_inventory_context[4])
        else:
            transfers = modsi3.prove_operands(instructions, edges, address, modsi3_context[2],
                logical_shift_signed16=signed_runtime_context is not None and
                    signed_divmod.context_selector(signed_runtime_context) == signed_divmod.SHIFT_SELECTOR)
    if inert_spin_context is not None:
        inert_spin_context["spins"] = [current - address for current in spins]
    if local_branches:
        from local_long_branch_profile import prove_frame
        prove_frame(instructions, edges, address, local_branches, calls)
    if function_thunk_context is not None and 'pool_switch' in function_thunk_context:
        from thunk_pool_switch import record as pool_record
        pool_record(data, address, switch_relocations, instructions.values())
    if signed_runtime_context is not None:
        signed_divmod.finish(data, address, calls, signed_runtime_context,
                             instructions.values(), divsi3_context[3], transfers)
    if remainder_inventory_context is not None:
        remainder_inventory.finish(data, address, calls, remainder_inventory_context,
                                   instructions.values())
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
    ap.add_argument("--control-flow-profile", default="ordinary", choices=("ordinary", inert_spin.SELECTOR))
    ap.add_argument("--signed-quotient-profile", choices=(divsi3.FRAMED_SELECTOR,))
    ap.add_argument("--signed-runtime-profile", choices=tuple(signed_divmod.SCHEMAS))
    ap.add_argument("--software-double-profile", choices=(software_double.SELECTOR,))
    ap.add_argument("--software-double-remainder-profile", choices=(software_double.REMAINDER_TARGET_SELECTOR,))
    ap.add_argument("--function-address-profile", choices=(function_thunk.SELECTOR,))
    ap.add_argument("--switch-profile", choices=("two-constants-v2", "two-constants-frame-v1"))
    ap.add_argument("--wsl", default="Ubuntu")
    ap.add_argument("--wsl-path", default=os.environ.get("FFTA_WSL_PATH",
                                                         DEFAULT_WSL_PATH))
    ap.add_argument("--label", default="")
    ap.add_argument("--no-write", action="store_true")
    ap.add_argument("--emit", help="write verified symbol bytes to a new file under the decomp build/")
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT"),
                    help="decomp repo (default: current directory)")
    ap.add_argument("--owner-runtime-profile", choices=("restoring-owner-runtime-v1",
                                                      "restoring-owner-acyclic-v1",
                                                      "restoring-owner-ignored-leaf-alias-v1",
                                                      "named-data-buffer-v1",
                                                      "static-callback-buffer-v1",
                                                      "protected-descriptor-word-v1",
                                                      "watched-switch-preservation-v1",
                                                      "descriptor-output-alias-v1",
                                                      "descriptor-single-store-v1",
                                                      "descriptor-disjunctive-alias-v1",
                                                      "descriptor-callee-constant-v1",
                                                      "descriptor-cursor-value-v1"))
    args = ap.parse_args()
    global ROOT
    ROOT = repo_root(args.root)

    addr = int(args.addr, 16)
    if args.signed_runtime_profile is not None:
        return signed_divmod.issue(Path(ROOT), addr, args)
    if args.signed_quotient_profile is not None and (
            args.mode != "thumb" or args.control_flow_profile != "ordinary" or
            args.software_double_profile or args.software_double_remainder_profile or
            args.function_address_profile or args.switch_profile or args.owner_runtime_profile):
        sys.exit("framed signed quotient excludes other selectors and requires Thumb mode")
    if args.owner_runtime_profile:
        import owner_admission_profile
        return owner_admission_profile.issue(Path(ROOT), addr, args)
    if args.switch_profile is not None:
        from switch_constants_profile import issue
        return issue(Path(ROOT), addr, args)
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
    empty_index = empty_body.index_snapshot(ROOT)
    empty_profile = False
    spin_profile = args.control_flow_profile == inert_spin.SELECTOR
    double_profile = args.software_double_profile == software_double.SELECTOR
    remainder_target_profile = args.software_double_remainder_profile == software_double.REMAINDER_TARGET_SELECTOR
    if remainder_target_profile and not double_profile:
        sys.exit("target-state remainder requires its explicit software-double profile")
    thunk_profile = args.function_address_profile == function_thunk.SELECTOR
    function_index = inert_spin.index_snapshot(ROOT) if spin_profile or double_profile or thunk_profile else None
    if thunk_profile:
        try:
            function_thunk.fixed_configuration(args)
        except ValueError as error:
            sys.exit(str(error))
        if spin_profile or double_profile or not thumb or len(list(Path(ROOT, "src").rglob(f"{addr:08X}.c"))) != 1:
            sys.exit("function thunks require a unique Thumb source and isolated explicit selector")
    if double_profile:
        try:
            software_double.fixed_configuration(args)
        except ValueError as error:
            sys.exit(str(error))
        if spin_profile or not thumb or len(list(Path(ROOT, "src").rglob(f"{addr:08X}.c"))) != 1:
            sys.exit("software double requires one unique Thumb source and no other profile selector")
    if spin_profile:
        try:
            inert_spin.fixed_configuration(args)
        except ValueError as error:
            sys.exit(str(error))
        if not thumb or len(list(Path(ROOT, "src").rglob(f"{addr:08X}.c"))) != 1:
            sys.exit("inert spins require one uniquely addressed Thumb source")

    print(f"function  0x{addr:08X}   {span} bytes ({'Thumb' if thumb else 'ARM'})")
    print(f"source    {src_rel}")
    print(f"compiler  {args.cc} {args.flags}")

    # the compile runs in a shell (possibly inside WSL), so give it a POSIX path
    runner = Runner(args.cc, args.wsl, args.wsl_path,
                    timeout=software_double.REPLAY_TIMEOUT if double_profile or thunk_profile else None)
    try:
        with runner.workspace() as workspace:
            object_data, text_data, original = compile_object(
                runner, workspace, args, ROOT, addr, src_rel, thumb)
            calls = {}
            data_relocations = {}
            function_relocations = {}
            switch_relocations = {}
            udivsi3_bindings = {}
            modsi3_bindings = {}
            divsi3_bindings = {}
            umodsi3_bindings = {}
            ashldi3_bindings = {}
            float_bindings = {}
            float_evidence = None
            shift_evidence = None
            shift_profile = ashldi3
            quotient_evidence = None
            remainder_evidence = None
            division_evidence = None
            unsigned_remainder_evidence = None
            address_manifest = None
            switch_evidence = None
            preloaded_profile = False
            spin_evidence = None
            double_evidence = None
            double_switch_relocations = {}
            thunk_evidence = None
            if thunk_profile:
                got, calls, function_relocations, data_relocations = function_thunk.object_bytes(
                    runner, workspace, args, original, addr, mapping, rom, data_mapping)
                linked_profile = True
            elif double_profile:
                got, calls, double_bindings = software_double.object_bytes(
                    runner, workspace, args, original, addr, mapping, rom, function_index,
                    data_mapping=data_mapping, data_relocations=data_relocations,
                    switch_relocations=double_switch_relocations)
                linked_profile = True
            elif spin_profile:
                if not thumb:
                    raise ValueError("inert spins require Thumb mode")
                got, calls = inert_spin.object_bytes(runner, workspace, args, original, addr, mapping, rom)
                linked_profile = bool(calls)
            elif original["relocations"]:
                if not thumb:
                    raise ValueError("linked profile supports only Thumb callers")
                got, calls, data_relocations = link_calls(runner, workspace, args, original,
                                                          addr, mapping, len(rom), rom, data_mapping,
                                                          function_relocations, switch_relocations,
                                                          allow_switch_data=True,
                                                          udivsi3_bindings=udivsi3_bindings,
                                                          allow_preloaded_switch=True,
                                                          modsi3_bindings=modsi3_bindings,
                                                          divsi3_bindings=divsi3_bindings,
                                                          umodsi3_bindings=umodsi3_bindings,
                                                          ashldi3_bindings=ashldi3_bindings,
                                                          ashldi3_index=empty_index,
                                                          float_bindings=float_bindings, float_index=empty_index)
                linked_profile = bool(calls)
            else:
                got = function_bytes(object_data, text_data, f"func_{addr:08X}", addr, thumb)
            buffer_proof = BufferCallProof(rom, mapping if calls else None)
            if thunk_profile:
                verified_instructions = verify_leaf_instructions(got, addr, True, calls, function_thunk_context={})
                thunk_evidence = function_thunk.make_manifest(calls, function_relocations, data_relocations,
                                                             addr, rom, data_mapping, verified_instructions)
                verified_instructions = function_thunk.verify(got, addr, rom, mapping, function_index,
                                                               data_mapping, thunk_evidence)
            elif double_profile:
                context = {"spins": []}
                try:
                    verified_instructions = verify_leaf_instructions(
                        got, addr, True, calls, double_context=(rom, mapping, function_index, double_bindings) +
                            ((True,) if remainder_target_profile else ()),
                        switch_relocations=double_switch_relocations or None)
                except ValueError as error:
                    if str(error) != "reachable control-flow region has no path to a verified return":
                        raise
                    context = {}
                    verified_instructions = verify_leaf_instructions(
                        got, addr, True, calls, double_context=(rom, mapping, function_index, double_bindings) +
                            ((True,) if remainder_target_profile else ()),
                        inert_spin_context=context, switch_relocations=double_switch_relocations or None)
                double_evidence = software_double.make_manifest(calls, addr, double_bindings, verified_instructions,
                                                                 literals=data_relocations, data_mapping=data_mapping,
                                                                 spins=context["spins"], remainder_target=remainder_target_profile,
                    switch=software_double.switch_record(got, addr, double_switch_relocations))
                verified_instructions = software_double.verify(
                    got, addr, rom, mapping, function_index, double_evidence, data_mapping=data_mapping)
            elif spin_profile:
                context = {}
                verified_instructions = verify_leaf_instructions(got, addr, True, calls,
                                                                  inert_spin_context=context)
                spin_evidence = {"calls": inert_spin.call_records(calls, addr),
                                 "frame": uses_stack_frame(verified_instructions), "spins": context["spins"]}
                verified_instructions = inert_spin.verify(got, addr, rom, mapping, function_index, spin_evidence)
            elif float_bindings:
                software_float.fixed_configuration(args)
                verified_instructions = verify_leaf_instructions(
                    got, addr, True, calls, float_context=(rom, mapping, empty_index, float_bindings))
                float_evidence = software_float.make_manifest(calls, addr, float_bindings,
                                                               data_relocations, data_mapping, verified_instructions)
                verified_instructions = software_float.verify(
                    got, addr, rom, mapping, empty_index, data_mapping, float_evidence)
            elif ashldi3_bindings:
                shift_profile = ashldi3.for_bindings(ashldi3_bindings)
                shift_profile.fixed_configuration(args)
                verified_instructions = verify_leaf_instructions(
                    got, addr, True, calls, ashldi3_context=(rom, mapping, empty_index, ashldi3_bindings))
                shift_evidence = shift_profile.make_manifest(calls, addr, ashldi3_bindings,
                                                       data_relocations, data_mapping, verified_instructions)
                verified_instructions = shift_profile.verify(
                    got, addr, rom, mapping, empty_index, data_mapping, shift_evidence)
            elif umodsi3_bindings:
                umodsi3.fixed_configuration(args)
                divisors = {}
                verified_instructions = verify_leaf_instructions(
                    got, addr, True, calls,
                    umodsi3_context=(rom, mapping, umodsi3_bindings, divisors))
                objects = parse_data_symbols(data_mapping) if data_relocations else {}
                unsigned_remainder_evidence = {
                    "runtime": umodsi3.RUNTIME,
                    "calls": [[site - addr, umodsi3_bindings.get(site, f"func_{target:08X}")]
                              for site, target in sorted(calls.items())],
                    "divisors": [[site - addr, divisor] for site, divisor in sorted(divisors.items())],
                    "data": [[offset, name, value - objects[name]]
                             for offset, (name, value) in sorted(data_relocations.items())],
                    "frame": uses_stack_frame(verified_instructions)}
                verified_instructions = umodsi3.verify(
                    got, addr, rom, mapping, data_mapping, unsigned_remainder_evidence)
            elif divsi3_bindings:
                if (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags) != \
                        (DEFAULT_CC, DEFAULT_CPP, DEFAULT_AS, DEFAULT_OBJCOPY, DEFAULT_LD, DEFAULT_FLAGS):
                    raise ValueError("signed quotient requires the fixed approved toolchain configuration")
                divisors = {}
                verify_leaf_instructions(got, addr, True, calls,
                                         divsi3_context=(rom, mapping, divsi3_bindings, divisors),
                                         signed_quotient_profile=args.signed_quotient_profile)
                quotient_evidence = {
                    "runtime": divsi3.RUNTIME,
                    "calls": [[site - addr, divsi3_bindings.get(site, f"func_{target:08X}")]
                              for site, target in sorted(calls.items())],
                    "divisors": [[site - addr, divisor] for site, divisor in sorted(divisors.items())]}
                if args.signed_quotient_profile is not None:
                    quotient_evidence["frame"] = True
                verified_instructions = verify_divsi3(got, addr, rom, mapping, quotient_evidence,
                                                       selector=args.signed_quotient_profile)
            elif modsi3_bindings:
                verified_instructions = verify_leaf_instructions(
                    got, addr, True, calls, modsi3_context=(rom, mapping, modsi3_bindings))
                if set(modsi3_bindings.values()) == {"__modsi3"}:
                    objects = parse_data_symbols(data_mapping) if data_relocations else {}
                    remainder_evidence = {
                        "runtime": modsi3.RUNTIME,
                        "calls": [[site - addr, modsi3_bindings.get(site, f"func_{target:08X}")]
                                  for site, target in sorted(calls.items())],
                        "operands": [[site - addr, "signed16", "nonzero"]
                                     for site in sorted(modsi3_bindings)],
                        "data": [[offset, name, value - objects[name]]
                                 for offset, (name, value) in sorted(data_relocations.items())]}
                    verified_instructions = verify_modsi3(
                        got, addr, rom, mapping, data_mapping, remainder_evidence)
            elif udivsi3_bindings:
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
                    "switch": selected_switch_layout(got, addr, switch_relocations,
                                                     data_relocations if data_relocations else None,
                                                     allow_preloaded_switch=True)}
                preloaded_profile = "preload" in switch_evidence["switch"]
                if data_relocations:
                    objects = parse_data_symbols(data_mapping)
                    switch_evidence["data"] = [
                        [offset, name, value - objects[name]]
                        for offset, (name, value) in sorted(data_relocations.items())]
                if preloaded_profile:
                    verified_instructions, _ = verify_preloaded_switches(
                        got, addr, rom, mapping, data_mapping, switch_evidence)
                else:
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
                try:
                    verified_instructions, _ = verify_function_addresses(
                        got, addr, rom, mapping, data_mapping, address_manifest)
                except ValueError as address_error:
                    if data_relocations:
                        raise
                    try:
                        verified_instructions, buffer_proof = verify_function_buffers(
                            got, addr, rom, mapping, address_manifest)
                    except ValueError as buffer_error:
                        raise ValueError(f"{address_error}; function-buffer proof: {buffer_error}") from buffer_error
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
            if args.signed_quotient_profile is not None and quotient_evidence is None:
                raise ValueError("framed signed quotient requires canonical __divsi3 ELF calls")
            verify_data_literals(verified_instructions, addr, data_relocations)
            function_thunk.verify_literal_bindings(got, addr, verified_instructions, calls,
                                                    mapping, function_relocations)
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
        schema = (FUNCTION_BUFFER_SCHEMA if buffer_proof.dependencies else
                  FRAMED_FUNCTION_ADDRESS_SCHEMA if framed_profile else FUNCTION_ADDRESS_SCHEMA)
    if switch_relocations:
        schema = (PRELOADED_SWITCH_SCHEMA if preloaded_profile else
                  SWITCH_DATA_SCHEMA if data_profile else SWITCH_SCHEMA)
    if udivsi3_bindings:
        schema = UDIVSI3_SCHEMA
    if remainder_evidence is not None:
        schema = modsi3.SCHEMA
    if quotient_evidence is not None:
        schema = divsi3.schema(args.signed_quotient_profile)
    if float_evidence is not None:
        schema = software_float.SCHEMA
    if shift_evidence is not None:
        schema = shift_profile.SCHEMA
    if unsigned_remainder_evidence is not None:
        schema = umodsi3.SCHEMA
    if spin_profile:
        schema = inert_spin.SCHEMA
    if double_profile:
        schema = software_double.SCHEMA
    if thunk_profile:
        schema = function_thunk.SCHEMA
    control_flow = CALL_SUMMARY if linked_profile else "closed leaf CFG"
    if preloaded_profile:
        control_flow = PRELOADED_SWITCH_CONTROL_FLOW
    if spin_profile or double_profile and "inert_spin" in double_evidence:
        control_flow = inert_spin.CONTROL_FLOW
    if thunk_profile:
        control_flow = function_thunk.CONTROL_FLOW
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
            checker_command = [sys.executable, plaus_path, "--quiet", "--addr", f"0x{addr:08X}",
                               "--json"] + lint_targets
            checker_result = (_run_replay_process(checker_command, ROOT, software_double.REPLAY_TIMEOUT)
                              if double_profile or thunk_profile else subprocess.run(checker_command, capture_output=True, text=True))
            findings, hand_asm_allowed = plausibility_result(checker_result, addr)
            if findings and identical and schema == SCHEMA and thumb:
                try:
                    software_double.fixed_configuration(args)
                    empty_body.check_findings(checker_result, ROOT, addr)
                    empty_body.verify_object(object_data, text_data, addr, thumb, rom, mapping, empty_index)
                except (OSError, ValueError, KeyError, TypeError):
                    pass
                else:
                    findings = []
                    empty_profile = True
                    schema = empty_body.SCHEMA
        except (OSError, ValueError, TypeError, RecursionError, subprocess.SubprocessError) as error:
            findings = [f"plausibility checker failed: {error}"]

    plausible = not findings
    if source_fingerprint(ROOT, addr) != fingerprint:
        sys.exit("source or headers changed during verification; re-run match.py")
    if empty_profile and (mapping_snapshot(ROOT) != mapping or
                          empty_body.index_snapshot(ROOT) != empty_index or report_rom_path(ROOT) != rom_file):
        sys.exit("empty-body indexes or selected ROM changed during verification; re-run match.py")
    if (linked_profile or data_profile or function_relocations or switch_relocations or spin_profile) and \
            mapping_snapshot(ROOT) != mapping:
        sys.exit("function mapping changed during verification; re-run match.py")
    if data_profile and data_snapshot(ROOT) != data_mapping:
        sys.exit("data symbol mapping changed during verification; re-run match.py")
    if schema == FUNCTION_BUFFER_SCHEMA and report_rom_path(ROOT) != rom_file:
        sys.exit("selected ROM changed during verification; re-run match.py")
    if spin_profile and (inert_spin.index_snapshot(ROOT) != function_index or report_rom_path(ROOT) != rom_file):
        sys.exit("inert-spin function index or selected ROM changed during verification; re-run match.py")
    if spin_profile and hand_asm_allowed:
        sys.exit("inert spins exclude hand-ASM exceptions")
    if thunk_profile:
        if hand_asm_allowed:
            sys.exit("function thunks exclude hand-ASM exceptions")
        try:
            function_thunk.verify_source(ROOT, addr, got_body, rom, mapping, function_index,
                                         data_mapping, fingerprint, thunk_evidence)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            sys.exit(f"function-thunk source replay failed: {error}")
    if double_profile:
        if software_double.index_snapshot(ROOT) != function_index or report_rom_path(ROOT) != rom_file or hand_asm_allowed:
            sys.exit("software-double index/ROM selection changed or hand-ASM exception requested")
        try:
            software_double.verify_source(ROOT, addr, got_body, rom, mapping, function_index,
                                          fingerprint, double_evidence, data_mapping=data_mapping)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            sys.exit(f"software-double source replay failed: {error}")
    if float_evidence is not None:
        if software_float.index_snapshot(ROOT) != empty_index or report_rom_path(ROOT) != rom_file or hand_asm_allowed or \
                spin_profile or double_profile or thunk_profile:
            sys.exit("software-float index/ROM selection changed or unsupported profile requested")
        try:
            software_float.verify_source(ROOT, addr, got_body, rom, mapping, empty_index,
                                         data_mapping, fingerprint, float_evidence)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            sys.exit(f"software-float source replay failed: {error}")
    if shift_evidence is not None:
        if shift_profile.index_snapshot(ROOT) != empty_index or report_rom_path(ROOT) != rom_file or hand_asm_allowed:
            sys.exit("ashldi3 index/ROM selection changed or hand-ASM exception requested")
        try:
            shift_profile.verify_source(ROOT, addr, got_body, rom, mapping, empty_index,
                                  data_mapping, fingerprint, shift_evidence)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            sys.exit(f"ashldi3 source replay failed: {error}")
    if args.signed_quotient_profile is not None:
        if hand_asm_allowed or report_rom_path(ROOT) != rom_file:
            sys.exit("framed signed quotient excludes hand-ASM exceptions and ROM selection changes")
        try:
            verify_divsi3_source(ROOT, addr, got_body, rom, mapping, fingerprint,
                                  quotient_evidence, selector=args.signed_quotient_profile)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            sys.exit(f"framed signed quotient source replay failed: {error}")
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
            if empty_profile:
                f.write(f"* mapping SHA-256: `{mapping_fingerprint(mapping)}`\n")
                f.write(f"* function index SHA-256: `{mapping_fingerprint(empty_index)}`\n")
                f.write(f"* control flow: {control_flow}\n")
                f.write(f"* empty body: {empty_body.SUMMARY}\n")
            if framed_profile:
                f.write(f"* stack frame: {STACK_SUMMARY}\n")
            if buffer_proof.dependencies:
                summary = STACK_BUFFER_SUMMARY if buffer_proof.stack_arguments else BUFFER_SUMMARY
                f.write(f"* buffer calls: {summary}\n")
                f.write(f"* buffer proof SHA-256: `{buffer_proof.fingerprint()}`\n")
            if linked_profile or data_profile or function_relocations or switch_relocations or spin_profile:
                f.write(f"* mapping SHA-256: `{mapping_fingerprint(mapping)}`\n")
                f.write(f"* control flow: {control_flow}\n")
            if data_profile:
                f.write(f"* data symbols SHA-256: `{mapping_fingerprint(data_mapping)}`\n")
            if function_relocations and not thunk_profile:
                encoded_manifest = function_address_manifest(address_manifest)
                f.write(f"* function addresses: {FUNCTION_ADDRESS_SUMMARY}\n")
                f.write(f"* function address manifest: `{encoded_manifest}`\n")
                proof_digest = function_address_fingerprint(
                    addr, got_body, address_manifest,
                    framed=schema == FRAMED_FUNCTION_ADDRESS_SCHEMA)
                f.write(f"* function address proof SHA-256: `{proof_digest}`\n")
                if schema == FUNCTION_BUFFER_SCHEMA:
                    proof_digest = function_buffer_fingerprint(
                        addr, got_body, address_manifest, fingerprint, mapping,
                        buffer_proof.fingerprint())
                    f.write(f"* function buffer proof SHA-256: `{proof_digest}`\n")
            if switch_relocations:
                summary = (PRELOADED_SWITCH_SUMMARY if preloaded_profile else
                           SWITCH_DATA_SUMMARY if data_profile else SWITCH_SUMMARY)
                f.write(f"* switches: {summary}\n")
                f.write(f"* switch manifest: `{switch_manifest(switch_evidence)}`\n")
                fingerprint_switch = (preloaded_switch_fingerprint if preloaded_profile else
                                      switch_data_fingerprint if data_profile else switch_fingerprint)
                proof_digest = fingerprint_switch(addr, got_body, switch_evidence)
                f.write(f"* switch proof SHA-256: `{proof_digest}`\n")
            if float_evidence is not None:
                f.write(f"* function index SHA-256: `{mapping_fingerprint(empty_index)}`\n")
                f.write(f"* ROM SHA-256: `{hashlib.sha256(rom).hexdigest()}`\n")
                f.write(f"* software float: {software_float.SUMMARY}\n")
                f.write(f"* software float manifest: `{software_float.manifest_text(float_evidence)}`\n")
                proof_digest = software_float.fingerprint(addr, got_body, float_evidence, fingerprint,
                                                          mapping, empty_index, data_mapping, rom)
                f.write(f"* software float proof SHA-256: `{proof_digest}`\n")
            if shift_evidence is not None:
                f.write(f"* function index SHA-256: `{mapping_fingerprint(empty_index)}`\n")
                f.write(f"* ROM SHA-256: `{hashlib.sha256(rom).hexdigest()}`\n")
                f.write(f"* {shift_profile.NAME}: {shift_profile.SUMMARY}\n")
                f.write(f"* {shift_profile.NAME} manifest: `{shift_profile.manifest_text(shift_evidence)}`\n")
                proof_digest = shift_profile.fingerprint(addr, got_body, shift_evidence, fingerprint,
                                                   mapping, empty_index, data_mapping, rom)
                f.write(f"* {shift_profile.NAME} proof SHA-256: `{proof_digest}`\n")
            if unsigned_remainder_evidence is not None:
                f.write(f"* unsigned remainder: {umodsi3.SUMMARY}\n")
                f.write(f"* unsigned remainder manifest: `{umodsi3.manifest_text(unsigned_remainder_evidence)}`\n")
                proof_digest = umodsi3.fingerprint(addr, got_body, unsigned_remainder_evidence)
                f.write(f"* unsigned remainder proof SHA-256: `{proof_digest}`\n")
            if udivsi3_bindings:
                f.write(f"* unsigned division: {UDIVSI3_SUMMARY}\n")
                f.write(f"* unsigned division manifest: `{udivsi3_manifest(division_evidence)}`\n")
                proof_digest = udivsi3_fingerprint(addr, got_body, division_evidence)
                f.write(f"* unsigned division proof SHA-256: `{proof_digest}`\n")
            if remainder_evidence is not None:
                f.write(f"* signed remainder: {modsi3.SUMMARY}\n")
                f.write(f"* signed remainder manifest: `{modsi3.manifest_text(remainder_evidence)}`\n")
                proof_digest = modsi3.fingerprint(addr, got_body, remainder_evidence)
                f.write(f"* signed remainder proof SHA-256: `{proof_digest}`\n")
            if quotient_evidence is not None:
                summary = (divsi3.FRAMED_SUMMARY if args.signed_quotient_profile else divsi3.SUMMARY)
                f.write(f"* signed quotient: {summary}\n")
                f.write(f"* signed quotient manifest: `{divsi3.manifest_text(quotient_evidence)}`\n")
                proof_digest = divsi3.fingerprint(addr, got_body, quotient_evidence,
                                                   selector=args.signed_quotient_profile)
                f.write(f"* signed quotient proof SHA-256: `{proof_digest}`\n")
            if spin_profile:
                f.write(f"* function index SHA-256: `{mapping_fingerprint(function_index)}`\n")
                f.write(f"* inert spins: {inert_spin.SUMMARY}\n")
                f.write(f"* inert spin manifest: `{inert_spin.manifest_text(spin_evidence)}`\n")
                proof_digest = inert_spin.fingerprint(addr, got_body, spin_evidence, fingerprint,
                                                      mapping, function_index)
                f.write(f"* inert spin proof SHA-256: `{proof_digest}`\n")
            if double_profile:
                f.write(f"* function index SHA-256: `{mapping_fingerprint(function_index)}`\n")
                f.write(f"* ROM SHA-256: `{hashlib.sha256(rom).hexdigest()}`\n")
                f.write(f"* software double: {software_double.summary(double_evidence)}\n")
                f.write(f"* software double ABI: `{software_double.ABI}`\n")
                f.write(f"* software double runtime: `{software_double.RUNTIME}`\n")
                f.write(f"* software double semantics: `{software_double.SEMANTICS}`\n")
                f.write(f"* software double manifest: `{software_double.manifest_text(double_evidence)}`\n")
                proof_digest = software_double.fingerprint(addr, got_body, double_evidence, fingerprint,
                                                           mapping, function_index, rom, data_mapping=data_mapping)
                f.write(f"* software double proof SHA-256: `{proof_digest}`\n")
            if thunk_profile:
                f.write(f"* function index SHA-256: `{mapping_fingerprint(function_index)}`\n")
                f.write(f"* ROM SHA-256: `{hashlib.sha256(rom).hexdigest()}`\n")
                f.write(f"* function-address thunks: {function_thunk.SELECTOR}\n")
                f.write(f"* function-address-thunk manifest: `{function_thunk.manifest_text(thunk_evidence)}`\n")
                proof_digest = function_thunk.fingerprint(addr, got_body, thunk_evidence, fingerprint,
                                                          mapping, function_index, data_mapping, rom)
                f.write(f"* function-address-thunk sha256: `{proof_digest}`\n")
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
