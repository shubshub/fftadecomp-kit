#!/usr/bin/env python3
"""
analyze.py - FFTA (AFXE / GBA) ROM analysis and layout extractor.

This is a from-scratch analysis pass over the base ROM:
  * validates the cartridge header (logo / checksum) and reports anomalies
  * performs recursive-descent disassembly (ARM + Thumb) from the entry point
    and from prologue candidates, producing provisional linear code extents
  * classifies the ROM into code / data / asset regions by coverage + entropy
  * writes config/rom_layout.json, symbols/functions.txt, logs/analysis.txt

Nothing here needs an ARM toolchain: capstone does the decoding.

Usage:  python tools/analyze.py [rom] [repo-root]
        python tools/analyze.py [rom] [repo-root] --refine-address 0x08123A1C

       The repo root defaults to the current directory, so this tool can
       be run from a decomp repo that vendors it (see fftadecomp-kit).
       Refinement reads the existing index and emits diagnostic JSON only.
"""

import argparse
import hashlib
import json
import math
import os
import struct
import sys
from collections import Counter, OrderedDict

try:
    from capstone import (Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB,
                          CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET)
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_REG_LR,
                                    ARM_REG_PC, ARM_REG_SP, ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG)
except ImportError:
    sys.exit("analyze.py needs capstone:  python -m pip install capstone")

ROM_BASE = 0x08000000
CODE_END = 0x08150000
HEADER_LEN = 0xC0          # GBA header (logo, title, code, pointer fields)
BLK = 0x400                # 4 KiB granularity for the coverage map

_LOG = []


def rom_path_default(here):
    """the ROM to analyse: the one in this directory, whatever it is called"""
    from rompath import rom_path
    return rom_path(here)


def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def say(*a):
    line = " ".join(str(x) for x in a)
    print(line, flush=True)
    _LOG.append(line)

NINTENDO_LOGO_SHA256 = "08a0153cfd6b0ea54b938f7d209933fa849da0d56f5a34c481060c9ff2fad818"


# --------------------------------------------------------------------------
# decoding
# --------------------------------------------------------------------------

class Decoder:
    """Address-aware instruction decoding with bounded per-mode caches."""

    CACHE_LIMIT = 4096

    def __init__(self, rom):
        self.rom = rom
        self.arm = Cs(CS_ARCH_ARM, CS_MODE_ARM)
        self.thumb = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        for c in (self.arm, self.thumb):
            c.detail = True
            c.skipdata = False
        self.arm_cache = OrderedDict()
        self.thumb_cache = OrderedDict()

    def arm_ins(self, off):
        """Decode one ARM word. Returns dict or None if undecodable."""
        return self._decode(off, self.arm, self.arm_cache, 4)

    def thumb_ins(self, off):
        return self._decode(off, self.thumb, self.thumb_cache, 2)

    def _decode(self, off, engine, cache, alignment):
        if off < 0 or off % alignment or off + alignment > len(self.rom):
            return None
        if off in cache:
            return cache[off]
        instruction = next(engine.disasm(self.rom[off:off + 4],
                                         ROM_BASE + off, count=1), None)
        info = self._describe(instruction) if instruction is not None else None
        if len(cache) >= self.CACHE_LIMIT:
            cache.popitem(last=False)
        cache[off] = info
        return info

    @staticmethod
    def _describe(ins):
        md = ins.mnemonic
        grp = ins.groups
        d = {
            "mn": md,
            "op": ins.op_str,
            "sz": ins.size,
            "cond": ins.cc not in (ARM_CC_AL, ARM_CC_INVALID),
            "jump": CS_GRP_JUMP in grp,
            "call": CS_GRP_CALL in grp,
            "ret": CS_GRP_RET in grp,
            "tgt": None,
            "writes_pc": False,
            "wr": (),       # registers written
            "pcldr": None,  # (dest_reg, displacement) for `ldr rX, [pc, #imm]`
            "opreg": None,  # rX for bx/bl rX style transfers
            "pop_regs": (),
        }
        ops = ins.operands
        if ops and ops[0].type == 2:  # ARM_OP_IMM
            if md.startswith("b"):
                d["tgt"] = ops[0].imm - ROM_BASE
        try:
            reads, writes = ins.regs_access()
            d["wr"] = tuple(writes)
        except Exception:
            pass
        # ldr rX, [pc, #imm]  -> remember the literal so a later bx rX resolves
        if md in ("ldr", "ldr.w") and len(ops) == 2 and ops[0].type == 1 \
                and ops[1].type == 3 and ops[1].mem.base == ARM_REG_PC:
            d["pcldr"] = (ops[0].reg, ops[1].mem.disp)
        if md in ("bx", "bl", "blx") and len(ops) == 1 and ops[0].type == 1:
            d["opreg"] = ops[0].reg
        any_pc = any(o.type == 1 and o.reg == ARM_REG_PC for o in ops)
        if md.startswith("pop"):
            d["pop_regs"] = tuple(operand.reg for operand in ops
                                  if operand.type == 1)
        d["writes_pc"] = ARM_REG_PC in d["wr"] or (bool(d["pop_regs"]) and any_pc)
        d["ret"] = d["ret"] or (md == "bx" and d["opreg"] == ARM_REG_LR) \
            or (bool(d["pop_regs"]) and any_pc) \
            or (md.startswith("mov") and len(ops) == 2
                and ops[0].type == 1 and ops[0].reg == ARM_REG_PC
                and ops[1].type == 1 and ops[1].reg == ARM_REG_LR)
        return d


def refinement_boundaries(functions, rom_end=CODE_END, *, full_rom_inventory=False):
    """Validate indexed starts, ignoring their provisional end addresses."""
    if type(full_rom_inventory) is not bool:
        raise ValueError("full-ROM inventory opt-in must be Boolean")
    code_end = 0x09000000 if full_rom_inventory else CODE_END
    if full_rom_inventory:
        rom_end = min(rom_end, code_end)
    if not isinstance(functions, list):
        raise ValueError("function index must be a list")
    starts = {}
    issues = {}
    for function in functions:
        if not isinstance(function, dict) or not isinstance(function.get("rom"), str):
            raise ValueError("function entry must have a string rom address")
        try:
            address = int(function["rom"], 0)
        except ValueError as error:
            raise ValueError("invalid function address") from error
        mode = function.get("mode")
        problems = issues.setdefault(address, set())
        if mode not in ("arm", "thumb"):
            problems.add("invalid mode")
            mode = None
        if not ROM_BASE + HEADER_LEN <= address < code_end:
            problems.add("outside code region")
        if not ROM_BASE <= address or address + (4 if mode == "arm" else 2) > rom_end:
            problems.add("outside ROM")
        if address % (4 if mode == "arm" else 2):
            problems.add("unaligned start")
        if address in starts:
            problems.add("duplicate start")
        starts[address] = mode
    return starts, {address: problems for address, problems in issues.items() if problems}


def refinement_ranges(intervals):
    """Merge occupied byte intervals without assigning meaning to gaps."""
    ranges = []
    for start, end in sorted(intervals):
        if ranges and start <= ranges[-1][1]:
            ranges[-1][1] = max(ranges[-1][1], end)
        else:
            ranges.append([start, end])
    return ranges


def refinement_word_switch(data, address, position, end, engine, *,
                           same_owner_long_branches=False, one_object_word_switch=False):
    """Recognize one adjacent guarded word table within the bounded window.

    This reuses the byte-exact matching parser, without inventing ELF relocation
    provenance. The enclosing CFG must separately prove the guard predecessors.
    """
    dispatch = position - address - 8
    if dispatch < 0:
        return None

    def instruction(offset):
        if offset < 0 or offset % 2 or address + offset + 2 > end:
            return None
        decoded = next(engine.disasm(data[offset:offset + 4], address + offset,
                                     count=1), None)
        return decoded if decoded is not None and decoded.size == 2 else None

    load = instruction(dispatch + 2)
    if load is None or load.mnemonic != "ldr" or len(load.operands) != 2 or \
            load.operands[1].type != ARM_OP_MEM or \
            load.operands[1].mem.base != ARM_REG_PC:
        return None
    literal = (((address + dispatch + 6) & ~3) + load.operands[1].mem.disp) - address
    candidates = []
    for guard_size in ((4, 6, 8) if same_owner_long_branches else (4, 6)):
        compare = instruction(dispatch - guard_size)
        if compare is None or compare.mnemonic != "cmp" or \
                len(compare.operands) != 2 or compare.operands[1].type != ARM_OP_IMM or \
                not 0 <= compare.operands[1].imm <= 255:
            continue
        count = compare.operands[1].imm + 1
        table_end = literal + 4 + count * 4
        if literal < dispatch + 10 or (address + literal) % 4 or \
                address + table_end > end:
            continue
        relocations = {offset: struct.unpack_from("<I", data, offset)[0] - address
                       for offset in range(literal, table_end, 4)}
        from match import switch_layout
        for interposed_words in (0, 5):
            if interposed_words and guard_size != 6:
                continue
            try:
                descriptor = switch_layout(data[:end - address], address, relocations,
                                           interposed_words=interposed_words)
            except ValueError:
                continue
            if descriptor["dispatch"] == dispatch and \
                    descriptor["comparison"] == dispatch - guard_size:
                if interposed_words:
                    descriptor["interposed_words"] = interposed_words
                candidates.append(descriptor)
        if one_object_word_switch and literal >= 4:
            object_word = literal - 4
            value = struct.unpack_from("<I", data, object_word)[0]
            try:
                descriptor = switch_layout(data[:end - address], address, relocations,
                    {object_word: ("inventory_object_word", value)})
            except ValueError:
                continue
            if descriptor["dispatch"] == dispatch and descriptor["comparison"] == dispatch - guard_size:
                descriptor["interposed_words"] = 1
                candidates.append(descriptor)
    return candidates[0] if len(candidates) == 1 else None


def refinement_arm_instruction(instruction):
    """Classify a conservative ARMv4T subset, without resolving indirect edges.

    Raw encoding checks exclude extension/system instructions even when the
    decoder recognizes a newer architecture. Return forms are syntactic only.
    """
    word = int.from_bytes(instruction.bytes, "little")
    conditional = word >> 28 != 14
    result = {"kind": "ordinary", "conditional": conditional, "literal": None}

    def reject(reason):
        return {**result, "reason": reason}

    if instruction.size != 4 or word >> 28 == 15:
        return reject("unsupported ARM encoding or cross-mode transfer")
    if word & 0x0E000000 == 0x0A000000:
        displacement = (word & 0xFFFFFF) << 2
        if displacement & 0x02000000:
            displacement -= 0x04000000
        return {**result, "kind": "call" if word & 0x01000000 else "branch",
                "target": instruction.address + 8 + displacement}
    if word & 0x0FFFFFF0 == 0x012FFF10:
        if word & 15 == 14:
            return {**result, "kind": "return"}
        return reject("unresolved or cross-mode ARM transfer")
    if word & 0x0FFFFFF0 == 0x012FFF30:
        return reject("unsupported cross-mode transfer")
    if word & 0x0FFFFFFF == 0x01A0F00E or (
            word & 0x0FFF0000 == 0x08BD0000 and word & 0x8000 and not word & 0x2000):
        return {**result, "kind": "return"}

    name = instruction.insn_name()
    data_names = {"adc", "add", "and", "asr", "bic", "cmn", "cmp", "eor",
                  "lsl", "lsr", "mov", "mvn", "orr", "ror", "rrx", "rsb",
                  "rsc", "sbc", "sub", "teq", "tst"}
    test_opcode = (word >> 21) & 15 in (8, 9, 10, 11)
    data_encoding = word & 0x0C000000 == 0 and (
        word & 0x02000000 or word & 0x90 != 0x90) and (
        not test_opcode or word & 0x00100000 and not word & 0x0000F000)
    multiply = name in {"mul", "mla"} and word & 0x0FC000F0 == 0x00000090
    transfer = name in {"ldr", "ldrb", "str", "strb"} and \
        word & 0x0C000000 == 0x04000000 and (not word & 0x02000000 or not word & 0x10)
    halfword = name in {"ldrh", "ldrsb", "ldrsh", "strh"} and \
        word & 0x0E000090 == 0x00000090
    multiple = name in {"ldm", "ldmda", "ldmdb", "ldmib", "pop", "push",
                        "stm", "stmda", "stmdb", "stmib"} and \
        word & 0x0E400000 == 0x08000000
    if not (name in data_names and data_encoding or multiply or transfer or halfword or multiple):
        return reject("unsupported ARM instruction")
    if multiple:
        registers = word & 0xFFFF
        base = 1 << ((word >> 16) & 15)
        # ARMv4T STM stores the original base only when it is the lowest
        # listed register. LDM/base writeback and other STM overlaps stay out.
        stores_base_first = not word & 0x00100000 and registers & -registers == base
        if not registers or word & 0x00200000 and registers & base and not stores_base_first:
            return reject("unsupported ARM register-list writeback")
    try:
        reads, writes = instruction.regs_access()
    except Exception:
        return reject("unavailable ARM register access")
    operands = instruction.operands
    if ARM_REG_PC in writes or any(operand.type == ARM_OP_REG and operand.reg == ARM_REG_PC
                                   for operand in operands[:1]):
        return reject("unsupported ARM PC write")
    # Only an immediate, preindexed word read with no writeback owns a literal.
    if transfer and name == "ldr" and word & 0x0F7F0000 == 0x051F0000:
        displacement = word & 0xFFF
        if not word & 0x00800000:
            displacement = -displacement
        return {**result, "literal": instruction.address + 8 + displacement}
    if ARM_REG_PC in reads or any(
            operand.type == ARM_OP_REG and operand.reg == ARM_REG_PC or
            operand.type == ARM_OP_MEM and ARM_REG_PC in (operand.mem.base, operand.mem.index)
            for operand in operands):
        return reject("unsupported ARM PC read")
    return result


def refine_function(data, address, functions, max_bytes=4096, max_instructions=1024,
                    rom_end=CODE_END, *, stack_adjusted_returns=False,
                    same_owner_long_branches=False, full_rom_inventory=False,
                    arm_inventory=False, one_object_word_switch=False):
    """Inspect a byte window beginning at an indexed entry, with ARM opt-in.

    The opt-in local-long-branch discovery still grants no ABI or match admission;
    its complete CFG must pass the existing restoring-frame proof separately.
    Closure is structural, assuming ordinary calls return to their continuation
    and syntactic ABI return forms terminate the path. It is not a return-value,
    stack-safety, exact-symbol, or exhaustive-inventory proof.
    Full-ROM inventory only extends the diagnostic address ceiling, bounded by
    the supplied ROM end and the original 16 MiB image, never its mirrors.
    """
    result = {
        "profile": "bounded-thumb-cfg-inventory-v1",
        "rom": f"0x{address:08X}" if type(address) is int else None,
        "mode": None,
        "index_issue_counts": {},
        "complete": False,
        "inventory_complete": False,
        "cfg_closed": False,
        "return_policy": "syntactic ABI return forms; no stack-safety proof",
        "call_policy": "indexed direct Thumb calls; continuation only",
        "window": None,
        "candidate_extent": None,
        "instrs": 0,
        "code_ranges": [],
        "literal_ranges": [],
        "literal_reads": [],
        "word_switches": [],
        "gaps": [],
        "calls": [],
        "returns": [],
        "partial_reasons": [],
    }
    reasons = set()

    def fail(reason, position=None):
        reasons.add(reason if position is None else f"{reason} at 0x{position:08X}")

    code_end = 0x09000000 if full_rom_inventory is True else CODE_END
    if type(address) is not int or address % 2 or not ROM_BASE + HEADER_LEN <= address < code_end:
        fail("invalid entry address")
    if not isinstance(data, (bytes, bytearray)):
        fail("window must contain bytes")
    if type(max_bytes) is not int or max_bytes <= 0 or \
            type(max_instructions) is not int or max_instructions <= 0:
        fail("budgets must be positive integers")
    if type(rom_end) is not int or rom_end < ROM_BASE:
        fail("invalid ROM end")
    if type(same_owner_long_branches) is not bool:
        fail("local long-branch inventory opt-in must be Boolean")
    if type(full_rom_inventory) is not bool:
        fail("full-ROM inventory opt-in must be Boolean")
    if type(arm_inventory) is not bool:
        fail("ARM inventory opt-in must be Boolean")
    if type(one_object_word_switch) is not bool:
        fail("one-object-word switch inventory opt-in must be Boolean")
    if reasons:
        result["partial_reasons"] = sorted(reasons)
        return result
    try:
        if full_rom_inventory:
            rom_end = min(rom_end, code_end)
            result["full_rom_inventory"] = True
        starts, index_issues = refinement_boundaries(
            functions, rom_end, full_rom_inventory=full_rom_inventory)
    except ValueError as error:
        fail(f"invalid function index: {error}")
        starts = {}
        index_issues = {}
    result["index_issue_counts"] = dict(sorted(Counter(
        problem for problems in index_issues.values() for problem in problems).items()))
    if reasons:
        result["partial_reasons"] = sorted(reasons)
        return result
    result["mode"] = starts.get(address)
    if address not in starts:
        fail("entry is not indexed")
    elif address in index_issues:
        fail("invalid indexed entry: " + ", ".join(sorted(index_issues[address])))
    elif starts[address] != "thumb" and not arm_inventory:
        fail("unsupported ARM entry")
    if reasons:
        result["partial_reasons"] = sorted(reasons)
        return result
    previous_start = max((start for start in starts if ROM_BASE + HEADER_LEN <= start < address),
                         default=None)
    next_start = min((start for start in starts if address < start < code_end), default=code_end)
    limits = {"provided window": address + len(data), "byte budget": address + max_bytes,
              "indexed boundary": next_start, "code boundary": code_end, "ROM boundary": rom_end}
    end = min(limits.values())
    result["window"] = {
        "start": f"0x{address:08X}",
        "end": f"0x{end:08X}",
        "max_bytes": max_bytes,
        "max_instructions": max_instructions,
        "limiting_boundaries": sorted(name for name, limit in limits.items() if limit == end),
    }
    for start in (previous_start, next_start if next_start <= end else None):
        if start in index_issues:
            fail("ambiguous neighboring start: " + ", ".join(sorted(index_issues[start])), start)
    if reasons:
        result["partial_reasons"] = sorted(reasons)
        return result
    arm_mode = starts[address] == "arm"
    alignment = 4 if arm_mode else 2
    if arm_mode:
        result["profile"] = "bounded-arm-cfg-inventory-v1"
        result["call_policy"] = "indexed direct ARM calls; continuation only"
        result["return_policy"] = "syntactic ARM bx lr/mov pc,lr/pop pc; no stack-safety proof"
    engine = Cs(CS_ARCH_ARM, CS_MODE_ARM if arm_mode else CS_MODE_THUMB)
    engine.detail = True
    engine.skipdata = False
    supported = {
        "adcs", "add", "adds", "ands", "asrs", "b", "beq", "bne", "bhs", "blo",
        "bmi", "bpl", "bvs", "bvc", "bhi", "bls", "bge", "blt", "bgt", "ble",
        "bics", "bl", "bx", "cmn", "cmp", "eors", "ldm", "ldr", "ldrb", "ldrh",
        "ldrsb", "ldrsh", "lsls", "lsrs", "mov", "movs", "muls", "mvns", "negs",
        "orrs", "pop", "push", "rors", "rsbs", "sbcs", "stm", "str", "strb",
        "strh", "sub", "subs", "tst",
    }
    pending = [(address, ())]
    visited = set()
    instructions = {}
    owners = {}
    literals = set()
    literal_bytes = set()
    literal_reads = {}
    calls = set()
    returns = set()
    edges = set()
    switches = {}

    def follow(source, target, previous_pop=()):
        edges.add((source, target))
        pending.append((target, previous_pop))

    while pending:
        position, previous_pop = pending.pop()
        state = (position, previous_pop)
        if state in visited:
            continue
        visited.add(state)
        if position % alignment or not address <= position or position + alignment > end:
            fail("control-flow boundary escape", position)
            continue
        if position in literal_bytes:
            fail("code/literal overlap", position)
            continue
        if position in owners and owners[position] != position:
            fail("instruction-interior target", position)
            continue
        if position not in instructions and len(instructions) >= max_instructions:
            fail("instruction budget exhausted", position)
            continue
        offset = position - address
        instruction = next(engine.disasm(data[offset:offset + min(4, end - position)],
                                         position, count=1), None)
        if instruction is None:
            fail("invalid or truncated instruction", position)
            continue
        info = Decoder._describe(instruction)
        size = instruction.size
        if position + size > end:
            fail("instruction crosses boundary", position)
            continue
        occupied = range(position, position + size)
        if any(byte in owners and owners[byte] != position for byte in occupied):
            fail("overlapping instructions", position)
            continue
        if any(byte in literal_bytes for byte in occupied):
            fail("code/literal overlap", position)
            continue
        instructions[position] = size
        owners.update((byte, position) for byte in occupied)
        if arm_mode:
            arm = refinement_arm_instruction(instruction)
            if "reason" in arm:
                fail(arm["reason"], position)
                continue
            literal = arm["literal"]
            if literal is not None:
                inside = literal % 4 == 0 and address <= literal and literal + 4 <= end
                literal_reads[position] = {
                    "site": f"0x{position:08X}", "address": f"0x{literal:08X}",
                    "size": 4, "inside_window": inside,
                }
                if literal % 4:
                    fail("unaligned ARM literal", position)
                elif not inside:
                    fail("literal outside window", position)
                else:
                    literals.add(literal)
                    literal_bytes.update(range(literal, literal + 4))
                    if any(byte in owners for byte in range(literal, literal + 4)):
                        fail("code/literal overlap", literal)
            if arm["kind"] == "return":
                returns.add(position)
                if arm["conditional"]:
                    follow(position, position + size)
            elif arm["kind"] == "branch":
                follow(position, arm["target"])
                if arm["conditional"]:
                    follow(position, position + size)
            elif arm["kind"] == "call":
                target = arm["target"]
                if address <= target < end:
                    fail("ambiguous local ARM BL", position)
                elif target not in starts:
                    fail("unmapped ARM call target", position)
                elif target in index_issues:
                    fail("ambiguous ARM call target", position)
                elif starts[target] != "arm":
                    fail("unsupported cross-mode ARM call", position)
                else:
                    calls.add((position, target))
                follow(position, position + size)
            else:
                follow(position, position + size)
            continue
        if instruction.mnemonic == "blx":
            fail("unsupported cross-mode transfer", position)
            continue
        if instruction.mnemonic not in supported or \
                (size != 2 and not (size == 4 and instruction.mnemonic == "bl")):
            fail("unsupported instruction", position)
            continue
        if size == 4:
            first, second = struct.unpack_from("<HH", data, offset)
            if first & 0xF800 != 0xF000 or second & 0xF800 != 0xF800:
                fail("unsupported Thumb BL encoding", position)
                continue
        if info["pcldr"] is not None:
            literal = ((position + 4) & ~3) + info["pcldr"][1]
            literal_reads[position] = {
                "site": f"0x{position:08X}", "address": f"0x{literal:08X}",
                "size": 4, "inside_window": address <= literal and literal + 4 <= end,
            }
            if literal % 4 or not address <= literal or literal + 4 > end:
                fail("literal outside window", position)
            else:
                literals.add(literal)
                literal_bytes.update(range(literal, literal + 4))
                if any(byte in owners for byte in range(literal, literal + 4)):
                    fail("code/literal overlap", literal)
        popped_return = instruction.mnemonic == "bx" and (
            previous_pop == (info["opreg"],) or stack_adjusted_returns and
            previous_pop == (info["opreg"], "stack-adjusted"))
        if info["ret"] or popped_return:
            returns.add(position)
            continue
        if info["call"]:
            target = info["tgt"] + ROM_BASE if info["tgt"] is not None else None
            if target is None:
                fail("unresolved call", position)
            elif address <= target < end:
                if same_owner_long_branches:
                    from local_long_branch_profile import target as local_target
                    try:
                        destination = local_target(instruction, address, end)
                    except ValueError as error:
                        fail(f"invalid local long branch: {error}", position)
                    else:
                        follow(position, destination)
                    continue
                fail("ambiguous local BL", position)
            elif target not in starts:
                fail("unmapped call target", position)
            elif target in index_issues:
                fail("ambiguous call target", position)
            elif starts[target] != "thumb":
                fail("unsupported cross-mode call", position)
            else:
                calls.add((position, target))
            follow(position, position + size)
            continue
        if info["jump"] or info["writes_pc"]:
            if info["tgt"] is None or instruction.mnemonic == "bx":
                switch = refinement_word_switch(
                    data, address, position, end, engine,
                    same_owner_long_branches=same_owner_long_branches,
                    one_object_word_switch=one_object_word_switch)
                if switch is None:
                    fail("unresolved jump", position)
                    continue
                switches[position] = switch
                for word in range(switch["literal"] - 4 * switch.get("interposed_words", 0),
                                  switch["literal"], 4):
                    literal = address + word
                    literals.add(literal)
                    literal_bytes.update(range(literal, literal + 4))
                    if any(byte in owners for byte in range(literal, literal + 4)):
                        fail("code/literal overlap", literal)
                for word, target in switch["relocations"]:
                    literal = address + word
                    literals.add(literal)
                    literal_bytes.update(range(literal, literal + 4))
                    if any(byte in owners for byte in range(literal, literal + 4)):
                        fail("code/literal overlap", literal)
                    if word != switch["literal"]:
                        follow(position, address + target)
                continue
            follow(position, info["tgt"] + ROM_BASE)
            if info["cond"]:
                follow(position, position + size)
            continue
        if any(operand.type == ARM_OP_REG and operand.reg == ARM_REG_PC
               for operand in instruction.operands):
            fail("unsupported PC read", position)
            continue
        # One explicit runtime ABI spills an argument before saving LR, then
        # restores that word after popping the return register. This recognizes
        # only the adjacent pop/add-SP-4/bx shape; the runtime machine-state
        # proof must separately establish LR provenance and balanced SP.
        operands = instruction.operands
        if stack_adjusted_returns and len(previous_pop) == 1 and \
                instruction.mnemonic == "add" and len(operands) == 2 and \
                operands[0].type == ARM_OP_REG and operands[0].reg == ARM_REG_SP and \
                operands[1].type == ARM_OP_IMM and operands[1].imm == 4:
            previous_pop = (previous_pop[0], "stack-adjusted")
        else:
            previous_pop = info["pop_regs"]
        follow(position, position + size, previous_pop)
    for position, switch in sorted(switches.items()):
        comparison, guard, dispatch = (address + switch[field]
                                       for field in ("comparison", "guard", "dispatch"))
        # Every instruction after CMP through MOV PC must have exactly its
        # guarded predecessor. In particular no branch may enter the lookup,
        # reuse stale flags, or execute MOV PC with a forged target register.
        expected = {guard: comparison, dispatch: guard}
        if dispatch - comparison in (6, 8):
            default_site = guard + 2
            if dispatch - comparison == 8:
                if instructions.get(default_site) != 4 or \
                        {source for source, target in edges if target == default_site} != {guard}:
                    fail("word-switch long default can be bypassed", position)
            else:
                expected[default_site] = guard
        expected.update({site: site - 2 for site in range(dispatch + 2, position + 2, 2)})
        if comparison not in instructions or any(
                instructions.get(site) != 2 or
                {source for source, target in edges if target == site} != {predecessor}
                or site == address for site, predecessor in expected.items()):
            fail("word-switch guard can be bypassed", position)
        if switch.get("interposed_words"):
            pool = {address + word for word in range(switch["literal"] - 4 * switch["interposed_words"],
                                                     switch["literal"], 4)}
            read_words = {int(read["address"], 16) for read in literal_reads.values()}
            if not pool <= read_words:
                fail("interposed switch pool requires every reached word load", position)
        result["word_switches"].append({"schema": "bounded-guarded-word-switch-v1", **switch})
    if not returns:
        fail("no recognized return")
    code_ranges = refinement_ranges((start, start + size)
                                    for start, size in instructions.items())
    literal_ranges = refinement_ranges((start, start + 4) for start in literals)
    occupied_ranges = refinement_ranges(code_ranges + literal_ranges)
    gaps = []
    cursor = address
    for start, stop in occupied_ranges:
        if cursor < start:
            gaps.append([cursor, start])
        cursor = stop
    if occupied_ranges:
        result["candidate_extent"] = {
            "start": f"0x{address:08X}", "end": f"0x{cursor:08X}", "bytes": cursor - address,
        }
    for name, ranges in (("code_ranges", code_ranges), ("literal_ranges", literal_ranges),
                         ("gaps", gaps)):
        result[name] = [[f"0x{start:08X}", f"0x{stop:08X}"] for start, stop in ranges]
    result["instrs"] = len(instructions)
    result["literal_reads"] = [literal_reads[site] for site in sorted(literal_reads)]
    result["calls"] = [{"site": f"0x{site:08X}", "target": f"0x{target:08X}"}
                       for site, target in sorted(calls)]
    result["returns"] = [f"0x{site:08X}" for site in sorted(returns)]
    result["partial_reasons"] = sorted(reasons)
    result["cfg_closed"] = not reasons
    return result


def refinement_main(arguments):
    """Run read-only, bounded diagnostics without entering normal discovery."""
    parser = argparse.ArgumentParser(description="Bounded provisional CFG refinement")
    parser.add_argument("rom", nargs="?")
    parser.add_argument("root", nargs="?")
    parser.add_argument("--refine-address", type=lambda value: int(value, 0),
                        action="append", required=True)
    parser.add_argument("--refine-max-bytes", type=lambda value: int(value, 0), default=4096)
    parser.add_argument("--refine-max-instructions", type=lambda value: int(value, 0), default=1024)
    parser.add_argument("--refine-arm-inventory", action="store_true",
                        help="enable bounded ARMv4T CFG diagnostics; grants no function, "
                             "ABI, match or inventory-completeness proof")
    parser.add_argument("--refine-full-rom-inventory", action="store_true",
                        help="allow diagnostic entries in the original ROM, up to 0x09000000; "
                             "grants no function, ABI, match or inventory-completeness proof")
    options = parser.parse_args(arguments)
    here = repo_root(options.root)
    rom_path = options.rom or rom_path_default(here)
    output = {"inventory_complete": False, "results": []}
    code_end = 0x09000000 if options.refine_full_rom_inventory else CODE_END
    if options.refine_full_rom_inventory:
        output["full_rom_inventory"] = True
    if options.refine_arm_inventory:
        output["arm_inventory"] = True

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate JSON object key")
            result[key] = value
        return result

    try:
        if options.refine_max_bytes <= 0 or options.refine_max_instructions <= 0:
            raise ValueError("budgets must be positive integers")
        with open(os.path.join(here, "config", "functions.json"), encoding="utf-8") as stream:
            functions = json.load(stream, object_pairs_hook=unique_object)
        with open(rom_path, "rb") as stream:
            rom_end = ROM_BASE + os.fstat(stream.fileno()).st_size
            if options.refine_full_rom_inventory:
                rom_end = min(rom_end, code_end)
            starts, _ = refinement_boundaries(
                functions, rom_end, full_rom_inventory=options.refine_full_rom_inventory)
            for address in options.refine_address:
                data = b""
                if address in starts and ROM_BASE + HEADER_LEN <= address < min(code_end, rom_end):
                    next_start = min((start for start in starts if address < start < code_end),
                                     default=code_end)
                    end = min(address + options.refine_max_bytes, next_start, code_end, rom_end)
                    stream.seek(address - ROM_BASE)
                    data = stream.read(end - address)
                output["results"].append(refine_function(
                    data, address, functions, options.refine_max_bytes,
                    options.refine_max_instructions, rom_end,
                    full_rom_inventory=options.refine_full_rom_inventory,
                    arm_inventory=options.refine_arm_inventory))
    except (OSError, ValueError) as error:
        output["error"] = str(error)
        print(json.dumps(output, indent=2))
        return 2
    print(json.dumps(output, indent=2))
    return 0


# --------------------------------------------------------------------------
# recursive-descent code discovery
# --------------------------------------------------------------------------

class Analyzer:
    def __init__(self, rom, dec):
        self.rom = rom
        self.dec = dec
        self.n = len(rom)
        self.code_limit = min(self.n, CODE_END - ROM_BASE)
        # coverage: one byte per 4-byte word (size) or 2-byte halfword (thumb)
        self.arm_seen = bytearray((self.n + 3) // 4)
        self.thumb_seen = bytearray((self.n + 1) // 2)
        self.covered = bytearray(self.n)   # 0 none, 1 arm, 2 thumb (verified)
        self.reached = bytearray(self.n)   # everything the walker stepped on
        self.functions = {}          # off -> dict
        self.externs = Counter()     # addresses left outside ROM (RAM/BIOS calls)
        self.calls = Counter()       # in-ROM call targets seen so far
        self.entry_targets = set() # where the entry point transfers to
        self.in_entry = False
        self.indirect = 0            # indirect transfers seen
        self.switch_tables = 0
        self.max_func_instr = 4000

    # -- helpers
    def in_rom(self, off, size):
        return 0 <= off and off + size <= self.n

    def in_code(self, off, size):
        return 0 <= off and off + size <= self.code_limit

    def prologue_ish(self, off, thumb=False):
        """cheap ARM/Thumb prologue test used to seed candidate functions"""
        if thumb:
            if off & 1 or not self.in_code(off, 2):
                return False
            w = struct.unpack_from("<H", self.rom, off)[0]
            return (w >> 8) in (0xB4, 0xB5)      # push {rlist[,lr]}
        if off & 3 or not self.in_code(off, 4):
            return False
        w = struct.unpack_from("<I", self.rom, off)[0]
        if (w & 0x0FFF0000) == 0x092D0000:      # stmdb sp!, {regs...}  (ARM push)
            return True
        if (w & 0x0FFF0000) == 0x09240000:      # stmib sp!, {regs...}
            return True
        if (w & 0x0FFF0000) == 0x052D0000 and (w & 0x4000) and (w & 0x1000):
            return True                         # str lr, [sp, #-imm]!  (single-reg push)
        return False

    # -- traversal -------------------------------------------------------
    def literal(self, off, thumb, disp):
        """value of `ldr rX, [pc, #disp]` at `off`"""
        pc = (off + 4) & ~3 if thumb else off + 8
        a = pc + disp
        if 0 <= a and a + 4 <= self.n:
            return struct.unpack_from("<I", self.rom, a)[0]
        return None

    def thumb_switch_targets(self, offset):
        """Recognize the bounded cmp/bls/word-table pattern as discovery evidence."""
        def instruction(position):
            if position % 2 or not self.in_code(position, 2):
                return None
            decoded = next(self.dec.thumb.disasm(self.rom[position:position + 4],
                                                ROM_BASE + position, count=1), None)
            return decoded if decoded is not None and decoded.size == 2 else None

        comparison = instruction(offset - 2)
        guard = instruction(offset)
        if comparison is None or guard is None or comparison.mnemonic != "cmp" or \
                guard.mnemonic != "bls" or len(comparison.operands) != 2 or \
                comparison.operands[0].type != ARM_OP_REG or \
                comparison.operands[1].type != ARM_OP_IMM or \
                not 0 <= comparison.operands[1].imm <= 255 or \
                len(guard.operands) != 1 or guard.operands[0].type != ARM_OP_IMM:
            return ()
        dispatch = guard.operands[0].imm - ROM_BASE
        if dispatch <= offset:
            return ()
        sequence = [instruction(dispatch + distance) for distance in range(0, 10, 2)]
        if any(item is None or item.cc not in (ARM_CC_AL, ARM_CC_INVALID)
               for item in sequence) or \
                tuple(item.mnemonic for item in sequence) != ("lsls", "ldr", "adds", "ldr", "mov"):
            return ()
        shift, literal, addition, load, transfer = (item.operands for item in sequence)
        if len(shift) != 3 or shift[0].type != ARM_OP_REG or \
                shift[1].type != ARM_OP_REG or shift[1].reg != comparison.operands[0].reg or \
                shift[2].type != ARM_OP_IMM or shift[2].imm != 2:
            return ()
        accumulator = shift[0].reg
        if len(literal) != 2 or literal[0].type != ARM_OP_REG or \
                literal[0].reg == accumulator or literal[1].type != ARM_OP_MEM or \
                literal[1].mem.base != ARM_REG_PC or literal[1].mem.index or \
                literal[1].mem.disp < 0 or literal[1].mem.disp % 4:
            return ()
        if len(addition) != 3 or any(operand.type != ARM_OP_REG for operand in addition) or \
                tuple(operand.reg for operand in addition) != (accumulator, accumulator, literal[0].reg):
            return ()
        if len(load) != 2 or load[0].type != ARM_OP_REG or load[0].reg != accumulator or \
                load[1].type != ARM_OP_MEM or load[1].mem.base != accumulator or \
                load[1].mem.index or load[1].mem.disp:
            return ()
        if len(transfer) != 2 or any(operand.type != ARM_OP_REG for operand in transfer) or \
                tuple(operand.reg for operand in transfer) != (ARM_REG_PC, accumulator):
            return ()
        pool = ((dispatch + 6) & ~3) + literal[1].mem.disp
        table = pool + 4
        count = comparison.operands[1].imm + 1
        if pool < dispatch + 10 or not self.in_code(pool, 4 + count * 4) or \
                struct.unpack_from("<I", self.rom, pool)[0] != ROM_BASE + table:
            return ()
        targets = tuple(value - ROM_BASE for value in
                        struct.unpack_from(f"<{count}I", self.rom, table))
        if any(target % 2 or target < HEADER_LEN or not self.in_code(target, 2) or
               offset - 2 <= target < table + count * 4 for target in targets):
            return ()
        return targets

    def traverse(self, start, thumb=False, seed_known=None):
        """Walk from `start` following branches; mode switches on BX/BLX/bit0.

        `ldr rX,[pc,#imm]` is resolved so the common `ldr r1,...; bx r1`
        startup pattern walks into the real code instead of dead-ending.
        returns (instr_count, lo_off, hi_off, ended_by)
        """
        thumb = thumb or bool(start & 1)
        start = start & ~1 if thumb else start
        stack = [(start, thumb, seed_known or {})]
        lo = hi = start
        count = 0
        ended = "fallthrough"
        while stack:
            off, thumb, known = stack.pop()
            unit = 2 if thumb else 4
            seen = self.thumb_seen if thumb else self.arm_seen
            while self.in_code(off, unit):
                idx = off // unit
                if seen[idx]:
                    break
                info = self.dec.thumb_ins(off) if thumb else self.dec.arm_ins(off)
                if info is None:
                    ended = "badinsn"
                    break
                size = info["sz"]
                if not self.in_code(off, size):
                    ended = "code-boundary"
                    break
                for position in range(off, off + size, unit):
                    seen[position // unit] = 1
                count += 1
                lo = min(lo, off)
                hi = max(hi, off + size)
                for i in range(off, off + size):
                    self.reached[i] = 2 if thumb else 1

                for r in info["wr"]:
                    known.pop(r, None)
                if info["pcldr"] is not None:
                    reg, disp = info["pcldr"]
                    val = self.literal(off, thumb, disp)
                    if val is not None:
                        known[reg] = val

                if thumb and info["mn"] == "bls":
                    switch_targets = self.thumb_switch_targets(off)
                    if switch_targets:
                        self.switch_tables += 1
                        stack.extend((target, True, {}) for target in sorted(set(switch_targets)))

                tgt = info["tgt"]
                if tgt is None and info["opreg"] is not None:
                    val = known.get(info["opreg"])
                    if val is not None:
                        tgt = val - ROM_BASE

                if tgt is not None and (info["jump"] or info["call"] or info["mn"] in ("bx", "blx")):
                    mn = info["mn"]
                    if mn in ("bx", "blx") and info["opreg"] is not None:
                        tthumb = bool(tgt & 1)   # interworking register branch
                    elif mn == "blx":
                        tthumb = not thumb
                    else:
                        tthumb = thumb           # b/bl stay in the current mode
                    toff = tgt & ~1
                    if self.in_code(toff, 2 if tthumb else 4) and not (not tthumb and toff & 3):
                        target = ROM_BASE + toff + int(tthumb)
                        if info["call"]:
                            self.calls[target] += 1
                        if self.in_entry:
                            self.entry_targets.add(target)
                        stack.append((toff, tthumb, {}))
                        if info["call"]:
                            known.clear()
                        elif not info["cond"]:
                            ended = "branch"
                            break
                        off += size
                        continue
                    if info["call"]:
                        ended = "call-out"
                        known.clear()
                    else:
                        self.externs[ROM_BASE + toff] += 1
                        ended = "branch-out"
                    if not info["cond"] and not info["call"]:
                        break
                    off += size
                    continue

                if info["ret"]:
                    ended = "return"
                    if not info["cond"]:
                        break
                elif info["call"]:
                    self.indirect += 1
                    known.clear()
                elif info["jump"] or info["writes_pc"]:
                    self.indirect += 1
                    ended = "indirect"
                    if not info["cond"]:
                        break
                off += size
        return count, lo, hi, ended

    def linear_body(self, off, thumb, limit=0x400):
        """Length of a straight-line instruction block at `off`.

        Functions found by walking the call graph are only known to start
        somewhere; a linear block keeps their asm assembleable instead of
        sweeping a literal pool in as instructions.
        """
        unit = 2 if thumb else 4
        position = off & ~1 if thumb else off
        count = 0
        previous_pop = ()
        ended = "fallthrough"
        while count < limit and self.in_code(position, unit):
            info = self.dec.thumb_ins(position) if thumb else self.dec.arm_ins(position)
            if info is None:
                ended = "badinsn"
                break
            if not self.in_code(position, info["sz"]):
                ended = "code-boundary"
                break
            count += 1
            position += info["sz"]
            popped_return = info["mn"] == "bx" and previous_pop == (info["opreg"],)
            if info["ret"] or popped_return:
                ended = "conditional-return" if info["cond"] else "return"
                break
            if not info["call"] and (info["jump"] or info["writes_pc"]):
                ended = "branch" if info["tgt"] is not None else "indirect"
                break
            previous_pop = info["pop_regs"]
        else:
            if count >= limit:
                ended = "limit"
        return count, position, ended

    def discover(self):
        """Entry point first, then every in-ROM call target, then ARM prologues.

        Call targets are the only trustworthy function starts in this ROM:
        a blind Thumb prologue scan matches ~16k false positives inside the
        4bpp tile data, where the byte pair 0xB5 is just two palette indices.
        """
        self.in_entry = True
        c, lo, hi, end = self.traverse(0xC0)
        self.in_entry = False
        n, stop, endby = self.linear_body(0xC0, thumb=False)
        if c:
            self.functions[0xC0] = {"start": 0xC0, "end": stop, "instrs": n,
                                    "kind": "entry", "mode": "arm", "endby": endby}
            for i in range(0xC0, stop):
                self.covered[i] = 1
        say(f"  entry 0x080000C0: walk {c} instrs to 0x{hi:X} ({end}); "
            f"body {n} instrs to 0x{stop:X}")

        # ---- pass 2: every in-ROM call target reached from the entry walk is a
        # function; take its straight-line body only (recursing here would
        # walk data-as-code and never terminate)
        added = 0
        for addr in sorted(set(self.calls) | self.entry_targets):
            off = (addr & ~1) - ROM_BASE
            if not self.in_code(off, 2 if addr & 1 else 4) or off in self.functions:
                continue
            tthumb = bool(addr & 1)
            n, stop, endby = self.linear_body(off, tthumb)
            if n < 2:
                continue
            self.functions[off] = {"start": off, "end": stop, "instrs": n,
                                   "kind": "call", "mode": "thumb" if tthumb else "arm",
                                   "endby": endby}
            for i in range(off, stop):
                self.covered[i] = 2 if tthumb else 1
            added += 1
        say(f"  call targets: +{added} functions ({len(self.functions)} total)")

        # ---- pass 3: verified prologue scan, ARM then Thumb
        added = self.scan_arm_functions()
        say(f"  arm prologue pass: +{added} functions ({len(self.functions)} total)")
        added = self.scan_thumb_functions()
        say(f"  thumb prologue pass: +{added} functions ({len(self.functions)} total)")
        return len(self.functions)

    def scan_candidates(self):
        """Every 4-aligned address that begins with an ARM push prologue."""
        return [off for off in range(HEADER_LEN, self.code_limit - 3, 4)
                if self.prologue_ish(off, thumb=False)]

    def verify_thumb(self, off, limit=128):
        """Linear-verify a Thumb candidate: push {...lr} ... pop {..,pc}/bx lr.

        Returns (instrs, end_off) or None.  This is what separates real
        functions from the 0xB5xx byte pairs that tile data throws off.

        `pop {r0}; bx r0` is the Thumb interworking return - capstone does not
        flag it as a return, so it is recognised here, otherwise every
        function using that epilogue swallows the next one.
        """
        if off & 1 or not self.in_code(off, 2):
            return None
        h = struct.unpack_from("<H", self.rom, off)[0]
        if (h >> 8) != 0xB5:                # must be `push {rlist, lr}`
            return None
        count, end, endby = self.linear_body(off, True, limit)
        if endby == "return" and count >= 5:
            return count, end
        return None

    def scan_thumb_functions(self):
        """Find provisional Thumb functions within the FFTA code region."""
        found = 0
        for off in range(HEADER_LEN, self.code_limit - 1, 2):
            if self.thumb_seen[off // 2]:
                continue
            r = self.verify_thumb(off)
            if r is None:
                continue
            n, end = r
            for o in range(off, end):
                self.covered[o] = 2
            for o in range(off, end, 2):
                self.thumb_seen[o // 2] = 1
            if off not in self.functions:
                self.functions[off] = {"start": off, "end": end, "instrs": n,
                                       "kind": "thumb-prologue", "mode": "thumb",
                                       "endby": "return"}
                found += 1
        return found

    def verify_arm(self, off, limit=128):
        """Same check for ARM push prologues."""
        if not self.prologue_ish(off, thumb=False):
            return None
        count, end, endby = self.linear_body(off, False, limit)
        if endby == "return" and count >= 5:
            return count, end
        return None

    def scan_arm_functions(self):
        found = 0
        for off in range(HEADER_LEN, self.code_limit - 3, 4):
            if self.arm_seen[off // 4]:
                continue
            r = self.verify_arm(off)
            if r is None:
                continue
            n, end = r
            for o in range(off, end, 4):
                self.arm_seen[o // 4] = 1
                self.covered[o:o + 4] = b"\x01\x01\x01\x01"
            if off not in self.functions:
                self.functions[off] = {"start": off, "end": end, "instrs": n,
                                       "kind": "arm-prologue", "mode": "arm",
                                       "endby": "return"}
                found += 1
        return found


# --------------------------------------------------------------------------
# header + segmentation
# --------------------------------------------------------------------------

def header_report(rom):
    if len(rom) < HEADER_LEN:
        raise ValueError(f"ROM is shorter than the {HEADER_LEN}-byte cartridge header")
    rep = {}
    title = rom[0xA0:0xAC]
    rep["title"] = title.rstrip(b"\x00").decode("latin-1")
    rep["game_code"] = rom[0xAC:0xB0].decode("latin-1")
    rep["maker_code"] = rom[0xB0:0xB2].decode("latin-1")
    entry_word = struct.unpack_from("<I", rom, 0)[0]
    rep["entry_word"] = f"{entry_word:08X}"
    if (entry_word >> 24) == 0xEA:
        off = ((entry_word & 0x00FFFFFF) << 2) + 8
        rep["entry"] = f"0x{ROM_BASE + off:08X}"
    else:
        rep["entry"] = None
    logo_digest = hashlib.sha256(rom[0x04:0xA0]).hexdigest()
    rep["nintendo_logo_ok"] = logo_digest == NINTENDO_LOGO_SHA256
    rep["nintendo_logo_sha256"] = logo_digest
    checksum = (-sum(rom[0xA0:0xBD]) - 0x19) & 0xFF
    rep["header_checksum"] = {"computed": f"{checksum:02X}", "stored": f"{rom[0xBD]:02X}",
                              "ok": checksum == rom[0xBD]}
    return rep


def entropy(b):
    if not b:
        return 0.0
    c = Counter(b)
    n = len(b)
    return -sum((v / n) * math.log2(v / n) for v in c.values())


def coverage_segments(rom, an, min_run=0x40):
    """Split the ROM into runs of arm / thumb / data using the coverage map."""
    n = len(rom)
    kind = an.covered
    segs = []
    start = 0
    cur = kind[0]
    for i in range(1, n):
        k = kind[i]
        if k != cur:
            segs.append([start, i, cur])
            start, cur = i, k
    segs.append([start, n, cur])
    merged = []
    for s, e, k in segs:
        if k == 0 and e - s < 0x200:          # ignore specks of data
            continue
        if merged and merged[-1][2] == k:
            merged[-1][1] = e
        else:
            merged.append([s, e, k])
    return [tuple(m) for m in merged]


def coverage_table(rom, an, step=0x10000):
    """code bytes per 64 KiB, so the real shape of the ROM is visible"""
    say(f"== code coverage per {step // 1024} KiB ==")
    say(f"  {'rom':<12} {'code':>8} {'%':>6}  {'arm':>7} {'thumb':>7}  entropy")
    for start in range(0, len(rom), step):
        chunk = an.covered[start:start + step]
        arm = chunk.count(1)
        thumb = chunk.count(2)
        tot = arm + thumb
        if tot == 0 and rom[start:start + step].count(0) == len(chunk):
            ent = "0.00"
        else:
            ent = f"{entropy(rom[start:start+step]):.2f}"
        bar = "#" * int(60 * tot / step)
        say(f"  0x{ROM_BASE + start:08X} {tot:8,} {100.0*tot/step:5.1f}%  "
            f"{arm:7,} {thumb:7,}  {ent:>6} {bar}")


def classify(rom, s, e, kind):
    """Give a segment a human/technical name from its content."""
    size = e - s
    chunk = rom[s:e]
    ent = entropy(chunk)
    zero = chunk.count(0)
    if size >= 0x1000 and zero > size * 0.995:
        return "padding", ent
    if kind == 1:
        return "code_arm", ent
    if kind == 2:
        return "code_thumb", ent
    if ent > 7.6:
        return "asset_compressed", ent
    if ent < 4.6:
        return "asset_gfx", ent
    return "data", ent


def main():
    if any(argument.startswith("--refine-") for argument in sys.argv[1:]):
        return refinement_main(sys.argv[1:])
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    here = repo_root(args[1] if len(args) > 1 else None)
    rom_path = args[0] if args else rom_path_default(here)
    json_path = os.path.join(here, "config", "rom_layout.json")
    txt_path = os.path.join(here, "symbols", "functions.txt")
    log_path = os.path.join(here, "logs", "analysis.txt")

    rom = open(rom_path, "rb").read()
    say(f"rom: {rom_path}  {len(rom)} bytes ({len(rom)/1048576:.1f} MiB)")

    hdr = header_report(rom)
    say("== header ==")
    for k, v in hdr.items():
        say(f"  {k}: {v}")

    dec = Decoder(rom)
    an = Analyzer(rom, dec)
    say("== code discovery ==")
    t0 = os.times()
    accepted = an.discover()
    say(f"  provisional function extents: {accepted} (inventory incomplete)")
    say(f"  ARM words covered: {sum(an.arm_seen)} / {len(an.arm_seen)}")
    say(f"  Thumb halfwords covered: {sum(an.thumb_seen)} / {len(an.thumb_seen)}")
    say(f"  code bytes: {sum(1 for v in an.covered if v):,} of {len(rom):,}")

    coverage_table(rom, an)
    segs = coverage_segments(rom, an)
    say("== segments ==")
    out_segs = []
    for s, e, kind in segs:
        name, ent = classify(rom, s, e, kind)
        say(f"  {s:08X}-{e:08X} {e-s:9,} {name:<18} entropy {ent:.2f}")
        out_segs.append({
            "name": name,
            "rom_start": f"0x{ROM_BASE + s:08X}",
            "file_start": f"0x{s:08X}",
            "rom_end": f"0x{ROM_BASE + e:08X}",
            "size": e - s,
            "entropy": round(ent, 3),
            "file": f"files/{name}_{s:08X}.bin",
        })

    funcs = sorted(an.functions.values(), key=lambda f: f["start"])
    os.makedirs(os.path.dirname(txt_path), exist_ok=True)
    with open(txt_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("# FFTA - provisional function extents (addr end size instrs endby)\n")
        for fn in funcs:
            f.write(f"{ROM_BASE + fn['start']:08X} {ROM_BASE + fn['end']:08X} "
                    f"{fn['end'] - fn['start']:6d} {fn['instrs']:5d} {fn['endby']}\n")
    say(f"  wrote {txt_path} ({len(funcs)} functions)")

    layout = {
        "rom": os.path.basename(rom_path),
        "size": len(rom),
        "rom_base": f"0x{ROM_BASE:08X}",
        "header": hdr,
        "stats": {
            "functions": len(funcs),
            "arm_words_covered": int(sum(an.arm_seen)),
            "thumb_halfwords_covered": int(sum(an.thumb_seen)),
            "code_bytes": sum(1 for v in an.covered if v),
            "cached_arm_instructions": len(dec.arm_cache),
            "recognized_switch_tables": an.switch_tables,
            "inventory_complete": False,
        },
        "segments": out_segs,
    }
    os.makedirs(os.path.dirname(json_path), exist_ok=True)
    with open(json_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(layout, f, indent=2)
    say(f"  wrote {json_path}")

    # machine-readable outputs the splitter consumes
    runs = []
    s = 0
    cur = an.covered[0]
    for i in range(1, len(rom)):
        if rom and an.covered[i] != cur:
            runs.append([s, i, cur])
            s, cur = i, an.covered[i]
    runs.append([s, len(rom), cur])
    with open(os.path.join(here, "config", "coverage.json"), "w",
              encoding="utf-8", newline="\n") as f:
        json.dump(runs, f)
    with open(os.path.join(here, "config", "functions.json"), "w",
              encoding="utf-8", newline="\n") as f:
        json.dump([{
            "rom": f"0x{ROM_BASE + fn['start']:08X}",
            "end": f"0x{ROM_BASE + fn['end']:08X}",
            "mode": fn.get("mode", "arm"),
            "instrs": fn["instrs"],
            "kind": fn["kind"],
            "endby": fn["endby"],
            "complete": False,
        } for fn in funcs], f, indent=1)
    say("  wrote config/coverage.json, config/functions.json")

    os.makedirs(os.path.dirname(log_path), exist_ok=True)
    with open(log_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(_LOG) + "\n")


if __name__ == "__main__":
    sys.exit(main())
