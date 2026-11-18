"""Prove the idempotent eighth-argument store in the USA transfer setup leaf."""
import hashlib
import json
import struct
from collections import defaultdict

from capstone.arm import (
    ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_R0, ARM_REG_R1, ARM_REG_R2,
    ARM_REG_R3, ARM_REG_IP, ARM_REG_LR, ARM_REG_SP,
)

import analyze
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
from software_float_profile import ROM_SHA256

SELECTOR = "transfer-masked-stack-argument-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CONTROL_FLOW = "straight-line transfer leaf with an idempotent one-bit store into the eighth stack argument"
ROOT = 0x08037C84
STORE = 0x08037DA2
CALLERS = {
    0x0803AE80: (0x0803B0CE,),
    0x0803BAE8: (0x0803BCD6,),
    0x0803D550: (0x0803D622, 0x0803D64E),
    0x0803F6F8: (0x0803F850,),
    0x08043468: (0x080435CA,),
    0x0804393C: (0x08043A5C,),
    0x08049C24: (0x08049D92, 0x08049DEA),
    0x0804A4CC: (0x0804A67A,),
}
ZERO_CASE = {0x0803BCD6: 0x0803BB20, 0x0803D64E: 0x0803D580}
BINDINGS = {
    "calls": [], "functions": [], "switches": [],
    "data": [[0x140, "g_state_03002810", 0], [0x144, "data_030009E0", 0],
             [0x150, "data_06008000", 0]],
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def references(rom):
    return references_at(rom, ROOT, CALLERS)


def references_at(rom, address, callers):
    """Index raw immediate transfers and unaligned address literals; computed targets are conditional."""
    require(len(rom) == 0x1000000, "complete USA ROM required")
    target = address - match.ROM_BASE
    pairs = []
    short = []
    arm = []
    for off in range(max(0, target - 0x400002), min(len(rom) - 4, target + 0x3FFFFC) + 1, 2):
        delta = target - off - 4
        first, second = struct.unpack_from("<HH", rom, off)
        if -0x400000 <= delta < 0x400000 and (first, second) == (
                0xF000 | (delta >> 12 & 0x7FF), 0xF800 | (delta >> 1 & 0x7FF)):
            pairs.append(off + match.ROM_BASE)
        if (-2048 <= delta <= 2046 and first == (0xE000 | (delta >> 1 & 0x7FF))) or (
                -256 <= delta <= 254 and first >> 12 == 13 and (first >> 8 & 15) < 14
                and first & 255 == (delta >> 1 & 255)):
            short.append(off + match.ROM_BASE)
    for off, (word,) in enumerate(struct.iter_unpack("<I", rom)):
        displacement = target - 4 * off - 8
        if word >> 28 != 15 and (word >> 25 & 7) == 5 and (
                (word & 0xFFFFFF) == (displacement >> 2 & 0xFFFFFF)):
            arm.append(off * 4 + match.ROM_BASE)
    require(pairs == sorted(pc for sites in callers.values() for pc in sites)
            and not short and not arm, "incoming immediate reference set differs")
    require(all(struct.pack("<I", value) not in rom for value in (address, address | 1)),
            "unexpected address literal naming the inventoried entry")
    require(sha(rom) == ROM_SHA256, "approved USA ROM required for reference inventory")
    return dict(thumb_bl=pairs, thumb_short=short, arm_b_bl=arm, address_literals=[])


def predecessors(edges):
    result = defaultdict(set)
    for pc, children in edges.items():
        for child in children:
            result[child].add(pc)
    return result


def backward(ins, pred, owner, use, stop):
    """All native paths backward to their first definition; reject a bypass at entry."""
    pending = list(pred[use])
    seen, found = set(), set()
    while pending:
        pc = pending.pop()
        if pc in seen or pc in found:
            continue
        if stop(ins[pc]):
            found.add(pc)
        else:
            require(pc != owner and pred[pc], "path bypasses required definition")
            seen.add(pc)
            pending.extend(pred[pc])
    require(len(found) == 1, "required unique native definition is absent or ambiguous")
    return found.pop(), seen


def writes(item, reg):
    return reg in item.regs_access()[1] or (
        item.mnemonic == "bl" and reg in (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2,
                                         ARM_REG_R3, ARM_REG_IP, ARM_REG_LR))


def outgoing(ins, pred, site):
    """Four initialized, distinct SP words on a single-entry prefix, with no intervening call."""
    cursor = site
    stores = {}
    while len(stores) < 4:
        require(site - cursor < 48 and len(pred[cursor]) == 1, "ambiguous outgoing argument setup")
        pc = next(iter(pred[cursor]))
        item = ins[pc]
        require(pc + 2 == cursor and item.size == 2, "nonlinear outgoing argument setup")
        raw = int.from_bytes(item.bytes, "little")
        if item.mnemonic == "str":
            offset = (raw & 255) * 4
            require(raw & 0xF800 == 0x9000 and offset == 12 - 4 * len(stores)
                    and item.operands[1].mem.base == ARM_REG_SP
                    and item.operands[1].mem.disp == offset
                    and item.operands[0].reg == ARM_REG_R0 + (raw >> 8 & 7),
                    "outgoing word write lacks its aligned scalar SP slot")
            stores[offset] = pc
        else:
            require(item.mnemonic in ("mov", "movs", "adds", "ldr")
                    and ARM_REG_SP not in item.regs_access()[1], "outgoing prefix changes frame or memory")
        cursor = pc
    return stores


def argument_value(ins, edges, pred, caller, site, store):
    reg = ins[store].operands[0].reg
    source, _ = backward(ins, pred, caller, store, lambda it: writes(it, reg))
    item = ins[source]
    if item.mnemonic == "movs" and item.operands[1].type == ARM_OP_IMM:
        value = item.operands[1].imm
        require(value in (0, 1), "eighth word is not a Boolean immediate")
        return dict(value=value, definition=source)
    branch = ZERO_CASE.get(site)
    require(branch in ins and item.mnemonic == "ldrb", "eighth word lacks a native Boolean definition")
    cmp = ins[branch - 2]
    require(ins[branch].mnemonic == "beq" and pred[branch] == {branch - 2}
            and cmp.mnemonic == "cmp" and cmp.operands[0].type == ARM_OP_REG
            and cmp.operands[0].reg == reg and cmp.operands[1].type == ARM_OP_IMM
            and cmp.operands[1].imm == 0, "phase case lacks exact zero test")
    before, _ = backward(ins, pred, caller, cmp.address, lambda it: writes(it, reg))
    require(before == source, "zero test uses another value")
    taken = ins[branch].operands[0].imm
    pending, reachable = [caller], set()
    while pending:
        pc = pending.pop()
        if pc in reachable:
            continue
        reachable.add(pc)
        pending.extend(child for child in edges[pc] if (pc, child) != (branch, taken))
    require(store not in reachable, "a path to the eighth word bypasses the zero case")
    _, guarded = backward(ins, pred, caller, store, lambda it: it.address == branch)
    require(not any(writes(ins[pc], reg) for pc in guarded),
            "phase register is redefined after the taken zero case")
    return dict(value=0, definition=source, zero_case_edge=[branch, taken])


def continuation(ins, edges, calls, site):
    """Describe first direct reuse, call or allocation change; later reuse may observe the same bits."""
    pending, visited, first = [site + 4], set(), {}
    while pending:
        pc = pending.pop()
        if pc in visited:
            continue
        visited.add(pc)
        item = ins[pc]
        width = 1 if item.mnemonic.endswith("b") else 2 if item.mnemonic.endswith("h") else 4
        access = any(op.type == ARM_OP_MEM and op.mem.base == ARM_REG_SP
                     and op.mem.disp < 16 and 12 < op.mem.disp + width for op in item.operands)
        if access or pc in calls or writes(item, ARM_REG_SP) or not edges[pc]:
            first[pc] = [pc, item.mnemonic, item.op_str]
        else:
            pending.extend(edges[pc])
    require(first, "missing transfer caller continuation")
    return [first[pc] for pc in sorted(first)]


def caller_record(rom, mapping, index, rows, caller, sites):
    end = next(int(row["end"], 16) for row in rows if int(row["rom"], 16) == caller)
    data = rom[caller - match.ROM_BASE:end - match.ROM_BASE]
    named.validate_owner(data, caller, rom, mapping, index)
    options = dict(two_constant_word_switch=True) if caller == 0x0803AE80 else {}
    ref = analyze.refine_function(data, caller, rows, max_bytes=len(data),
        max_instructions=len(data) // 2, rom_end=match.ROM_BASE + len(rom),
        same_owner_long_branches=True, **options)
    ins, edges, branches, calls, words = graph.graph(data, caller, ref, **options)
    graph.partition(data, caller, ref, ins, words)
    require(all(tuple(edges[pc]) == (target,) for pc, target in branches.items()),
            "local BL must have only its same-owner target as successor")
    require({pc for pc, target in calls.items() if target == ROOT} == set(sites),
            "caller must have exactly the inventoried native direct BL sites")
    pred = predecessors(edges)
    records = []
    for site in sites:
        stores = outgoing(ins, pred, site)
        allocation, _ = backward(ins, pred, caller, site,
                                 lambda it: writes(it, ARM_REG_SP) or it.mnemonic in ("push", "pop"))
        count = match.thumb_stack_adjustment(ins[allocation])
        require(count is not None and count <= -4 and allocation < min(stores.values()),
                "four outgoing words lack dominating writable allocation")
        value = argument_value(ins, edges, pred, caller, site, stores[12])
        records.append(dict(site=site, allocation=allocation, allocated_bytes=-4 * count,
                            stores=[[off, stores[off]] for off in sorted(stores)], eighth_word=value,
                            next_direct_use_or_call=continuation(ins, edges, calls, site)))
    return dict(address=caller, end=end, sha256=sha(data), instructions=len(ins), calls=records)


def validate_mask(data, ins, edges):
    """The saved scalar is masked with one and reloaded for the resource bit update."""
    sequence = bytes.fromhex("0120 1199 0140 1191 517a 0220 4042 0840 119b 1843 5072")
    begin = STORE - 6
    require(data[begin-ROOT:begin-ROOT+len(sequence)] == sequence and all(
        tuple(edges[pc]) == (pc + 2,) for pc in range(begin, begin+len(sequence), 2)
    ), "missing straight-line incoming word mask and same-word reload")
    require(all(len(edges[pc]) == 1 and edges[pc][0] == pc + ins[pc].size
                for pc in ins if pc != max(ins)), "transfer setup must be straight-line")


class MaskedArgumentProof:
    def __init__(self, data, ins, edges, rom, mapping, index):
        validate_mask(data, ins, edges)
        named.validate_owner(data, ROOT, rom, mapping, index)
        self.references = references(rom)
        rows = json.loads(mapping)
        self.callers = [caller_record(rom, mapping, index, rows, caller, sites)
                        for caller, sites in CALLERS.items()]
        self.data = data
        self.observed = False

    def kind_read(self, instruction, frame_words):
        if instruction.address != 0x08037D8E:
            return None
        result = match.thumb_incoming_narrow_read(instruction, self.data, ROOT, frame_words)
        require(result == (ARM_REG_R0, 8, 1), "transfer resource kind must read the seventh argument byte")
        return result

    def store(self, address, pc, offset, item, aliases, returns):
        require(address == ROOT and pc == STORE and offset == 12 and item.bytes == b"\x11\x91"
                and ARM_REG_R1 not in aliases and ARM_REG_R1 not in returns,
                "transfer write outside its exact non-pointer argument word")
        self.observed = True


def prove(data, address, rom, mapping, index, objects, *, ins, edges, calls, refinement, bindings):
    require(address == ROOT and len(data) == 364 and len(ins) == 159 and not calls and bindings == BINDINGS,
            "transfer leaf requires its three genuine, zero-addend object bindings and exact extent")
    proof = MaskedArgumentProof(data, ins, edges, rom, mapping, index)
    verified = match.verify_leaf_instructions(data, address, True, masked_argument_proof=proof)
    require(proof.observed and {it.address for it in verified} == set(ins), "transfer frame coverage differs")
    return dict(schema=SCHEMA, instructions=len(ins), calls=[], runtime_calls=[],
        partition=graph.partition(data, address, refinement, ins, {}),
        transfer_argument=dict(references=proof.references, callers=proof.callers, source_word_offset=12,
            mask=1, store=STORE, readback=STORE+10,
            contract="Ordinary returning ARM ABI with aligned, writable outgoing arguments. Non-stack objects "
                     "and resource storage are distinct from active frames. At every enumerated game BL the "
                     "eighth word is already zero or one, so any continuation reads identical bits. Any "
                     "additional computed or external caller must supply a writable Boolean eighth word."))
