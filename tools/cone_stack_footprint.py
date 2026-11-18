"""Native stack footprint and false-result continuations of the cone tile query."""

import hashlib
import json
import struct
from collections import defaultdict

from capstone.arm import (
    ARM_OP_MEM,
    ARM_OP_REG,
    ARM_OP_IMM,
    ARM_REG_SP,
    ARM_REG_R0,
    ARM_REG_R2,
    ARM_REG_R3,
    ARM_REG_R10,
    ARM_INS_B,
)

import analyze
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
import owner_runtime_profile as operations
from software_float_profile import ROM_SHA256

ROOT = 0x080B48CC
CALLER = 0x080B4A1C
PREDICATE = 0x080A0254
MAP_QUERY = 0x0801CC7C
HEIGHT = 0x0801CC18
ROOT_CALLS = {0x080B490A: 0x0809D66C, 0x080B49B2: PREDICATE, 0x080B49C6: HEIGHT}
SELECTOR = "conditional-cone-tile-stack-footprint-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CONTROL_FLOW = "complete cone writer with native nested stack footprints, a checked R2 failure continuation, and a caller-owned writable cursor slot"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def native_graph(proof, address, entries):
    end = entries[address]
    data = proof.rom[address - match.ROM_BASE : end - match.ROM_BASE]
    named.validate_owner(data, address, proof.rom, proof.mapping, proof.index)
    if address == 0x080C8570:
        # The existing decoder authenticates the entire preloaded switch, including
        # each case, its backward guard and every byte of its read-only table.
        ins, transfers = proof.inspect(address, data)
        require(len(transfers) == 1, "missing preloaded query switch")
        instructions = {item.address: item for item in ins}
        edges = {}
        for pc, item in instructions.items():
            if pc in transfers:
                destinations = transfers[pc]
            elif item.mnemonic == "bx" or item.mnemonic == "pop" and "pc" in item.op_str:
                destinations = ()
            elif item.id == ARM_INS_B:
                require(item.mnemonic != "bl", "preloaded leaf called another owner")
                destinations = [item.operands[0].imm]
                if item.mnemonic != "b":
                    destinations.append(pc + item.size)
            else:
                destinations = [pc + item.size]
            require(all(dest in instructions for dest in destinations), "preloaded case leaves owner")
            edges[pc] = tuple(destinations)
        return data, instructions, edges, {}
    options = {"one_object_word_switch": True} if address == 0x080CA7A4 else {}
    ref = analyze.refine_function(
        data,
        address,
        json.loads(proof.mapping),
        max_bytes=len(data),
        max_instructions=len(data) // 2,
        rom_end=0x09000000,
        same_owner_long_branches=True,
        **options,
    )
    ins, edges, branches, calls, words = graph.graph(data, address, ref, **options)
    graph.partition(data, address, ref, ins, words)
    require(not branches, "unhandled internal BL in cone footprint")
    operations.verify_operations(ins, edges, address, branches, calls, ref)
    return data, ins, edges, calls


def stack_sites(address, instructions, edges, calls):
    """Calculate each direct SP-relative byte interval and each exact BL depth."""
    depths = {address: 0}
    pending = [address]
    memory, call_depth, materialized = {}, {}, []
    while pending:
        pc = pending.pop()
        item = instructions[pc]
        depth = depths[pc]
        if item.mnemonic in ("push", "pop"):
            count = len(item.operands)
            require(all(o.type == ARM_OP_REG for o in item.operands), "irregular stack register list")
            depth += count * (4 if item.mnemonic == "pop" else -4)
        elif (adjustment := match.thumb_stack_adjustment(item)) is not None:
            depth += 4 * adjustment
        else:
            if pc in calls:
                call_depth[pc] = depth
            for op in item.operands:
                if op.type == ARM_OP_REG and op.reg == ARM_REG_SP:
                    require(
                        address == MAP_QUERY
                        and pc in (0x0801CC96, 0x0801CC9A, 0x0801CC9E, 0x0801CCA2, 0x0801CCBC),
                        "unproved materialized stack address",
                    )
                    materialized.append(pc)
                if op.type != ARM_OP_MEM:
                    continue
                require(op.mem.index != ARM_REG_SP, "SP used as a memory index")
                if op.mem.base == ARM_REG_SP:
                    require(
                        item.mnemonic in ("ldr", "str")
                        and item.size == 2
                        and not op.mem.index
                        and int.from_bytes(item.bytes, "little") & 0xF000 == 0x9000,
                        "SP footprint requires an immediate aligned Thumb word",
                    )
                    memory[pc] = (item.mnemonic, depth + op.mem.disp)
        require(-4096 <= depth <= 0 and (edges[pc] or depth == 0), "unbalanced native stack depth")
        for dest in edges[pc]:
            if dest in depths:
                require(depths[dest] == depth, "different SP depths join at one instruction")
            else:
                depths[dest] = depth
                pending.append(dest)
    require(set(depths) == set(instructions), "unused instruction in native stack footprint")
    return memory, call_depth, sorted(materialized)


def footprint(proof, entries):
    """Rebuild all descendants. Direct SP words inherited by a child must fit a parent's private frame."""
    owners, active, records = {}, set(), {}

    def visit(address):
        require(address not in active, "recursive cone stack footprint")
        if address in owners:
            return
        require(len(owners) < 32, "cone stack footprint exceeded its owner budget")
        active.add(address)
        data, ins, edges, calls = native_graph(proof, address, entries)
        memory, depths, materialized = stack_sites(address, ins, edges, calls)
        observed = sorted({off for op, off in memory.values() if off >= 0})
        expected = {PREDICATE: [0, 4, 8, 12], 0x0809FEF0: [0, 4, 8], 0x0812E1A8: [0, 4, 8]}.get(address, [])
        require(
            observed == expected and all(op == "ldr" for op, off in memory.values() if off >= 0),
            "callee stack accesses differ from its read-only incoming words",
        )
        owners[address] = (data, ins, edges, calls)
        for pc, target in calls.items():
            visit(target)
            child = records[target]["incoming"]
            require(
                all(depths[pc] + off + 4 <= 0 for off in child),
                "nested outgoing words extend into an ancestor frame",
            )
        active.remove(address)
        records[address] = dict(
            end=entries[address],
            sha256=sha(data),
            instructions=len(ins),
            incoming=observed,
            stack_words=[[pc, role, off] for pc, (role, off) in sorted(memory.items())],
            call_depths=[[pc, depths[pc], target] for pc, target in sorted(calls.items())],
            materialized_stack_addresses=materialized,
        )

    visit(PREDICATE)
    visit(HEIGHT)
    require(len(owners) == 29, "unexpected cone predicate/height closure")
    return owners, records


def false_continuation(owner, start, value):
    """Follow a known scalar result until a return or the root's first R2 overwrite."""
    data, instructions, edges, calls = owner
    pc = start
    visited = []
    compare = None
    while True:
        require(pc not in visited and len(visited) < 80, "cyclic false-result continuation")
        visited.append(pc)
        item = instructions[pc]
        reads, writes = item.regs_access()
        require(ARM_REG_R2 not in reads and pc not in calls, "expired R2 observed by a continuation")
        if ARM_REG_R2 in writes:
            require(
                pc == 0x080B49F4 and item.mnemonic == "movs" and item.op_str == "r2, #1",
                "unknown expired R2 overwrite",
            )
            return visited, "killed"
        operands = item.operands
        dests = edges[pc]
        if not dests:
            require(item.mnemonic == "bx" and value is not None, "missing scalar return")
            return visited, value
        if len(dests) > 1:
            require(
                compare is not None and item.mnemonic in ("bne", "beq", "bgt"),
                "unproved false-result branch",
            )
            signed_value = compare if compare < 1 << 31 else compare - (1 << 32)
            taken = {"bne": compare != 0, "beq": compare == 0, "bgt": signed_value > 0}[item.mnemonic]
            dest = operands[0].imm if taken else pc + item.size
            require(dest in dests, "false-result edge differs from native branch")
        else:
            dest = dests[0]
        if item.mnemonic == "cmp" and item.op_str == "r0, #0":
            compare = value
        elif item.update_flags:
            compare = None
        if ARM_REG_R0 in writes:
            if item.mnemonic == "movs" and operands[1].type == ARM_OP_IMM:
                value = operands[1].imm
            elif item.mnemonic == "rsbs" and item.op_str == "r0, r0, #0" and value is not None:
                value = -value & 0xFFFFFFFF
            elif item.mnemonic == "lsls" and item.op_str == "r0, r0, #0x18" and value is not None:
                value = value << 24 & 0xFFFFFFFF
            else:
                value = None
        pc = dest


def scratch_lifetime(proof, owners):
    """Reissue the existing exact callee certificate, then follow every one of its consumers."""
    data, ins, edges, calls = owners[MAP_QUERY]
    scratch = named.RootReturnScratchBufferProof(proof.rom, proof.mapping, proof.index, proof.objects)
    scratch.bind_return_root(MAP_QUERY, data)
    match.verify_leaf_instructions(data, MAP_QUERY, True, calls, buffer_proof=scratch)
    receipt = scratch.root_scratch_manifest()
    require(
        sha(data) == "4525b72830d12a86414a578da0d8ddcc256d25ec0a69c08c84d6b70198fc8690"
        and receipt["observations"] == [[136, 2, -35]]
        and not receipt["dead_joins"],
        "query lacks its sole established private R2 return",
    )
    # This fixed complete query assigns R2 = entry SP - 35 at CCC8. It reads
    # the live local at CCCA. The false edge reaches CCF4 and the true edge
    # overwrites R2 immediately. Recheck both edges and the false continuation.
    require(
        ins[0x0801CCC8].op_str == "r2, r8"
        and ins[0x0801CCCA].op_str == "r1, [r2]"
        and set(edges[0x0801CCD0]) == {0x0801CCF4, 0x0801CCD2}
        and ins[0x0801CCD2].mnemonic == "ldr"
        and ARM_REG_R2 in ins[0x0801CCD2].regs_access()[1]
        and ARM_REG_R2 not in ins[0x0801CCD2].regs_access()[0],
        "wrong private R2 branch or overwrite",
    )
    path, value = false_continuation(owners[MAP_QUERY], 0x0801CCF4, None)
    require(value == 0, "private R2 accompanies a nonzero map result")
    inbound = defaultdict(list)
    for owner, (_, _, _, bindings) in owners.items():
        for site, target in bindings.items():
            inbound[target].append((owner, site))
    observations = [[MAP_QUERY, 0x0801CCF4, path, value]]
    pending = [(MAP_QUERY, value)]
    finished = set()
    while pending:
        target, scalar = pending.pop()
        if (target, scalar) in finished:
            continue
        finished.add((target, scalar))
        require(inbound[target], "unconsumed expired scratch return")
        for owner, pc in sorted(inbound[target]):
            path, result = false_continuation(owners[owner], pc + 4, scalar)
            observations.append([owner, pc, path, result])
            if result != "killed":
                pending.append((owner, result))
    require(
        {(row[0], row[1]) for row in observations[1:]}
        == {
            (0x0809D79C, 0x0809D7C2),
            (0x0809FEF0, 0x0809FF34),
            (PREDICATE, 0x080A0298),
            (PREDICATE, 0x080A02AE),
            (PREDICATE, 0x080A02BC),
            (PREDICATE, 0x080A031C),
            (ROOT, 0x080B49B2),
        },
        "expired scratch has unexpected producer or consumer sites",
    )
    require(any(row[-1] == "killed" for row in observations), "missing final R2 kill")
    return dict(root_certificate=receipt, continuations=observations)


def paths_from_definition(predecessors, use, definition):
    """Visit every predecessor of a use until the required definition is reached."""
    pending = [use]
    reached = set()
    while pending:
        pc = pending.pop()
        if pc in reached:
            continue
        reached.add(pc)
        if pc != definition:
            require(pc != CALLER and predecessors[pc], "cone call bypasses required cursor definition")
            pending.extend(predecessors[pc])
    require(definition in reached, "cursor definition is unreachable from its use")
    return reached - {definition}


def raw_cursor_references(rom, site):
    """Inventory raw Thumb-1 BL pairs and literal Thumb pointers in the supplied ROM."""
    require(len(rom) == 0x1000000, "cone reference inventory requires the complete 16 MiB USA ROM")
    # A Thumb BL has displacement [-2^22, 2^22 - 2] relative to the first halfword + 4.
    first = max(match.ROM_BASE, ROOT - 4 - ((1 << 22) - 2))
    last = min(match.ROM_BASE + len(rom) - 4, ROOT - 4 + (1 << 22))
    pair = struct.Struct("<HH")
    direct = []
    for pc in range(first, last + 1, 2):
        prefix, suffix = pair.unpack_from(rom, pc - match.ROM_BASE)
        if prefix & 0xF800 != 0xF000:
            continue
        delta = ROOT - (pc + 4)
        expected_prefix = 0xF000 | ((delta >> 12) & 0x7FF)
        expected_suffix = 0xF800 | ((delta >> 1) & 0x7FF)
        if (prefix, suffix) == (expected_prefix, expected_suffix):
            direct.append(pc)
    require(direct == [site], "unexpected raw Thumb BL reference to cone writer")
    require((ROOT | 1).to_bytes(4, "little") not in rom, "literal Thumb pointer to cone writer found")
    digest = sha(rom)
    require(digest == ROM_SHA256, "cone reference inventory requires the approved USA ROM identity")
    return dict(
        raw_thumb_bl_sites=direct,
        encoded_thumb_pointer_occurrences=0,
        rom_bytes=len(rom),
        rom_sha256=digest,
    )


def outgoing_cursor(proof, entries, root):
    from capstone.arm import ARM_REG_R4

    data, ins, edges, calls = native_graph(proof, CALLER, entries)
    site = 0x080B4BF2
    require(calls.get(site) == ROOT, "cone cursor caller missing its direct binding")
    predecessor = defaultdict(set)
    for pc, children in edges.items():
        for child in children:
            predecessor[child].add(pc)
    cursor = 0x080B4BE4
    for pc in range(cursor, site + 2, 2):
        if pc != cursor:
            require(predecessor[pc] == {pc - 2}, "entry into middle of outgoing stack arguments")
    stores = [ins[pc] for pc in (0x080B4BE4, 0x080B4BE8, 0x080B4BEC, 0x080B4BF0)]
    require(
        all(
            i.mnemonic == "str"
            and i.operands[0].reg == ARM_REG_R4
            and i.operands[1].mem.base == ARM_REG_SP
            and not i.operands[1].mem.index
            and i.operands[1].mem.disp == k * 4
            for k, i in enumerate(stores)
        ),
        "missing four outgoing argument stores",
    )
    allocation, initialization, transfer = 0x080B4A26, 0x080B4A2A, 0x080B4BEE
    require(
        ins[allocation].mnemonic == "sub" and match.thumb_stack_adjustment(ins[allocation]) == -8,
        "outgoing cursor lacks its native allocation",
    )
    require(
        bytes(ins[initialization].bytes) == b"\x9a\x46" and bytes(ins[transfer].bytes) == b"\x54\x46",
        "outgoing cursor requires MOV r10,r3 and MOV r4,r10",
    )
    # R3 retains the caller's original output argument up to the initialization. A
    # direct BL may clobber R3. The ordinary returning ABI preserves R10 after it.
    before_copy = paths_from_definition(predecessor, initialization, CALLER) | {CALLER}
    require(
        not any(
            pc in calls or ARM_REG_R3 in ins[pc].regs_access()[1] for pc in before_copy - {initialization}
        ),
        "incoming output argument R3 is overwritten",
    )
    after_copy = paths_from_definition(predecessor, site, initialization)
    require(
        not any(ARM_REG_R10 in ins[pc].regs_access()[1] for pc in after_copy),
        "original output pointer is overwritten before the cone call",
    )
    after_allocation = paths_from_definition(predecessor, site, allocation)
    require(
        not any(
            ARM_REG_SP in ins[pc].regs_access()[1] or ins[pc].mnemonic in ("push", "pop")
            for pc in after_allocation
        ),
        "outgoing allocation changes before the cone BL",
    )
    discarded = []
    pc = site + 4
    released = False
    while True:
        item = ins[pc]
        require(
            pc not in discarded and pc not in calls and len(discarded) < 20,
            "unproved caller continuation after cursor update",
        )
        discarded.append(pc)
        if not released:
            if match.thumb_stack_adjustment(item) == 8:
                released = True
            else:
                require(
                    item.mnemonic in ("b", "adds")
                    and all(op.type != ARM_OP_MEM for op in item.operands)
                    and ARM_REG_SP not in item.regs_access()[0],
                    "outgoing cursor observed before frame discard",
                )
        else:
            require(
                item.mnemonic in ("pop", "mov", "bx")
                and not any(op.type == ARM_OP_MEM for op in item.operands),
                "unexpected read after outgoing frame discard",
            )
        if not edges[pc]:
            require(released and item.mnemonic == "bx", "outgoing allocation did not reach normal return")
            break
        require(len(edges[pc]) == 1, "ambiguous caller continuation")
        pc = edges[pc][0]
    root_ins, root_edges = root[1:3]
    cursor_ops = [
        ("ldr", "r2, [sp, #0x74]"),
        ("strb", "r0, [r2, #2]"),
        ("adds", "r2, #4"),
        ("str", "r2, [sp, #0x74]"),
    ]
    for index, (mnemonic, operands) in enumerate(cursor_ops):
        pc = 0x080B49CA + 2 * index
        require(
            (root_ins[pc].mnemonic, root_ins[pc].op_str) == (mnemonic, operands)
            and all(previous == pc - 2 for previous, dests in root_edges.items() if index and pc in dests),
            "cone cursor is not a single-entry four-byte advancement",
        )
    return dict(
        caller=CALLER,
        caller_sha256=sha(data),
        cursor_moves=[
            [initialization, ins[initialization].bytes.hex()],
            [transfer, ins[transfer].bytes.hex()],
        ],
        references=raw_cursor_references(proof.rom, site),
        call=site,
        outgoing=[0, 4, 8, 12],
        private_bytes=32,
        updated_incoming_word=12,
        discard_continuation=discarded,
    )


class ConeStackProof(named.NamedDataBufferProof):
    def __init__(self, rom, mapping, index, objects, *, policy):
        super().__init__(rom, mapping, index, objects)
        require(policy == SELECTOR, "explicit cone stack-footprint selector required")
        self.observations = set()

    def bind_root(self, data, address, calls):
        from known_query_native_closure_profile import environment_fingerprint
        import local_long_branch_profile as frames
        import readonly_entry_stack_words_profile as incoming

        require(
            address == ROOT and calls == ROOT_CALLS and not hasattr(self, "certificate"),
            "cone proof requires its exact three canonical native calls",
        )
        entries = {int(e["rom"], 16): int(e["end"], 16) for e in json.loads(self.mapping)}
        owners, records = footprint(self, entries)
        for target, (_, instructions, edges, bindings) in owners.items():
            if target == MAP_QUERY:
                continue  # scratch_lifetime verifies this complete frame and its local outputs.
            offsets = records[target]["incoming"]
            policy = (
                {"schema": incoming.SCHEMA, "words": [off // 4 for off in offsets]} if offsets else None
            )
            frames.prove_frame(instructions, edges, target, {}, bindings, entry_stack_policy=policy)
        owners[ROOT] = native_graph(self, ROOT, entries)
        require(
            owners[ROOT][0] == data and owners[ROOT][3] == calls and len(owners[ROOT][1]) == 165,
            "wrong complete cone owner or linked call inventory",
        )
        cursor = outgoing_cursor(self, entries, owners[ROOT])
        scratch = scratch_lifetime(self, owners)
        self.certificate = dict(
            schema=SCHEMA,
            source_environment=environment_fingerprint(),
            native_closure=[[address, record] for address, record in sorted(records.items())],
            r2_lifetime=scratch,
            outgoing_cursor=cursor,
            premises="On normal return, external arguments and addresses loaded from non-stack memory "
            "do not alias private active frames or their saved control words. Each external caller "
            "provides four writable aligned outgoing stack words and a separate output buffer "
            "of sufficient capacity for accepted four-byte records. Ordinary call ABI and "
            "word-aligned, nonwrapping stack storage are assumed. The identified game caller "
            "establishes the outgoing cursor slot. No global spatial safety or termination claim.",
        )

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if site in (0x080B49B2, 0x080B49C6):
            require(
                hasattr(self, "certificate")
                and address == ROOT_CALLS[site]
                and not aliases
                and not words
                and len(stack) == 26
                and slots == {-52: -88},
                "cone call must have no register aliases and only its private SP+52 spill",
            )
            self.access(-52, 4, stack)
            self.validate_pointer_value(-88, stack)
            self.observations.add(site)
            return {}
        return super().check_call(
            address, aliases, stack, slots, constants=constants, site=site, words=words
        )

    def cursor_store(self, address, pc, offset, instruction, aliases, returns):
        require(
            hasattr(self, "certificate")
            and address == ROOT
            and pc == 0x080B49D0
            and offset == 12
            and bytes(instruction.bytes) == b"\x1d\x92"
            and ARM_REG_R2 not in aliases
            and ARM_REG_R2 not in returns,
            "cone cursor store outside authenticated writable formal or with private/return alias",
        )
        self.observations.add(pc)

    def contract_manifest(self):
        require(
            self.observations == {0x080B49B2, 0x080B49C6, 0x080B49D0} and 0x0809D66C in self.records,
            "missing ordinary output callee, protected-spill call or writable cursor store",
        )
        return self.certificate
