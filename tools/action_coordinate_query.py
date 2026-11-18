"""USA action 26, its two coordinate outputs, and the native scratch lifetime."""

from collections import deque
from hashlib import sha256
from pathlib import Path
import struct
import json

import match
import function_thunk_profile as thunk
import known_list_query_closure_profile as search
import known_query_stack_buffer_profile as collector
import literal_callback_closure_profile as closure
import scheduler_event_definition as event
from capstone.arm import ARM_OP_MEM, ARM_OP_IMM, ARM_REG_PC, ARM_REG_SP

ROOT, QUERY, DISPATCH = 0x08132208, 0x08098E7C, 0x0813388C
SITE, STEP, FLAG, WALK, GATHER = 0x0813223E, 0x0809D66C, 0x080CDBCC, 0x080C7CC0, 0x08099CDC
KEY, TILE = 0x0809AB5C, 0x0809ABB0
SIZES = {
    ROOT: (96, 44),
    QUERY: (494, 225),
    DISPATCH: (228, 97),
    STEP: (78, 39),
    FLAG: (24, 12),
    TILE: (54, 26),
}
BINDINGS = dict(
    calls=[[16, "func_08096D7C"], [22, "func_08099560"], [34, "func_08096D7C"], [54, "func_08098E7C"]],
    data=[],
    functions=[],
    switches=[],
)
# Local positions are relative to the fully allocated query frame. Special
# values represent the selected 13-word vector entry and the two caller outputs.
VECTOR, OUT_X, OUT_Y = 0x200, 0x201, 0x202
R0 = match.ARM_REG_R0
EXTERNAL = frozenset()
require = event.require


def unique(value):
    return frozenset((value,))


def region(offset, width):
    return ((1 << width) - 1) << offset


def check_loop(data, edges):
    event.sequence(
        data,
        QUERY,
        0x08098F18,
        [
            "add r1, sp, #0x10",
            "bl #0x8099cdc",
            "mov r8, r0",
            "movs r3, #0",
            "str r3, [sp, #0x54]",
            "movs r0, #0x80",
            "lsls r0, r0, #3",
            "mov sl, r0",
            "movs r6, #0",
            "cmp r3, r8",
            "bge #0x8098f8e",
            "add r1, sp, #0x10",
            "lsls r0, r6, #2",
            "adds r5, r1, r0",
            "ldr r1, [r5]",
        ],
    )
    event.sequence(data, QUERY, 0x08098F88, ["adds r6, #1", "cmp r6, r8", "blt #0x8098f30"])
    incoming = {s for s, es in edges.items() if 0x08098F30 in es}
    require(incoming == {0x08098F2E, 0x08098F8C}, "array loop has another entrance")
    # R8 is the authentic collector count, and the only R6 write in the loop is +1.
    # The collector initializes precisely the first R8 entries.
    return dict(array=[16, 68], capacity=13, guard=0x08098F2E, advance=0x08098F88)


def frame(proof, data, ins, edges, calls):
    event.sequence(
        data,
        QUERY,
        QUERY,
        [
            "push {r4, r5, r6, r7, lr}",
            "mov r7, sl",
            "mov r6, sb",
            "mov r5, r8",
            "push {r5, r6, r7}",
            "sub sp, #0x58",
        ],
    )
    event.sequence(
        data,
        QUERY,
        0x0809905A,
        [
            "add sp, #0x58",
            "pop {r3, r4, r5}",
            "mov r8, r3",
            "mov sb, r4",
            "mov sl, r5",
            "pop {r4, r5, r6, r7}",
            "pop {r1}",
            "bx r1",
        ],
    )
    loop = check_loop(data, edges)
    require(all(R0 + 11 not in i.regs_access()[1] for i in ins.values()), "unsaved R11 written")
    # A saved register may contain an outer caller's private pointer. Verify
    # every initial high-register value is dead before first use in this body;
    # the exact entry and exit reconstruct the original saved registers.
    for r in range(R0 + 4, R0 + 12):
        todo = [0x08098E88]
        checked = set()
        while todo:
            pc = todo.pop()
            if pc in checked or pc == 0x0809905A:
                continue
            checked.add(pc)
            reads, writes = ins[pc].regs_access()
            require(r not in reads, "coordinate query reads an undefined preserved input")
            if r not in writes:
                todo.extend(edges[pc])
    for pc in ins:
        if 0x08098F30 <= pc < 0x08098F8E:
            writes = set(ins[pc].regs_access()[1])
            require(
                R0 + 8 not in writes and (R0 + 6 not in writes or pc == 0x08098F88),
                "array loop counter changed",
            )
    # Each state tracks every possible private alias in R0-R12, definitely
    # initialized bytes and definitely written caller outputs. Joins union aliases
    # and intersect initialization. Ordinary scalar contents are not interpreted.
    start = 0x08098E88
    states = {start: ((EXTERNAL,) * 13, 0, 0)}
    pending = deque([start])
    observed = set()
    live_returns = set()
    accesses = set()
    list_sites = {0x08098F0A: KEY, 0x08098FD4: TILE}
    while pending:
        pc = pending.popleft()
        current, init, out = states[pc]
        regs = list(current)
        if pc == 0x0809905A:
            # Only R2/R3 are discarded by the caller. R1 is overwritten while
            # restoring LR, and R4-R11 are restored from the authenticated prologue.
            require(not regs[0] and not regs[12], "query returns private provenance through R0/R12")
            live_returns.update((i, v) for i in (2, 3) for v in regs[i])
            continue
        item = ins[pc]
        ops = item.operands
        op = item.mnemonic
        observed.add(pc)

        def alias(reg):
            if reg == ARM_REG_SP:
                return unique(0)
            return regs[reg - R0] if R0 <= reg <= R0 + 12 else EXTERNAL

        def write_reg(reg, values):
            require(R0 <= reg <= R0 + 12, "unexpected SP/PC write within fixed query frame")
            regs[reg - R0] = values

        if pc in calls:
            dest = calls[pc]
            low = {i: v for i, v in enumerate(regs[:4]) if v}
            after = {}
            if pc == 0x08098ECE:
                require(
                    dest == STEP and low == {1: unique(0), 2: unique(1)}, "direction output aliases differ"
                )
                init |= region(0, 2)
                after = low
            elif pc == 0x08098EEE:
                require(dest == FLAG and low == {1: unique(0), 2: unique(1)}, "flag scratch aliases differ")
                after = {2: regs[2]}  # MOVS R1,#8 before any use; leaf never touches R2.
            elif pc in list_sites:
                require(
                    dest == WALK and regs[2] == unique(4) and not regs[0] and not regs[1],
                    "list visitor has an invalid descriptor",
                )
                needed = region(4, 4) if pc == 0x08098F0A else region(8, 2)
                require(
                    init & (needed | region(12, 4)) == needed | region(12, 4),
                    "list visitor reads an uninitialized coordinate or key",
                )
                # Empty list preserves R2/R3. Neither comparator returns private
                # provenance in another scratch register or retains the descriptor.
                after = {2: regs[2], 3: regs[3]}
            elif pc == 0x08098F1A:
                require(dest == GATHER and low == {1: unique(16)}, "collector base differs")
                # On no nodes the iterator leaves the collector's own descriptor
                # (-20+8 relative to this SP) in R2. Otherwise the last callback
                # leaves R2 just past its actual writes, from one through 13 words.
                after = {2: frozenset([-12] + [16 + 4 * n for n in range(1, 14)])}
            elif pc == 0x08098FE4 and low:
                require(dest == 0x0812E3E8 and low == {3: unique(0)}, "unexpected stale tile-search scratch")
                # Negative x can return before R3 is overwritten. The caller
                # already rejects both negative coordinates on every path here.
                event.sequence(
                    data,
                    QUERY,
                    0x08098F94,
                    [
                        "ldr r1, [sp, #0x4c]",
                        "lsls r0, r1, #0x18",
                        "asrs r6, r0, #0x18",
                        "cmp r6, #0",
                        "blt #0x809903a",
                        "ldr r2, [sp, #0x50]",
                        "lsls r0, r2, #0x18",
                        "asrs r5, r0, #0x18",
                        "cmp r5, #0",
                        "blt #0x809903a",
                        "cmp r6, #0xf",
                        "bgt #0x809903a",
                        "cmp r5, #0xf",
                        "bgt #0x809903a",
                    ],
                )
                event.sequence(
                    data,
                    QUERY,
                    0x08098FDE,
                    ["adds r0, r7, #0", "adds r1, r6, #0", "adds r2, r5, #0", "bl #0x812e3e8"],
                )
                event.sequence(
                    match.BufferCallProof.span(proof, dest),
                    dest,
                    dest,
                    [
                        "push {r4, r5, r6, lr}",
                        "adds r6, r0, #0",
                        "lsls r2, r2, #0x18",
                        "lsrs r2, r2, #0x18",
                        "lsls r4, r1, #0x18",
                        "asrs r0, r4, #0x18",
                        "cmp r0, #0",
                        "blt #0x812e462",
                        "lsls r1, r2, #0x18",
                        "asrs r3, r1, #0x18",
                    ],
                )
            else:
                require(not low, f"ordinary query callee receives a private alias at {pc:08X}")
            for i in (0, 1, 2, 3, 12):
                regs[i] = after.get(i, EXTERNAL)
        elif op.startswith(("ldr", "str")):
            load = op.startswith("ldr")
            sizes = {"ldr": 4, "str": 4, "ldrb": 1, "strb": 1, "ldrsb": 1, "ldrh": 2, "strh": 2, "ldrsh": 2}
            width = sizes[op]
            mem = ops[1].mem
            addresses = alias(mem.base)
            require(not alias(mem.index), "private pointer used as memory index")
            result = set()
            if not load:
                require(not alias(ops[0].reg), "private address stored to memory")
            for address in addresses:
                require(not mem.index, "unbounded offset in private coordinate storage")
                at = address + mem.disp
                if address in (OUT_X, OUT_Y):
                    require(
                        not load
                        and width == 1
                        and mem.disp == 0
                        and (pc, address) in ((0x0809904E, OUT_X), (0x08099056, OUT_Y)),
                        "unexpected formal output access",
                    )
                    out |= 1 if address == OUT_X else 2
                elif address == VECTOR:
                    require(
                        load
                        and width == 4
                        and not mem.disp
                        and pc in (0x08098F36, 0x08098F44, 0x08098F5A, 0x08098F6C, 0x08098F7A),
                        "invalid access through selected list entry",
                    )
                elif at in (120, 124):
                    require(
                        load
                        and width == 4
                        and mem.base == ARM_REG_SP
                        and (pc, at) in ((0x08099048, 120), (0x08099050, 124)),
                        "foreign caller argument access",
                    )
                    result.add(OUT_X if at == 120 else OUT_Y)
                else:
                    require(
                        0 <= at and at + width <= 88 and at % width == 0,
                        "access outside allocated query locals",
                    )
                    mask = region(at, width)
                    if load:
                        require(init & mask == mask, f"uninitialized local read at {pc:08X}")
                    else:
                        init |= mask
                accesses.add((pc, address, mem.disp, width, load))
            if load:
                write_reg(ops[0].reg, frozenset(result))
        elif op == "mov" or (
            op == "adds" and len(ops) == 3 and ops[2].type == ARM_OP_IMM and ops[2].imm == 0
        ):
            write_reg(ops[0].reg, alias(ops[1].reg))
        elif pc == 0x08098F34:
            require(regs[1] == unique(16) and not regs[0], "collector cursor base differs")
            write_reg(R0 + 5, unique(VECTOR))
        elif op in ("adds", "add") and ops[-1].type == ARM_OP_IMM:
            base = ops[0].reg if len(ops) == 2 else ops[1].reg
            vals = alias(base)
            delta = ops[-1].imm
            require(
                all(0 <= pos + delta < 88 and pos < 88 for pos in vals),
                "private address arithmetic escapes frame",
            )
            write_reg(ops[0].reg, frozenset(pos + delta for pos in vals))
        else:
            read, written = item.regs_access()
            require(not any(alias(r) for r in read), "unmodeled private alias use at %08X" % pc)
            require(
                ARM_REG_SP not in written and (ARM_REG_PC not in written or op.startswith("b")),
                "unexpected stack/control mutation",
            )
            for r in written:
                if R0 <= r <= R0 + 12:
                    write_reg(r, EXTERNAL)
        if pc == 0x08099058:
            require(out == 3, "successful query lacks both initialized byte outputs")
        if pc == 0x0809903A:
            require(out == 0, "unsuccessful query writes an output byte")
        for successor in edges[pc]:
            require(start <= successor <= 0x0809905A, "query body branches outside restored frame")
            nxt = (tuple(regs), init, out)
            if successor in states:
                old, oldinit, oldout = states[successor]
                nxt = (tuple(a | b for a, b in zip(old, regs)), init & oldinit, out & oldout)
            if states.get(successor) != nxt:
                states[successor] = nxt
                pending.append(successor)
    require(
        observed == {s for s in ins if start <= s < 0x0809905A} and (2, 1) in live_returns,
        "incomplete query or missing actual R2 scratch path",
    )
    return dict(
        locals=88,
        saved_bytes=32,
        output_arguments=[120, 124],
        typed_accesses=[list(v) for v in sorted(accesses)],
        reachable_body_instructions=len(observed),
        vector=loop,
        exit_scratch=[list(v) for v in sorted(live_returns)],
    )


def get(proof, address):
    size, count = SIZES[address]
    return closure.complete(address, size, count, proof.rom, proof.mapping, proof.index)


def direction_writes(proof):
    _, ins, edges, _, _ = get(proof, STEP)
    # Execute both successors of each condition. Each input pointer may only be
    # used as the base of its corresponding byte store until overwritten.
    pending = [(STEP, frozenset((R0 + 1, R0 + 2)), frozenset())]
    seen = set()
    returns = set()
    while pending:
        pc, live, writes = pending.pop()
        if (pc, live, writes) in seen:
            continue
        seen.add((pc, live, writes))
        item = ins[pc]
        read, written = item.regs_access()
        observed = set(read) & live
        if observed:
            require(
                item.mnemonic == "strb"
                and len(observed) == 1
                and item.operands[1].type == ARM_OP_MEM
                and item.operands[1].mem.base in observed
                and not item.operands[1].mem.index
                and not item.operands[1].mem.disp
                and item.operands[0].reg not in live,
                "direction observes a private pointer outside its byte store",
            )
            writes = writes | observed
        live = live - set(written)
        if not edges[pc]:
            require(
                writes == {R0 + 1, R0 + 2} and R0 + 2 in live, "direction exit lacks a byte or original R2"
            )
            returns.add(pc)
        pending.extend((v, live, writes) for v in edges[pc])
    return dict(
        returns=sorted(returns),
        states=len(seen),
        writes=["argument R1 byte", "argument R2 byte"],
        R2_preserved=True,
    )


def dispatcher_liveness(proof, register):
    # Explore the original dispatcher and the actual direct calls it makes until
    # the incoming scratch is overwritten. A call may preserve it on some exits.
    import named_data_buffer_profile as named

    inventory = {}
    memo = {}
    active = set()
    kills = set()

    def visit(address, start):
        key = (address, start)
        if key in memo:
            return memo[key]
        require(key not in active and len(inventory) < 48, "unbounded scratch continuation")
        active.add(key)
        if address not in inventory:
            body = match.BufferCallProof.span(proof, address)
            named.validate_owner(body, address, proof.rom, proof.mapping, proof.index)
            cs = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
            cs.detail = True
            inventory[address] = (body, cs)
        data, decoder = inventory[address]
        todo = [start]
        seen = set()
        returns_live = False
        while todo:
            pc = todo.pop()
            if pc in seen:
                continue
            seen.add(pc)
            require(
                address <= pc < address + len(data) and len(seen) < 300, "dispatcher scratch leaves its owner"
            )
            item = next(decoder.disasm(data[pc - address :], pc, count=1), None)
            require(item is not None, "invalid scratch continuation instruction")
            read, written = item.regs_access()
            require(register not in read, f"dispatcher or nested callee uses entry scratch at {pc:08X}")
            if register in written:
                kills.add(pc)
                continue
            if item.mnemonic == "bl":
                require(item.operands[0].type == ARM_OP_IMM, "indirect scratch continuation call")
                dest = item.operands[0].imm
                if visit(dest, dest):
                    todo.append(pc + item.size)
            elif item.mnemonic == "bx" or item.mnemonic == "pop" and "pc" in item.op_str:
                require(
                    item.mnemonic == "pop"
                    or item.op_str == "lr"
                    or (
                        pc >= address + 2
                        and int.from_bytes(data[pc - address - 2 : pc - address], "little") & 0xFF00 == 0xBC00
                    ),
                    "unknown indirect scratch exit",
                )
                returns_live = True
            elif item.id == match.ARM_INS_B:
                todo.append(item.operands[0].imm)
                if item.mnemonic != "b":
                    todo.append(pc + item.size)
            else:
                require(ARM_REG_PC not in written, "unhandled scratch transfer")
                todo.append(pc + item.size)
        active.remove(key)
        memo[key] = returns_live
        return returns_live

    survives = visit(DISPATCH, 0x081338BE)
    return dict(
        register=register - R0,
        first_writes=sorted(kills),
        may_survive_dispatcher_return=survives,
        inspected=[
            [address, len(data), sha256(data).hexdigest()] for address, (data, _) in sorted(inventory.items())
        ],
    )


def verify_call(proof, aliases, stack, slots, words):
    require(
        not proof.active
        and aliases == {R0 + 5: -19}
        and len(stack) == 7
        and slots == {-28: -20, -24: -19}
        and not words,
        "action requires distinct local coordinate outputs in arguments five and six",
    )
    for at in slots:
        proof.access(at, 4, stack)
    for at in slots.values():
        proof.access(at, 1, stack)
    if hasattr(proof, "action_coordinates"):
        return {}
    # This approved query verifies the complete original ROM, matched iterator,
    # getter and key comparator as well as their indexed extents.
    key_query = search.prove(
        match.BufferCallProof.span(proof, 0x08099560),
        0x08099560,
        proof.rom,
        proof.mapping,
        proof.index,
        selector=search.SELECTOR,
    )
    collection = collector.contract(proof.rom, proof.mapping, proof.index)
    division = collector.quotient_contract(proof.rom, proof.mapping, proof.index)
    root, rins, _, rcalls, _ = get(proof, ROOT)
    data, ins, edges, calls, partition = get(proof, QUERY)
    dispatch, _, _, _, _ = get(proof, DISPATCH)
    require(
        sha256(root).hexdigest() == "2dcca8a0ede44509240af688469ef652e4c67f2d52b26e18669d48986328112e"
        and sha256(data).hexdigest() == "eea78c3abc460bc746eb516239a2f2383f94a7f49d96331788778580a850dc31"
        and sha256(dispatch).hexdigest()
        == "b1a2ee4c8cefef5b7581b6599971145c0e7a1a78a4e47f2b1c344ca282824d5c",
        "action, query or dispatcher differs from the original native body",
    )
    for a, expected in (
        (STEP, "fe9e3f7c9773ee7e9e2c96decf013debbb82c4801eaf5873764d4f6cd62be3ca"),
        (FLAG, "ae38d516fe9c84165d4c86454e3afd7b83135f40a12f48a499c0abbd140574c2"),
        (TILE, "89ac3320654c0bfe88943c26d2aead7a38c6c2710b7d4030704e6a884aa9a1ce"),
    ):
        b, _, _, _, _ = get(proof, a)
        require(sha256(b).hexdigest() == expected, "native coordinate helper changed")
    # On each direction branch, both byte stores precede return; the flag leaf kills
    # R1 before reading it and never mentions R2, preserving the caller's exact alias.
    flag, fins, _, _, _ = get(proof, FLAG)
    # Both the key search and tile search pass the same 12-byte query layout.
    # The second callback reads its two signed bytes and may update only result+8.
    tile = match.BufferCallProof.span(proof, TILE)
    event.sequence(
        tile,
        TILE,
        TILE,
        [
            "push {r4, lr}",
            "adds r4, r1, #0",
            "bl #0x80c7b74",
            "adds r3, r0, #0",
            "movs r0, #4",
            "ldrsb r0, [r4, r0]",
            "ldr r2, [r3]",
            "adds r1, r2, #0",
            "adds r1, #0xf6",
            "ldrb r1, [r1]",
            "cmp r0, r1",
            "bne #0x809abde",
            "movs r1, #5",
            "ldrsb r1, [r4, r1]",
            "adds r0, r2, #0",
            "adds r0, #0xf7",
            "ldrb r0, [r0]",
            "cmp r1, r0",
            "bne #0x809abde",
            "str r3, [r4, #8]",
            "movs r0, #0",
            "b #0x809abe0",
            "movs r0, #1",
            "pop {r4}",
            "pop {r1}",
            "bx r1",
        ],
    )
    event.sequence(flag, FLAG, FLAG, ["push {lr}", "adds r0, #0xea", "movs r1, #8", "ldrb r0, [r0]"])
    require(
        all(R0 + 2 not in set(i.regs_access()[0]) | set(i.regs_access()[1]) for i in fins.values()),
        "actor flag leaf observes R2",
    )
    require(
        struct.unpack_from("<I", dispatch, 0x08133920 - DISPATCH)[0] == 0x083A87B0
        and struct.unpack_from("<I", proof.rom, 0x083A87B0 + 26 * 12 - match.ROM_BASE)[0] == ROOT | 1,
        "dispatch row does not name action 26",
    )
    (dispatcher_thunk,) = thunk.dependencies(["_call_via_r1"], proof.rom)
    require(
        struct.unpack_from("<II", data, 0x08099040 - QUERY) == (KEY | 1, TILE | 1),
        "query comparator literals differ",
    )
    report = frame(proof, data, ins, edges, calls)
    direction = direction_writes(proof)
    dispatch_r2 = dispatcher_liveness(proof, R0 + 2)
    dispatch_r3 = dispatcher_liveness(proof, R0 + 3)
    require(
        not any(r["may_survive_dispatcher_return"] for r in (dispatch_r2, dispatch_r3)),
        "dispatcher does not kill all remaining query scratch",
    )
    # R2/R3 leave the query only as dead scratch: the entire actual callback
    # continuation, including its restored return, never reads either one.
    suffix = {p: i for p, i in rins.items() if p >= SITE + 4}
    require(
        rcalls.get(SITE) == QUERY
        and not any(p in rcalls or set(i.regs_access()[0]) & {R0 + 2, R0 + 3} for p, i in suffix.items()),
        "outer callback observes scratch",
    )
    proof.dependencies[QUERY] = data
    proof.records[QUERY] = dict(
        address=QUERY,
        end=QUERY + len(data),
        bytes=len(data),
        body_sha256=sha256(data).hexdigest(),
        structure=dict(kind="two original caller-byte outputs", instructions=len(ins), partition=partition),
        **proof.identities,
    )
    proof.action_coordinates = dict(
        schema="action-26-coordinate-output-v1",
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        root_sha256=sha256(root).hexdigest(),
        query=QUERY,
        frame=report,
        direction=direction,
        dispatcher_R2=dispatch_r2,
        dispatcher_R3=dispatch_r3,
        collector=collection,
        division=division,
        key_search=dict(
            address=0x08099560,
            callback=KEY,
            sha256=sha256(json.dumps(key_query, sort_keys=True).encode()).hexdigest(),
        ),
        table=0x083A87B0,
        row=26,
        dispatcher_thunk=dispatcher_thunk,
        conditions=[
            "Finite live scene lists, with at most 13 nodes in the collector input. External actors, list nodes, tile records, scene globals and caller result storage must remain initialized, separate from active frames, and valid for their original accesses.",
            "Ordinary direct callees with external arguments preserve SP, R4-R11 and the active frames. The ordinary root returns void and its caller discards R2/R3 as scratch.",
        ],
    )
    proof._scratch_returns["action-26"] = dict(
        address=QUERY,
        site=0x08099068,
        consumer=ROOT,
        call_site=SITE,
        projected=[[r, v - 120] for r, v in report["exit_scratch"]],
        continuation_states=len(suffix),
        exact_early_actor_flag_R2=-119,
        checked_query_private_scratch=report["exit_scratch"],
    )
    return {}
