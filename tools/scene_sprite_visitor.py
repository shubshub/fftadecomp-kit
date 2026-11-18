"""The original two-slot sprite renderer and its external-scene visitor."""

from hashlib import sha256
from pathlib import Path
import struct

import function_thunk_profile as thunk
import literal_callback_closure_profile as closure
import match
import scalar_callback_adapter_inventory as adapter
import scheduler_event_definition as event

OWNER, ITERATOR, ADAPTER, CALLBACK = 0x0809A48C, 0x080C7CC0, 0x0809ABE8, 0x08097F04
VISIT = 0x0809A50A
TABLE = 0x083915CC
FRAMES = [(1, 0x08391592), (3, 0x083915A0), (4, 0x083915AE), (4, 0x083915BC)]
BINDINGS = dict(
    calls=[
        [56, "_call_via_r2"],
        [68, "_call_via_r2"],
        [86, "func_0808EFCC"],
        [126, "func_080C7CC0"],
    ],
    data=[
        [144, "data_08394038", 0],
        [148, "data_083915CC", 0],
        [152, "data_08394040", 0],
    ],
    functions=[[156, "func_08097F04"], [160, "func_0809ABE8"]],
    switches=[],
)
DIGEST = {
    0x080231F4: "870bf6c164487be611de62ca28200741e5abc67c66b26d01bd797915661c5a5c",
    0x08096D7C: "87a96ac9b624426930b1c117b9e2b0809fc860ad0b25bab627b1d9211207c8a9",
    0x08096ED4: "7831a5b2924e2127e34175564b557580586e9b85c4787bce28b75b112a6925a6",
    0x0809A48C: "b71cf12379496f1f2efe790517b38f8a1f499ad530c5cda80541eb87a08bc6c7",
    0x08097000: "f8c57feef8172de6d1527c3a19c1ddc343ba1423250a3c4ce7091a568aec80cc",
    0x080993F4: "7613ab70817f0c0527e6f7febe2ecd1683053386e9962b709bb7c2c4669b2b01",
    0x08097A04: "60a0905b3ce0b54f7fca4ac2b4d345ef75279188fb90e0634e84b552a8c3ad36",
    0x0809A3F4: "1cd275ba4815bfb4a4b7dc5f8a319318c2a62b1adac843acf705437cc5b449e9",
    0x08097F04: "56feb611cc3944958a5a1694eba9027486dd2ac6a7b436ba0021c23379fecb38",
    0x0808EFCC: "f2a9d65abf725a47f33db7fe661f9644d873e5485fa0c2de915731c2b718bdb6",
    0x0808F74C: "dae82a252def4d79ada655196e1a5fdbefda77684efbb28127473d5741180386",
    0x0814186C: "07967ebdc3979cd4fd4de37fd22b3e6de8965b00dae4ac5585577c9709839652",
    0x08A39720: "28fbf7ea3c419aff077a4047df36d1dd3a9027fa06f9f7bf33250a6847201cdb",
    0x08A39770: "6515cdef1ed8aa656d53d81b6200b25eb3a3519175620327cd77f616abe6442b",
}
require = event.require


def read(rom, address, size):
    return rom[address - match.ROM_BASE : address - match.ROM_BASE + size]


def pinned(proof, address):
    from inert_spin_profile import validate_span

    data = match.BufferCallProof.span(proof, address)
    validate_span(data, address, proof.rom, proof.mapping, proof.index)
    require(
        sha256(data).hexdigest() == DIGEST[address],
        "scene sprite complete dependency changed",
    )
    return data


def prove_visitor(proof):
    info = closure.ITERATORS[ITERATOR]
    body, ins, edges, calls, partition = closure.complete(
        ITERATOR, info["size"], info["count"], proof.rom, proof.mapping, proof.index
    )
    selected, r2 = closure.iterator_structure(body, ITERATOR, info, ins, edges, calls)
    require(
        selected == thunk.ALIASES["_call_via_r6"] and r2,
        "scene iterator cannot preserve the empty-list R2",
    )
    entries, rows = closure.indices(proof.mapping, proof.index)
    identity = closure.span_record(selected, selected + 2, entries, rows, proof.rom)
    require(identity["instrs"] == 1, "scene visitor requires the indexed single-instruction BX R6")
    occupied = [(int(entry["rom"], 16), int(entry["end"], 16)) for entry in entries]
    occupied += [(int(row[0], 16), int(row[1], 16)) for row in rows]
    require(
        all(start >= selected + 4 or end <= selected + 2 for start, end in occupied),
        "scene iterator thunk padding overlaps an indexed function",
    )
    (canonical,) = thunk.dependencies(["_call_via_r6"], proof.rom)
    scalar = adapter.verify(
        ADAPTER,
        0x080C7B74,
        proof.rom,
        proof.mapping,
        proof.index,
        selector=adapter.SELECTOR,
    )
    require(
        scalar["callback"]["descriptor_address_passed_as_argument"] is False
        and [o["offset"] for o in scalar["descriptor_reads"]] == [0, 4],
        "adapter no longer consumes only the two original closure words",
    )
    proof.dependencies[ITERATOR] = body
    proof.records[ITERATOR] = dict(
        address=ITERATOR,
        end=ITERATOR + len(body),
        bytes=len(body),
        body_sha256=sha256(body).hexdigest(),
        structure=dict(
            kind="two-word external-scene list visitor",
            instructions=len(ins),
            partition=partition,
            canonical_thunk=canonical,
            adapter=ADAPTER,
            empty_R2_preserved=r2,
        ),
        **proof.identities,
    )
    return scalar


def visit_call(proof, aliases, stack, slots, words):
    r2 = match.ARM_REG_R0 + 2
    require(
        not proof.active and aliases == {r2: -36} and len(stack) == 9 and not slots and not words,
        "scene visitor requires exactly the private eight-byte closure as R2",
    )
    for offset in (-36, -32):
        proof.access(offset, 4, stack)
    if not hasattr(proof, "scene_adapter"):
        proof.scene_adapter = prove_visitor(proof)
    proof.scene_visit_seen = True
    # The empty list preserves the incoming R2. Track it to the normal root return,
    # where the existing scratch policy checks the epilogue and ABI obligations.
    return {r2: -36}


def sprite_image(proof):
    import iwram_installation_prerequisite as installation
    import owner_admission_profile as owner
    import owner_graph_profile as graph

    address = 0x0808F74C
    data = pinned(proof, address)
    ins, edges, branches, calls, words = graph.graph(data, address, owner.refine(data, address, proof.mapping))
    call = 0x0808F75A
    require(
        not branches
        and not words
        and calls == {call: 0x0814186C}
        and pinned(proof, 0x0814186C) == bytes.fromhex("0bdf7047"),
        "changed sprite image CpuSet wrapper",
    )
    arguments = installation.constant_states(ins, edges, address, data)[call]
    source, destination, units = [arguments[match.ARM_REG_R0 + n] for n in range(3)]
    require(
        (source, destination, units) == (0x08A38ADC, 0x03005F28, 0x720),
        "sprite installer source, destination or halfword count changed",
    )
    entries = []
    for slot, native, length in [
        (0x08394038, 0x08A39720, 20),
        (0x08394040, 0x08A39770, 4),
    ]:
        (entry,) = struct.unpack("<I", read(proof.rom, slot, 4))
        require(
            entry & 1
            and 0 <= native - source <= 2 * units - length
            and (entry & ~1) - destination == native - source,
            "sprite slot no longer points into the corresponding copied original code",
        )
        body = pinned(proof, native)
        require(len(body) == length, "sprite image range changed")
        entries.append(
            dict(
                slot=slot,
                entry=entry,
                source=native,
                bytes=length,
                body_sha256=DIGEST[native],
            )
        )
    event.sequence(
        pinned(proof, 0x08A39720),
        0x08A39720,
        0x08A39720,
        [
            "adds r2, r0, #0",
            "movs r3, #0xac",
            "lsls r3, r3, #1",
            "adds r0, r2, r3",
            "str r1, [r0]",
            "movs r1, #0xaa",
            "lsls r1, r1, #1",
            "adds r0, r2, r1",
            "ldr r0, [r0]",
            "bx lr",
        ],
    )
    event.sequence(
        pinned(proof, 0x08A39770),
        0x08A39770,
        0x08A39770,
        ["strb r1, [r0, #0x16]", "bx lr"],
    )
    return dict(
        installer=address,
        cpuset_site=call,
        source=source,
        destination=destination,
        halfwords=units,
        entries=entries,
        writes=[[0, 0x158, 4], [0, 0x16, 1]],
        unused_return_word=[0, 0x154, 4],
        installed_identity_proved=False,
    )


def scene_origin(proof):
    caller, getter, setup = 0x080231F4, 0x08096D7C, 0x08096ED4
    scene_global = 0x0200F4B0
    producer = pinned(proof, setup)
    event.sequence(producer, setup, 0x08096F18, ["bl #0x8097000", "ldr r1, [pc, #0x18]", "str r0, [r1]"])
    reader = pinned(proof, getter)
    event.sequence(reader, getter, getter, ["ldr r0, [pc, #4]", "ldr r0, [r0]", "bx lr"])
    require(
        struct.unpack_from("<I", producer, 0x08096F38 - setup)[0] == scene_global
        and struct.unpack_from("<I", reader, 8)[0] == scene_global,
        "scene constructor and getter no longer share their original global",
    )
    event.sequence(
        pinned(proof, caller),
        caller,
        0x080231FC,
        ["bl #0x8096d7c", "cmp r0, #0", "beq #0x802320c", "bl #0x8096d7c", "bl #0x809a48c"],
    )
    return dict(
        caller=caller,
        getter=getter,
        scene_global=scene_global,
        setup=setup,
        stores_constructor_return=0x08096F1E,
        render_call=0x08023208,
        second_load_still_live_required=True,
    )


def lifecycle(proof):
    # The native selection loop stops at the first inactive slot. It may find none.
    # Only the reached initializer writes the frame; no external entry-state bound is inferred.
    create, activate, update, destroy = 0x08097000, 0x08097A04, 0x0809A3F4, 0x080993F4
    init = pinned(proof, create)
    event.sequence(
        init,
        create,
        create + 6,
        [
            "movs r4, #0xed",
            "lsls r4, r4, #2",
            "adds r1, r4, #0",
            "bl #0x8007138",
            "adds r7, r0, #0",
            "ldr r6, [pc, #0xd0]",
            "ldr r2, [r6]",
            "adds r1, r4, #0",
            "bl #0x814224c",
        ],
    )
    event.sequence(
        init,
        create,
        0x080970BC,
        [
            "movs r0, #0xe5",
            "lsls r0, r0, #2",
            "adds r4, r7, r0",
            "movs r5, #1",
            "bl #0x808f79c",
            "str r0, [r4]",
            "adds r4, #0x10",
            "subs r5, #1",
            "cmp r5, #0",
            "bge #0x80970c4",
        ],
    )
    start = pinned(proof, activate)
    event.sequence(
        start,
        activate,
        0x08097EB8,
        [
            "movs r5, #0",
            "movs r3, #1",
            "ldr r1, [pc, #0x40]",
            "add r1, sb",
            "mov r4, sb",
            "ldrb r0, [r1]",
            "adds r2, r3, #0",
            "ands r2, r0",
            "cmp r2, #0",
            "beq #0x8097e38",
            "adds r1, #0x10",
            "adds r4, #0x10",
            "adds r5, #1",
            "cmp r5, #1",
            "ble #0x8097ec2",
        ],
    )
    require(
        struct.unpack_from("<I", start, 0x08097F00 - activate)[0] == 0x39E,
        "activation flag no longer points into the two scene slots",
    )
    event.sequence(
        start,
        activate,
        0x08097E44,
        [
            "movs r3, #0xe5",
            "lsls r3, r3, #2",
            "adds r4, r4, r3",
            "strb r2, [r4, #0xb]",
            "ldrb r2, [r4, #0xa]",
            "movs r3, #1",
            "orrs r2, r3",
            "strb r2, [r4, #0xa]",
        ],
    )
    event.sequence(start, activate, 0x08097E5A, ["movs r5, #0", "strh r2, [r4, #4]"])
    event.sequence(start, activate, 0x08097E72, ["strh r0, [r4, #6]", "strb r5, [r4, #0xc]"])
    step = pinned(proof, update)
    event.sequence(
        step,
        update,
        0x0809A448,
        [
            "ldrb r0, [r2, #0xc]",
            "lsls r0, r0, #3",
            "adds r0, r0, r7",
            "ldr r0, [r0]",
            "cmp r1, r0",
            "bls #0x809a46a",
            "strb r5, [r2, #0xb]",
            "ldrb r0, [r2, #0xc]",
            "adds r0, #1",
            "strb r0, [r2, #0xc]",
            "lsls r0, r0, #0x18",
            "lsrs r0, r0, #0x18",
            "cmp r0, #3",
            "bls #0x809a46a",
            "movs r0, #0xfe",
            "ands r0, r3",
            "strb r0, [r2, #0xa]",
            "adds r6, #1",
            "cmp r6, #1",
            "ble #0x809a42a",
        ],
    )
    require(
        struct.unpack_from("<I", step, 0x0809A488 - update)[0] == TABLE,
        "slot updater duration table changed",
    )
    event.sequence(
        pinned(proof, destroy),
        destroy,
        0x080993F8,
        [
            "movs r0, #0xe5",
            "lsls r0, r0, #2",
            "adds r4, r5, r0",
            "movs r6, #1",
            "ldr r0, [r4]",
            "bl #0x808f7cc",
            "adds r4, #0x10",
            "subs r6, #1",
            "cmp r6, #0",
            "bge #0x8099400",
        ],
    )
    return dict(
        allocation_size=0x3B4,
        constructor=create,
        sprite_allocation=0x080970C4,
        activation=activate,
        first_inactive_scan=0x08097EC2,
        frame_zero=0x08097E74,
        update=update,
        last_frame=3,
        clear_active=0x0809A468,
        destruction=destroy,
        sprite_release=0x08099402,
    )


def manifest(proof, data, bindings):
    require(
        getattr(proof, "scene_visit_seen", False) and bindings == BINDINGS and data == pinned(proof, OWNER),
        "scene visitor requires its exact root, typed relocation set and replay",
    )
    closure.complete(OWNER, 164, 68, proof.rom, proof.mapping, proof.index)
    for address in DIGEST:
        pinned(proof, address)
    syms = match.parse_data_symbols(proof.objects)
    require(
        all(syms.get(f"data_{p:08X}") == p for p in [TABLE, 0x08394038, 0x08394040])
        and list(struct.iter_unpack("<II", read(proof.rom, TABLE, 32))) == FRAMES,
        "scene frame pointer table changed",
    )
    event.sequence(
        data,
        OWNER,
        0x0809A4FE,
        [
            "ldr r0, [pc, #0x28]",
            "str r5, [sp]",
            "str r0, [sp, #4]",
            "ldr r0, [r5, #0x10]",
            "ldr r1, [pc, #0x24]",
            "mov r2, sp",
            "bl #0x80c7cc0",
        ],
    )
    require(
        struct.unpack_from("<II", data, 156) == (CALLBACK | 1, ADAPTER | 1),
        "changed original visitor or node adapter",
    )
    event.sequence(
        pinned(proof, CALLBACK),
        CALLBACK,
        0x08098008,
        ["movs r0, #1", "add sp, #0xc", "pop {r4, r5, r6}", "pop {r1}", "bx r1"],
    )
    scalar = proof.scene_adapter
    return dict(
        schema="scene-two-sprite-list-visitor-v1",
        source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        root_sha256=DIGEST[OWNER],
        sprite_image=sprite_image(proof),
        records=dict(address=TABLE, stride=8, entries=[list(row) for row in FRAMES]),
        slots=dict(offset=0x394, count=2, stride=16, active_bit=1, index_offset=12),
        lifecycle=lifecycle(proof),
        caller=scene_origin(proof),
        traversal=dict(
            iterator=ITERATOR,
            adapter=scalar,
            callback=CALLBACK,
            descriptor_entry_sp=[-36, -28],
            empty_list_R2_entry_sp=-36,
            list_head=4,
            node_value=0,
            node_next=8,
            beyond_callback_abi_proved=False,
        ),
        assumptions=[
            "The scene has two writable 16-byte slots at +0x394, distinct from this frame. Each active "
            "slot has a live sprite and a frame index 0..3. The original activation resets the frame "
            "and the update disables after frame 3; arbitrary incoming objects need this domain separately.",
            "The sprite CpuSet image was installed before execution, remains intact, and the pointed-to "
            "sprites, graphics and projection context meet the physical bounds required by the original callees.",
            "When scene flag bit 1 is clear, the list and each reached node are aligned, live and separate "
            "from the private frame. The callback receives the node value and scene pointer. Calls, interrupt "
            "handlers and physical aliases must preserve protected frames and the applicable returning ABI. "
            "Termination, external callback effects and list lifetime are conditional.",
        ],
    )
