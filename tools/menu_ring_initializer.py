"""The original menu's ring allocation, slot-zero initializer and callback installation."""

import hashlib
import struct

import iwram_installation_prerequisite as installation
import installed_zero_effects as zero
import literal_callback_closure_profile as closure
import scheduler_event_definition as event

OWNER = 0x0804C8C4
SIZE = 0x394
USA = "43fc8204c6dceee58828aebc7af0c72eb807e99f35ad641c8bb0a4fa8b6edc19"
TABLE = 0x0836D4B8
IMAGE = 0x03005E78
CALLS = {
    10: 0x08006B8C,
    18: 0x08006B8C,
    22: 0x0804CA00,
    34: 0x0804CA58,
    46: 0x0814224C,
    64: 0x0814186C,
    84: 0x0814186C,
    98: 0x08006A7C,
    108: 0x08006ADC,
    118: 0x08006ADC,
    128: 0x08006ADC,
}
OBJECTS = {
    140: "data_03000880",
    144: "data_0201F540",
    148: "g_callbacks_0836D4B8",
    152: "data_03003860",
    160: "data_03002710",
    164: "data_03002820",
    168: "data_03000E40",
}
CALLBACKS = (0x0804D86C, 0x0804CAE4, 0x0804E05C)
DEPENDENCIES = {
    0x0800052C: 96,
    0x0804C888: 60,
    0x0804C97C: 102,
    0x0804C9E4: 28,
    0x080069F4: 136,
    0x08006A7C: 60,
    0x08006ADC: 28,
    0x08006B8C: 14,
    0x0804CA00: 68,
    0x0804CA58: 20,
    0x0804CA6C: 20,
    0x0804CA8C: 36,
    0x080070C8: 112,
    0x08007138: 54,
    0x0804D86C: 176,
    0x0804CAE4: 206,
    0x0804E05C: 204,
}


def callback_site(instructions, edges, calls, address, records):
    expected = [[pos, name, 0] for pos, name in OBJECTS.items()]
    expected.extend([172 + i * 4, f"func_{target:08X}", 0] for i, target in enumerate(CALLBACKS))
    event.require(
        address == OWNER and sorted(map(tuple, records)) == sorted(map(tuple, expected)),
        "menu ring requires every original typed object and handler",
    )
    event.require(
        calls == {address + pos: target for pos, target in CALLS.items()},
        "menu ring requires its exact heap, BIOS and table calls",
    )
    # R0 retains the returned allocation through its publication to the global. R5
    # survives the allocation call and supplies the same byte count to the initializer.
    sites = [
        0x0804C8DE,
        0x0804C8E0,
        0x0804C8E2,
        0x0804C8E4,
        0x0804C8E6,
        0x0804C8EA,
        0x0804C8EC,
        0x0804C8EE,
        0x0804C8F0,
        0x0804C8F2,
    ]
    expected_code = [
        "ldr r4, [pc, #0x74]",
        "movs r5, #0xe5",
        "lsls r5, r5, #2",
        "adds r0, r5, #0",
        "bl #0x804ca58",
        "str r0, [r4]",
        "ldr r1, [pc, #0x68]",
        "ldr r2, [r1]",
        "adds r1, r5, #0",
        "bl #0x814224c",
    ]
    for pc, code in zip(sites, expected_code):
        item = instructions[pc]
        event.require(item.mnemonic + " " + item.op_str == code, "menu initializer argument or slot changed")
        event.require(edges[pc] == (pc + item.size,), "menu initializer has a nonsequential successor")
    predecessors = {target: {a for a, ends in edges.items() if target in ends} for target in sites[1:]}
    event.require(
        all(predecessors[end] == {start} for start, end in zip(sites, sites[1:])),
        "menu initializer has an alternate entry",
    )
    return [
        [
            46,
            40,
            42,
            148,
            OBJECTS[148],
            dict(
                base_register="r1",
                target_register="r2",
                slot_offset=0,
                destination="returned 0804CA58 allocation",
                bytes=SIZE,
            ),
        ]
    ]


def layout(ring, setter, data):
    """Bind ring stride/wrap, the table's two write widths and all three registrations."""
    event.sequence(
        ring,
        0x0804CA8C,
        0x0804CA8C,
        [
            "ldr r0, [pc, #0x1c]",
            "ldr r0, [r0]",
            "movs r1, #0xe4",
            "lsls r1, r1, #2",
            "adds r3, r0, r1",
            "ldr r2, [r3]",
            "lsls r1, r2, #3",
            "subs r1, r1, r2",
            "lsls r1, r1, #2",
            "adds r1, #0x10",
            "adds r0, r0, r1",
            "adds r2, #1",
            "movs r1, #0x1f",
            "ands r2, r1",
            "str r2, [r3]",
            "bx lr",
        ],
    )
    event.require(struct.unpack_from("<I", ring, 32) == (0x0201F540,), "ring cursor uses another allocation")
    event.sequence(
        setter,
        0x08006ADC,
        0x08006ADC,
        [
            "push {r4, lr}",
            "lsls r1, r1, #0x18",
            "lsrs r1, r1, #0x18",
            "ldr r4, [r0, #8]",
            "lsls r3, r1, #2",
            "adds r3, r3, r4",
            "str r2, [r3]",
            "ldr r0, [r0, #0xc]",
            "adds r0, r0, r1",
            "movs r1, #0",
            "strb r1, [r0]",
            "pop {r4}",
            "pop {r0}",
            "bx r0",
        ],
    )
    event.sequence(
        data,
        OWNER,
        0x0804C91C,
        [
            "ldr r4, [pc, #0x44]",
            "ldr r1, [pc, #0x48]",
            "ldr r2, [pc, #0x48]",
            "adds r0, r4, #0",
            "movs r3, #5",
            "bl #0x8006a7c",
            "ldr r2, [pc, #0x44]",
            "adds r0, r4, #0",
            "movs r1, #0",
            "bl #0x8006adc",
            "ldr r2, [pc, #0x3c]",
            "adds r0, r4, #0",
            "movs r1, #1",
            "bl #0x8006adc",
            "ldr r2, [pc, #0x38]",
            "adds r0, r4, #0",
            "movs r1, #2",
            "bl #0x8006adc",
        ],
    )
    return dict(header=16, entries=32, stride=28, cursor=0x390)


def manifest(rom, mapping, index, data):
    import match
    import owner_admission_profile as owner

    event.require(hashlib.sha256(rom).hexdigest() == USA, "menu ring requires the USA image")
    original, _, _, _, _ = closure.complete(OWNER, 184, 59, rom, mapping, index)
    event.require(data == original, "menu initializer differs from the original")
    event.require(
        struct.unpack_from("<11I", data, 140)
        == (
            0x03000880,
            0x0201F540,
            TABLE,
            0x03003860,
            0x01000100,
            0x03002710,
            0x03002820,
            0x03000E40,
            *(pc | 1 for pc in CALLBACKS),
        ),
        "menu ring original pool changed",
    )
    evidence = []
    bodies = {}
    for address, size in DEPENDENCIES.items():
        body = rom[address - match.ROM_BASE : address + size - match.ROM_BASE]
        owner.validate_span(body, address, rom, mapping, index)
        bodies[address] = body
        evidence.append([address, size, hashlib.sha256(body).hexdigest()])
    ring = layout(bodies[0x0804CA8C], bodies[0x08006ADC], data)
    plan = installation.verify(
        rom[0x2768:0x27B8],
        0x08002768,
        rom,
        mapping,
        index,
        selector=installation.SELECTOR,
        call_site=0x08002796,
        pointer_address=TABLE,
    )
    event.require(
        plan["arguments"] == dict(source=0x08A38A2C, destination=IMAGE, control=88)
        and plan["entry"]["pointer_word"] == (IMAGE | 1)
        and plan["copy_plan"]["bytes"] == 176,
        "menu ring requires the boot-installed slot-zero image",
    )
    effect = zero.verify_aligned_menu_ring(bytes.fromhex(plan["source_image"]["bytes"]), IMAGE)
    event.require(
        effect["writes"] == [("stack", -4, 4)] + [("destination", i, 4) for i in range(0, SIZE, 4)]
        and effect["reads"] == [("stack", -4, 4)]
        and effect["SP_restored"]
        and effect["protected_return"],
        "menu ring clear differs from its complete word-aligned allocation",
    )
    return dict(
        schema="usa-menu-ring-initializer-v1",
        callbacks=list(CALLBACKS),
        callback_slots=[0, 1, 2],
        slot_count=5,
        clear_bytes=SIZE,
        zero_word_stores=SIZE // 4,
        arena=[0x0201F550, 0x02040000],
        palette_fills=[[0x03003860, 0x200], [0x03003A60, 0x200]],
        boot=plan["copy_plan"],
        ring=ring,
        dependencies=evidence,
        conditions=[
            "Boot has installed the original unchanged IWRAM routine. The menu owns its arena and both palette halves.",
            "The aligned allocation succeeds. Its 916 writable bytes, the saved return, input/output tables, palettes and executing code are physically distinct.",
            "The existing top-level runner has at least two slots. The stack is aligned and private, BIOS CpuSet executes normally, and no asynchronous writer changes the image, tables or frames.",
        ],
    )
