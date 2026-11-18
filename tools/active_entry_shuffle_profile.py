"""The initialized twenty-byte local used by the original active-entry removal shuffle."""

import hashlib

from installed_shuffle_profile import RNG, REMAINDER, rng_record, words

BASE = 0x08000000
ADDRESS, END = 0x08128E40, 0x08128EE0
CLEAR, COMPACT = 0x08038678, 0x080CC2B4
STATE, ENTRIES = 0x02000000, 0x02001F3C
SELECTOR = "active-entry-shuffle-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CALLS = [
    [0x3C, "func_08002804"],
    [0x46, "__modsi3"],
    [0x7C, "func_08038678"],
    [0x86, "func_080CC2B4"],
]
BINDINGS = dict(
    calls=CALLS, data=[[0x98, "g_state_02000000", 0]], functions=[], switches=[]
)
TARGETS = {
    name: (target, False)
    for (_, name), target in zip(CALLS, (RNG, REMAINDER, CLEAR, COMPACT))
}
TARGETS["g_state_02000000"] = (STATE, True)
DIGESTS = {
    ADDRESS: "41a7ee344d2fbc4d489b718aa01691b9893dfa307c8c047f7986019af2733fb8",
    CLEAR: "19c49eac819bd292fcf4f756abc9155dc6cc0e658a0fa5206dfa8974c3bc18d9",
    COMPACT: "2859691f1842c539ecd1e345ec5b62c2a4d3a65f811d5aeea86b9d66a26f6578",
}


def require(condition, description):
    if not condition:
        raise ValueError("active-entry shuffle: " + description)


def check_original(image, address, bindings, targets):
    import match

    symbol, offset = match.function_record(image, "func_08128E40", address, True)
    require(
        address == ADDRESS
        and bindings == BINDINGS
        and targets == TARGETS
        and not offset
        and symbol["size"] == len(image["text"]) == END - ADDRESS,
        "original ELF extent, call, table or relocation role differs",
    )
    compiler_symbol_roles(image, targets)


def compiler_symbol_roles(image, targets):
    for table, symbols in image["symbol_tables"].items():
        for n, row in enumerate(symbols):
            if row["name"] in targets:
                require(
                    row["type"] == 0 and image["section_data"][table][n * 16 + 13] == 0,
                    "unexpected compiler symbol type or visibility",
                )


def exact_edges(ins, edges, base, branches):
    for pc, instruction in ins.items():
        targets = branches.get(pc - base, (pc - base + instruction.size,))
        require(
            set(edges[pc]) == {base + n for n in targets},
            f"unexpected edge at {pc:08X}",
        )


def block(ins, start, halfwords):
    words(ins, start, tuple(int(word, 16) for word in halfwords.split()))


def owner_shape(ins, edges, calls, partition):
    require(
        calls == {ADDRESS + offset: TARGETS[name][0] for offset, name in CALLS},
        "actual BLs differ",
    )
    require(
        [
            (w["address"] - ADDRESS, w["value"], w["load_sites"])
            for w in partition["words"]
        ]
        == [(0x98, STATE, [ADDRESS + 0x10]), (0x9C, ENTRIES - STATE, [ADDRESS + 0x12])],
        "owner entry-table base or offset differs",
    )
    # R7 is the low input byte. R4 is the increasing physical slot, R5 the
    # initialized prefix length. Only a nonzero table member appends to order.
    block(ins, ADDRESS, "b5f0 4647 b480 b085 0600 0e07 2500 2400 4821 4a22 1881")
    block(
        ins,
        ADDRESS + 0x16,
        "8808 2800 d003 466e 1970 7004 3501 3102 3401 2c13 ddf4 2d00 d02c",
    )
    # R8 counts completed passes, R4 enumerates the current prefix. Signed
    # extension of the actual 15-bit result preserves its value; divisor is R5.
    block(ins, ADDRESS + 0x30, "2000 2400 3001 4680 42ac da12")
    block(ins, ADDRESS + 0x40, "0400 1400 1c29")
    # Unequal indexes swap two initialized bytes. Equal indexes bypass both stores.
    block(
        ins,
        ADDRESS + 0x4A,
        "42a0 d006 4669 190a 7813 1809 7808 7010 700b 3401 42ac dbec 4640 2803 dde4",
    )
    # R7 = min(requested, total); neither truncate nor expose an uninitialized entry.
    block(ins, ADDRESS + 0x68, "42bd da01 0628 0e07 2400 42bc da07 466a 1910 7800")
    block(ins, ADDRESS + 0x80, "3401 42bc dbf7")
    block(ins, ADDRESS + 0x8A, "b005 bc08 4698 bcf0 bc01 4700")
    exact_edges(
        ins,
        edges,
        ADDRESS,
        {
            0x1A: (0x24, 0x1C),
            0x2A: (0x16, 0x2C),
            0x2E: (0x8A, 0x30),
            0x3A: (0x62, 0x3C),
            0x4C: (0x5C, 0x4E),
            0x60: (0x3C, 0x62),
            0x66: (0x32, 0x68),
            0x6A: (0x70, 0x6C),
            0x74: (0x86, 0x76),
            0x84: (0x76, 0x86),
            0x94: (),
        },
    )


def collection_lengths():
    # Both outcomes of each original presence test are admitted. n is the exact
    # initialized prefix at that step, not an assumption that all 20 bytes exist.
    lengths = {0}
    for slot in range(20):
        require(
            all(0 <= n <= slot < 20 for n in lengths),
            "append reaches protected stack words",
        )
        lengths |= {n + 1 for n in lengths}
    require(lengths == set(range(21)), "collection lengths differ")
    return lengths


def initialized_prefix():
    lengths = collection_lengths()
    # At each shuffle step either R4==other and no access occurs, or the two
    # bytes are exchanged. An exchange preserves the initialized prefix and
    # its set of unique collected slot indices across the next step/pass.
    exchanges = 0
    for length in sorted(lengths - {0}):
        for index in range(length):
            for other in range(length):
                # Positions are symbolic distinct original entries. Only these
                # positions can change under the checked two LDRB/STRB pairs.
                positions = list(range(length))
                positions[index], positions[other] = positions[other], positions[index]
                require(
                    sorted(positions) == list(range(length)),
                    "exchange loses a collected index",
                )
                exchanges += 1
        for requested in range(256):
            take = length if length < requested else requested
            require(
                0 <= take <= length <= 20, "removal can consume an uninitialized byte"
            )
    return dict(
        maximum=20,
        entry_sp_offsets=[-44, -24],
        append_site=ADDRESS + 0x20,
        active_slot_range=[0, 19],
        possible_lengths=sorted(lengths),
        passes=4,
        swap_load_sites=[ADDRESS + 0x52, ADDRESS + 0x56],
        swap_store_sites=[ADDRESS + 0x58, ADDRESS + 0x5A],
        possible_index_pairs_across_lengths=exchanges,
        selection_count="min(low input byte, initialized length)",
        selected_byte_site=ADDRESS + 0x7A,
        empty_path_has_no_local_read=True,
    )


def native_spans(rom, mapping, index):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import software_double_profile as canonical

    rows, symbols = canonical.indices(mapping, index)

    def native(start, end, expected_count):
        record = canonical.span_record(start, end, rows, symbols, rom)
        raw = rom[start - BASE : end - BASE]
        refined = owner.refine(raw, start, mapping)
        ins, edges, branches, calls, table = graph.graph(raw, start, refined)
        require(
            not branches
            and not table
            and len(ins) == record["instrs"] == expected_count,
            "callee extent, reachable count or branch role differs",
        )
        return raw, ins, edges, calls, graph.partition(raw, start, refined, ins, table)

    return native


def rng_and_remainder(native, data, address, calls, site, rom, mapping, index):
    import modsi3_profile as remainder
    import mod_only_structural_inventory as mod_inventory
    import software_double_profile as canonical

    rng, _, _, rng_calls, _ = native(RNG, RNG + 32, 10)
    require(not rng_calls, "RNG gained a callee")
    seed = rng_record(rng)
    require(
        remainder.verify_context(
            data, address, calls, (rom, mapping, {site: "__modsi3"})
        ),
        "signed remainder call differs",
    )
    mod_frame = mod_inventory.runtime_frames(
        rom, mapping, canonical.prove_remainder_closure(rom, mapping, index)
    )

    return seed, mod_frame


def prove(data, address, rom, mapping, index, objects, bindings):
    import match
    import local_long_branch_profile as frame

    require(
        address == ADDRESS and bindings == BINDINGS,
        "owner or original compiler bindings differ",
    )
    names = match.parse_data_symbols(objects)
    require(
        all(
            names.get(name) == point
            for name, point in [
                ("g_state_02000000", STATE),
                ("data_02001F3C", ENTRIES),
                ("g_state_030034B0", 0x030034B0),
            ]
        ),
        "state, entry table or RNG seed binding differs",
    )
    native = native_spans(rom, mapping, index)
    body, ins, edges, calls, partition = native(ADDRESS, END, 71)
    require(data == body, "linked output differs from the ROM owner")
    owner_shape(ins, edges, calls, partition)
    prefix = initialized_prefix()
    seed, mod_frame = rng_and_remainder(
        native, data, address, calls, address + 0x46, rom, mapping, index
    )
    clear, ci, ce, cc, cp = native(CLEAR, CLEAR + 28, 9)
    compact, mi, me, mc, mp = native(COMPACT, COMPACT + 76, 36)
    require(not cc and not mc, "table mutation helper gained a callee")
    require(
        [w["value"] for w in cp["words"]] == [STATE, ENTRIES - STATE]
        and [(w["value"], w["load_sites"]) for w in mp["words"]]
        == [(ENTRIES, [COMPACT + 4, COMPACT + 0x1A])],
        "clear or compactor table differs",
    )
    # CLEAR narrows R0 to u16 and doubles it; no other incoming argument is consumed.
    block(ci, CLEAR, "0400 4904 0bc0 4a04 1889 1840 2100 8001 4770")
    # Both loops in COMPACT check the same 20-element boundary. Its table
    # pointers derive only from the fixed literal and the local loop indices.
    block(
        mi, COMPACT, "b5f0 2100 4f0a 004b 19d8 8800 1c4d 2800 d115 0628 0e02 2a13 d811"
    )
    block(mi, COMPACT + 0x1A, "4c05 191b 2600 0050 1900 8801 2900 d004 8019 8006 e006")
    block(
        mi,
        COMPACT + 0x34,
        "1c50 0600 0e02 2a13 d9f0 0628 0e01 2913 d9df bcf0 bc01 4700",
    )
    exact_edges(
        mi,
        me,
        COMPACT,
        {
            0x10: (0x3E, 0x12),
            0x18: (0x3E, 0x1A),
            0x28: (0x34, 0x2A),
            0x2E: (0x3E,),
            0x3C: (0x20, 0x3E),
            0x44: (0x06, 0x46),
            0x4A: (),
        },
    )
    for point, raw in ((ADDRESS, body), (CLEAR, clear), (COMPACT, compact)):
        require(
            hashlib.sha256(raw).hexdigest() == DIGESTS[point],
            "original owner or table helper differs",
        )
    return dict(
        schema=SCHEMA,
        bindings=bindings,
        partition=partition,
        initialized_prefix=prefix,
        rng=seed,
        signed_remainder=dict(
            dividends=[0, 32767],
            divisors=[1, 20],
            result="0..total-1",
            zero_divisor_reachable=False,
            frame=mod_frame,
        ),
        root_frame=dict(
            saved_registers=["r4", "r5", "r6", "r7", "r8", "lr"],
            bytes=44,
            local=[-44, -24],
            saved=[-24, 0],
            restored_at=ADDRESS + 0x94,
        ),
        table_helpers=dict(
            address=ENTRIES,
            halfwords=20,
            clear=CLEAR,
            compact=COMPACT,
            clear_frame=frame.prove_frame(ci, ce, CLEAR, {}, cc),
            compact_frame=frame.prove_frame(mi, me, COMPACT, {}, mc),
        ),
        scratch_call_contract="RNG and table helpers derive their own addresses; MOD touches only its own saves",
        private_stack_required=True,
    ), list(ins.values())
