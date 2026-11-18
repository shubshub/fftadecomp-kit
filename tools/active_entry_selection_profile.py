"""The original active-template collector, selector, clear and text lookup at 08128EE0."""

import hashlib
import struct

import active_entry_shuffle_profile as prefix
import stat_drain_profile as stats

BASE = prefix.BASE
ADDRESS, END = 0x08128EE0, 0x08128FC4
TEMPLATES = 0x02002E78
TEXT = 0x085567F0
CLEAR, NAME = 0x080CC510, 0x080CCB68
UNIT_IDS, RECORDS, NAMES = 0x08394778, 0x08521A14, 0x08526680
SELECTOR = "active-template-selection-v1"
SCHEMA = "elf-symbol-thumb-" + SELECTOR
CALLS = [
    [0x6C, "func_08002804"],
    [0x76, "__modsi3"],
    [0xCC, "func_080CC510"],
    [0xD2, "func_080CCB68"],
]
BINDINGS = dict(
    calls=CALLS,
    data=[
        [0x48, "data_02002E78", 0],
        [0x4C, "g_table_085567F0", 0],
        [0x68, "g_state_02000000", 0],
        [0xA8, "g_state_02000000", 0x2E7D],
    ],
    functions=[],
    switches=[],
)
TARGETS = {
    name: (point, False)
    for (_, name), point in zip(CALLS, [prefix.RNG, prefix.REMAINDER, CLEAR, NAME])
}
TARGETS.update(
    data_02002E78=(TEMPLATES, True),
    g_table_085567F0=(TEXT, True),
    g_state_02000000=(prefix.STATE, True),
)
DIGESTS = {
    ADDRESS: "2658472e1ac6a3e372c198345355406ac2e9ebac23a7b2a4ebf5fe24f71a2e3f",
    CLEAR: "ddd60dc2ad22466dc64ae79fc25bdc48b045b204c07d7279082112191c110f2d",
    NAME: "e22607f98f6653ee06005be20f28a4953a393039c4797ec1b81c5c09b941157b",
}


def require(value, reason):
    if not value:
        raise ValueError("active template selection: " + reason)


def check_original(image, address, bindings, targets):
    import match

    symbol, offset = match.function_record(image, "func_08128EE0", address, True)
    require(
        address == ADDRESS
        and not offset
        and bindings == BINDINGS
        and targets == TARGETS
        and symbol["size"] == len(image["text"]) == END - ADDRESS,
        "original owner or exact call and data relocation roles differ",
    )
    prefix.compiler_symbol_roles(image, targets)


def checked_words(partition, start, expected):
    require(
        [
            (
                w["address"] - start,
                w["value"],
                [site - start for site in w["load_sites"]],
            )
            for w in partition["words"]
        ]
        == expected,
        "literal value or use differs",
    )


def owner_shape(ins, edges, calls, partition):
    require(
        calls == {ADDRESS + o: TARGETS[n][0] for o, n in CALLS}, "unexpected owner BL"
    )
    checked_words(
        partition,
        ADDRESS,
        [
            (0x48, TEMPLATES, [0x0A]),
            (0x4C, TEXT, [0x3C]),
            (0x68, prefix.STATE, [0x60]),
            (0xA8, TEMPLATES + 5, [0x88]),
            (0xE0, TEMPLATES + 5 - prefix.STATE, [0xB4]),
        ],
    )
    # The little-endian name consumes four separate bytes of each 16-byte record.
    # R3 enumerates physical indices, R4 counts only appended local bytes.
    prefix.block(
        ins,
        ADDRESS,
        "b5f0 b085 0600 0e05 2600 4a0f 2400 2300 7811 7850 0200 4308 7891 0409 4301 78d0 0600 4308 2800 d003",
    )
    prefix.block(
        ins,
        ADDRESS + 0x28,
        "4669 1908 7003 3401 3301 3210 2b13 ddeb 2c00 d109 4803 21ba 0109 1840 6800 e046",
    )
    # Mode 2 sign-extends the authentic 15-bit RNG result. On entry to this branch R4>0.
    prefix.block(
        ins, ADDRESS + 0x50, "2d02 d00b 2d03 d013 2563 2300 42a3 da34 4801 4684 e022"
    )
    prefix.block(ins, ADDRESS + 0x70, "0400 1400 1c21")
    # High/low comparisons include equality. The initial physical selection is zero.
    prefix.block(
        ins,
        ADDRESS + 0x7A,
        "4468 7806 e024 2500 2300 42a3 da20 4f07 4669 18c8 7802 0110 19c1 7808 42a8 d301 1c05 1c16 3301 42a3 dbf2 e011",
    )
    prefix.block(
        ins,
        ADDRESS + 0xAC,
        "4669 18c8 7802 0111 480a 4460 1809 7808 42a8 d801 1c05 1c16 3301 42a3 dbf0 1c30",
    )
    prefix.block(ins, ADDRESS + 0xD0, "1c30")
    prefix.block(ins, ADDRESS + 0xD6, "b005 bcf0 bc02 4708")
    prefix.exact_edges(
        ins,
        edges,
        ADDRESS,
        {
            0x26: (0x30, 0x28),
            0x36: (0x10, 0x38),
            0x3A: (0x50, 0x3C),
            0x46: (0xD6,),
            0x52: (0x6C, 0x54),
            0x56: (0x80, 0x58),
            0x5E: (0xCA, 0x60),
            0x64: (0xAC,),
            0x7E: (0xCA,),
            0x86: (0xCA, 0x88),
            0x98: (0x9E, 0x9A),
            0xA2: (0x8A, 0xA4),
            0xA4: (0xCA,),
            0xBE: (0xC4, 0xC0),
            0xC8: (0xAC, 0xCA),
            0xDC: (),
        },
    )


def table_value(rom, address, fmt):
    require(
        BASE <= address <= BASE + len(rom) - struct.calcsize(fmt),
        "table read outside ROM",
    )
    return struct.unpack_from(fmt, rom, address - BASE)[0]


def lookup_rows(rom, mapping, index, objects):
    import match
    import owner_admission_profile as owner

    # Authenticate the whole read-only lookup before specializing its switch to selector 0.
    point = stats.LOOKUP
    data = rom[point - BASE : 0x080C8A24 - BASE]
    owner.validate_span(data, point, rom, mapping, index)
    require(
        hashlib.sha256(data).hexdigest() == stats.HASHES[point],
        "original nested lookup differs",
    )
    jump_words = {
        offset: struct.unpack_from("<I", data, offset)[0] - point
        for offset in range(44, 240, 4)
    }
    require(
        jump_words[44] == 48 and jump_words[48] == 0xF0,
        "lookup case zero or dispatch base differs",
    )
    symbol = "g_table_08521A14"
    switch = match.preloaded_switch_layout(
        data, point, jump_words, {40: (symbol, RECORDS)}
    )
    instructions, flow = match.verify_preloaded_switches(
        data,
        point,
        rom,
        mapping,
        objects,
        dict(calls=[], data=[[40, symbol, 0]], switch=switch),
    )
    require(len(instructions) == 501, "nested lookup instruction count differs")
    decoder = {i.address: i for i in instructions}
    # Entry computes record = table + first*52; selector zero reaches case at +0xF0.
    prefix.block(
        decoder,
        point,
        "b570 0600 0e00 0609 0e0c 0612 0e15 2134 4341 4805 180b 1c02 4e04 2d2f d8fd 00a8 1980 6800 4687",
    )
    prefix.block(
        decoder,
        point + 0xF0,
        "7958 28ff d100 e1cc 2800 d000 e1cf 7819 7858 0200 4308 e1d2",
    )
    prefix.block(decoder, point + 0x4AE, "bc70 bc02 4708")
    rows = []
    for slot in range(20):
        unit = table_value(rom, UNIT_IDS + slot, "<B")
        record = RECORDS + 52 * unit
        require(table_value(rom, record + 5, "<B") == 0, "selectable record redirects")
        key = table_value(rom, record, "<H")
        value = table_value(rom, NAMES + 4 * key, "<I")
        require(BASE <= value < BASE + len(rom), "selected text pointer outside ROM")
        rows.append([slot, unit, key, value])
    # The original slot table, relevant record projections and referenced words
    # are bounded independently from the rest of the text/data sections.
    require(
        hashlib.sha256(b"".join(struct.pack("<BBHI", *row) for row in rows)).hexdigest()
        == "0d0c8d0f3aa6f0ead7a68b73f4b3d1e785696065aee8574f54c8773351385f7c",
        "selectable name rows or values differ",
    )
    return dict(
        address=point, instructions=len(instructions), flow=flow, selector=0, rows=rows
    )


def prove(data, address, rom, mapping, index, objects, bindings):
    import match
    import local_long_branch_profile as frame

    require(
        address == ADDRESS and bindings == BINDINGS, "owner or compiler bindings differ"
    )
    expected = {
        "g_state_02000000": prefix.STATE,
        "data_02002E78": TEMPLATES,
        "g_table_085567F0": TEXT,
        "g_state_030034B0": 0x030034B0,
        "g_table_08394778": UNIT_IDS,
        "g_table_08521A14": RECORDS,
        "g_table_08526680": NAMES,
    }
    names = match.parse_data_symbols(objects)
    require(
        all(names.get(name) == v for name, v in expected.items()),
        "RAM or ROM object binding differs",
    )
    native = prefix.native_spans(rom, mapping, index)
    root, ins, edges, calls, partition = native(ADDRESS, END, 97)
    require(root == data, "linked owner differs from ROM")
    owner_shape(ins, edges, calls, partition)
    lengths = sorted(prefix.collection_lengths())
    seed, mod_frame = prefix.rng_and_remainder(
        native, data, address, calls, address + 0x76, rom, mapping, index
    )
    clear, ci, ce, cc, cp = native(CLEAR, CLEAR + 136, 57)
    name, ni, ne, nc, np = native(NAME, NAME + 44, 16)
    for where, body in ((ADDRESS, root), (CLEAR, clear), (NAME, name)):
        require(
            hashlib.sha256(body).hexdigest() == DIGESTS[where],
            "original owner or helper differs",
        )
    require(
        not cc and nc == {NAME + 0x12: stats.LOOKUP},
        "clear or name call inventory differs",
    )
    checked_words(
        cp,
        CLEAR,
        [
            (0x74, prefix.STATE, [4]),
            (0x78, 0x2E78, [0xA]),
            (0x7C, 0x2E79, [0x12]),
            (0x80, 0x2E7F, [0x34]),
            (0x84, 0x2E87, [0x66]),
        ],
    )
    prefix.exact_edges(ci, ce, CLEAR, {0x70: ()})
    # 080CC510 performs fifteen STRB instructions, each with value zero. Its
    # only protected record byte is +4; the selected slot may be the inactive zero slot.
    prefix.block(
        ci,
        CLEAR,
        "b530 0600 4c1b 0d00 1903 4a1b 1899 2200 700a 4d1a 1959 700a 3501 1959 700a 3501 1959 700a 3502 1961 1841 700a 3501 1961 1841 700a 4912 1864 1900 7002 3502 1958 7002 3102 1858 7002 3502 1958 7002 3102 1858 7002 3502 1958 7002 3102 1858 7002 3502 1958 7002 4807 181b 701a bc30 bc01 4700",
    )
    checked_words(np, NAME, [(0x24, NAMES, [6]), (0x28, UNIT_IDS, [8])])
    prefix.block(ni, NAME, "b510 0600 0e00 4c07 4907 1840 7801 1c08 2200")
    prefix.block(ni, NAME + 0x16, "0080 1900 6800 bc10 bc02 4708")
    prefix.exact_edges(ni, ne, NAME, {0x20: ()})
    lookup = lookup_rows(rom, mapping, index, objects)
    fallback = table_value(rom, TEXT + 0xBA0, "<I")
    require(fallback == 0x085566C4, "empty-table return word differs")
    return dict(
        schema=SCHEMA,
        bindings=bindings,
        partition=partition,
        collection=dict(
            local_entry_sp_offsets=[-40, -20],
            saved_entry_sp_offsets=[-20, 0],
            lengths=lengths,
            slots=20,
            stride=16,
            presence_bytes=[0, 1, 2, 3],
            append_site=ADDRESS + 0x2C,
        ),
        selection=dict(
            empty_text=[TEXT + 0xBA0, fallback],
            random_mode=2,
            maximum_mode=3,
            maximum_initial=0,
            minimum_initial=99,
            tie="last qualifying entry",
            minimum_no_qualifier_slot=0,
            appearance_offset=5,
            local_read_sites=[ADDRESS + 0x7C, ADDRESS + 0x8E, ADDRESS + 0xB0],
        ),
        rng=seed,
        remainder=dict(dividend=[0, 32767], divisor=[1, 20], frame=mod_frame),
        clear=dict(
            address=CLEAR,
            offsets=[0, 1, 2, 3, *range(5, 16)],
            frame=frame.prove_frame(ci, ce, CLEAR, {}, cc),
        ),
        name=dict(
            address=NAME, frame=frame.prove_frame(ni, ne, NAME, {}, nc), lookup=lookup
        ),
        private_stack_required=True,
    ), list(ins.values())
