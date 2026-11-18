"""Conditional source replay for the eight-byte action-table shuffle."""

import hashlib
import struct

SELECTOR = 'conditional-installed-action-shuffle-v1'
SCHEMA = 'elf-symbol-thumb-conditional-installed-action-shuffle-v1'
ADDRESS = 0x08132064
BASE = 0x08000000
THUNK = 0x08142250
RNG = 0x08002804
REMAINDER = 0x08142950
POINTER = 0x0836D4BC
TABLE = 0x083A8C0C
CALLS = [[0x1E, '_call_via_r3'], [0x28, 'func_08002804'], [0x32, '__modsi3'], [0x5A, '_call_via_r3']]
DATA = [[0x7C, 'data_0836D4BC', 0], [0x80, 'data_083A8C0C', 0]]
TARGETS = {
    '_call_via_r3': (THUNK, False),
    'func_08002804': (RNG, False),
    '__modsi3': (REMAINDER, False),
    'data_0836D4BC': (POINTER, True),
    'data_083A8C0C': (TABLE, True),
}


def check_bindings(address, bindings, targets=None):
    if (
        address != ADDRESS
        or bindings != dict(calls=CALLS, data=DATA, functions=[], switches=[])
        or (targets is not None and targets != TARGETS)
    ):
        raise ValueError('action shuffle needs its six exact original compiler bindings and symbol roles')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def words(instructions, start, expected):
    """Check each Thumb16 instruction at its actual reachable address."""
    for offset, value in enumerate(expected):
        item = instructions.get(start + 2 * offset)
        if item is None or item.bytes != value.to_bytes(2, 'little'):
            raise ValueError(f'action shuffle instruction differs at {start + 2 * offset:08X}')


def caller_shape(data, address, instructions, edges, calls):
    if (
        address != ADDRESS
        or len(data) != 132
        or len(instructions) != 57
        or calls != {address + offset: TARGETS[name][0] for offset, name in CALLS}
    ):
        raise ValueError('action shuffle requires its complete indexed owner and four genuine calls')
    # Save R4..R7, LR and high R8; allocate eight local bytes. Test object+38 bit 4.
    words(
        instructions,
        address,
        (0xB5F0, 0x4647, 0xB480, 0xB082, 0x1C07, 0x8CF9, 0x2010, 0x4008, 0x2800, 0xD12C),
    )
    # R4 = pointer word address, R1 = source, R3 = *R4, R0 = SP, R2 = 8, BL.
    words(instructions, address + 0x14, (0x4C19, 0x491A, 0x6823, 0x4668, 0x2208))
    # R5 = count 8, R6 = output index 1, R8 = preserved pointer-word address.
    words(instructions, address + 0x22, (0x2508, 0x2601, 0x46A0))
    # Sign extend low halfword of RNG; use the live R5 for the signed remainder.
    words(instructions, address + 0x2C, (0x0400, 0x1400, 0x1C29))
    # R3 = remainder; reload unit from object+8. Copy local[index] to unit+12+i.
    words(instructions, address + 0x36, (0x1C03, 0x68B9, 0x310C, 0x1989, 0x4668, 0x18C4, 0x7820, 0x7008))
    # R2 = count - index - 1. On zero, skip both pointers and the callback.
    words(instructions, address + 0x46, (0x1AE8, 0x1E42, 0x2A00, 0xD007))
    # R1 = SP + (index+1), R3 = *R8, R0 = R4 = SP + index, BL.
    words(instructions, address + 0x4E, (0x1C58, 0x466B, 0x1819, 0x4640, 0x6803, 0x1C20))
    # R6++, R5 = (u8)(R5-1). Signed i > 8 exits before the distinct count test.
    words(instructions, address + 0x5E, (0x3601, 0x1E68, 0x0600, 0x0E05, 0x2E08, 0xDC01, 0x2D00, 0xD1DC))
    # Release local, restore R8 via R3, restore R4..R7, return via saved LR in R0.
    words(instructions, address + 0x6E, (0xB002, 0xBC08, 0x4698, 0xBCF0, 0xBC01, 0x4700))
    branches = {0x12: (0x6E, 0x14), 0x4C: (0x5E, 0x4E), 0x68: (0x6E, 0x6A), 0x6C: (0x28, 0x6E), 0x78: ()}
    for site, item in instructions.items():
        expected = branches.get(site - address, (site + item.size - address,))
        if set(edges[site]) != {address + offset for offset in expected}:
            raise ValueError('action shuffle has an incoming bypass, changed loop edge or unproved exit')
    if struct.unpack_from('<II', data, 0x7C) != (POINTER, TABLE):
        raise ValueError('action shuffle literal words do not bind its pointer slot and table')


def rng_record(rng):
    """Authenticate the exact original seed update and its nonnegative 15-bit projection."""
    import match
    if len(rng) != 32:
        raise ValueError('action shuffle RNG extent differs')
    # Written seed is (old*A+B) modulo 2**32, then LSL 1 / LSR 17 leaves only bits 16..30.
    decoded = {
        item.address: item for item in match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB).disasm(rng[:20], RNG)
    }
    words(decoded, RNG, (0x4A04, 0x6811, 0x4804, 0x4348, 0x4904, 0x1840, 0x6010, 0x0040, 0x0C40, 0x4770))
    if struct.unpack_from('<III', rng, 20) != (0x030034B0, 0x41C64E6D, 0x3039):
        raise ValueError('action shuffle RNG state or recurrence literals differ')
    return dict(address=RNG, sha256=sha(rng), seed=0x030034B0, range=[0, 32767])


def prove(data, address, rom, mapping, index, objects, bindings):
    import installed_copy_effects as copy
    import iwram_installation_prerequisite as install
    import match
    import modsi3_profile as remainder
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import indices, span_record

    check_bindings(address, bindings)
    names = match.parse_data_symbols(objects)
    required = dict(
        data_0836D4BC=POINTER,
        data_083A8C0C=TABLE,
        g_state_030034B0=0x030034B0,
        data_083A87B0=0x083A87B0,
        data_0200F3F0=0x0200F3F0,
    )
    if any(names.get(name) != value for name, value in required.items()):
        raise ValueError(
            'action shuffle requires its indexed callback, initializer, RNG state and dispatcher objects'
        )
    entries, rows = indices(mapping, index)

    def body(start, end, count):
        row = span_record(start, end, entries, rows, rom)
        if row['instrs'] != count:
            raise ValueError('action shuffle dependency instruction count differs')
        return rom[start - BASE : end - BASE]

    if data != body(address, address + 132, 57):
        raise ValueError('action shuffle linked bytes differ from the complete original owner')
    refined = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, table_words = graph.graph(data, address, refined)
    if branches or table_words:
        raise ValueError('action shuffle excludes local calls and switch tables')
    partition = graph.partition(data, address, refined, instructions, table_words)
    caller_shape(data, address, instructions, edges, calls)

    # The pinned caller loads u8 kind, computes kind*12, and invokes BX R1 with state in R0.
    dispatch = body(0x0813388C, 0x08133970, 97)
    slot = 0x083A87B0 + 18 * 12
    if (
        sha(dispatch) != 'b1a2ee4c8cefef5b7581b6599971145c0e7a1a78a4e47f2b1c344ca282824d5c'
        or struct.unpack_from('<I', rom, slot - BASE)[0] != address | 1
        or body(0x08142248, 0x0814224A, 1) != bytes.fromhex('0847')
    ):
        raise ValueError('action shuffle requires the original dispatcher, descriptor and BX R1')
    rng = rng_record(body(RNG, RNG + 32, 10))
    if body(THUNK, THUNK + 2, 1) != bytes.fromhex('1847'):
        raise ValueError('action shuffle requires complete BX R3')
    if not remainder.verify_context(data, address, calls, (rom, mapping, {address + 0x32: '__modsi3'})):
        raise ValueError('action shuffle needs genuine signed remainder identity')
    for (start, end, _), count in zip(remainder.IDENTITIES, (102, 1)):
        body(start, end, count)

    plan = install.verify(
        body(0x08002768, 0x080027B8, 26),
        0x08002768,
        rom,
        mapping,
        index,
        selector=install.SELECTOR,
        call_site=0x08002796,
        pointer_address=POINTER,
    )
    source, destination = plan['copy_plan']['source'][0], plan['copy_plan']['destination'][0]
    entry = plan['entry']['address']
    if (source, destination, plan['copy_plan']['bytes'], entry, plan['entry']['source_address']) != (
        0x08A38A2C,
        0x03005E78,
        176,
        0x03005EE8,
        0x08A38A9C,
    ):
        raise ValueError('action shuffle installation and Thumb pointer disagree')
    payload = bytes.fromhex(plan['source_image']['bytes'])
    helper = body(0x08A38A9C, 0x08A38ADA, 31)
    inventory = plan['inventory']
    if (
        inventory['reached_bytes'] != len(helper)
        or {row['site'] for row in inventory['instructions']} != set(range(entry, entry + len(helper), 2))
        or payload[entry - destination : entry - destination + len(helper)] != helper
    ):
        raise ValueError('action shuffle copy helper is outside its installed image')
    initializer = rom[TABLE - BASE : TABLE - BASE + 8]
    if len(initializer) != 8:
        raise ValueError('action shuffle must read the complete ROM initializer')
    first = copy.verify_conditional(payload, destination, entry, 8, selector=copy.SELECTOR)
    # Induct at the loop header with opaque table bytes and arbitrary RNG state. The pinned
    # returning callees preserve R5..R8. R4 on entry is dead before its first use.
    cases = []
    i, count = 1, 8
    while True:
        for chosen in range(count):
            rest = count - chosen - 1
            case = dict(iteration=i, count=count, index=chosen, bytes=rest, called=bool(rest))
            if rest:
                case['copy'] = copy.verify_adjacent_table(payload, destination, entry, count, chosen)
            cases.append(case)
        i += 1
        count = (count - 1) & 255
        if i > 8 or count == 0:
            break
    return dict(
        schema=SCHEMA,
        bindings=bindings,
        partition=partition,
        dispatcher=[0x081338BA, 0x08142248, slot],
        rng=rng,
        runtime=dict(
            identities=[list(row) for row in remainder.IDENTITIES],
            dividends=[0, 32767],
            divisors=[1, 8],
            zero_divisor_reachable=False,
        ),
        installation=dict(
            arguments=plan['arguments'],
            copy_plan=plan['copy_plan'],
            entry=plan['entry'],
            installer=plan['installer'],
            wrapper=plan['wrapper'],
            image_sha256=sha(payload),
            helper_sha256=sha(helper),
            obligations=plan['obligations'],
        ),
        initial_copy=dict(
            table=TABLE, bytes=initializer.hex(), case=first['cases'][0], premises=first['unproved_premises']
        ),
        loop=cases,
        flag_set_skips_all_calls=True,
        frame_from_entry_SP=dict(local=[-32, -24], saves=[-24, 0], callee_scratch=[-40, -32]),
        protected_return='saved caller LR via R0',
        premises=[
            'CpuSet executes and returns with the authenticated image resident at every fetch',
            'Word-aligned stack and ordinary accessible, nonwrapping private/save words persist through the calls',
            'Object+38 and each reload at object+8 are readable; unit+12+i is byte-writable on that iteration',
            'RNG state is a readable and writable word; external accesses preserve code, ROM and protected saves',
            'Ordinary little-endian bus memory and stable mapping; no asynchronous or external interference during each copy',
        ],
        unit_output_disjoint_from_local_proved=False,
        unconditional_permutation_proved=False,
    ), instructions
