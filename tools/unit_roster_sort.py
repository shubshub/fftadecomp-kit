"""The six roster keys, packed list and signed in-place partition in the USA menu."""
from hashlib import sha256
from pathlib import Path
import struct

import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
from ability_range_local_bytes import block, require
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

OWNER = 0x08071DC8
SORT = 0x08087D98
PARTITION = 0x0808A0B4
BASE = 0x02000000
COUNT = 24
STRIDE = 0x108
# Dispatch target offset, collection-loop flag read, key store, call and unit field.
CASES = ((0x5C, 0x6A, 0x7E, 0xA0, 9), (0xC4, 0xD2, 0xE6, 0x108, 0x1A),
         (0x12C, 0x13A, 0x14E, 0x170, 0x1E), (0x194, 0x1A6, 0x1C0, 0x1E4, 0xD6),
         (0x208, 0x216, 0x22A, 0x24C, 6), (0x270, 0x27E, 0x28E, 0x2B0, 4))
LITERALS = (0xC0, 0x128, 0x190, 0x204, 0x26C, 0x2CC, 0x32C, 0x364)
NATIVE = {
    OWNER: (0x08072130, '9ff041fd482b1ee09fa42d627cffcc2e7a2aa31c2dc25dbe01c469d027d2a2a4'),
    SORT: (0x08087F0A, '064636cfa6cbdb91f90be3b7b1a0e993b4092d245270c2d1415a5b0264c0f58c'),
    PARTITION: (0x0808A158, 'ab7c01a30a26114b921368c71e04851887e515a1657885ef6c4fbad5c0194645'),
}
SORT_CALLS = (0x08087E3E, 0x08087E4C, 0x08087EE8, 0x08087EF6)
RECURSION = (0x0808A138, 0x0808A146)


def check_source(root, address):
    import plausible

    require(address == OWNER, 'unexpected roster source')
    source = (Path(root) / 'src/08071DC8.c').read_text()
    header = (Path(root) / 'include/ffta.h').read_bytes()
    require(base_header(header, ('func_08071DC8', 'func_08087D98', 'g_state_02000000'))
            and not any(marker in source for marker in (chr(92), '??', '%:', chr(0))),
            'unexpected source preprocessing or header')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    end = 'SortEntry08071DC8 list [ 24 ] ;'
    prefix, separator, body = tokens.partition(end)
    # Bind physical addresses to the declared 24 objects, their field widths,
    # the eight-byte pair, both function prototypes and the actual local array.
    require(separator and '#' not in body and sha256((prefix + end).encode()).hexdigest()
            == 'e7b3ea996a06b3f9284c924ec208bb67a198d172cc1cb17b2e2bc0e0de1f6ac3',
            'unexpected roster declarations or local array capacity')


def bindings():
    table = 0x44
    return dict(calls=[[site, 'func_08087D98'] for _, _, _, site, _ in CASES],
                data=[[site, 'g_state_02000000', 0] for site in LITERALS], functions=[],
                switches=[[0x40, table]] + [[table + i * 4, case[0]] for i, case in enumerate(CASES)])


def extent(rom, mapping, index, address):
    end, digest = NATIVE[address]
    entries, rows = indices(mapping, index)
    row = span_record(address, end, entries, rows, rom)
    require(row['instrs'] == {OWNER: 392, SORT: 181, PARTITION: 80}[address],
            'roster owner or helper instruction count differs')
    data = rom[address - match.ROM_BASE:end - match.ROM_BASE]
    require(sha256(data).hexdigest() == digest, f'changed roster code at {address:08X}')
    return data


def collection(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #0xc0')
    block(ins, OWNER + 0x1A, 'movs r1, #0xff', 'adds r0, r6, #0', 'adds r0, #0x17',
          'strb r1, [r0]', 'subs r0, #1', 'cmp r0, r6', 'bge #0x8071de8')
    block(ins, OWNER + 0x356, 'add sp, #0xc0', 'pop {r3}', 'mov r8, r3',
          'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')
    for start, flag, store, call, field in CASES:
        count, old = ('r1', 'r2') if field == 4 else ('r2', 'r1')
        block(ins, OWNER + start, f'movs {count}, #0', 'movs r3, #0')
        block(ins, OWNER + flag, 'ldrb r0, [r5]' if field == 0xD6 else 'ldrb r0, [r4]', 'cmp r0, #0')
        block(ins, OWNER + flag + 6, f'adds {old}, {count}, #0', f'lsls r0, {old}, #3',
              'mov r7, sp', f'adds {count}, r7, r0')
        if field == 0xD6:
            block(ins, OWNER + flag + 14, 'movs r7, #0xab', 'lsls r7, r7, #1',
                  'adds r0, r4, r7', 'ldrh r0, [r0]')
        elif field == 4:
            block(ins, OWNER + flag + 14, 'ldrb r0, [r4]')
        else:
            load = 'ldrb' if field < 0x10 else 'ldrh'
            off = str(field - 4) if field - 4 < 10 else hex(field - 4)
            block(ins, OWNER + flag + 14, f'{load} r0, [r4, #{off}]')
        if field != 4:
            block(ins, OWNER + store - 4, 'lsls r0, r0, #8', 'adds r0, r0, r3')
        block(ins, OWNER + store, f'str r0, [{count}]', f'adds r0, {old}, #1', 'lsls r0, r0, #0x18',
              f'lsrs {count}, r0, #0x18', f'lsls {old}, {old}, #3', 'add r0, sp, #4',
              f'adds r0, r0, {old}', 'str r3, [r0]')
        block(ins, OWNER + call - 16, 'adds r3, #1', 'cmp r3, #0x17', f'ble #{hex(OWNER + flag)}',
              f'adds r4, {count}, #0', 'subs r2, r4, #1', 'mov r0, sp', 'movs r1, #0', 'mov r3, ip')
        output = call + (10 if field == 4 else 12)
        block(ins, OWNER + output, 'add r2, sp, #4', 'adds r1, r6, r3', 'ldr r0, [r2]',
              'strb r0, [r1]', 'adds r2, #8', 'adds r3, #1', 'cmp r3, r4')
    # Either flag outcome is possible at each physical slot. Both edges advance
    # the slot once. Only the enabled edge writes, using the pre-increment count.
    counts = {0}
    for slot in range(COUNT):
        require(counts == set(range(slot + 1)) and max(counts) * 8 + 8 <= COUNT * 8,
                'packed-list count no longer bounds both stores')
        counts |= {count + 1 for count in counts}
    return dict(slots=COUNT, stride=STRIDE, first_unit=BASE + 0x80,
                enabled_offset=4, key_fields=[case[-1] for case in CASES],
                count_at_end=sorted(counts), record_size=8, saved_bytes=24, local_bytes=192)


def partition_bounds():
    """Cover every possible pair of scan stops for a nonempty interval of at most 24."""
    checked = 0
    for size in range(1, COUNT + 1):
        last = size - 1
        pivot = last // 2
        # First scans cannot cross the selected pivot. Each swap leaves a <=
        # sentinel at the old left stop and a >= sentinel at the old right stop.
        pending = [(0, last, pivot, pivot)]
        seen = set()
        while pending:
            state = pending.pop()
            if state in seen:
                continue
            seen.add(state)
            i, j, left_limit, right_limit = state
            require(0 <= i <= j <= last and i <= left_limit <= last and 0 <= right_limit <= j,
                    'partition scan lost its in-range stopping keys')
            for a in range(i, left_limit + 1):
                for b in range(right_limit, j + 1):
                    if a <= b:
                        next_i, next_j = a + 1, b - 1
                        if next_i <= next_j:
                            require(next_j - next_i < j - i, 'partition scans failed to advance')
                            pending.append((next_i, next_j, b, a))
                            continue
                    else:
                        next_i, next_j = a, b
                    # The actual recursion uses [0,next_j] and [next_i,last],
                    # and calls only when each proposed child has >=2 elements.
                    require((next_j <= 0 or next_j < last) and (next_i >= last or next_i > 0),
                            'recursive partition could repeat its parent interval')
        checked += len(seen)
    return checked


def partitions(rom, mapping, index):
    import owner_admission_profile as owner

    wrapper = extent(rom, mapping, index, SORT)
    ref = owner.refine(wrapper, SORT, mapping)
    ins, _, _, calls, words = graph.graph(wrapper, SORT, ref)
    require(ref['cfg_closed'] and len(ins) == 181 and not words and
            calls == dict.fromkeys(SORT_CALLS, PARTITION), 'sort wrapper calls or extent differ')
    recursive = extent(rom, mapping, index, PARTITION)
    code = match.verify_leaf_instructions(recursive, PARTITION, True,
                validated_calls=dict.fromkeys(RECURSION, PARTITION), self_calls=frozenset(RECURSION))
    require(len(code) == 80, 'recursive partition changed')
    ins.update({item.address: item for item in code})
    block(ins, 0x08087DBA, 'mov r2, sp', 'movs r3, #0x17', 'ldm r4!, {r0, r1}',
          'stm r2!, {r0, r1}', 'subs r3, #1', 'cmp r3, #0', 'bge #0x8087dbe')
    block(ins, 0x08087E62, 'ldr r0, [r2]', 'ldr r1, [r2, #4]', 'stm r4!, {r0, r1}',
          'subs r2, #8', 'subs r3, #1', 'cmp r3, #0', 'bne #0x8087e62')
    # All three partitions have the same comparisons, paired key/value swap,
    # and inclusive rescan. Registers holding the record base differ.
    for head in (0x08087DE6, 0x08087E90, 0x0808A0E2):
        block(ins, head, 'ldr r0, [r7]', 'cmp r0, ip', f'bge #{hex(head + 24)}')
        block(ins, head + 20, 'cmp r0, ip', f'blt #{hex(head + 12)}',
              'ldr r0, [r4]', 'cmp ip, r0', f'bge #{hex(head + 48)}')
        block(ins, head + 44, 'cmp ip, r0', f'blt #{hex(head + 36)}',
              'cmp r6, r5', f'bgt #{hex(head + 76)}', 'ldr r2, [r7]', 'ldr r3, [r7, #4]',
              'ldr r0, [r4]', 'ldr r1, [r4, #4]', 'stm r7!, {r0, r1}', 'str r2, [r4]',
              'str r3, [r4, #4]', 'adds r6, #1', 'subs r4, #8', 'subs r5, #1',
              'cmp r6, r5', f'ble #{hex(head)}')
    return dict(wrapper=SORT, recursive=PARTITION, wrapper_calls=list(SORT_CALLS),
                partition_states_checked=partition_bounds(),
                recursive_calls=list(RECURSION), signed_key=True, stable_ties=False,
                first_pivot='key[(left + right) / 2], signed division toward zero',
                scan_bounds='The first pair of scans stops at or before the midpoint from each side. '
                  'After each swap the exchanged keys bound the next left and right scans. '
                  'Each swap advances both indices; each nontrivial recursive subrange strictly shrinks.',
                range='0 <= left <= right < 24; empty case excluded',
                reverse_reads=192, reverse_writeback='8 * (right + 1) bytes, starting at record zero',
                wrapper_frame=232, recursive_frame=32, conditional_stack_capacity=24 + 192 + 232 + 24 * 32)


def menu_mode(rom):
    # Authentic initializer, menu selection and direction toggle, plus the two
    # matched consumers. A menu writer alone does not establish every live value.
    ranges = ((0x306D8, '064980200875'), (0x73B12, '69888020400008400004040c002c00d187e0'),
              (0x73C34, '8020800008400004050c002d1ad06420cdf07cfc0349487d032805d80130487503e00000d02000024c75'), (0x73B2A, '1c4f397d7f2008407a7d904237d0'),
              (0x73B82, '397d80200840797d08433875387d'), (0x73BA8, '802048403875'),
              (0x6121A, '2948007d494610f0d2fd00260025484641190878ff2838d0'),
              (0xB8174, '18206af763fb80461b48007d4146b9f721fe00210091002541460878'))
    for offset, hex_data in ranges:
        data = bytes.fromhex(hex_data)
        require(rom[offset:offset + len(data)] == data, 'changed menu writer or consuming call')
    require(all(struct.unpack_from('<I', rom, offset)[0] == 0x020020D0
                for offset in (0x306F4, 0x73B9C, 0x612C0, 0xB81EC)), 'changed selection-state pointer')
    return dict(selection_byte=0x020020E4, initialized=0x80, one_menu_cursor_cycle=[0, 1, 2, 3, 4], writer=0x08073B8C,
                toggle=0x08073BAC, consumers=[0x08061220, 0x080B8182], heap_request=24)


def prove(data, address, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(address == OWNER and extent(rom, mapping, index, OWNER) == data and len(ins) == 392
            and original == bindings() and calls == {OWNER + c[3]: SORT for c in CASES}
            and sorted(words.items()) == [tuple(row) for row in original['switches']]
            and match.parse_data_symbols(objects).get('g_state_02000000') == BASE,
            'unexpected roster extent, table, calls or typed object')
    block(ins, OWNER + 0xA, 'lsls r0, r0, #0x18', 'lsrs r2, r0, #0x18', 'lsrs r0, r0, #0x1f',
          'mov ip, r0', 'movs r0, #1', 'mov r1, ip', 'eors r1, r0', 'mov ip, r1')
    block(ins, OWNER + 0x28, 'movs r0, #0x7f', 'ands r0, r2', 'subs r0, #1', 'cmp r0, #5')
    block(ins, OWNER + 0x31C, 'subs r1, r4, r3', 'strb r1, [r0]')
    block(ins, OWNER + 0x34A, 'adds r1, r6, r1', 'strb r3, [r1]')
    return dict(schema=named.ROSTER_SORT_SCHEMA, instructions=len(ins), calls=original['calls'],
                runtime_calls=[], partition=graph.partition(data, address, refinement, ins, words),
                roster=collection(ins), sort=partitions(rom, mapping, index), menu=menu_mode(rom),
                conditions=[
                    'The 24-slot roster is stable, the 24-byte output is writable ordinary GBA RAM, '
                    'and both are disjoint from each other and the live stack.',
                    'For low-seven-bit modes 1..6, at least one unit must be enabled. '
                    'The callee reads its first pivot before testing for an empty partition.',
                    'With bit 7 clear the sorter reads all 192 local bytes as ordinary readable machine words. '
                    'Only the initialized prefix contributes to comparisons and output. No C initialization '
                    'of the suffix or stability of equal enabled-byte keys is established.',
                    'Other low-seven-bit modes do not call the sorter. With bit 7 set, enabled slot indices '
                    'are emitted directly. With bit 7 clear, the result for each enabled physical slot i is '
                    '(enabled_count - 1 - i) modulo 256. A dense prefix guarantees valid indices on this path; '
                    'an arbitrary sparse roster does not. Unused output bytes retain 0xff.'],
                environment=environment_fingerprint())
