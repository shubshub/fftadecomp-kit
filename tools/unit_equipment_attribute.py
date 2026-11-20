"""The five equipment slots and the two selected entries used by the battle attribute caller."""
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

BASE = 0x08000000
OWNER, WRAPPER, SORT, COLLECT = 0x0812F5E0, 0x0812F0D8, 0x0812E55C, 0x0812E4F4
FLAG, SLOT, ITEM, DEFAULT = 0x080CD95C, 0x080C7EA4, 0x080CA7A4, 0x08130820
SCENES, ITEMS = 0x0854CD54, 0x0851D180
COPY_POINTER = 0x0836D4BC
CALLS = {20: FLAG, 40: WRAPPER, 70: ITEM, 78: DEFAULT, 96: SLOT, 152: ITEM}
GROUPS = {1: (8, 0x0852A4D0), 2: (9, 0x0852A650), 4: (8, 0x0852A860),
          23: (10, 0x0852C480), 37: (7, 0x0852D740)}

# Complete extents and historical index annotations from both game maps.
PINS = {
    0x080C7EA4: (0x080C817C, 224, '29dd15c43bb1bffac2764ef500fea0cc258ebea77360b3d04e0ee382b738ffcb'),
    0x080C95A8: (0x080C95C0, 8, '1972a08b68f4413fbec69e9c0ceef5227ed3608bb39299597a4de0c061164b84'),
    0x080C9644: (0x080C9B8C, 676, '7b09c15e21881b39738c6613c9bf6d6226c2721f78f4af04c870bd6d2aa22861'),
    0x080CA268: (0x080CA2E8, 53, 'b8e2ae4afe8a92bee5f1313a47f803ef872f8412beb4a53cef45553f1d7162fc'),
    0x080CA7A4: (0x080CA8FE, 126, 'ff46b43099ea0296e3f9646af8166d45efb5375d73b657984d4b2370b01221f1'),
    0x080CD95C: (0x080CD974, 12, '3d6f342fb7428653eeb5544eefb40079fad73943ed9f12b6e8d29230367ee494'),
    0x081256D4: (0x0812575E, 58, '110f29ecbf29d8eb7b795868aec7136deaf467ff1670641ffaa298f4eb85a290'),
    0x0812E4F4: (0x0812E55C, 49, '6633d9e397d8baf8197ce513bed28a1dc01683aa6c48d1bac976ffd61edf85fa'),
    0x0812E55C: (0x0812E5B4, 40, 'e46c5071dc02387cb4d759b1b3ef8b8087cf28b2b16bb335080c0e933b510495'),
    0x0812F0D8: (0x0812F0E2, 4, '25d905c010abae7cf07c564bee8bbeaf3b04b81d9464c11cbabbf4d228cdf11a'),
    0x0812F5E0: (0x0812F690, 82, '0be7e0e5860c4af7029b16b50334a98b5f2695baf6c26e8fa9fe71d183c96d2b'),
    0x0812F690: (0x0812F6DE, 37, '2b6eb80f8b11b3a57733934b82b385d93ec837e8060ae009eb67dfddf442531c'),
    0x0812FD44: (0x0812FDDA, 69, 'd26175e58ca0bf9f4ecdac751f0902fffa8b8b5a29085f381e8fedd7ae51592f'),
    0x0812FE38: (0x0813010C, 322, 'aa7c7ec8a62daa353cc4a0280b78225e0e8e726eeca2d7526319dee0249bd6a5'),
    0x08130820: (0x08130834, 8, '939752b4db797ff5cfcbdaec3bd7484798f8b33e64bde99ca3b3e9082ce3606d'),
    0x08142250: (0x08142252, 1, '477db9ac7ca5efc12e37f882656b8fe5a363ffeb99b2e565a953d10c3c91ab21'),
}


def bindings(calls=CALLS):
    return dict(calls=[[site, f'func_{target:08X}'] for site, target in calls.items()],
                data=[], functions=[], switches=[])


def check_original(image, address, original, targets):
    from active_entry_shuffle_profile import compiler_symbol_roles
    import battle_action_value as battle
    import battle_eligibility as guard
    import battle_action_dispatch as dispatch
    if address == dispatch.OWNER:
        dispatch.check_original(image, original, targets)
        return
    calls = {OWNER: CALLS, battle.OWNER: battle.CALLS, guard.OWNER: guard.CALLS}.get(address)
    require(calls is not None, 'unexpected equipment owner')
    expected = bindings(calls)
    expected_targets = {f'func_{target:08X}': (target, False) for target in calls.values()}
    if address == guard.OWNER:
        expected['data'] = guard.DATA
        expected_targets[guard.STATE_NAME] = (guard.STATE, True)
    require(original == expected and targets == expected_targets,
            'equipment owner original call roles differ')
    compiler_symbol_roles(image, targets)
    require(all(not s['size'] for s in image['symbols'] if s['name'] in targets),
            'equipment helper reference has a size')


def check_source(root, address):
    import plausible
    root = Path(root)
    import battle_action_value as battle
    import battle_eligibility as guard
    import battle_action_dispatch as dispatch
    name = f'func_{address:08X}'
    source_name = f'src/{address:08X}.c'
    source = root / source_name
    text = source.read_text()
    headers = {source_name, 'include/ffta.h'}
    if address == dispatch.OWNER:
        headers.add(dispatch.HEADER_PATH)
        header = (root / dispatch.HEADER_PATH).read_text()
        require(not any(marker in header for marker in (chr(92), '??', '%:', chr(0))),
                'unexpected battle dispatch header syntax')
        tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(header)))
        require(sha256(tokens.encode()).hexdigest() == dispatch.HEADER_HASH,
                'battle dispatch callback declarations or state layout differ')
    require(address in (OWNER, battle.OWNER, guard.OWNER, dispatch.OWNER) and plausible.include_closure(root, source) ==
            (headers, []) and
            base_header((root/'include/ffta.h').read_bytes(), (name,)) and
            not any(s in text for s in (chr(92), '??', '%:', chr(0))),
            'equipment owner requires its reviewed C types and local array')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text)))
    expected = {OWNER: 'e8109fe2fae349a72960c94532ca90763119b4967bf309bbdaee4b46f768af5c',
                battle.OWNER: battle.SOURCE_HASH, guard.OWNER: guard.SOURCE_HASH,
                dispatch.OWNER: dispatch.SOURCE_HASH}[address]
    require(sha256(tokens.encode()).hexdigest() == expected,
            'equipment declarations, local array, or reviewed arithmetic differ')


def word(rom, address):
    return struct.unpack_from('<I', rom, address - BASE)[0]


def ops(rom, start, *expected):
    decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
    decoded = {i.address: i for i in decoder.disasm(rom[start-BASE:start-BASE+4*len(expected)], start)}
    block(decoded, start, *expected)


def equipment_access(rom):
    # The two native lookup tables bind the abstract per-slot predicate to ROM data.
    require(word(rom, 0x080C7EBC) == 0x080C7EC0 and word(rom, 0x080CA7C4) == ITEMS
            and word(rom, 0x080CA7C8) == 0x080CA7CC, 'equipment lookup literals differ')
    for i in range(5):
        target = word(rom, 0x080C7EC0+4*(29+i))
        ops(rom, target, f'ldrh r0, [r2, #{hex(42+2*i)}]', 'b #0x80c8178')
    ops(rom, 0x080CA7AE, 'lsls r1, r5, #5', 'ldr r0, [pc, #0x10]', 'adds r4, r1, r0')
    ops(rom, word(rom, 0x080CA7CC+4*6), 'ldrb r0, [r4, #0xb]', 'b #0x80ca8f8')
    ops(rom, word(rom, 0x080CA7CC+4*3), 'ldrb r0, [r4, #8]', 'b #0x80ca8f8')
    ops(rom, DEFAULT, 'ldrb r1, [r0, #5]', 'movs r0, #0x34', 'muls r0, r1, r0',
        'ldr r1, [pc, #8]', 'adds r0, r0, r1', 'adds r0, #0x33', 'ldrb r0, [r0]', 'bx lr')
    require(word(rom, DEFAULT+16) == 0x08521A14, 'unit default table differs')
    ops(rom, FLAG+2, 'movs r1, #1', 'adds r0, #0xe9', 'ldrb r0, [r0]', 'ands r0, r1')


def producer(rom):
    ops(rom, WRAPPER, 'push {lr}', 'bl #0x812e55c', 'pop {r1}', 'bx r1')
    ops(rom, SORT+2, 'adds r4, r0, #0', 'adds r5, r1, #0', 'movs r0, #0', 'strh r0, [r5]',
        'strh r0, [r5, #2]', 'adds r0, r4, #0', 'bl #0x80cd95c')
    ops(rom, 0x0812E56E, 'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x812e578',
        'movs r0, #0', 'b #0x812e5ae')
    ops(rom, 0x0812E578, 'adds r0, r4, #0', 'adds r1, r5, #0', 'bl #0x812e4f4', 'adds r6, r0, #0',
        'cmp r6, #1', 'ble #0x812e5ae', 'ldrh r0, [r5]', 'movs r1, #0xa', 'bl #0x80ca7a4')
    ops(rom, 0x0812E594, 'ldrh r0, [r5, #2]', 'movs r1, #0xa', 'bl #0x80ca7a4',
        'lsls r4, r4, #0x18', 'lsls r0, r0, #0x18', 'cmp r4, r0', 'bge #0x812e5ac',
        'ldrh r1, [r5]', 'ldrh r0, [r5, #2]', 'strh r0, [r5]', 'strh r1, [r5, #2]', 'adds r0, r6, #0')
    ops(rom, 0x0812E5AE, 'pop {r4, r5, r6}', 'pop {r1}', 'bx r1')
    ops(rom, 0x0812E4FC, 'mov sb, r0', 'adds r6, r1, #0', 'movs r0, #0', 'strh r0, [r6]',
        'strh r0, [r6, #2]', 'movs r7, #0', 'movs r0, #0', 'mov r8, r0')
    ops(rom, 0x0812E50C, 'adds r1, r7, #0', 'adds r1, #0x1d', 'lsls r1, r1, #0x18',
        'lsrs r1, r1, #0x18', 'mov r0, sb', 'bl #0x80c7ea4', 'adds r4, r0, #0',
        'cmp r4, #0', 'beq #0x812e548', 'lsls r0, r4, #0x10', 'lsrs r5, r0, #0x10',
        'adds r0, r5, #0', 'movs r1, #6', 'bl #0x80ca7a4', 'cmp r0, #2',
        'bhi #0x812e548', 'cmp r0, #1', 'blo #0x812e548', 'adds r0, r5, #0',
        'movs r1, #3', 'bl #0x80ca7a4', 'cmp r0, #0x14', 'beq #0x812e548',
        'strh r4, [r6]', 'adds r6, #2', 'movs r0, #1', 'add r8, r0', 'adds r7, #1',
        'cmp r7, #4', 'ble #0x812e50c', 'mov r0, r8')


def local_search(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #4')
    block(ins, 0x0812F5E8, 'adds r7, r0, #0', 'lsls r1, r1, #0x10', 'lsrs r4, r1, #0x10',
          'lsls r2, r2, #0x10', 'lsrs r2, r2, #0x10', 'mov r8, r2', 'bl #0x80cd95c',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x812f602', 'movs r0, #0', 'b #0x812f684')
    block(ins, 0x0812F602, 'movs r6, #0', 'adds r0, r7, #0', 'mov r1, sp', 'bl #0x812f0d8',
          'adds r5, r0, #0', 'cmp r5, #0', 'bgt #0x812f614', 'movs r5, #0', 'mov r0, r8',
          'cmp r0, #0xa', 'beq #0x812f61e', 'movs r5, #0', 'b #0x812f634')
    block(ins, 0x0812F61E, 'cmp r4, #0', 'beq #0x812f62c', 'adds r0, r4, #0',
          'movs r1, #0xa', 'bl #0x80ca7a4', 'b #0x812f632', 'adds r0, r7, #0',
          'bl #0x8130820', 'adds r6, r0, #0')
    block(ins, 0x0812F634, 'movs r4, #0', 'adds r1, r4, #0', 'adds r1, #0x1d', 'lsls r1, r1, #0x18',
          'lsrs r1, r1, #0x18', 'adds r0, r7, #0', 'bl #0x80c7ea4', 'lsls r0, r0, #0x10',
          'lsrs r2, r0, #0x10', 'adds r4, #1', 'cmp r2, #0', 'beq #0x812f67e', 'movs r3, #0',
          'cmp r3, r5', 'bge #0x812f670', 'mov r0, sp', 'ldrh r0, [r0]', 'cmp r0, r2',
          'beq #0x812f66c', 'mov r1, sp', 'adds r1, #2', 'adds r3, #1', 'cmp r3, r5',
          'bge #0x812f670', 'ldrh r0, [r1]', 'cmp r0, r2', 'bne #0x812f65e',
          'cmp r3, r5', 'blt #0x812f67e')
    block(ins, 0x0812F670, 'mov r0, r8', 'lsls r1, r0, #0x18', 'adds r0, r2, #0',
          'lsrs r1, r1, #0x18', 'bl #0x80ca7a4', 'adds r6, r6, r0')
    block(ins, 0x0812F67E, 'cmp r4, #4', 'ble #0x812f636', 'adds r0, r6, #0', 'add sp, #4',
          'pop {r3}', 'mov r8, r3', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')


def cursor_cases():
    cases = []
    for mask in range(32):
        if mask.bit_count() > 2:
            continue
        stores = []
        for slot in range(5):
            if mask & (1 << slot):
                stores.append(2*len(stores))
        # The flag/attribute path can suppress the search. Attribute 10 can stop
        # at either matching halfword or exhaust the count returned in R5.
        searches = []
        for count in sorted({0, len(stores)}):
            for match_index in [*range(count), None]:
                reads = []
                index = 0
                while index < count:
                    offset = 2 * index
                    require(offset in stores and offset + 2 <= 4,
                            'consumer reads outside the initialized selection')
                    reads.append(offset)
                    if index == match_index:
                        break
                    index += 1
                searches.append(dict(count=count, match_index=match_index, read_offsets=reads))
        require(all(offset + 2 <= 4 for offset in stores), 'producer exceeds selection capacity')
        cases.append(dict(mask=mask, selected=len(stores), write_offsets=stores,
                          searches=searches, last_miss_read_offsets=searches[-1]['read_offsets']))
    return cases


def installed_copy(rom, mapping, index):
    import installed_copy_effects as copy
    import iwram_installation_prerequisite as install
    import scheduler_zero_descriptor as boot
    for start, end, digest in boot.BOOT:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, 'boot installer path differs')
    plan = install.verify(rom[0x2768:0x27B8], 0x08002768, rom, mapping, index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=COPY_POINTER)
    require(plan['arguments'] == dict(source=boot.IMAGE, destination=boot.DESTINATION, control=88) and
            plan['source_image']['sha256'] == boot.IMAGE_SHA256 and
            plan['entry']['pointer_word'] == 0x03005EE9, 'installed copy image or entry differs')
    effect = copy.verify_conditional(bytes.fromhex(plan['source_image']['bytes']), boot.DESTINATION,
                                     0x03005EE8, 10, selector=copy.SELECTOR)
    return dict(site=0x080CA278, installed_at=0x08002796, image_sha256=effect['image_sha256'],
                source_offset=8, destination_offset=42, byte_count=10,
                transport=effect['conditional_conclusion'], premises=effect['unproved_premises'])


def scene_rows(rom):
    ops(rom, 0x081256DA, 'lsls r1, r0, #2', 'adds r1, r1, r0', 'lsls r1, r1, #3',
        'ldr r0, [pc, #8]', 'adds r7, r1, r0', 'ldr r1, [r7, #4]')
    require(word(rom, 0x081256EC) == SCENES, 'scene table literal differs')
    ops(rom, 0x081256F8, 'adds r6, r1, #0', 'adds r6, #0x30')
    require(word(rom, 0x08125750) == 0x02002FC4, 'scene unit bank differs')
    ops(rom, 0x08125728, 'adds r3, r5, #0', 'adds r1, r6, #0', 'ldrh r0, [r7]',
        'cmp r3, r0', 'blt #0x81256f0')
    ops(rom, 0x08125712, 'adds r0, r4, #0', 'movs r2, #0', 'bl #0x80c9644')
    ops(rom, 0x080C9AA2, 'adds r0, r7, #0', 'mov r1, r8', 'bl #0x80ca268')
    ops(rom, 0x080CA270, 'adds r0, #0x2a', 'adds r1, #8', 'ldr r3, [r2]', 'movs r2, #0xa', 'bl #0x8142250')
    require(word(rom, 0x080CA2E4) == COPY_POINTER and word(rom, COPY_POINTER) == 0x03005EE9,
            'equipment initializer copy slot differs')
    records = []
    for group, expected in GROUPS.items():
        count, source = struct.unpack_from('<H2xI', rom, SCENES-BASE+40*group)
        require((count, source) == expected, 'reviewed scene count or definition pointer differs')
        for row in range(count):
            slots = struct.unpack_from('<5H', rom, source-BASE+48*row+8)
            selected = []
            for item in slots:
                require(item < (0x08520080-ITEMS)//32, 'scene item outside the original item table')
                offset = ITEMS-BASE+32*item
                if item and rom[offset+11] in (1, 2) and rom[offset+8] != 20:
                    selected.append(item)
            require(len(selected) <= 2, 'scene equipment does not meet the selection premise')
            records.append([group, row, list(slots), selected])
    return records


def prove(data, address, rom, mapping, index, objects, original, ins, calls, refinement, words):
    from software_float_profile import ROM_SHA256
    import battle_action_value as battle
    import battle_eligibility as guard
    import battle_action_dispatch as dispatch
    if address == dispatch.OWNER:
        return dispatch.prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words)
    if address == guard.OWNER:
        return guard.prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words)
    if address == battle.OWNER:
        return battle.prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words)
    require(address == OWNER and sha256(rom).hexdigest() == ROM_SHA256 and
            data == rom[OWNER-BASE:OWNER-BASE+176] and len(ins) == 82 and not words and
            original == bindings() and calls == {OWNER+s: t for s, t in CALLS.items()},
            'equipment owner requires the exact original body and six Thumb calls')
    entries, rows = indices(mapping, index)
    for start, (end, count, digest) in PINS.items():
        row = span_record(start, end, entries, rows, rom)
        require(row['instrs'] == count and sha256(rom[start-BASE:end-BASE]).hexdigest() == digest,
                f'equipment dependency changed at {start:08X}')
    names = match.parse_data_symbols(objects)
    for name, target in (('g_table_0854CD54', SCENES), ('g_table_0851D180', ITEMS),
                         ('g_table_08521A14', 0x08521A14), ('data_0836D4BC', COPY_POINTER)):
        require(names.get(name) == target, f'equipment mapping changed for {name}')
    equipment_access(rom)
    producer(rom)
    local_search(ins)
    ops(rom, 0x0812F6C0, 'adds r0, r6, #0', 'adds r1, r5, #0', 'movs r2, #0xa', 'bl #0x812f5e0')
    ops(rom, 0x0812F6B8, 'adds r0, r6, #0', 'adds r1, r5, #0', 'movs r2, #0xc', 'b #0x812f6c6')
    ops(rom, 0x0812FF64, 'mov r0, r8', 'mov r1, sb', 'movs r2, #0xa', 'bl #0x812f5e0')
    return dict(schema=named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'], runtime_calls=[],
                partition=graph.partition(data, address, refinement, ins, words),
                cases=cursor_cases(), scene_equipment=scene_rows(rom),
                equipment_copy=installed_copy(rom, mapping, index),
                caller_sites=[0x0812F6C6, 0x0812FF6A], local=[-28, -24], saved=[-24, 0],
                output_chain=[WRAPPER, SORT, COLLECT], clears=[0, 2], swap_offsets=[0, 2],
                result='Attribute 10 excludes selected items and begins with the supplied item or unit default. '
                       'Other attributes include every nonempty slot. The entry status bit short-circuits to zero.',
                conditions=[
                    'At entry the five equipped halfwords in the live unit are stable. At most two nonzero '
                    'items have field 6 equal to 1 or 2 and field 3 different from 20. This bounds both '
                    'the collector and the caller even when its requested attribute is different from 10.',
                    'The scene rows certify their original initial equipment values. At use the actual '
                    'loadout must satisfy the same predicate after any edits, on either caller route.',
                    'The unit, item and default rows and accessed state bytes must be live, readable, '
                    'aligned and separate from the active stack. The returning original helpers preserve '
                    'their saved registers and stack words. Only the described producer and sorter access '
                    'the two local halfwords through their output argument. No concurrent equipment changes.'],
                environment=environment_fingerprint())
