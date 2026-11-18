"""Conditional menu indices produced by the original fixed-roster sorter."""
from hashlib import sha256
from pathlib import Path
import struct

import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
import packed_transfer_task
import scheduler_zero_descriptor as boot
import scroll_prefix_scene
import unit_roster_sort as roster
from ability_range_local_bytes import block, require
from history_word_copy import aligned_manager_clear
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

OWNER = 0x0805451C
END = 0x0805459C
SLOT = 0x0200F428
LIST = 0x2D3A
SIZE = 0x2FA0
BANK = 0x080543EC
BODY = 'd86d2a25445a362ca8594bc4110a4e70e3b0babb89efc3d5c646b1fb6c0bc6e3'
DECLARATIONS = '4b5b3177988b46f24733e6db7f700a7882b26c4641c281bc1f8e8ffac52a93f5'
PROVIDERS = ((BANK, OWNER, 'ead6412ce2685fc3d0958edb6eb9bf1118a3d03ab7e0493589f5b376a9a51c4f'),
             (0x08050F1C, 0x08051048, '6674a40f78da94566378babe2ba78dd519607e5414f2da70ebd6f0793e77644c'),
             (0x08055C38, 0x08055DC4, 'b0eb13a6c84efafb7977b57be6e411355914cd1af270ed69f4caba050114d623'),
             (0x08022854, 0x08022868, 'dc40e21202fe3f3244adc6024444db000876a9b76336db4627e6826cb0f5d37b'))
HEAP = {0x080227E8, 0x08022840, 0x080070C8, 0x08006C88, 0x08006D38, 0x08006DA0,
        0x08006E28, 0x08006EC0, 0x08007138, 0x08007170, 0x08006FCC}


def check_source(root, address):
    import plausible
    require(address == OWNER, 'unexpected menu roster filter')
    source = (Path(root) / f'src/{address:08X}.c').read_text()
    header = (Path(root) / 'include/ffta.h').read_bytes()
    require(base_header(header, ('func_0805451C', 'func_08071DC8', 'g_state_02000000', 'data_0200F428'))
            and not any(marker in source for marker in (chr(92), '??', '%:', chr(0))),
            'unexpected source preprocessing or header')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    stop = 'u8 indices [ 24 ] ; u8 i ; u8 count ;'
    declarations, present, body = tokens.partition(stop)
    require(present and '#' not in body and sha256((declarations + stop).encode()).hexdigest() == DECLARATIONS,
            'unexpected source roster fields, menu extent or local indices')


def bindings():
    return dict(calls=[[10, 'func_08071DC8']], data=[[112, 'g_state_02000000', 0x20D0],
                [120, 'data_0200F428', 0]], functions=[], switches=[])


def producer(rom, mapping, index, objects):
    """Reapply the original machine proof to the called producer and both partitions."""
    import owner_admission_profile as admission

    data = roster.extent(rom, mapping, index, roster.OWNER)
    refinement = admission.refine(data, roster.OWNER, mapping)
    ins, _, _, calls, words = graph.graph(data, roster.OWNER, refinement)
    return roster.prove(data, roster.OWNER, rom, mapping, index, objects, roster.bindings(),
                        ins, calls, refinement, words)


def index_domain():
    # The six sorted cases carry the enabled physical slot in the value word.
    # Forward default emits the same slot; reverse default uses a subtraction.
    # Cover every feasible (enabled count, enabled physical slot) pair.
    for count in range(1, roster.COUNT + 1):
        for slot in range(roster.COUNT):
            value = (count - 1 - slot) & 255
            require((value < roster.COUNT or value == 255) == (slot <= count),
                    'reverse-default index domain differs')
    return dict(slots=roster.COUNT, sorted='one or more enabled entries; all emitted indices in 0..23',
                forward_default='the enabled indices, including an empty list',
                reverse_default='every enabled physical slot i <= count. Slot i == count emits 0xff '
                                'and is skipped. A dense prefix preserves a complete reverse enumeration.',
                reverse_default_witness=dict(count=2, enabled=[0, 4], output=[1, 253]))


def lifetime(rom, mapping, index):
    entries, rows = indices(mapping, index)
    heap = {row[0]: row for row in (*scroll_prefix_scene.PROVIDER, *packed_transfer_task.PROVIDERS)
            if row[0] in HEAP}
    require(heap.keys() == HEAP, 'incomplete root heap inventory')
    for address, end, digest in (*PROVIDERS, *heap.values()):
        span_record(address, end, entries, rows, rom)
        require(sha256(rom[address-match.ROM_BASE:end-match.ROM_BASE]).hexdigest() == digest,
                f'changed scene allocation or consumer at {address:08X}')
    at = lambda address: struct.unpack_from('<I', rom, address-match.ROM_BASE)[0]
    require([at(i) for i in (0x08054464, 0x08054468, 0x0805446C, 0x08054518)] ==
            [SLOT, SIZE, boot.POINTER, SLOT], 'changed scene constructor or release')
    require((at(0x08050F94), at(0x08050F98)) == (SLOT, 0x1D7C) and 0x1D7C < LIST,
            'changed smaller scene sharing the same pointer')
    require(at(0x08055CBC) == LIST + roster.COUNT < SIZE, 'menu count is not adjacent to the list')
    boot.initializer(rom, mapping, index)
    clear = rom[boot.IMAGE-match.ROM_BASE:boot.IMAGE-match.ROM_BASE+176]
    # This proof is relative to any aligned EWRAM allocation of this size.
    _, _, clear_words = aligned_manager_clear(clear, 0x02000000, SIZE)
    return dict(pointer=SLOT, constructor=BANK, allocation_call=0x08054412, size=SIZE,
                installed_clear=boot.DESTINATION, clear_words=clear_words, list=[LIST, LIST+roster.COUNT],
                count=LIST+roster.COUNT, release=0x080544F8, other_scene_size=0x1D7C,
                premise='An aligned, successful live allocation from this menu occupies the shared pointer '
                        'when an entry is appended. Release, the other menu and concurrent mutation are excluded.')


def prove(data, address, rom, mapping, index, objects, original, ins, calls, refinement, words):
    entries, rows = indices(mapping, index)
    row = span_record(address, END, entries, rows, rom)
    require(address == OWNER and sha256(data).hexdigest() == BODY and row['instrs'] == len(ins) == 54
            and not words and original == bindings() and calls == {OWNER+10: roster.OWNER},
            'changed menu roster filter or original ELF bindings')
    names = match.parse_data_symbols(objects)
    require(names.get('g_state_02000000') == roster.BASE and names.get('data_0200F428') == SLOT
            and list(struct.unpack_from('<4I',data,112)) == [roster.BASE+0x20D0, (-0x20D0)&0xffffffff, SLOT, LIST],
            'changed roster base, selection addend or scene list address')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x18', 'ldr r4, [pc, #0x68]',
          'ldrb r0, [r4, #0x14]', 'mov r1, sp', 'bl #0x8071dc8', 'movs r5, #0', 'movs r6, #0')
    block(ins, OWNER+0x16, 'mov r7, sp', 'adds r1, r7, r5', 'ldrb r0, [r1]', 'cmp r0, #0xff',
          'beq #0x8054576', 'adds r3, r0, #0', 'lsls r0, r3, #5', 'adds r0, r0, r3', 'lsls r0, r0, #3')
    block(ins, OWNER+0x28, 'adds r2, r0, r4', 'adds r0, r2, #0', 'adds r0, #0x84', 'ldrb r1, [r0]',
          'cmp r1, #0', 'beq #0x8054576', 'movs r7, #0xb8', 'lsls r7, r7, #1', 'adds r0, r2, r7',
          'ldrb r0, [r0]', 'cmp r0, #0', 'beq #0x8054576', 'cmp r1, #2', 'beq #0x8054576',
          'cmp r1, #0xf', 'beq #0x8054576')
    block(ins, OWNER+0x48, 'ldr r0, [pc, #0x2c]', 'ldr r0, [r0]', 'ldr r1, [pc, #0x2c]',
          'adds r0, r0, r1', 'adds r0, r0, r6', 'strb r3, [r0]', 'adds r0, r6, #1',
          'lsls r0, r0, #0x18', 'lsrs r6, r0, #0x18', 'adds r0, r5, #1', 'lsls r0, r0, #0x18',
          'lsrs r5, r0, #0x18', 'cmp r5, #0x17', 'bls #0x8054532', 'adds r0, r6, #0',
          'add sp, #0x18', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    return dict(schema=named.ROSTER_FILTER_SCHEMA, instructions=len(ins), calls=original['calls'], runtime_calls=[],
                partition=graph.partition(data,address,refinement,ins,words), producer=producer(rom,mapping,index,objects),
                index_domain=index_domain(), scene=lifetime(rom,mapping,index),
                filter=dict(frame=24, saved=20, relative_to_filter_entry_sp=dict(
                            local_output=[-44, -20], saved=[-20, 0], nested_stack=[-1260, -44]),
                            input='24 bytes at sp; 0xff is skipped',
                            stride=roster.STRIDE, kind_offset=4, excluded_kinds=[0, 2, 15],
                            active_offset=0xf0, accepted='active byte nonzero and kind not excluded',
                            result='Accepted input indices in original order, count 0..24. Before a store, '
                                   'count <= scan slot < 24. Unused menu bytes are not written.',
                            native_caller=0x08055C72, consumer_count_store=0x08055C7E),
                environment=roster.environment_fingerprint())
