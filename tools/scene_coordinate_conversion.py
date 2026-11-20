"""The two nullable signed-halfword outputs of the original scene coordinate converter."""
from hashlib import sha256

import owner_graph_profile as graph
from ability_range_local_bytes import block
from software_double_profile import indices, span_record
from unit_equipment_attribute import BASE, SLOT, PINS as EQUIPMENT_PINS

CONVERT, OBJECT_KIND = 0x080DC224, 0x080DD6E0
PINS = {
    CONVERT: (0x080DC268, 33, '5e33c9454882631b53cff55db8489155b472b3b275037c26da77156317dbfac2'),
    OBJECT_KIND: (0x080DD6F2, 8, '81144f51e4613bd3a499ac770bc38494f29ee820cddd7ed54bc110ab024b7dba'),
    SLOT: EQUIPMENT_PINS[SLOT],
}


def require(condition, reason):
    if not condition:
        raise ValueError('scene coordinates: ' + reason)


def verify(rom, mapping, index):
    from owner_admission_profile import refine
    entries, rows = indices(mapping, index)
    graphs = {}
    for address, (end, count, digest) in PINS.items():
        body = rom[address-BASE:end-BASE]
        row = span_record(address, end, entries, rows, rom)
        result = refine(body, address, mapping)
        ins, edges, long_jumps, calls, words = graph.graph(body, address, result)
        graph.partition(body, address, result, ins, words)
        require(row['instrs'] == len(ins) == count and not long_jumps and sha256(body).hexdigest() == digest,
                f'complete span or reachable graph differs at {address:08X}')
        graphs[address] = ins, edges, calls, words
    ins, _, calls, words = graphs[CONVERT]
    require(not words and calls == {0x080DC250: OBJECT_KIND}, 'conversion provider edge differs')
    block(ins, CONVERT, 'push {r4, r5, lr}', 'adds r5, r0, #0', 'ldr r4, [sp, #0xc]',
          'lsls r1, r1, #0x10', 'lsrs r0, r1, #0x10', 'lsls r2, r2, #0x10', 'lsrs r2, r2, #0x10',
          'cmp r3, #0', 'beq #0x80dc240', 'movs r1, #0x10', 'lsls r0, r0, #0x10', 'asrs r0, r0, #0x10',
          'subs r1, r1, r0', 'strh r1, [r3]', 'cmp r4, #0', 'beq #0x80dc262', 'movs r0, #0x30',
          'lsls r1, r2, #0x10', 'asrs r1, r1, #0x10', 'subs r0, r0, r1', 'strh r0, [r4]', 'adds r0, r5, #0',
          'bl #0x80dd6e0', 'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'cmp r0, #0x51', 'bne #0x80dc262',
          'ldrh r0, [r4]', 'subs r0, #4', 'strh r0, [r4]', 'pop {r4, r5}', 'pop {r0}', 'bx r0')
    ins, _, calls, words = graphs[OBJECT_KIND]
    require(not words and calls == {0x080DD6E6: SLOT}, 'object lookup edge differs')
    block(ins, OBJECT_KIND, 'push {lr}', 'ldr r0, [r0]', 'movs r1, #1', 'bl #0x80c7ea4',
          'lsls r0, r0, #0x10', 'lsrs r0, r0, #0x10', 'pop {r1}', 'bx r1')
    ins, edges, calls, words = graphs[SLOT]
    block(ins, SLOT, 'push {lr}', 'adds r2, r0, #0', 'lsls r1, r1, #0x18', 'lsrs r0, r1, #0x18',
          'cmp r0, #0x44', 'bls #0x80c7eb2', 'b #0x80c8176', 'lsls r0, r0, #2',
          'ldr r1, [pc, #4]', 'adds r0, r0, r1', 'ldr r0, [r0]', 'mov pc, r0')
    require(words[24] == 28 and len(words) == 70 and words[32] == 0x080C7FD8-SLOT and
            0x080C7FD8 in edges[0x080C7EBA], 'constant selector 1 must load the second native table entry')
    block(ins, 0x080C7FD8, 'ldrb r0, [r2, #4]', 'b #0x80c8178')
    block(ins, 0x080C8178, 'pop {r1}', 'bx r1')
    return dict(converter=CONVERT, converter_frame_bytes=12, inputs=['object', 's16 x', 's16 y'],
                writable_outputs=[['r3', 2], ['entry_sp+0', 2]], x_store=0x080DC23E, y_store=0x080DC24C,
                null_x_skips_to=0x080DC240, null_y_skips_to=0x080DC262, kind_lookup=OBJECT_KIND,
                coordinate_query=[SLOT, 1, 0x080C7FD8, 4], corrected_kind=0x51, correction_store=0x080DC260,
                x_value='(16 - x) mod 65536', y_value='(48 - y - (kind == 81 ? 4 : 0)) mod 65536',
                pins=[[a, end, count, digest] for a, (end, count, digest) in PINS.items()])
