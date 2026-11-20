"""The first selected equipment entry and six outgoing arguments of 0812C8DC."""
from hashlib import sha256
import re
import struct

import battle_action_value as battle
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from software_float_profile import ROM_SHA256

OWNER, END = 0x0812C8DC, 0x0812C95E
CHANCE, STATUS = 0x0812C7F4, 0x080CDA64
CALLS = {14: equipment.WRAPPER, 96: CHANCE, 108: STATUS}
SOURCE_HASH = '0e701291f2614910e97c5fc7c986eaa1d7f51d874b7ed4f593cfc87bbbd9a019'
HEADER_PATH = 'include/positioned_equipment.h'
HEADER_HASH = '7ea45d942b44ad8831e6ecedee93fd32b3c9114f4b3f3c60bb0e644a4396da13'
PINS = {
    OWNER: (END, 'b1e69ac73381541c3a3fd54138ae74406a43dc091d0dd24f5f0ce6c05f6728ca'),
    CHANCE: (OWNER, 'bb2454bbeccd62042b1108cf0d8fc49bdc5c65ad31e8939b144eae75891a702b'),
    STATUS: (0x080CDA7C, '09401897cec7e931ef8d19d7a1e020b3f99399c035ff21c0ea63d66050c2e478'),
}

# Each site is an incoming direct Thumb BL. The dispatcher contains three.
CALLERS = {
    0x0812D388: (0x0812D396, (0x0812D38E,)),
    0x0812D5F4: (0x0812D65E, (0x0812D626,)),
    0x0812D7FC: (0x0812D99C, (0x0812D988,)),
    0x0812DA0C: (0x0812DAB6, (0x0812DAA4,)),
    0x0812DAB8: (0x0812DAEA, (0x0812DAE0,)),
    0x0812DBA8: (0x0812E0BC, (0x0812DF34, 0x0812DF42, 0x0812DF68)),
    0x0812E0BC: (0x0812E0FA, (0x0812E0D0,)),
    0x0812F054: (0x0812F068, (0x0812F05A,)),
    0x0812F068: (0x0812F07E, (0x0812F06E,)),
    0x0812F080: (0x0812F090, (0x0812F088,)),
}

# Lookahead retains overlapping candidates. ARMv4T BL uses two consecutive halfwords.
THUMB_BL = re.compile(rb'(?=(.[\xf0-\xf7].[\xf8-\xff]))', re.DOTALL)


def direct_sites(rom):
    found = []
    first = max(0, OWNER-equipment.BASE-0x400002)
    last = min(len(rom), OWNER-equipment.BASE+0x400000)
    for pair in THUMB_BL.finditer(rom, first, last):
        offset = pair.start()
        if offset & 1:
            continue
        high, low = struct.unpack_from('<HH', rom, offset)
        displacement = ((high & 0x3ff) << 12) + ((low & 0x7ff) << 1)
        if high & 0x400:
            displacement -= 0x400000
        if equipment.BASE + offset + 4 + displacement == OWNER:
            found.append(equipment.BASE + offset)
    return found


def dispatch_routes(rom):
    # The ordinary CFG inventory stops at the first mov pc. Check both guarded
    # word tables and the three actual evaluation routes instead.
    equipment.ops(rom, 0x0812DC9A, 'ldrb r0, [r5, #1]', 'subs r0, #7', 'cmp r0, #0x55',
                  'bls #0x812dca4', 'b #0x812de4e', 'lsls r0, r0, #2', 'ldr r1, [pc, #0xc]',
                  'adds r0, r0, r1', 'ldr r0, [r0]', 'mov pc, r0')
    require(equipment.word(rom, 0x0812DCB4) == 0x0812DCB8 and
            equipment.word(rom, 0x0812DCBC) == 0x0812DE4E, 'first chance dispatcher table differs')
    equipment.ops(rom, 0x0812DE4E, 'bl #0x8131474', 'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18',
                  'subs r0, #1', 'cmp r0, #0x1e', 'bls #0x812de5e', 'b #0x812e0a6',
                  'lsls r0, r0, #2', 'ldr r1, [pc, #4]', 'adds r0, r0, r1', 'ldr r0, [r0]', 'mov pc, r0')
    table = equipment.word(rom, 0x0812DE68)
    require(table == 0x0812DE6C, 'second chance dispatcher table differs')
    for case, entry in ((10, 0x0812DF2C), (11, 0x0812DF3A), (18, 0x0812DF52)):
        require(equipment.word(rom, table+4*(case-1)) == entry, 'chance dispatch route differs')
    equipment.ops(rom, 0x0812DF52, 'add r1, sp, #0x14', 'adds r0, r4, #0', 'bl #0x812f0cc',
                  'cmp r0, #0', 'bne #0x812df60', 'b #0x812e0ae')
    for entry in (0x0812DF2C, 0x0812DF3A, 0x0812DF60):
        equipment.ops(rom, entry, 'adds r0, r6, #0', 'adds r1, r4, #0', 'movs r2, #2',
                      'movs r3, #0', 'bl #0x812c8dc')


def caller_inventory(rom, mapping, index):
    from owner_admission_profile import refine
    sites = direct_sites(rom)
    require(sites == [pc for _, pcs in CALLERS.values() for pc in pcs], 'chance incoming BL inventory differs')
    entries, rows = equipment.indices(mapping, index)
    owners = []
    for start, (end, expected) in CALLERS.items():
        equipment.span_record(start, end, entries, rows, rom)
        if start == 0x0812DBA8:
            dispatch_routes(rom)
        else:
            data = rom[start-equipment.BASE:end-equipment.BASE]
            refined = refine(data, start, mapping)
            _, _, _, calls, _ = equipment.graph.graph(data, start, refined)
            require(sorted(pc for pc, target in calls.items() if target == OWNER) == list(expected),
                    'chance caller CFG differs')
        for site in expected:
            if site == 0x0812F088:
                equipment.ops(rom, site-6, 'lsls r2, r2, #0x18', 'lsrs r2, r2, #0x18',
                              'movs r3, #0', 'bl #0x812c8dc')
            elif site == 0x0812E0D0:
                equipment.ops(rom, site-12, 'lsls r3, r3, #0x18', 'lsrs r3, r3, #0x18', 'cmp r2, #0',
                              'bne #0x812e0d6', 'adds r2, r3, #0', 'movs r3, #0', 'bl #0x812c8dc')
            else:
                equipment.ops(rom, site-4, 'movs r2, #2', 'movs r3, #0', 'bl #0x812c8dc')
        owners.append(dict(owner=start, sites=list(expected)))
    return sites, owners


def frame_accesses(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x1c', 'adds r5, r0, #0',
          'adds r6, r1, #0', 'lsls r4, r2, #0x18', 'lsrs r4, r4, #0x18',
          'add r1, sp, #0x18', 'bl #0x812f0d8', 'add r0, sp, #0x18', 'ldrh r7, [r0]',
          'movs r2, #0', 'cmp r4, #1', 'bne #0x812c8fa', 'movs r2, #1', 'movs r1, #1')
    block(ins, 0x0812C8FC, 'adds r0, r5, #0', 'adds r0, #0xf6', 'movs r3, #0',
          'ldrsb r3, [r0, r3]', 'adds r0, #1', 'ldrb r0, [r0]',
          'lsls r0, r0, #0x18', 'asrs r0, r0, #0x18', 'str r0, [sp]')
    for start, field, offset in ((0x0812C90E, 0xF6, '4'), (0x0812C91A, 0xF7, '8'),
                                 (0x0812C926, 0xF8, '0xc')):
        block(ins, start, 'adds r0, r6, #0', f'adds r0, #{field:#x}', 'ldrb r0, [r0]',
              'lsls r0, r0, #0x18', 'asrs r0, r0, #0x18',
              f'str r0, [sp, #{offset}]')
    block(ins, 0x0812C932, 'str r2, [sp, #0x10]', 'str r1, [sp, #0x14]',
          'adds r0, r5, #0', 'adds r1, r6, #0', 'adds r2, r7, #0', 'bl #0x812c7f4',
          'adds r4, r0, #0', 'cmp r4, #0', 'beq #0x812c954', 'adds r0, r6, #0',
          'bl #0x80cda64', 'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x812c954',
          'movs r4, #0x64', 'adds r0, r4, #0', 'add sp, #0x1c',
          'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')


def selection_accesses(mask):
    """Frame-relative addresses for the appended entries of a stable five-slot loadout."""
    require(type(mask) is int and 0 <= mask < 32, 'invalid five-slot mask')
    writes = [24 + 2*i for i in range(mask.bit_count())]
    require(all(offset + 2 <= 28 for offset in writes), 'selection crosses the saved registers')
    return dict(mask=mask, append_offsets=writes)


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and
            data == rom[OWNER-equipment.BASE:END-equipment.BASE] and len(ins) == 62 and not words
            and original == equipment.bindings(CALLS)
            and calls == {OWNER+offset: target for offset, target in CALLS.items()},
            'positioned chance body, literal partition or direct calls differ')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, len(ins))
    frame_accesses(ins)
    sites, owners = caller_inventory(rom, mapping, index)
    cases = [selection_accesses(row['mask']) for row in equipment.cursor_cases()]
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins),
                partition=equipment.graph.partition(data, OWNER, refinement, ins, words),
                calls=original['calls'], runtime_calls=[], caller_sites=sites, direct_callers=owners,
                outgoing=[-48, -24], local=[-24, -20], saved=[-20, 0],
                collection=[equipment.WRAPPER, equipment.SORT, equipment.COLLECT],
                frame_clear_offsets=[24, 26], frame_sort_offsets=[24, 26], frame_read_offset=24,
                cases=cases, scene_equipment=equipment.scene_rows(rom),
                equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='The first halfword, initialized even when no items qualify, is passed with the signed '
                       'coordinates and target direction. A low mode byte of 1 enables the position check; option is 1. '
                       'A nonzero evaluator result becomes 100 when target flag bit 1 at +0xEA is set.',
                conditions=['The live source has five stable and readable equipment slots. At most two nonzero '
                            'items have field 6 equal to 1 or 2 and field 3 different from 20. Original scene '
                            'equipment establishes initial values only; the live loadout must still satisfy '
                            'this condition after equipment changes. The 12 incoming BL sites in ten indexed '
                            'owners establish the direct call inventory. None establishes this live equipment '
                            'invariant for all arriving units. The 42 reviewed original scene rows in five groups '
                            'demonstrate initial values only. Indirect or transitive calls and later equipment '
                            'changes have no whole-game coverage here.',
                            'The unit pointers, coordinates, direction, item records and battle state satisfy '
                            'the original helper contracts and are separate from the active stack. Helpers '
                            'return with saved registers and SP preserved. The equipment producer retains no '
                            'output pointer and touches only its two halfwords in the active caller frame.'],
                environment=equipment.environment_fingerprint())
