"""Original battle evaluator, signed score, and its two-entry equipment output."""
from hashlib import sha256

import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require

OWNER, END = 0x080BDECC, 0x080BDF9A
GUARD, ADJUSTMENT, EFFECT = 0x080C48A4, 0x0812E0BC, 0x08130200
CALLS = {32: GUARD, 58: ADJUSTMENT, 72: equipment.WRAPPER, 136: EFFECT}
SOURCE_HASH = '1f5a55e2fb01504f3c0e5d729a9e7778aa579db30887974d3f45e702cb9afc49'
PINS = {
    OWNER: (END, 'a36abbea39f142a7ebc3b82987a4485b9f47061b36a4c443952fa420dcb28003'),
    0x080BE494: (0x080BE5F4, 'fd49f67f9c07c0d48996bdeae5ea3974e8e38897832564ca2e765dff3224c60b'),
    0x080BE5F4: (0x080BE7AC, 'efd75135d917c88c3cf828b0716d0a4c8462bd1f244773666f7163cc11cc8904'),
    GUARD: (0x080C4964, '5c3035b68698c1524db4cfd5aa92365269c9880346ff7fbaf769ba2fdb4652e2'),
    ADJUSTMENT: (0x0812E0FA, '7c4b89fcf7f2c1ffb74de066b8ba424fb5aa6488933a67fc2fdcb8eae6ff602c'),
    EFFECT: (0x081302F8, '95351f7b520aeac1151de498d02bb743a145b2e53f1861a0c9c73602fed8281b'),
}


def local_accesses(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb',
          'mov r5, r8', 'push {r5, r6, r7}', 'sub sp, #0xc', 'adds r7, r0, #0',
          'mov sb, r1', 'lsls r2, r2, #0x10', 'lsrs r6, r2, #0x10',
          'lsls r3, r3, #0x10', 'lsrs r4, r3, #0x10', 'movs r5, #0')
    block(ins, 0x080BDEE6, 'ldr r0, [r7]', 'ldr r1, [r1]', 'adds r2, r6, #0', 'bl #0x80c48a4',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'bne #0x80bdefa', 'movs r0, #0', 'b #0x80bdf8a')
    block(ins, 0x080BDEFA, 'ldr r0, [r7]', 'mov r2, sb', 'ldr r1, [r2]', 'str r4, [sp]',
          'adds r2, r6, #0', 'movs r3, #1', 'bl #0x812e0bc', 'lsls r0, r0, #0x10',
          'lsrs r0, r0, #0x10', 'mov r8, r0', 'ldr r0, [r7]', 'add r1, sp, #8', 'bl #0x812f0d8')
    block(ins, 0x080BDF18, 'lsls r0, r0, #0x10', 'lsrs r1, r0, #0x10', 'cmp r0, #0',
          'bne #0x80bdf26', 'add r0, sp, #8', 'strh r5, [r0]', 'movs r1, #1', 'cmp r6, #0',
          'bne #0x80bdf2c', 'movs r1, #1', 'movs r2, #0', 'lsls r0, r1, #0x10',
          'asrs r1, r0, #0x10', 'mov sl, r0', 'cmp r5, r1', 'bge #0x80bdf6c')
    block(ins, 0x080BDF38, 'ldr r0, [r7]', 'mov r3, sb', 'ldr r1, [r3]', 'lsls r4, r2, #0x10',
          'asrs r4, r4, #0x10', 'lsls r2, r4, #1', 'add r2, sp, r2', 'adds r2, #8',
          'ldrh r3, [r2]', 'movs r2, #0', 'str r2, [sp]', 'movs r2, #2', 'str r2, [sp, #4]',
          'adds r2, r6, #0', 'bl #0x8130200', 'lsls r1, r5, #0x10', 'asrs r1, r1, #0x10',
          'adds r1, r1, r0', 'lsls r1, r1, #0x10', 'lsrs r5, r1, #0x10', 'adds r4, #1',
          'lsls r4, r4, #0x10', 'lsrs r2, r4, #0x10', 'cmp r4, sl', 'blt #0x80bdf38')
    block(ins, 0x080BDF6C, 'lsls r0, r5, #0x10', 'asrs r1, r0, #0x10', 'cmp r1, #0',
          'bge #0x80bdf7e', 'mov r2, r8', 'lsls r0, r2, #0x10', 'rsbs r0, r0, #0',
          'lsrs r0, r0, #0x10', 'mov r8, r0', 'mov r3, r8', 'lsls r0, r3, #0x10',
          'asrs r0, r0, #0x10', 'adds r0, r1, r0', 'lsls r0, r0, #0x10', 'asrs r0, r0, #0x10',
          'add sp, #0xc', 'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4', 'mov sl, r5',
          'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')


def selection_cases():
    cases = []
    for row in equipment.cursor_cases():
        for zero_action in (False, True):
            selected = row['selected']
            count = 1 if not selected or zero_action else selected
            offsets = [8 + 2*i for i in range(count)]
            initialized = {8 + off for off in row['write_offsets']} if selected else {8}
            require(set(offsets) <= initialized and all(8 <= off <= 10 for off in offsets),
                    'battle effect reads outside the produced selection')
            cases.append(dict(mask=row['mask'], selected=selected, zero_action=zero_action,
                              fallback=not selected, read_offsets=offsets))
    return cases


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    from software_float_profile import ROM_SHA256
    require(sha256(rom).hexdigest() == ROM_SHA256 and len(ins) == 99 and not words and
            data == rom[OWNER-equipment.BASE:END-equipment.BASE] and original == equipment.bindings(CALLS)
            and calls == {OWNER+s: t for s, t in CALLS.items()}, 'battle evaluator body or four calls differ')
    entries, rows = equipment.indices(mapping, index)
    shared = (equipment.WRAPPER, equipment.SORT, equipment.COLLECT, equipment.SLOT, equipment.ITEM,
              equipment.FLAG, equipment.DEFAULT, 0x081256D4, 0x080C9644, 0x080CA268, 0x08142250)
    spans = dict(PINS)
    for address in shared:
        end, _, digest = equipment.PINS[address]
        spans[address] = (end, digest)
    for address, (end, digest) in spans.items():
        row = equipment.span_record(address, end, entries, rows, rom)
        require(sha256(rom[address-equipment.BASE:end-equipment.BASE]).hexdigest() == digest and
                (address != OWNER or row['instrs'] == 99), 'battle evaluator dependency differs')
    equipment.equipment_access(rom)
    equipment.producer(rom)
    local_accesses(ins)
    # The guard collects on its own frame before inspecting the first halfword.
    equipment.ops(rom, GUARD, 'push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #4',
                  'adds r5, r0, #0', 'adds r7, r1, #0', 'lsls r2, r2, #0x10', 'lsrs r4, r2, #0x10',
                  'mov r1, sp', 'bl #0x812f0d8', 'lsls r0, r0, #0x10', 'asrs r1, r0, #0x10',
                  'cmp r1, #0', 'bne #0x80c48c6', 'mov r0, sp', 'strh r1, [r0]', 'mov r0, sp',
                  'ldrh r0, [r0]', 'mov r8, r0')
    for site in (0x080BE566, 0x080BE73C):
        equipment.ops(rom, site, 'bl #0x80bdecc', 'lsls r0, r0, #0x10')
    names = equipment.match.parse_data_symbols(objects)
    require(names.get('g_table_0851D180') == equipment.ITEMS and names.get('g_table_0854CD54') == equipment.SCENES
            and names.get('data_0836D4BC') == equipment.COPY_POINTER, 'battle equipment data roles differ')
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=99, calls=original['calls'], runtime_calls=[],
                partition=equipment.graph.partition(data, OWNER, refinement, ins, words),
                outgoing=[-44,-36], local=[-36,-32], saved=[-32,0], guard_local=[-72,-68],
                collection=[equipment.WRAPPER, equipment.SORT, equipment.COLLECT],
                caller_sites=[0x080BE566, 0x080BE73C], cases=selection_cases(),
                scene_equipment=equipment.scene_rows(rom), equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='A failed eligibility check returns zero. Otherwise an empty collection supplies item zero. '
                       'Action zero uses only the first item. Each signed halfword subtotal is narrowed after the '
                       'original effect call; a negative subtotal reverses the signed adjustment.',
                conditions=['Every equipment query on this path sees a stable five-slot loadout with at most two '
                            'nonzero items whose field 6 is 1 or 2 and field 3 differs from 20. This applies to '
                            'the guard and to any further equipment queries made on either unit by battle helpers.',
                            'The 42 scene definitions certify initial equipment only. Both AI callers require the '
                            'predicate on live actors after any equipment changes.',
                            'Live actors, wrappers, action and battle state are valid and separate from the active '
                            'stack. Original returning helpers preserve their ABI, do not retain the array or '
                            'modify the active frame except for the two collector output halfwords. The signed '
                            '32-bit addition of an effect to its signed halfword subtotal is representable.'],
                environment=equipment.environment_fingerprint())
