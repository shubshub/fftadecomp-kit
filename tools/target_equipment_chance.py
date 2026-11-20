"""Target-equipment gate for action handler 18 at 081311DC."""
from hashlib import sha256
import struct

import battle_action_value as battle
import battle_eligibility
import positioned_equipment_chance as chance
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from software_float_profile import ROM_SHA256

OWNER, END = 0x081311DC, 0x08131204
QUERY, EVALUATE, ADJUST = 0x0812F0CC, 0x08131160, 0x0812F054
DISPATCH, SITE, THUNK = 0x08131378, 0x08131448, 0x08142248
TABLE, STATE, SLOT = 0x083A8678, 0x0200F3F0, 18
CALLS = {10: QUERY, 20: EVALUATE}
SOURCE_HASH = '39ff52e3257e9cc8b59c40bf15a5d25d9a0cbce98bbf7b9cd3c99cb93703f683'
PINS = {
    OWNER: (END, '24fac1bf76c8adceaa61d99c60e021fe4544ee77c4d4d9c2187caa585f318d97'),
    QUERY: (0x0812F0D6, '234924c6f989586162c545f7666af5acdded38cfb4894fd0929beb8edfa01cd1'),
    EVALUATE: (0x08131174, '8f09d6eb91f1181824ccd228806c226445257db34f227918c7f44d2574c516fd'),
    ADJUST: (0x0812F068, '2102755fc329323ff2110ee508171ccfc47c34c584b9907417cb799c2b881895'),
    DISPATCH: battle_eligibility.PINS[DISPATCH],
    THUNK: (THUNK + 2, 'bac8ca6ee9f77b46c7ab5824c7c59d99fd0ca53ae998ea2872b78bb6a5189cc5'),
    **chance.PINS,
}


def callback_route(rom):
    entry = TABLE + 4 * SLOT
    require(chance.direct_sites(rom, OWNER) == [], 'unexpected direct call to equipment gate')
    for value, address in ((OWNER | 1, entry), (TABLE, 0x0813146C)):
        word = struct.pack('<I', value)
        require(rom.find(word) == rom.rfind(word) == address - equipment.BASE,
                'equipment callback table reference differs')
    require(equipment.word(rom, 0x08131470) == STATE,
            'equipment callback state literal differs')
    equipment.ops(rom, 0x0813143A, 'ldr r2, [pc, #0x30]', 'ldr r0, [pc, #0x30]',
                  'ldr r1, [r0, #0x30]', 'ldrb r1, [r1, #2]', 'lsls r1, r1, #2',
                  'adds r1, r1, r2', 'ldr r1, [r1]', 'bl #0x8142248',
                  'lsls r0, r0, #0x18', 'lsrs r4, r0, #0x18')
    equipment.ops(rom, THUNK, 'bx r1')
    return dict(owner=DISPATCH, call=SITE, thunk=THUNK, table=TABLE, slot=SLOT,
                pointer_word=entry, context=STATE)


def frame(ins):
    block(ins, OWNER, 'push {r4, lr}', 'sub sp, #4', 'adds r4, r0, #0',
          'ldr r0, [r4, #4]', 'mov r1, sp', 'bl #0x812f0cc', 'cmp r0, #0',
          'beq #0x81311fa', 'adds r0, r4, #0', 'bl #0x8131160',
          'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'b #0x81311fc',
          'movs r0, #0', 'add sp, #4', 'pop {r4}', 'pop {r1}', 'bx r1')


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-equipment.BASE:END-equipment.BASE]
            and len(ins) == 18 and not words and original == equipment.bindings(CALLS)
            and calls == {OWNER + site: target for site, target in CALLS.items()},
            'target equipment owner, frame or calls differ')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, len(ins))
    names = equipment.match.parse_data_symbols(objects)
    require(names.get('data_083A8678') == TABLE and names.get('data_0200F3F0') == STATE,
            'target equipment callback data mappings differ')
    route = callback_route(rom)
    frame(ins)
    equipment.ops(rom, QUERY, 'push {lr}', 'bl #0x812e4f4', 'pop {r1}', 'bx r1')
    equipment.ops(rom, EVALUATE, 'push {lr}', 'ldr r2, [r0]', 'ldr r1, [r0, #4]',
                  'adds r0, r2, #0', 'bl #0x812f054', 'lsls r0, r0, #0x18',
                  'lsrs r0, r0, #0x18', 'pop {r1}', 'bx r1')
    equipment.ops(rom, ADJUST, 'push {lr}', 'movs r2, #2', 'movs r3, #0', 'bl #0x812c8dc',
                  'cmp r0, #0x63', 'bgt #0x812f064', 'asrs r0, r0, #1', 'pop {r1}', 'bx r1')
    cases = [dict(mask=c['mask'], count=c['selected'], append_offsets=c['write_offsets'],
                  evaluate=bool(c['selected'])) for c in equipment.cursor_cases()]
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'],
                runtime_calls=[], partition=equipment.graph.partition(data, OWNER, refinement, ins, words),
                callback=route, local=[-12, -8], saved=[-8, 0], collection=[QUERY, equipment.COLLECT],
                clear_offsets=[0, 2], cases=cases, scene_equipment=equipment.scene_rows(rom),
                equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='No qualifying target equipment returns zero. Otherwise the same context enters '
                       'the chance evaluator. Its signed value below 100 is arithmetically halved, and the '
                       'low byte is returned.',
                conditions=['The live target has five stable readable equipment slots and at most two '
                            'nonzero items with field 6 in {1, 2} and field 3 different from 20. On the '
                            'evaluation branch the source meets the existing positioned-chance equipment '
                            'and battle-state preconditions too. The 42 initial scene loadouts establish '
                            'examples only. The dispatch does not enforce the live bound after equipment changes.',
                            'The context, units, battle state and item rows are live and separate from the '
                            'active stack. The collector retains no output pointer. Returning callees preserve '
                            'SP and callee-saved registers.'], environment=equipment.environment_fingerprint())
