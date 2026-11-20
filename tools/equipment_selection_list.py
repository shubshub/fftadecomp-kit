"""Equipment selection and the bounded list of entry evaluators in 0813569C."""
from hashlib import sha256

import battle_action_value as battle
import positioned_equipment_chance as chance
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from owner_admission_profile import refine
from software_float_profile import ROM_SHA256

OWNER, END, CALLER, SITE = 0x0813569C, 0x08135750, 0x080C2618, 0x080C26CA
EFFECT, EVALUATE = battle.EFFECT, 0x081343C8
STATE, TABLE = 0x02000000, 0x08528F34
STATE_NAME, TABLE_NAME = 'g_state_02000000', 'g_table_08528F34'
OBJECTS = {STATE_NAME: STATE, TABLE_NAME: TABLE}
DATA = [[0x88, STATE_NAME, 0], [0x94, TABLE_NAME, 0]]
CALLS = {0x1C: equipment.WRAPPER, 0x4C: EFFECT, 0x76: EVALUATE}
SOURCE_HASH = '226b8f8b0f305b64aceff369b88874f425799c92fdd3d270af8f3be1d74701b9'
PINS = {
    OWNER: (END, 'b740e12d8aa8daab183d276bace4e0f76113a1039ac32af4cbca852498b3152e'),
    CALLER: (0x080C26EC, '9a55aa637bf488c236704c8da9c43b38dd1e9aab56d80706fbd70d6b7f242a46'),
    EFFECT: battle.PINS[EFFECT],
    EVALUATE: (0x08134A0E, '57fe221ccbbaea2eaaa1baa6e3266242bcc731786d7a81560332157eef8f2605'),
}


def caller_sites(rom, mapping):
    sites = chance.direct_sites(rom, OWNER)
    require(sites == [SITE], 'selection caller inventory differs')
    data = rom[CALLER-equipment.BASE:PINS[CALLER][0]-equipment.BASE]
    _, _, _, calls, _ = equipment.graph.graph(data, CALLER, refine(data, CALLER, mapping))
    require([pc for pc, target in calls.items() if target == OWNER] == sites,
            'selection caller control flow differs')
    equipment.ops(rom, SITE-10, 'ldr r0, [r6]', 'mov r2, sb', 'ldr r1, [r2]', 'mov r2, r8',
                  'movs r3, #0', 'bl #0x813569c', 'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x80c26dc')
    return sites


def owner_frame(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #0x14', 'adds r5, r0, #0', 'mov r8, r1',
          'lsls r2, r2, #0x10', 'lsrs r7, r2, #0x10', 'lsls r3, r3, #0x18', 'lsrs r3, r3, #0x18',
          'mov sb, r3', 'add r1, sp, #0x10', 'bl #0x812f0d8', 'adds r1, r0, #0', 'cmp r1, #0',
          'bne #0x81356c6', 'add r0, sp, #0x10', 'strh r1, [r0]')
    block(ins, 0x081356C6, 'movs r4, #0', 'ldr r1, [pc, #0x58]', 'ldr r2, [pc, #0x5c]',
          'adds r0, r1, r2', 'ldrb r3, [r0]', 'cmp r4, r3', 'bge #0x813573e',
          'movs r6, #0', 'mov sl, r0', 'add r0, sp, #0x10', 'ldrh r3, [r0]',
          'str r6, [sp]', 'movs r0, #2', 'str r0, [sp, #4]', 'adds r0, r5, #0',
          'mov r1, r8', 'adds r2, r7, #0', 'bl #0x8130200')
    block(ins, 0x081356EC, 'lsls r0, r0, #0x10', 'asrs r0, r0, #0x10', 'str r6, [sp]',
          'str r0, [sp, #4]', 'str r6, [sp, #8]', 'lsls r0, r4, #1', 'ldr r2, [pc, #0x28]',
          'ldr r3, [pc, #0x30]', 'adds r1, r2, r3', 'adds r0, r0, r1', 'ldrh r0, [r0]',
          'lsls r0, r0, #4', 'ldr r1, [pc, #0x28]', 'adds r0, r0, r1', 'str r0, [sp, #0xc]',
          'adds r0, r5, #0', 'mov r1, r8', 'adds r2, r7, #0', 'mov r3, sb', 'bl #0x81343c8',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x8135734', 'adds r0, r4, #1',
          'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'b #0x8135740')
    block(ins, 0x08135734, 'adds r4, #1', 'mov r0, sl', 'ldrb r0, [r0]', 'cmp r4, r0',
          'blt #0x81356d8', 'movs r0, #0', 'add sp, #0x14', 'pop {r3, r4, r5}',
          'mov r8, r3', 'mov sb, r4', 'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')


def list_partition(data, refinement, ins, words):
    part = equipment.graph.partition(data, OWNER, refinement, ins, words)
    values = [(w['address']-OWNER, w['value'], [s-OWNER for s in w['load_sites']]) for w in part['words']]
    require(part['code_bytes'] == 164 and not part['alignment'] and values == [
        (0x88, STATE, [0x2C, 0x5C]), (0x8C, 0x3C33, [0x2E]),
        (0x90, 0x3C34, [0x5E]), (0x94, TABLE, [0x68])], 'selection literal values or load sites differ')
    return part


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(data == rom[OWNER-equipment.BASE:END-equipment.BASE] and sha256(rom).hexdigest() == ROM_SHA256
            and len(ins) == 79 and not words and original == dict(equipment.bindings(CALLS), data=DATA)
            and calls == {OWNER+off: target for off, target in CALLS.items()},
            'selection complete owner, bindings or calls differ')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, len(ins))
    names = equipment.match.parse_data_symbols(objects)
    require(all(names.get(name) == value for name, value in OBJECTS.items()), 'selection data mappings differ')
    owner_frame(ins)
    cases = equipment.cursor_cases()
    for case in cases:
        require(all(off in (0, 2) for off in case['write_offsets']) and case['selected'] <= 2,
                'equipment output reaches saved registers')
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'],
                runtime_calls=[], partition=list_partition(data, refinement, ins, words),
                caller_sites=caller_sites(rom, mapping), outgoing=[-52, -36], local=[-36, -32], saved=[-32, 0],
                collector_frame_offsets=[16, 18], owner_fallback_offset=16, owner_read_offset=16,
                effect_stack_arguments=[0, 2], evaluator_stack_arguments=[0, 's16(effect)', 0, 'entry'],
                cases=cases, scene_equipment=equipment.scene_rows(rom),
                equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='Each list iteration evaluates the current action with the first sorted item, or zero '
                       'if none qualify. It passes the signed low halfword, low mode byte and indexed 16-byte '
                       'entry to the predicate. The first nonzero predicate returns its one-based index. '
                       'A list that is empty or exhausted returns zero.',
                conditions=['The live source has at most two qualifying entries across five stable equipment '
                            'slots (item field 6 is 1 or 2 and field 3 differs from 20). The direct caller '
                            'sets mode zero but does not enforce this live equipment limit. The 42 original '
                            'initial loadouts do not establish it after runtime equipment changes.',
                            'Each reached list index and corresponding 16-byte table record must be live and '
                            'readable. The units, state and any external accesses by the original callees '
                            'must satisfy their contracts and stay disjoint from the saved frame. The callees '
                            'preserve SP and callee-saved registers. Only the equipment producer takes a '
                            'pointer into the local array, and retains no alias.'],
                environment=equipment.environment_fingerprint())
