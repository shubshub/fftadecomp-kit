"""Action 67 consumes the two selected halfwords while updating live equipment."""
from hashlib import sha256

import battle_action_value as battle
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from software_float_profile import ROM_SHA256
from owner_admission_profile import refine

OWNER, END = 0x081332F8, 0x08133386
WRAPPER, CLEAR, VALIDATE, REFRESH = 0x0812F0CC, 0x080CAF78, 0x080CB54C, 0x080CA2E8
DISPATCH, THUNK = 0x0813388C, 0x08142248
STATE, TABLE, RECORDS, KIND = 0x0200F3F0, 0x083A87B0, 0x08553E70, 67
CALLS = {0x1C: WRAPPER, 0x32: equipment.SLOT, 0x5E: CLEAR, 0x66: VALIDATE, 0x7A: REFRESH}
SOURCE_HASH = 'd3a3cb5917b582af17a1d90644ac9646300e7871dd92336446312ef48bced8d0'
PINS = {
    OWNER: (END, '0998a990995d62ac246763fe70cde2ae40aeda53eba742ceef6182b51eb78f0b'),
    WRAPPER: (0x0812F0D6, '234924c6f989586162c545f7666af5acdded38cfb4894fd0929beb8edfa01cd1'),
    CLEAR: (0x080CB0D6, 'b81fec14607a100e4142197746c640ceca8ecb6deefa3f1a822579f40b762591'),
    VALIDATE: (0x080CB5A8, '046e1abf4b21c75e21dabcd12ed7eb092c9bad2b5c380a444d9df429ffc5cc6e'),
    REFRESH: (0x080CA392, '56fe099416dd92717c8320a038ef557fa52e21eacb2794a5975985c349aaed12'),
    DISPATCH: (0x08133970, 'b1a2ee4c8cefef5b7581b6599971145c0e7a1a78a4e47f2b1c344ca282824d5c'),
    THUNK: (0x0814224A, 'bac8ca6ee9f77b46c7ab5824c7c59d99fd0ca53ae998ea2872b78bb6a5189cc5'),
}


def dispatch(rom, objects, *, kind=KIND, callback=OWNER, record_index=156):
    names = equipment.match.parse_data_symbols(objects)
    for name, address in (('data_0200F3F0', STATE), ('data_083A87B0', TABLE), ('data_08553E70', RECORDS)):
        require(names.get(name) == address, 'action state, descriptor or record mapping differs')
    equipment.ops(rom, 0x081338A8, 'ldr r5, [pc, #0x74]', 'ldr r0, [r4, #0x30]', 'ldrb r1, [r0, #1]',
                  'lsls r0, r1, #1', 'adds r0, r0, r1', 'lsls r0, r0, #2', 'adds r0, r0, r5',
                  'ldr r1, [r0]', 'adds r0, r4, #0', 'bl #0x8142248')
    equipment.ops(rom, THUNK, 'bx r1')
    require(equipment.word(rom, 0x08133918) == STATE and equipment.word(rom, 0x08133920) == TABLE and
            equipment.word(rom, TABLE + 12*kind) == callback | 1 and
            rom[RECORDS-equipment.BASE+4*record_index+1] == kind, 'original equipment action dispatch differs')
    return dict(caller=DISPATCH, site=0x081338BA, thunk=THUNK, descriptor=TABLE+12*kind,
                record=RECORDS+4*record_index, kind=kind, callback=callback, argument=STATE)


def owner_frame(ins):
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #4', 'adds r6, r0, #0', 'ldrh r1, [r6, #0x26]',
          'movs r0, #0x10', 'ands r0, r1', 'cmp r0, #0', 'bne #0x8133376', 'ldr r0, [r6, #8]',
          'mov r1, sp', 'bl #0x812f0cc', 'mov sl, r0', 'cmp r0, #0', 'ble #0x8133376', 'movs r4, #0')
    block(ins, 0x08133320, 'ldr r0, [r6, #8]', 'adds r1, r4, #0', 'adds r1, #0x1d',
          'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'bl #0x80c7ea4', 'lsls r0, r0, #0x10',
          'lsrs r7, r0, #0x10', 'adds r0, r4, #1', 'mov sb, r0', 'cmp r7, #0', 'beq #0x813336a',
          'mov r3, sl', 'cmp r3, #0', 'ble #0x813336a', 'mov r5, sp', 'lsls r4, r4, #0x18',
          'mov r8, r4', 'mov r4, sl')
    block(ins, 0x08133348, 'ldrh r0, [r5]', 'cmp r0, r7', 'bne #0x8133362', 'ldr r0, [r6, #8]',
          'movs r1, #0', 'mov r3, r8', 'lsrs r2, r3, #0x18', 'bl #0x80caf78', 'ldr r0, [r6, #8]',
          'movs r1, #1', 'bl #0x80cb54c', 'adds r5, #2', 'subs r4, #1', 'cmp r4, #0',
          'bne #0x8133348', 'mov r4, sb', 'cmp r4, #4', 'ble #0x8133320', 'ldr r0, [r6, #8]',
          'bl #0x80ca2e8', 'add sp, #4', 'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4',
          'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r0}', 'bx r0')


def validate_mutators(rom, mapping, index):
    # The legacy text rows for these callees count every halfword in the symbol.
    # Check both span boundaries and derive their actual reachable counts from the ROM.
    helpers = {CLEAR: 161, VALIDATE: 44, REFRESH: 67}
    for target, count in helpers.items():
        end, digest = PINS[target]
        body = rom[target-equipment.BASE:end-equipment.BASE]
        equipment.named.validate_owner(body, target, rom, mapping, index)
        decoded = equipment.graph.graph(body, target, refine(body, target, mapping))[0]
        require(len(decoded) == count and sha256(body).hexdigest() == digest,
                'equipment mutation or refresh helper differs')
    return helpers


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-equipment.BASE:END-equipment.BASE]
            and len(ins) == 66 and not words and original == equipment.bindings(CALLS)
            and calls == {OWNER+offset: target for offset, target in CALLS.items()},
            'equipment removal requires the complete original symbol and its five calls')
    helpers = validate_mutators(rom, mapping, index)
    battle.check_dependencies(rom, mapping, index, objects,
                              {a: pin for a, pin in PINS.items() if a not in helpers}, OWNER, len(ins))
    equipment.ops(rom, WRAPPER, 'push {lr}', 'bl #0x812e4f4', 'pop {r1}', 'bx r1')
    owner_frame(ins)
    cases = []
    for case in equipment.cursor_cases():
        writes = case['write_offsets']
        reads = list(range(0, 2*case['selected'], 2))
        require(reads == writes and all(off in (0, 2) for off in reads), 'consumer crosses its frame')
        cases.append(dict(mask=case['mask'], count=case['selected'], collector_writes=writes,
                          reads_per_nonempty_slot=reads))
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'],
                runtime_calls=[], partition=equipment.graph.partition(data, OWNER, refinement, ins, words),
                caller=dispatch(rom, objects), local=[-36, -32], saved=[-32, 0], cases=cases,
                output_chain=[WRAPPER, equipment.COLLECT], initial_clears=[0, 2],
                scene_equipment=equipment.scene_rows(rom), equipment_copy=equipment.installed_copy(rom, mapping, index),
                result='Flag 0x10 skips all work. A positive selection count scans the five current slots. '
                       'Every equality against the original selected halfwords invokes the clear and validation '
                       'helpers, including repeated equalities. The final refresh runs once for a positive count.',
                conditions=['At collection the five live slots contain at most two nonzero items whose field 6 '
                            'is 1 or 2 and whose field 3 differs from 20. The collector has no two-entry clamp. '
                            'The original scene rows establish initial loadouts only. The dispatcher does not '
                            'enforce this limit on a live, edited target.',
                            'The state, target and reached item rows must be valid, aligned and separate from '
                            'the stack. No concurrent changes during collection. Subsequent slots are reread '
                            'after the effect edits the target. Original returning helpers preserve SP, saved '
                            'registers and the selected array, except for the collector writes. They do not '
                            'retain pointers into the array.'],
                environment=equipment.environment_fingerprint())
