"""Two selected equipment halfwords, the basic attack, and the three action variants."""
from hashlib import sha256

import battle_action_value as battle
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require

OWNER, END = battle.GUARD, 0x080C4964
STATE, STATE_NAME = 0x0200F3F0, 'data_0200F3F0'
DATA = [[72, STATE_NAME, 0]]
SOURCE_HASH = 'c3f58e04e607a8086b0151493959d9722b7cda857828baf9aca13c7581e9097a'
CALLS = {18: equipment.WRAPPER, 52: 0x080C8280, 80: 0x080CCD50, 96: 0x0812F39C,
         102: 0x0812F34C, 116: 0x0812F2A4, 138: 0x0812F328, 144: 0x0812F34C,
         148: 0x08130FBC, 158: 0x08131378}
PINS = {
    OWNER: battle.PINS[OWNER], battle.OWNER: battle.PINS[battle.OWNER],
    0x080BE1F4: (0x080BE3B8,'57fddfe36c03884f030f88e080de537f2f8dcbd63a54d0ec4cbc3c330533cdd2'),
    0x080BFDB0: (0x080C01CE,'3e2f6dbca20afc460b9b698a85cc88d7f71613e4cb0bd23a13817dee41aaae40'),
    0x080C8280: (0x080C8296,'33e067dc316794030f84309a4c8d18596a7fe650cb28b690d0492074a005519a'),
    0x080CCD50: (0x080CCE60,'39e1d10703ef3fcb25361d3ef7d555157f6a0af5358b4fdf3f1e609df98c3c77'),
    0x0812F2A4: (0x0812F2CC,'700f371dc3fb00ae3e5bbbfc0d5e898c7b5c75006b328fe17e2cbf5f67b79891'),
    0x0812F328: (0x0812F34C,'6df1d24522a390793caa1378beea29aec74c2dc82d09c6dc12608ef3164d6518'),
    0x0812F34C: (0x0812F358,'9389992425624f21b0e786307edb434c6582d9c1a7a2887b7b47f2f1572fd1e8'),
    0x0812F39C: (0x0812F3B0,'27bfcb5c6b471ac90b30e57eebc04c8eca70dbee2a308f957b5a5370faac4ff5'),
    0x08130FBC: (0x08131024,'be4b782c4b1d19cee70ffd1da6a473c032773e0a7fddfdbfc2cbd64ca9f4ef94'),
    0x08131378: (0x08131474,'a329cdf8789ac899d53f36157a0c62eb5c1e740ebed873086e4c1c2b5021ec6c'),
}


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    from software_float_profile import ROM_SHA256
    expected = equipment.bindings(CALLS)
    expected['data'] = DATA
    require(original == expected and calls == {OWNER+s: t for s,t in CALLS.items()} and not words and
            sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-equipment.BASE:END-equipment.BASE]
            and len(ins) == 83, 'eligibility whole symbol, literal, or call sites differ')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, 83)
    require(equipment.match.parse_data_symbols(objects).get(STATE_NAME) == STATE, 'action state mapping differs')
    partition = equipment.graph.partition(data, OWNER, refinement, ins, words)
    require(partition['code_bytes'] == 186 and partition['alignment'] == [[0x080C48EA,0x080C48EC]]
            and partition['words'] == [dict(address=0x080C48EC,value=STATE,load_sites=[0x080C48CC],
                                             switch_word=False)], 'eligibility code, data or alignment differs')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, r8', 'push {r7}', 'sub sp, #4',
          'adds r5, r0, #0', 'adds r7, r1, #0', 'lsls r2, r2, #0x10', 'lsrs r4, r2, #0x10',
          'mov r1, sp', 'bl #0x812f0d8', 'lsls r0, r0, #0x10', 'asrs r1, r0, #0x10',
          'cmp r1, #0', 'bne #0x80c48c6', 'mov r0, sp', 'strh r1, [r0]', 'mov r0, sp',
          'ldrh r0, [r0]', 'mov r8, r0', 'ldr r6, [pc, #0x1c]', 'cmp r4, #0', 'bne #0x80c48f0',
          'cmp r5, r7', 'beq #0x80c4952', 'adds r0, r7, #0', 'bl #0x80c8280', 'movs r1, #0',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'bne #0x80c48e6', 'movs r1, #1',
          'adds r0, r1, #0', 'b #0x80c4954')
    block(ins, 0x080C48F0, 'adds r0, r4, #0', 'movs r1, #0xb', 'bl #0x80ccd50', 'cmp r0, #0',
          'bne #0x80c4912', 'cmp r5, r7', 'bne #0x80c4912', 'b #0x80c4952')
    block(ins, 0x080C4902, 'adds r0, r4, #0', 'bl #0x812f39c', 'adds r0, r7, #0',
          'bl #0x812f34c', 'movs r0, #1', 'b #0x80c4954')
    block(ins, 0x080C4912, 'adds r0, r4, #0', 'mov r1, r8', 'movs r2, #0', 'bl #0x812f2a4',
          'str r5, [r6]', 'str r7, [r6, #4]', 'ldrh r1, [r6, #0x26]', 'movs r0, #0x10',
          'orrs r0, r1', 'strh r0, [r6, #0x26]', 'movs r4, #0', 'lsls r0, r4, #0x18',
          'lsrs r0, r0, #0x18', 'bl #0x812f328', 'movs r0, #0', 'bl #0x812f34c', 'bl #0x8130fbc',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x80c494c', 'bl #0x8131378', 'lsls r0, r0, #0x18',
          'cmp r0, #0', 'bne #0x80c4902', 'adds r4, #1', 'cmp r4, #2', 'ble #0x80c492a', 'movs r0, #0',
          'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'add sp, #4', 'pop {r3}', 'mov r8, r3',
          'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    for site in (0x080BDEEC, 0x080BE278, 0x080BFDF8):
        equipment.ops(rom, site, 'bl #0x80c48a4', 'lsls r0, r0, #0x18')
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=83, calls=original['calls'],
                runtime_calls=[], partition=partition, local=[-28,-24], saved=[-24,0],
                collection=[equipment.WRAPPER,equipment.SORT,equipment.COLLECT],
                collector_cases=equipment.cursor_cases(), read_offsets=[0], empty_fallback=0,
                caller_sites=[0x080BDEEC,0x080BE278,0x080BFDF8], variants=[0,1,2],
                scene_equipment=equipment.scene_rows(rom), equipment_copy=equipment.installed_copy(rom,mapping,index),
                result='The basic action requires distinct actors and a living target. A nonzero action must '
                       'permit self-targeting or have distinct actors. The first of three variants passing both '
                       'original queries is selected. The shared return zero-extends the Boolean to one byte.',
                conditions=['At each equipment query the actor has a stable five-slot loadout with at most '
                            'two nonzero items whose field 6 is 1 or 2 and field 3 differs from 20. The 42 '
                            'verified original scene rows certify only initial equipment. All three caller paths '
                            'require the same condition after any changes.',
                            'Live actors, action tables, callbacks and mutable battle state remain valid and '
                            'separate from the frame. Returning helpers preserve the ABI, do not retain the '
                            'output pointer or alias the saved frame, and only the collector and sorter use '
                            'the local through its output argument.'], environment=equipment.environment_fingerprint())
