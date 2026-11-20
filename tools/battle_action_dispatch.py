"""Battle action evaluator selection, installed scene clear and two arena allocations."""
from hashlib import sha256

import battle_action_value as battle
import function_thunk_profile as thunk
import installed_zero_effects as zero
import iwram_installation_prerequisite as install
import scheduler_zero_descriptor as boot
import unit_equipment_attribute as equipment
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from software_float_profile import ROM_SHA256

OWNER, END, SIZE = 0x080C01D0, 0x080C034C, 0x21C
SOURCE_HASH = 'b64c5313cb894df31a3ac7dc56b637251b611dbff8ea5c1114c63579082cacb4'
HEADER_PATH = 'include/battle_position_search.h'
HEADER_HASH = 'd15bd913c90bb5d52861acc6a3be9a71dc2ffb907bd2c8d68dab38f30c057bde'
ALLOC, QUERY, UNIT_FLAG = 0x08022840, 0x08099544, 0x080CD944
ABILITY, KIND = 0x080CCD50, 0x0812EE98
CALLS = {44: thunk.ALIASES['_call_via_r2'], 94: ALLOC, 110: ALLOC, 146: QUERY, 158: UNIT_FLAG,
         216: ABILITY, 254: equipment.WRAPPER, 266: KIND, 300: ABILITY, 324: ABILITY}
EVALUATORS = {208: 0x080BF5A4, 292: 0x080BF7C4, 340: 0x080BFDB0, 352: 0x080BEF28, 376: 0x080BEAC8}
TABLE = 'g_callbacks_0836D4B8'
BINDINGS = equipment.bindings(CALLS)
BINDINGS['calls'][0][1] = '_call_via_r2'
BINDINGS['data'] = [[200, TABLE, 0]]
BINDINGS['functions'] = [[off, f'func_{target:08X}'] for off, target in EVALUATORS.items()]
PINS = {
    0x08007138: (0x0800716E, '41bb84543d24c53f9292d190bc5e895370602a394d7b1db5169b21fcfa6f027f'),
    0x08022840: (0x08022854, '14cb0536da48cf8687d014bc016ba15e46c4576c2f39fcccd74b5d3cd6daf29c'),
    0x08099544: (0x08099560, '52885cefa4dae85fe40546a8a51013b80943a090610fce3154f496206cc2579a'),
    0x08099840: (0x0809985C, '55d837fe60c03fad5a01852612f6feabe87d595695bbe421cb506e952ba7c386'),
    0x0809AB3C: (0x0809AB5C, '9d9f6b2d8b299a27baf693fb8489787d459dab56fb03ac43da67309b1bcb7160'),
    0x0809ABE8: (0x0809ABFE, '65ec4ecbbacee97448810c0c4bb966405fc392884ba09795dc94b0b00aeff3d4'),
    0x080BEAC8: (0x080BEF28, 'd0101fe4ae244b647b0d4654d19e2763dbbb6c0765ee52237199525cdd21ea47'),
    0x080BEF28: (0x080BF5A2, 'a14fd7c9326e8b1ce9bafd9aee91c5f912de429f7dad9ac1654001a4b111e196'),
    0x080BF5A4: (0x080BF7C2, '43b207b10dcae3a87cc3296e0d5058c48428f8fba945b7754e83f4f51a488cb8'),
    0x080BF7C4: (0x080BFDB0, '58843d34bfc25d4b9fe7658036bc0ad7d8a0527d1df515bdb02266ec5a588d1c'),
    0x080BFDB0: (0x080C01CE, '3e2f6dbca20afc460b9b698a85cc88d7f71613e4cb0bd23a13817dee41aaae40'),
    0x080C01D0: (0x080C034C, '8777122c3557d976a88b464cdb1d22c57c266fd3f6e042758ed52cd2d27caf3a'),
    0x080C045C: (0x080C127C, '2a7b253ca14bb697fb49bfde0b88227f3dabbe517c55dc6695a66b42578d3f57'),
    0x080C2618: (0x080C26EC, '9a55aa637bf488c236704c8da9c43b38dd1e9aab56d80706fbd70d6b7f242a46'),
    0x080C26EC: (0x080C286A, '842e92af9c018b8784749dc2a848ae4e6ebdc5a1a1d3831071a1431096ba08a9'),
    0x080C32C0: (0x080C47A8, '08f3a9736cde36c260483db59890bf62eaa8344e55f70a2465393dd77825baec'),
    0x080C7B74: (0x080C7B78, 'a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da'),
    0x080C7CC0: (0x080C7CE2, '47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1'),
    0x080C8298: (0x080C82B6, 'f2c339da0525b4ad4a4f7957435f8cde0cd4562f3af26d9b808c48ab7004eb3d'),
    0x080C8570: (0x080C8A24, '1fa2f1bfd1d7974ce8a3387acaa6b2b301d42c79475938e5f6f6cc7cd8a18057'),
    0x080C92F0: (0x080C9314, '75875c8fb568e97c7d96eee0e6bf7a48f39a75601d60204372f4ad19cd0a4c25'),
    0x080CCD50: (0x080CCE60, '39e1d10703ef3fcb25361d3ef7d555157f6a0af5358b4fdf3f1e609df98c3c77'),
    0x080CD944: (0x080CD95C, '73b7bcf972ff7be1e3f9b617744ccedc37108ce4eafd7c00033aab5c8c85bb3d'),
    0x0812EE98: (0x0812EECE, 'b56d82be60300fe077482eeb6229b3db0004c7fe82be550c029f6f6c55e9129b'),
    0x0814224C: (0x0814224E, 'dd9261f0471768edc33bf979649f6297463be423da17c3f881684f5747e163a1'),
}


def check_original(image, original, targets):
    expected = {name: (CALLS[off], False) for off, name in BINDINGS['calls']}
    expected.update({name: (EVALUATORS[off], False) for off, name in BINDINGS['functions']})
    expected[TABLE] = (boot.POINTER, True)
    require(original == BINDINGS and targets == expected, 'battle dispatch ELF roles or relocation sites differ')
    compiler_symbol_roles(image, targets)
    require(all(not s['size'] for s in image['symbols'] if s['name'] in targets),
            'battle dispatch reference must be unsized')


def installed_clear(rom, mapping, index):
    plan = install.verify(rom[0x2768:0x27B8], 0x08002768, rom, mapping, index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=boot.POINTER)
    require(plan['arguments'] == dict(source=boot.IMAGE, destination=boot.DESTINATION, control=88)
            and plan['copy_plan']['bytes'] == 176 and plan['copy_plan']['width'] == 2
            and plan['entry']['pointer_word'] == boot.DESTINATION | 1
            and plan['source_image']['sha256'] == boot.IMAGE_SHA256, 'battle clear installation differs')
    # This owner passes a word-aligned external state and the single constant 540.
    case = zero._case(bytes.fromhex(plan['source_image']['bytes']), boot.DESTINATION, boot.DESTINATION, SIZE, 0)
    writes = [('destination', offset, 4) for offset in range(0, SIZE, 4)]
    require(case['writes'] == [('stack', -4, 4), *writes] and case['reads'] == [('stack', -4, 4)]
            and case['SP_restored'] and case['protected_return'], '540-byte state initialization differs')
    return dict(installer=plan['call_site'], pointer=boot.POINTER, entry=boot.DESTINATION | 1,
                image_sha256=boot.IMAGE_SHA256, size=SIZE, aligned_zero_words=len(writes))


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(original == BINDINGS and len(ins) == 164 and not words and
            calls == {OWNER+off: target for off,target in CALLS.items()} and
            data == rom[OWNER-equipment.BASE:END-equipment.BASE] and sha256(rom).hexdigest() == ROM_SHA256,
            'battle dispatch requires the complete original owner and all ten call sites')
    battle.check_dependencies(rom, mapping, index, objects, PINS, OWNER, 164)
    require(equipment.match.parse_data_symbols(objects).get(TABLE) == boot.POINTER,
            'battle dispatch callback table differs')
    partition = equipment.graph.partition(data, OWNER, refinement, ins, words)
    literals = {entry['address']-OWNER: entry['value'] for entry in partition['words']}
    require(partition['code_bytes'] == 348 and partition['alignment'] ==
            [[0x080C02F2,0x080C02F4],[0x080C0346,0x080C0348]] and
            literals == {200: boot.POINTER, 204: 0x109, **{off: target | 1 for off,target in EVALUATORS.items()}},
            'battle dispatch code, literal pool or alignment differs')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #4')
    block(ins, 0x080C02C8, 'mov r1, sb', 'ldr r0, [r1]', 'mov r1, sp', 'bl #0x812f0d8',
          'mov r2, sb', 'ldr r0, [r2]', 'mov r1, sp', 'ldrh r1, [r1]', 'bl #0x812ee98')
    block(ins, 0x080C0336, 'add sp, #4', 'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4',
          'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    equipment.ops(rom, 0x080C09A8, 'mov r0, sl', 'mov r1, ip', 'mov r2, sb', 'adds r3, r5, #0',
                  'bl #0x80c01d0', 'ldr r2, [pc, #0x2c]', 'adds r1, r7, r2', 'str r0, [r1]')
    equipment.ops(rom, 0x080C09F4, 'ldr r1, [r7]', 'ldr r2, [r2]', 'bl #0x814224c',
                  'lsls r0, r0, #0x18', 'lsrs r4, r0, #0x18', 'cmp r4, #0', 'beq #0x80c0a08')
    return dict(schema=equipment.named.EQUIPMENT_SCHEMA, instructions=len(ins), calls=original['calls'][1:],
                runtime_calls=original['calls'][:1], partition=partition, local=[-36,-32], saved=[-32,0],
                entry_stack_arguments=[0,4,8,12,16], read_offsets=[0], clear=installed_clear(rom,mapping,index),
                allocations=[[1024,0x204],[256,0x200]], caller_site=0x080C09B0, invocation_site=0x080C09F8,
                callbacks=original['functions'], scene_equipment=equipment.scene_rows(rom),
                collector_cases=equipment.cursor_cases(), equipment_copy=equipment.installed_copy(rom,mapping,index),
                result='The constructor clears 540 bytes, binds the selected units and action, allocates two '
                       'work buffers and returns a Thumb evaluator. The special action 265 selects BF5A4. '
                       'The basic or equipment-based action selects BF7C4 for item kinds 13, 14 or 19, '
                       'otherwise BFDB0. Ability kinds 4, 6 and 7 or ability bit 0x40 also select BFDB0. '
                       'The remaining cases select BEAC8 for identical units and BEF28 for distinct units.',
                conditions=['Any reached equipment query requires a stable five-slot loadout with at most two qualifying '
                            'items (field 6 is 1 or 2 and field 3 differs from 20). The producer initializes both '
                            'halfwords, including when the collection is empty.',
                            'The aligned external state has 540 writable bytes. The clear entry is installed unchanged, '
                            'the arena has room for both allocations, and the actor, list and ability records are live. '
                            'External storage is disjoint from the current native frame and its saved return.'],
                environment=equipment.environment_fingerprint())
