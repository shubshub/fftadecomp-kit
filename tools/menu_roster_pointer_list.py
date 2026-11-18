"""The mode-seven roster menu's optional list of pointers to live unit records."""
from hashlib import sha256
from pathlib import Path
import struct

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB

import match
import menu_roster_filter as filters
from ability_range_local_bytes import block, require
from history_word_copy import aligned_manager_clear
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record

OWNER = 0x08067FFC
ACCESSOR = 0x080C7EA4
BANK = 0x08064EF8
EVENT = 0x080651FC
CONSUMER = 0x0806617C
SLOT = 0x0200F454
ROSTER = 0x02000080
STATE = 0x020020D0
TABLE = 0x424
STATES = (2, 8, 0x5E, 10, 4, 9, 12)
PROVIDERS = (
    (OWNER, 0x0806807C, '7343f254140b943aa289b92b69a11cbb16be211aed04c79e2168f5ed9f285d65'),
    (ACCESSOR, 0x080C817C, '29dd15c43bb1bffac2764ef500fea0cc258ebea77360b3d04e0ee382b738ffcb'),
    (BANK, 0x08064FA0, '895c49d076936d60be1ca00f0a5b4108cc2f24f41411400d772162596db5ebcd'),
    (EVENT, 0x08065608, '5c952cb6932767e30979a40dc050c62098fcd7d98f6ecabe339e0255a3c7b5f7'),
    (CONSUMER, 0x080664C4, '82b391abf330d6f5eccfb9003c728392c6294b955ab04b9cbbf5aca2c276eef4'),
    (0x08064FA0, 0x08065028, '6e9fd84f2c0af4f8c4bbb4836e076c4b84bbfd8e68bd0cdbf8e1fb2c04998ee0'),
    (0x08005954, 0x08005A22, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    (0x08005A24, 0x08005AFE, '92a60c7b7568e688bda0434c5efc4945c67b84c3d73a03bb7f2a51fdb5f99187'),
    (0x08005C14, 0x08005C32, 'caccd91ce3241962205e03a6cd4b6b51a3b584a42e73622787c0741cd62e17c2'),
    (0x08005C34, 0x08005C4C, '7fee90067f24b703cb2863e6902edb735918a714b93b6a93e56e198be17072a0'),
    (0x08005B18, 0x08005B28, '8d118f29504fc5a36a5d3f75787df391301f80b998915410608319fa4697f252'),
    (0x08005B28, 0x08005B40, 'ba04646db5270381ed1163725929afbf1af7d9702d082ec8b0c891ed2d56b3f3'),
    (0x080C8310, 0x080C832C, '9cc97fa94262c87ba345353f6d485264077f25a404db2171ecf39cb3d0718bdb'),
    (0x080C82D8, 0x080C82F4, 'ef57c0a692e33b090e00841c38ef25e51f254d91de0ad6ddfbb170cdaf6a3ac2'),
    (0x08022854, 0x08022868, 'dc40e21202fe3f3244adc6024444db000876a9b76336db4627e6826cb0f5d37b'),
)


def check_source(root):
    import plausible
    source = (Path(root) / 'src/08067FFC.c').read_text()
    header = (Path(root) / 'include/ffta.h').read_bytes()
    require(base_header(header, ('func_08067FFC', 'func_08071DC8', 'func_080C7EA4',
                                 'g_state_020020D0', 'g_state_02000080'))
            and not any(marker in source for marker in (chr(92), '??', '%:', chr(0))),
            'unexpected roster pointer source preprocessing or header')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(source)))
    prefix, end, body = tokens.partition('s32 i ;')
    require(end and '#' not in body and sha256((prefix+end).encode()).hexdigest() ==
            '6fc77626205d1b67180a0f96a2280a52d5501f0d080eeb71d21de4a58288de7e',
            'unexpected roster array, accessor return, pointer output or local capacity')


def bindings():
    return dict(calls=[[12, 'func_08071DC8'], [50, 'func_080C7EA4']],
                data=[[120, 'g_state_020020D0', 0], [124, 'g_state_02000080', 0]], functions=[], switches=[])


def consumer(rom, mapping, index):
    entries, rows = indices(mapping, index)
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    for address, end, digest in (*PROVIDERS, *filters.heap_providers()):
        row = span_record(address, end, entries, rows, rom)
        if address == OWNER:
            require(row['instrs'] == 57, 'changed roster pointer filter instruction count')
        data = rom[address-match.ROM_BASE:end-match.ROM_BASE]
        require(sha256(data).hexdigest() == digest, f'changed roster pointer provider at {address:08X}')

    def check(address, *operations):
        offset = address - match.ROM_BASE
        instructions = {item.address: item for item in decoder.disasm(rom[offset:offset+4*len(operations)], address)}
        block(instructions, address, *operations)

    def word(address):
        return struct.unpack_from('<I', rom, address-match.ROM_BASE)[0]

    require(tuple(word(site) for site in (0x08064F44, 0x08064F48, 0x08064F4C, 0x08064F50,
            0x08064F84, 0x080652A8, 0x080661EC, 0x080661F0, 0x080664BC)) ==
            (SLOT, filters.boot.POINTER, 0x1704, 0x20FC, SLOT, SLOT, filters.boot.POINTER, TABLE, TABLE),
            'changed menu allocation, callbacks or list offset')
    check(0x08064F12, 'movs r0, #0xe0', 'lsls r0, r0, #6', 'bl #0x8022840', 'adds r4, r0, #0',
          'ldr r5, [pc, #0x24]', 'str r4, [r5]')
    check(0x08064F26, 'adds r0, r4, #0', 'adds r1, r6, #0', 'bl #0x814224c',
          'ldr r0, [r5]', 'str r4, [r0, #4]', 'adds r4, r4, r6', 'ldr r1, [pc, #0x18]',
          'adds r0, r4, #0', 'bl #0x8005c14')
    check(0x08064F74, 'adds r0, r4, #0', 'bl #0x8022854', 'movs r0, #0', 'str r0, [r5]')
    require(word(0x08065020) == SLOT and word(0x08065024) == EVENT+1,
            'changed scheduler scene pointer or callback')
    check(0x08065004, 'ldr r0, [pc, #0x18]', 'ldr r0, [r0]', 'ldr r0, [r0]',
          'ldr r1, [pc, #0x18]', 'movs r2, #0', 'str r2, [sp]', 'movs r2, #0xdc',
          'add r3, sp, #4', 'bl #0x8005954')
    check(0x08065298, 'mov r1, r8', 'ldrh r0, [r1, #0x14]', 'strb r0, [r7, #8]',
          'ldr r0, [pc, #8]', 'ldr r0, [r0]', 'str r0, [r7]')
    check(0x080652AC, 'adds r0, r7, #0', 'bl #0x806617c')
    check(0x080661B2, 'ldr r2, [pc, #0x38]', 'ldr r0, [r5]', 'ldr r1, [pc, #0x38]',
          'adds r0, r0, r1', 'movs r1, #0xbc', 'lsls r1, r1, #3', 'ldr r2, [r2]', 'bl #0x814224c',
          'ldr r1, [r5]', 'movs r0, #0', 'strh r0, [r1, #0xe]')
    require(word(0x080661F4) == 0x080661F8 and word(0x080661F8+6*4) == 0x080663F8, 'changed mode seven')
    check(0x080663F8, 'ldr r0, [r5]', 'ldr r1, [pc, #0xc0]', 'adds r0, r0, r1', 'bl #0x8067ffc',
          'ldr r1, [r5]', 'strh r0, [r1, #0xe]')
    check(0x08066410, 'lsls r0, r6, #2', 'ldr r2, [pc, #0xa8]', 'adds r1, r1, r2',
          'adds r1, r1, r0', 'ldr r4, [r1]', 'adds r0, r4, #0', 'bl #0x80c8310')
    layout = word(0x080661E4)
    require(layout == 0x08393A24 and struct.unpack_from('<H', rom, layout-match.ROM_BASE+7*16+4)[0] == 22,
            'changed mode-seven enable-byte count')
    check(0x0806619A, 'ldrh r0, [r7, #4]', 'bl #0x8005b28')
    check(0x08066432, 'adds r0, r5, #0', 'adds r0, #0x98', 'ldr r0, [r0]', 'adds r0, r0, r6',
          'movs r1, #0', 'strb r1, [r0]')
    require(word(0x080C7EBC) == 0x080C7EC0 and word(0x080C7EC4) == 0x080C7FD8,
            'changed accessor selector-one dispatch')
    check(0x080C7FD8, 'ldrb r0, [r2, #4]', 'b #0x80c8178')
    filters.boot.initializer(rom, mapping, index)
    clear = rom[filters.boot.IMAGE-match.ROM_BASE:filters.boot.IMAGE-match.ROM_BASE+176]
    _, _, prefix_words = aligned_manager_clear(clear, 0x02000000, 0x1704)
    _, _, list_words = aligned_manager_clear(clear, 0x02000000+TABLE, 0x5E0)
    require(TABLE+24*4 <= TABLE+0x5E0 <= 0x1704 and 0x1704+0x20FC == 0x3800, 'scene extent mismatch')
    return dict(constructor=BANK, scene_slot=SLOT, allocation=0x3800, scene_clear_words=prefix_words,
                private_manager=[0x1704,0x3800], scheduler_request=0x08064FA0, callback=EVENT,
                phase_zero_context_copy=0x080652A2, event_100=0x080652AE,
                consumer=CONSUMER, mode=7, clear_words=list_words, pointer_list=[TABLE,TABLE+24*4],
                cleared_list=[TABLE,TABLE+0x5E0], count_halfword=14, store=0x08066404,
                pointer_use=0x08066418, enabled_allocation=22, enabled_guard=
                'For the complete mode-seven consumer, require at most 22 accepted units so the '
                'flag loop indexes only the separate 22-byte enable allocation. The standalone filter '
                'can return 24 when its caller supplies 24 pointer slots.', released_at=0x08064F76,
                premise='Successful live scene, initialized saved pointer and mode seven. Its cleared list '
                        'is separate from the unit records and active frames. The saved pointer expires at release.')


def prove(data, rom, mapping, index, objects, original, ins, calls, refinement, words):
    require(len(ins) == 57 and not words and sha256(data).hexdigest() == PROVIDERS[0][2]
            and calls == {OWNER+12: filters.roster.OWNER, OWNER+50: ACCESSOR} and original == bindings(),
            'changed native roster pointer filter, calls or ELF bindings')
    names = match.parse_data_symbols(objects)
    require((names.get('g_state_020020D0'), names.get('g_state_02000080')) ==
            struct.unpack_from('<2I',data,120) == (STATE, ROSTER), 'changed roster pointer filter bases')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'sub sp, #0x1c', 'adds r7, r0, #0',
          'ldr r0, [pc, #0x70]', 'ldrb r0, [r0, #0x14]', 'mov r1, sp', 'bl #0x8071dc8',
          'movs r2, #0', 'movs r6, #0', 'adds r5, r7, #0', 'mov r0, sp', 'adds r1, r0, r6',
          'ldrb r0, [r1]', 'cmp r0, #0xff', 'beq #0x8068062', 'adds r1, r0, #0', 'lsls r0, r1, #5',
          'adds r0, r0, r1', 'lsls r0, r0, #3', 'ldr r1, [pc, #0x50]', 'adds r4, r0, r1',
          'adds r0, r4, #0', 'movs r1, #1', 'str r2, [sp, #0x18]', 'bl #0x80c7ea4',
          'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18', 'ldr r2, [sp, #0x18]',
          'cmp r4, #0', 'beq #0x8068058')
    for index_, kind in enumerate(STATES):
        block(ins, 0x0806803C+4*index_, f'cmp r0, #{hex(kind) if kind >= 10 else kind}', 'beq #0x8068062')
    block(ins, 0x08068058, 'cmp r7, #0', 'beq #0x806805e', 'str r4, [r5]', 'adds r5, #4',
          'adds r2, #1', 'adds r6, #1', 'cmp r6, #0x17', 'ble #0x8068012', 'adds r0, r2, #0',
          'add sp, #0x1c', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    return dict(schema=filters.named.ROSTER_FILTER_SCHEMA, instructions=len(ins), calls=original['calls'],
                runtime_calls=[], partition=filters.graph.partition(data, OWNER, refinement, ins, words),
                producer=filters.producer(rom, mapping, index, objects), index_domain=filters.index_domain(),
                scene=consumer(rom, mapping, index), filter=dict(accessor=ACCESSOR, selector=1, byte_offset=4,
                    excluded_states=list(STATES), roster=[ROSTER, ROSTER+24*filters.roster.STRIDE],
                    entry_stack=dict(indices=[-48,-24], count_spill=[-24,-20], saved=[-20,0],
                                     nested_stack=[-1264,-48]), count=[0,24],
                    output='NULL counts accepted units without storing pointers. Otherwise a word-aligned '
                           'writable list with room for the accepted units, disjoint from the roster, '
                           'selection and all currently used frames. Only accepted pointers are written.'),
                environment=filters.roster.environment_fingerprint())
