"""Normal movement-path output and the caller's two local tile searches."""
from hashlib import sha256
from pathlib import Path

import named_data_buffer_profile as named
import owner_graph_profile as graph
import plausible
import scheduler_zero_descriptor as boot
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import ops, word

BASE = 0x08000000
OWNER, WRAPPER = 0x080989AC, 0x0809A604
VALID, PATH, TRACE, ELIGIBLE = 0x08149384, 0x081492D0, 0x08148A0C, 0x08097504
ITERATOR, CALLBACK = 0x080C7CC0, 0x0809ABB0
COPY_SLOT, COPY_ENTRY = 0x0836D4BC, 0x03005EE8
FIRST, LAST, CAPACITY = 0x03006108, 0x03006164, 24
CALLS = {38: VALID, 68: ITERATOR, 90: PATH, 138: ELIGIBLE, 166: ITERATOR}
SOURCE = 'src/080989AC.c'
SOURCE_TOKENS = 'a919efd2e63e95ec62f81bbfee9034c668b133a7437466fc4ca4bea7776b5c4b'

# Exact indexed Thumb boundaries in the authenticated USA ROM. The owner count
# is also derived independently from the reached graph in prove().
EXTENTS = {
    OWNER: 0x08098A88, WRAPPER: 0x0809A624, ITERATOR: 0x080C7CE2,
    CALLBACK: 0x0809ABE6, 0x080C7B74: 0x080C7B78, 0x0814225C: 0x0814225E,
    0x08142250: 0x08142252, VALID: 0x081493AA, PATH: 0x08149368,
    TRACE: 0x08148A98, ELIGIBLE: 0x080975DA, 0x081493AC: 0x081493C0,
    0x0801CC7C: 0x0801CD06, 0x0801CD08: 0x0801CD28,
}


def bindings():
    return dict(calls=[[offset, f'func_{target:08X}'] for offset, target in CALLS.items()],
                functions=[[104, 'func_0809ABB0'], [216, 'func_0809ABB0']], data=[], switches=[])


def check_original(image, address, roles, targets):
    expected = {f'func_{target:08X}': (target, False) for target in {*CALLS.values(), CALLBACK}}
    require(address == OWNER and roles == bindings() and targets == expected,
            'movement path requires five typed calls and two tile callback references')
    compiler_symbol_roles(image, targets)
    require(all(not symbol['size'] for symbol in image['symbols'] if symbol['name'] in targets),
            'movement path helper reference has a size')


def check_source(root, address):
    root = Path(root)
    source = root / SOURCE
    text = source.read_text()
    require(address == OWNER and plausible.include_closure(root, source) == ({SOURCE, 'include/ffta.h'}, [])
            and base_header((root/'include/ffta.h').read_bytes(), ('func_080989AC',))
            and not any(fragment in text for fragment in (chr(92), '??', '%:', chr(0))),
            'movement path requires its reviewed declarations and ordinary header')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text)))
    require(sha256(tokens.encode()).hexdigest() == SOURCE_TOKENS, 'movement path source layout or traversal differs')


def tile_search(rom, ins):
    # R2 is the local descriptor. Only +4,+5 and the result word +8 are
    # observed by the callback. In particular it does not read padding or +0.
    block(ins, 0x080989E0, 'movs r0, #0', 'str r0, [sp, #8]', 'mov r0, sp',
          'strb r6, [r0, #4]', 'strb r5, [r0, #5]')
    block(ins, 0x08098A42, 'movs r1, #0', 'str r1, [sp, #8]', 'mov r1, sb',
          'strb r5, [r1, #4]', 'strb r4, [r1, #5]')
    block(ins, 0x08098A1E, 'mov sb, sp')
    for site, list_register, displacement in ((0x080989EA, 'r1', '0x24'), (0x08098A4C, 'r0', '0x34')):
        block(ins, site, f'ldr r0, [{list_register}, #0x10]', f'ldr r1, [pc, #{displacement}]',
              'mov r2, sp', 'bl #0x80c7cc0', 'ldr r0, [sp, #8]')
    tile_callback(rom)


def tile_callback(rom):
    ops(rom, ITERATOR, 'push {r4, r5, r6, lr}', 'adds r6, r1, #0', 'adds r5, r2, #0',
        'ldr r4, [r0, #4]', 'b #0x80c7ccc', 'ldr r4, [r4, #8]', 'cmp r4, #0',
        'beq #0x80c7cdc', 'adds r0, r4, #0', 'adds r1, r5, #0', 'bl #0x814225c',
        'cmp r0, #0', 'bne #0x80c7cca', 'pop {r4, r5, r6}', 'pop {r0}', 'bx r0')
    ops(rom, 0x0814225C, 'bx r6')
    ops(rom, 0x080C7B74, 'ldr r0, [r0]', 'bx lr')
    ops(rom, CALLBACK, 'push {r4, lr}', 'adds r4, r1, #0', 'bl #0x80c7b74',
        'adds r3, r0, #0', 'movs r0, #4', 'ldrsb r0, [r4, r0]', 'ldr r2, [r3]',
        'adds r1, r2, #0', 'adds r1, #0xf6', 'ldrb r1, [r1]', 'cmp r0, r1', 'bne #0x809abde',
        'movs r1, #5', 'ldrsb r1, [r4, r1]', 'adds r0, r2, #0', 'adds r0, #0xf7',
        'ldrb r0, [r0]', 'cmp r1, r0', 'bne #0x809abde', 'str r3, [r4, #8]',
        'movs r0, #0', 'b #0x809abe0', 'movs r0, #1', 'pop {r4}', 'pop {r1}', 'bx r1')


def original_path(rom, mapping, index):
    import installed_copy_effects as copy
    import iwram_installation_prerequisite as install

    require(word(rom, 0x081492F4) == LAST and word(rom, 0x08149364) == FIRST
            and LAST == FIRST + 4*(CAPACITY-1) and word(rom, 0x08149360) == COPY_SLOT
            and word(rom, COPY_SLOT) == COPY_ENTRY | 1 and word(rom, 0x08148A80) == 0x089A5D3C,
            'original movement buffer or installed copy slot changed')
    ops(rom, VALID+6, 'lsrs r2, r2, #0x14', 'lsrs r1, r1, #0x18', 'adds r2, r2, r1',
        'lsls r1, r2, #3', 'subs r1, r1, r2', 'adds r0, r0, r1', 'ldrb r1, [r0, #2]',
        'movs r0, #0x80', 'ands r0, r1')
    ops(rom, 0x08148A24, 'strb r5, [r4]', 'strb r3, [r4, #1]', 'ldrb r0, [r2]',
        'lsls r0, r0, #0x19', 'lsrs r0, r0, #0x19', 'strb r0, [r4, #2]',
        'strb r6, [r4, #3]', 'subs r4, #4')
    ops(rom, 0x08148A34, 'ldrb r0, [r2, #2]', 'lsls r0, r0, #0x19', 'lsrs r1, r0, #0x19',
        'cmp r1, #0xf', 'beq #0x8148a90')
    ops(rom, 0x08149320, 'adds r0, r5, #0', 'adds r1, r6, #0', 'mov r2, r8', 'adds r3, r7, #0',
        'bl #0x8148a0c', 'adds r4, r0, #0', 'cmp r4, #0', 'bge #0x81492f8')
    ops(rom, 0x08149338, 'ldr r3, [pc, #0x24]', 'movs r1, #0x18', 'subs r1, r1, r4',
        'lsls r1, r1, #2', 'ldr r0, [pc, #0x20]', 'adds r1, r1, r0', 'lsls r2, r4, #2',
        'ldr r3, [r3]', 'mov r0, sb', 'bl #0x8142250', 'adds r0, r4, #0')
    ops(rom, 0x08142250, 'bx r3')
    for start, end, digest in boot.BOOT:
        require(sha256(rom[start-BASE:end-BASE]).hexdigest() == digest, 'original boot installer differs')
    plan = install.verify(rom[0x2768:0x27B8], 0x08002768, rom, mapping, index,
                          selector=install.SELECTOR, call_site=0x08002796, pointer_address=COPY_SLOT)
    require(plan['arguments'] == dict(source=boot.IMAGE, destination=boot.DESTINATION, control=88)
            and plan['source_image']['sha256'] == boot.IMAGE_SHA256 and plan['entry']['pointer_word'] == COPY_ENTRY | 1,
            'movement path requires the original installed copy image')
    image = bytes.fromhex(plan['source_image']['bytes'])
    counts = []
    for steps in range(1, CAPACITY+1):
        size = 4 * steps
        offset = 4 * (CAPACITY - steps)
        effect = copy.verify_conditional(image, boot.DESTINATION, COPY_ENTRY, size, selector=copy.SELECTOR)
        require(effect['conditional_conclusion']['source_read_span'] == [0, size]
                and effect['conditional_conclusion']['destination_write_span'] == [0, size]
                and FIRST+offset == LAST-4*(steps-1), 'path copy span differs from initialized suffix')
        counts.append([steps, offset, size])
    return dict(entry=COPY_ENTRY, image_sha256=boot.IMAGE_SHA256, installer=0x08002796,
                scratch=[FIRST, LAST+4], copies=counts)


def prove(data, address, rom, mapping, index, roles, ins, calls, refinement, words):
    require(address == OWNER and sha256(rom).hexdigest() == ROM_SHA256 and data == rom[0x989AC:0x98A88]
            and len(ins) == 100 and roles == bindings() and calls == {OWNER+k: v for k, v in CALLS.items()}
            and not words, 'movement path requires its exact native extent, callback words and calls')
    entries, rows = indices(mapping, index)
    for start, end in EXTENTS.items():
        row = span_record(start, end, entries, rows, rom)
        if start == OWNER:
            require(row['instrs'] == len(ins), 'movement path instruction index differs')
    for offset, _ in roles['functions']:
        require(word(rom, OWNER+offset) == CALLBACK | 1, 'tile callback literal differs')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #0x10')
    block(ins, 0x080989FC, 'mov r1, r8', 'ldr r0, [r1, #0x3c]', 'ldr r1, [sp, #0x30]',
          'mov r2, sb', 'adds r3, r7, #0', 'bl #0x81492d0', 'cmp r0, #0', 'bgt #0x8098a18',
          'movs r0, #1', 'rsbs r0, r0, #0', 'b #0x8098a72')
    block(ins, 0x08098A18, 'subs r7, r0, #1', 'cmp r7, #0', 'blt #0x8098a70', 'mov sb, sp',
          'lsls r0, r7, #2', 'ldr r1, [sp, #0x30]', 'adds r6, r0, r1',
          'movs r5, #0', 'ldrsb r5, [r6, r5]', 'movs r4, #1', 'ldrsb r4, [r6, r4]')
    block(ins, 0x08098A58, 'movs r1, #1', 'cmp r0, #0', 'beq #0x8098a64', 'cmp r0, r8',
          'beq #0x8098a64', 'movs r1, #0', 'cmp r1, #0', 'bne #0x8098a70', 'subs r6, #4',
          'subs r7, #1', 'cmp r7, #0', 'bge #0x8098a26', 'adds r0, r7, #1', 'add sp, #0x10',
          'pop {r3, r4, r5}', 'mov r8, r3', 'mov sb, r4', 'mov sl, r5', 'pop {r4, r5, r6, r7}',
          'pop {r1}', 'bx r1')
    block(ins, 0x080989CA, 'str r3, [sp, #0xc]', 'ldr r0, [r0, #0x3c]', 'adds r1, r6, #0',
          'adds r2, r5, #0', 'bl #0x8149384', 'cmp r0, #0', 'beq #0x8098a0e')
    block(ins, 0x080989F4, 'ldr r0, [sp, #8]', 'mov sl, r4', 'cmp r0, #0', 'bne #0x8098a0e')
    block(ins, 0x08098A2E, 'mov r0, r8', 'adds r1, r5, #0', 'adds r2, r4, #0',
          'ldr r3, [sp, #0xc]', 'bl #0x8097504', 'cmp r0, #0', 'beq #0x8098a68')
    ops(rom, 0x080975BC, 'bl #0x81493ac', 'lsls r0, r0, #0x18', 'lsrs r0, r0, #0x18',
        'cmp r0, sb', 'bhi #0x80975cc', 'movs r0, #1', 'b #0x80975ce', 'movs r0, #0')
    tile_search(rom, ins)
    for caller in (0x08093826, 0x08096568):
        ops(rom, caller, 'movs r4, #0x92', 'lsls r4, r4, #1', 'add r4, r8', 'str r4, [sp]',
            'bl #0x809a604', 'movs r1, #0xd2', 'lsls r1, r1, #1', 'add r1, r8', 'str r0, [r1]')
    ops(rom, WRAPPER, 'push {r4, lr}', 'sub sp, #4', 'ldr r4, [sp, #0xc]')
    ops(rom, 0x0809A616, 'str r4, [sp]', 'bl #0x80989ac', 'add sp, #4', 'pop {r4}', 'pop {r1}', 'bx r1')
    return dict(schema=named.MOVEMENT_PATH_SCHEMA, instructions=len(ins), calls=roles['calls'], runtime_calls=[],
                partition=graph.partition(data, address, refinement, ins, words), copy=original_path(rom, mapping, index),
                local_query=[-48, -36], range_slot=[-36, -32], saved=[-32, 0], path_argument=5,
                action_state_path=[0x124, 0x1A4], caller_sites=[0x0809382E, 0x08096570, 0x0809A618],
                callbacks=roles['functions'], result='Invalid or occupied destination returns -1. A traced path is '
                'scanned backward for an eligible empty or self-occupied tile; its inclusive prefix length is returned.',
                conditions=['Initialized game movement grid and board, live actor, scene, finite linked list and nodes. '
                            'A destination that reaches the provider has an in-board predecessor chain ending at '
                            'direction 15 with 1 through 24 initialized steps. Unready or malformed grids are outside this premise.',
                            'The installed original copy image remains live, the caller supplies room for the copied records, '
                            'and those records, IWRAM scratch, live game objects and active stack frames are disjoint. '
                            'No concurrent changes. Returning original helpers preserve their callee-saved ABI.'],
                environment=environment_fingerprint())
