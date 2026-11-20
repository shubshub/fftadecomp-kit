"""Two-stage battle movement overlay with an original caller and finite board scan."""
from hashlib import sha256
from pathlib import Path
import struct

import known_query_stack_buffer_profile as quotient
import movement_path_prefix as path
import named_data_buffer_profile as named
import owner_graph_profile as graph
import plausible
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles
from known_query_native_closure_profile import environment_fingerprint
from sdk_cpuset_halfword import TOKEN, base_header
from software_double_profile import indices, span_record
from software_float_profile import ROM_SHA256
from unit_equipment_attribute import ops, word

OWNER, END = 0x08098A88, 0x08098BAE
SOURCE = 'src/08098A88.c'
SOURCE_TOKENS = '088eb32f1e818a89bd903b560408a927e23c82fecc565f9e9555d9bc61125d88'
READY, DISPLAY, SETUP = 0x08149368, 0x0801D8B8, 0x0801D938
MOVEMENT, DIV, MARK, SHOW = 0x080CA3EC, 0x08142AB0, 0x0801D624, 0x0801D918
UNIT_RANGE, DRAW, QUADRANT = 0x080CA394, 0x0801D130, 0x0801CF10
CALLS = {16: READY, 24: DISPLAY, 46: DISPLAY, 56: SETUP, 100: MOVEMENT, 106: DIV,
         124: path.ELIGIBLE, 154: path.ITERATOR, 200: path.ITERATOR, 220: MARK, 254: MOVEMENT, 260: DIV, 266: SHOW}
EXTENTS = {
    OWNER: END, READY: 0x08149384, DISPLAY: 0x0801D8E6, SETUP: 0x0801D980,
    MOVEMENT: 0x080CA3FE, UNIT_RANGE: 0x080CA3EC, 0x080C92F0: 0x080C9314,
    MARK: 0x0801D818, DRAW: 0x0801D2B8, QUADRANT: 0x0801D130, SHOW: 0x0801D928,
    0x08141868: 0x0814186C, 0x08099FB0: 0x0809A018,
    **{a: path.EXTENTS[a] for a in (path.ELIGIBLE, path.ITERATOR, path.CALLBACK, 0x080C7B74, 0x0814225C)},
}


def symbol(target):
    return '__udivsi3' if target == DIV else f'func_{target:08X}'


def bindings():
    return dict(calls=[[offset, symbol(target)] for offset, target in CALLS.items()],
                functions=[[272, symbol(path.CALLBACK)]], data=[], switches=[])


def check_source(root, address):
    root = Path(root)
    source = root / SOURCE
    text = source.read_text()
    require(address == OWNER and plausible.include_closure(root, source) == ({SOURCE, 'include/ffta.h'}, [])
            and base_header((root/'include/ffta.h').read_bytes(), ('func_08098A88',))
            and not any(fragment in text for fragment in (chr(92), '??', '%:', chr(0))),
            'movement overlay requires its ordinary C source')
    tokens = ' '.join(TOKEN.findall(plausible.strip_comments_and_strings_keep_strings(text)))
    require(sha256(tokens.encode()).hexdigest() == SOURCE_TOKENS, 'movement overlay C types or state machine differ')


def check_original(image, address, roles, targets):
    expected = {symbol(target): (target, False) for target in {*CALLS.values(), path.CALLBACK}}
    require(address == OWNER and roles == bindings() and targets == expected,
            'overlay requires two compiler quotients, eleven ordinary calls and one tile callback word')
    compiler_symbol_roles(image, targets)
    require(all(not s['size'] for s in image['symbols'] if s['name'] in targets), 'overlay reference has a size')
    require(image['text'][END-OWNER:] == bytes.fromhex('c046'), 'overlay requires external Thumb NOP alignment')


def board_scan(ins):
    block(ins, 0x08098ACC, 'movs r0, #0', 'mov r7, sp', 'lsls r1, r0, #0x18', 'str r1, [sp, #0x14]',
          'adds r0, #1', 'str r0, [sp, #0x10]', 'asrs r2, r1, #0x18', 'str r2, [sp, #0xc]',
          'movs r0, #0', 'mov r8, r0', 'mov sb, r2', 'movs r1, #0xf', 'mov sl, r1')
    block(ins, 0x08098AE6, 'mov r2, r8', 'asrs r4, r2, #0x18', 'ldr r0, [r6]', 'bl #0x80ca3ec',
          'movs r1, #0xa', 'bl #0x8142ab0', 'adds r3, r0, #0', 'lsls r3, r3, #0x18',
          'lsrs r3, r3, #0x18', 'adds r5, r4, #0', 'adds r0, r6, #0', 'adds r1, r5, #0',
          'mov r2, sb', 'bl #0x8097504', 'cmp r0, #0', 'beq #0x8098b68')
    block(ins, 0x08098B0C, 'adds r4, r6, #0', 'adds r4, #0x80', 'ldr r1, [r4]', 'movs r0, #0',
          'str r0, [sp, #8]', 'strb r5, [r7, #4]', 'mov r0, sb', 'strb r0, [r7, #5]',
          'ldr r0, [r1, #0x10]', 'ldr r1, [pc, #0x78]', 'mov r2, sp', 'bl #0x80c7cc0',
          'ldr r0, [sp, #8]', 'movs r1, #1', 'cmp r0, #0', 'beq #0x8098b34',
          'cmp r0, r6', 'beq #0x8098b34', 'movs r1, #0', 'cmp r1, #0', 'beq #0x8098b68')
    block(ins, 0x08098B38, 'mov r2, r8', 'asrs r1, r2, #0x18', 'ldr r2, [r4]', 'movs r0, #0',
          'str r0, [sp, #8]', 'strb r1, [r7, #4]', 'mov r0, sp', 'ldrb r0, [r0, #0xc]',
          'strb r0, [r7, #5]', 'ldr r0, [r2, #0x10]', 'ldr r1, [pc, #0x48]', 'mov r2, sp',
          'bl #0x80c7cc0', 'ldr r0, [sp, #8]', 'cmp r0, #0', 'bne #0x8098b68',
          'mov r1, r8', 'lsrs r0, r1, #0x18', 'ldr r2, [sp, #0x14]', 'lsrs r1, r2, #0x18',
          'movs r2, #1', 'bl #0x801d624')
    block(ins, 0x08098B68, 'movs r0, #0x80', 'lsls r0, r0, #0x11', 'add r8, r0',
          'movs r1, #1', 'rsbs r1, r1, #0', 'add sl, r1', 'mov r2, sl', 'cmp r2, #0',
          'bge #0x8098ae6', 'ldr r0, [sp, #0x10]', 'cmp r0, #0xf', 'ble #0x8098ad0')


def eligibility_result(rom, mapping):
    import owner_admission_profile as owner

    start, end = path.ELIGIBLE, path.EXTENTS[path.ELIGIBLE]
    body = rom[start-path.BASE:end-path.BASE]
    ins, edges, _, _, _ = graph.graph(body, start, owner.refine(body, start, mapping))
    true, false, restore, ret = 0x080975C8, 0x080975CC, 0x080975CE, 0x080975D8
    block(ins, true, 'movs r0, #1', 'b #0x80975ce', 'movs r0, #0', 'pop {r3, r4}',
          'mov r8, r3', 'mov sb, r4', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    # All paths to the sole return enter the preserving epilogue through a
    # full-register MOV. A branch directly into the epilogue would bypass it.
    tail = {true+2, *range(restore, end, 2)}
    entries = {(site, dest) for site, successors in edges.items() for dest in successors
               if site not in tail and dest in tail}
    require({site for site, successors in edges.items() if not successors} == {ret}
            and entries == {(true, true+2), (false, restore)},
            'eligibility result requires a full-word 0 or 1 on every return')
    return dict(callee=start, returns=[ret], definitions=[[true, 1], [false, 0]], caller_test=0x08098B08)


def display_setup(rom, mapping, index):
    import scheduler_zero_descriptor as boot
    # The existing installer proves the zero-entry identity and the byte/word
    # loop. For this distinct aligned 512-byte buffer, replay its word-bound
    # decrement exactly; no tail bytes remain.
    plan = boot.initializer(rom, mapping, index)
    require(word(rom, SETUP+56) == 0x02008168 and word(rom, SETUP+60) == 0x01001000
            and word(rom, SETUP+64) == boot.POINTER and word(rom, boot.POINTER) == boot.DESTINATION | 1,
            'overlay display or original zero slot differs')
    ops(rom, 0x0801D93E, 'ldrh r0, [r4, #8]', 'str r0, [sp]', 'ldr r1, [r4, #0x10]',
        'ldr r2, [pc, #0x2c]', 'mov r0, sp', 'bl #0x8141868', 'ldr r2, [pc, #0x28]',
        'adds r0, r4, #0', 'adds r0, #0x28', 'movs r1, #0x80', 'lsls r1, r1, #2',
        'ldr r2, [r2]', 'bl #0x814224c')
    ops(rom, 0x08141868, 'svc #0xc', 'bx lr')
    ops(rom, 0x0814224C, 'bx r2')
    require((0x02008168+0x28) % 4 == 0 and struct.unpack_from('<5H', rom, boot.IMAGE-path.BASE+0x16) ==
            (0xC201, 0x3904, 0x2903, 0xD8FB, 0x2900), 'installed aligned zero-word loop differs')
    return dict(display=0x02008168, bios_fill_words=0x1000, bios_control=0x01001000,
                cells=[0x02008190, 0x02008390], aligned_word_stores=512//4,
                installed_entry=boot.DESTINATION, installed_image=boot.IMAGE_SHA256, boot_entry=plan['entry'])


def prove(data, address, rom, mapping, index, roles, ins, calls, refinement, words):
    require(address == OWNER and sha256(rom).hexdigest() == ROM_SHA256 and data == rom[OWNER-path.BASE:END-path.BASE]
            and roles == bindings() and len(ins) == 132 and not words
            and calls == {OWNER+offset: target for offset, target in CALLS.items()},
            'movement overlay requires the exact original CFG and relocations')
    entries, rows = indices(mapping, index)
    for start, end in EXTENTS.items():
        row = span_record(start, end, entries, rows, rom)
        if start == OWNER:
            require(row['instrs'] == len(ins), 'movement overlay instruction count differs')
    require(word(rom, OWNER+272) == path.CALLBACK | 1, 'movement overlay callback differs')
    ops(rom, 0x08096992, 'mov r4, r8', 'ldr r0, [r4, #8]', 'bl #0x8098a88', 'cmp r0, #0',
        'bne #0x80969a0', 'b #0x8096b14', 'b #0x8096b00')
    block(ins, OWNER, 'push {r4, r5, r6, r7, lr}', 'mov r7, sl', 'mov r6, sb', 'mov r5, r8',
          'push {r5, r6, r7}', 'sub sp, #0x18', 'adds r6, r0, #0', 'ldr r0, [r6, #0x3c]',
          'bl #0x8149368', 'cmp r0, #0', 'beq #0x8098ac8', 'bl #0x801d8b8',
          'lsls r0, r0, #0x18', 'cmp r0, #0', 'beq #0x8098ac8')
    block(ins, 0x08098AAA, 'ldrb r0, [r6, #0x1a]', 'cmp r0, #0', 'beq #0x8098ab6',
          'cmp r0, #1', 'beq #0x8098acc', 'b #0x8098b9c', 'bl #0x801d8b8', 'lsls r0, r0, #0x18',
          'cmp r0, #0', 'beq #0x8098b9c', 'bl #0x801d938', 'movs r0, #1',
          'strb r0, [r6, #0x1a]', 'movs r0, #0', 'b #0x8098b9e')
    board_scan(ins)
    block(ins, 0x08098B80, 'movs r0, #2', 'strb r0, [r6, #0x1a]', 'ldr r0, [r6]',
          'bl #0x80ca3ec', 'movs r1, #0xa', 'bl #0x8142ab0', 'strb r0, [r6, #0x1b]',
          'bl #0x801d918', 'b #0x8098ac8')
    block(ins, 0x08098B9C, 'movs r0, #1', 'add sp, #0x18', 'pop {r3, r4, r5}',
          'mov r8, r3', 'mov sb, r4', 'mov sl, r5', 'pop {r4, r5, r6, r7}', 'pop {r1}', 'bx r1')
    path.tile_callback(rom)
    ops(rom, MOVEMENT, 'push {lr}', 'bl #0x80ca394', 'adds r1, r0, #0', 'lsls r0, r1, #2',
        'adds r0, r0, r1', 'lsls r0, r0, #1', 'pop {r1}', 'bx r1')
    return dict(schema=named.MOVEMENT_OVERLAY_SCHEMA, instructions=len(ins),
                calls=[v for v in roles['calls'] if v[1] != '__udivsi3'],
                runtime_calls=[v for v in roles['calls'] if v[1] == '__udivsi3'],
                partition=graph.partition(data, address, refinement, ins, words),
                source_range=quotient.quotient_contract(rom, mapping, index), divisor=10,
                eligibility_result=eligibility_result(rom, mapping),
                board=[16, 16], eligibility_calls_per_scan=256, range_queries_per_scan=257,
                local_query=[-56, -44], local_loop=[-44, -32], saved=[-32, 0],
                setup=display_setup(rom, mapping, index), caller=0x08096996,
                conditions=['Original initialized unit, grid, finite object list, board, camera, display renderer, '
                            'tile buffers and BIOS are live. Display setup supplies an aligned 16384-byte writable '
                            'tile destination, disjoint from the 512 display cells and active stack frames.',
                            'The boot-installed IWRAM zero image stays intact. Returning ordinary game helpers '
                            'preserve their saved-register/stack ABI. Tile-rendering geometry and storage are valid '
                            'for each marked tile. No concurrent changes to the board, objects or display.'],
                environment=environment_fingerprint())
