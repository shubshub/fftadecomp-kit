"""Scoped tile search using the actor's movement allowance."""
from hashlib import sha256

import movement_overlay as overlay
import movement_path_prefix as path
from ability_range_local_bytes import block, require
from active_entry_shuffle_profile import compiler_symbol_roles

OWNER, END = 0x08099FB0, 0x0809A018
SOURCE = 'src/08099FB0.c'
SOURCE_TOKENS = '2bd4686ef684473aa775bedb915c19f40702cbe3aef9fec8963d37030f787c43'
CALLS = {20: overlay.MOVEMENT, 26: overlay.DIV, 42: path.ELIGIBLE, 72: path.ITERATOR}
CALLERS = (0x0809647E, 0x080C065A, 0x080C4B6E, 0x080C4FA2, 0x080C5246)


def bindings():
    return dict(calls=[[offset, overlay.symbol(target)] for offset, target in CALLS.items()],
                functions=[[100, overlay.symbol(path.CALLBACK)]], data=[], switches=[])


def check_original(image, address, roles, targets):
    expected = {overlay.symbol(target): (target, False) for target in {*CALLS.values(), path.CALLBACK}}
    require(address == OWNER and roles == bindings() and targets == expected and len(image['text']) == END-OWNER,
            'movement tile requires the exact full-width ELF, quotient, calls and callback')
    compiler_symbol_roles(image, targets)
    require(all(not symbol['size'] for symbol in image['symbols'] if symbol['name'] in targets),
            'movement tile references must be undefined, unsized Thumb symbols')


def check_source(root, address):
    path.check_movement_source(root, address, OWNER, SOURCE, SOURCE_TOKENS)


def prove(data, address, rom, mapping, index, roles, ins, calls, refinement, words):
    require(address == OWNER and sha256(rom).hexdigest() == overlay.ROM_SHA256
            and data == rom[OWNER-path.BASE:END-path.BASE] and roles == bindings() and len(ins) == 45
            and not words and calls == {OWNER+offset: target for offset, target in CALLS.items()},
            'movement tile requires its complete original owner and four direct calls')
    entries, rows = overlay.indices(mapping, index)
    owner = overlay.span_record(OWNER, END, entries, rows, rom)
    require(owner['instrs'] == 45, 'movement tile instruction count differs')
    for start in (overlay.MOVEMENT, overlay.UNIT_RANGE, path.ELIGIBLE, path.ITERATOR, path.CALLBACK,
                  0x080C7B74, 0x0814225C):
        overlay.span_record(start, overlay.EXTENTS[start], entries, rows, rom)
    partition = overlay.graph.partition(data, OWNER, refinement, ins, words)
    require(partition['alignment'] == [[0x0809A012, 0x0809A014]]
            and [(row['address'], row['value'], row['load_sites']) for row in partition['words']] ==
            [(0x0809A014, path.CALLBACK | 1, [0x08099FF4])], 'movement tile literal pool differs')
    block(ins, OWNER, 'push {r4, r5, r6, lr}', 'sub sp, #0xc', 'adds r6, r0, #0',
          'adds r4, r1, #0', 'adds r5, r2, #0', 'lsls r4, r4, #0x18', 'asrs r4, r4, #0x18',
          'lsls r5, r5, #0x18', 'asrs r5, r5, #0x18', 'ldr r0, [r6]', 'bl #0x80ca3ec',
          'movs r1, #0xa', 'bl #0x8142ab0', 'adds r3, r0, #0', 'lsls r3, r3, #0x18',
          'lsrs r3, r3, #0x18', 'adds r0, r6, #0', 'adds r1, r4, #0', 'adds r2, r5, #0',
          'bl #0x8097504', 'cmp r0, #0', 'beq #0x809a008', 'adds r0, r6, #0', 'adds r0, #0x80',
          'ldr r1, [r0]', 'movs r0, #0', 'str r0, [sp, #8]', 'mov r0, sp', 'strb r4, [r0, #4]',
          'strb r5, [r0, #5]', 'ldr r0, [r1, #0x10]', 'ldr r1, [pc, #0x1c]', 'mov r2, sp',
          'bl #0x80c7cc0', 'ldr r1, [sp, #8]', 'movs r0, #1', 'cmp r1, #0', 'beq #0x809a00a',
          'cmp r1, r6', 'beq #0x809a00a', 'movs r0, #0', 'add sp, #0xc', 'pop {r4, r5, r6}',
          'pop {r1}', 'bx r1')
    path.tile_callback(rom)
    overlay.ops(rom, overlay.MOVEMENT, 'push {lr}', 'bl #0x80ca394', 'adds r1, r0, #0',
                'lsls r0, r1, #2', 'adds r0, r0, r1', 'lsls r0, r0, #1', 'pop {r1}', 'bx r1')
    for site in CALLERS:
        overlay.ops(rom, site, 'bl #0x8099fb0')
    return dict(schema=overlay.named.MOVEMENT_TILE_SCHEMA, instructions=len(ins), partition=partition,
                calls=[row for row in roles['calls'] if row[1] != '__udivsi3'],
                runtime_calls=[row for row in roles['calls'] if row[1] == '__udivsi3'],
                caller_sites=list(CALLERS), local_query=[-28,-16], saved=[-16,0],
                eligibility_result=overlay.eligibility_result(rom, mapping, caller_test=0x08099FDE),
                quotient=overlay.quotient.quotient_contract(rom, mapping, index), divisor=10,
                conditions=['Initialized actor, unit, grid and finite live object list with stable storage disjoint '
                            'from the active frames. Returning ordinary helpers preserve callee-saved registers.'],
                result='An eligible tile is accepted if the first matching occupant is absent or is the actor.',
                environment=overlay.environment_fingerprint())
