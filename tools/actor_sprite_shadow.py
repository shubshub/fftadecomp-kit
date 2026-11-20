"""Scoped occupant search and installed shadow-byte update in the actor visitor."""
from hashlib import sha256

import match
import movement_path_prefix as movement
import scene_sprite_visitor as sprite
from software_double_profile import indices, span_record

OWNER, VISIT, SHADOW = sprite.CALLBACK, 0x08097FB6, 0x08097FE6
SPRITE_TABLE, INSTALL_PHASE, INSTALL_CALL = 0x08394040, 0x08023F00, 0x08023F72
PHASE_DIGEST = "6dba691524a6f086deed2dd02b2aefa5419c76f089661ff636f29956789b052d"
TILE_DIGESTS = {
    0x080C7CC0: "47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1",
    0x0809ABB0: "89ac3320654c0bfe88943c26d2aead7a38c6c2710b7d4030704e6a884aa9a1ce",
    0x080C7B74: "a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da",
    0x0814225C: "8726ef5c42206476b80835e7e75d7377ac67a1d964a577f875d20c9dcc98dd97",
}
SOURCE_TOKENS = '6e3ba58068dfede5015e743a95ad9c87d8f18f6fecda413fe0b9f8289983835f'
BINDINGS = dict(calls=[[62, 'func_0808EFCC'], [144, 'func_0809D79C'], [178, 'func_080C7CC0'],
                       [226, '_call_via_r2'], [256, 'func_0808EFCC']],
                functions=[[272, 'func_0809ABB0']], data=[[276, 'data_08394040', 0]], switches=[])
require = sprite.require


def check_source(root):
    movement.check_movement_source(root, OWNER, OWNER, 'src/08097F04.c', SOURCE_TOKENS)


def check_original(image, bindings, targets):
    expected = {name: (int(name[5:], 16), False)
                for role in ('calls', 'functions') for _, name in BINDINGS[role] if name.startswith('func_')}
    expected.update(_call_via_r2=(0x0814224C, False), data_08394040=(SPRITE_TABLE, True))
    require(bindings == BINDINGS and targets == expected,
            'actor shadow requires its exact compiler imports and relocation roles')
    movement.compiler_symbol_roles(image, targets)
    require(all(not symbol['size'] for symbol in image['symbols'] if symbol['name'] in targets),
            'actor shadow compiler import has a size')


def tile_dependencies(proof):
    """Authenticate the iterator, scoped payload callback, accessor and padded R6 thunk."""
    entries, rows = indices(proof.mapping, proof.index)
    dependencies = [span_record(start, movement.EXTENTS[start], entries, rows, proof.rom)
                    for start in TILE_DIGESTS]
    require([entry['instrs'] for entry in dependencies] == [16, 26, 2, 1],
            'actor tile lookup index counts differ')
    for entry, (start, digest) in zip(dependencies, TILE_DIGESTS.items()):
        body = sprite.read(proof.rom, start, movement.EXTENTS[start] - start)
        require(sha256(body).hexdigest() == digest, 'actor tile lookup original dependency changed')
        entry['body_sha256'] = digest
    thunk = 0x0814225C
    spans = [(int(row['rom'], 16), int(row['end'], 16)) for row in entries]
    spans.extend((int(row[0], 16), int(row[1], 16)) for row in rows)
    require(all(start >= thunk+4 or end <= thunk+2 for start, end in spans),
            'actor tile lookup thunk padding overlaps indexed code')
    canonical, = sprite.thunk.dependencies(['_call_via_r6'], proof.rom)
    movement.tile_callback(proof.rom)
    return dependencies, canonical


def tile_lookup(proof, aliases, stack, slots, words):
    r2 = match.ARM_REG_R0 + 2
    require(not proof.active and aliases == {r2: -28} and len(stack) == 7 and not slots and not words
            and proof._thunk_root[:2] == (OWNER, sprite.pinned(proof, OWNER)),
            'actor tile lookup requires its exact root and 12-byte private search at R2')
    for offset, size in ((-24, 1), (-23, 1), (-20, 4)):
        proof.access(offset, size, stack)
    if not hasattr(proof, 'occupant_search'):
        dependencies, canonical = tile_dependencies(proof)
        # R5 is the masked 0x8000 bit. Only its zero arm reaches the initializer.
        movement.ops(proof.rom, 0x08097F46, 'ldr r5, [r4, #0x30]', 'movs r0, #0x80',
                     'lsls r0, r0, #8', 'ands r5, r0', 'cmp r5, #0', 'bne #0x8098008')
        movement.ops(proof.rom, 0x08097F9A, 'ldrh r1, [r4, #8]', 'lsrs r1, r1, #5',
                     'ldrh r2, [r4, #0xc]', 'lsrs r2, r2, #5', 'adds r0, r4, #0',
                     'adds r0, #0x80', 'ldr r3, [r0]', 'str r5, [sp, #8]', 'mov r0, sp',
                     'strb r1, [r0, #4]', 'strb r2, [r0, #5]', 'ldr r0, [r3, #0x10]',
                     'ldr r1, [pc, #0x60]', 'mov r2, sp', 'bl #0x80c7cc0', 'ldr r0, [sp, #8]')
        require(movement.word(proof.rom, 0x08098014) == movement.CALLBACK | 1,
                'actor tile lookup callback literal changed')
        proof.occupant_search = dict(site=VISIT, descriptor=[-28, -16], reads=[[4, 1], [5, 1]],
                                     result=[8, 4], empty_list_R2=-28, dependencies=dependencies,
                                     canonical_thunk=canonical)
        proof.dependencies[movement.ITERATOR] = match.BufferCallProof.span(proof, movement.ITERATOR)
        body = proof.dependencies[movement.ITERATOR]
        proof.records[movement.ITERATOR] = dict(address=movement.ITERATOR, end=movement.ITERATOR+len(body),
                                                bytes=len(body), body_sha256=sha256(body).hexdigest(),
                                                structure=proof.occupant_search, **proof.identities)
    # An empty list preserves the incoming R2. Keep that possible frame pointer live.
    return {r2: -28}


def manifest(proof, data, bindings):
    require(bindings == BINDINGS and data == sprite.pinned(proof, OWNER) and hasattr(proof, 'occupant_search'),
            'actor shadow requires the original ELF bindings, root and scoped tile lookup')
    require(match.parse_data_symbols(proof.objects).get('data_08394040') == SPRITE_TABLE
            and movement.word(proof.rom, 0x08098018) == SPRITE_TABLE,
            'actor shadow requires its original ROM table')
    _, _, _, _, partition = sprite.closure.complete(OWNER, 280, 130, proof.rom, proof.mapping, proof.index)
    require(proof._return_root[2] == {0x08098010}, 'actor shadow has a different normal return')
    movement.ops(proof.rom, 0x08098008, 'movs r0, #1', 'add sp, #0xc', 'pop {r4, r5, r6}',
                 'pop {r1}', 'bx r1')
    image = sprite.sprite_image(proof)
    setter, = [entry for entry in image['entries'] if entry['slot'] == SPRITE_TABLE]
    require((setter['entry'], setter['source'], setter['bytes']) == (0x03006BBD, 0x08A39770, 4),
            'actor shadow setter installation differs')
    phase = match.BufferCallProof.span(proof, INSTALL_PHASE)
    entries, rows = indices(proof.mapping, proof.index)
    span_record(INSTALL_PHASE, 0x08023FCE, entries, rows, proof.rom)
    require(sha256(phase).hexdigest() == PHASE_DIGEST, 'sprite installation phase changed')
    movement.ops(proof.rom, INSTALL_PHASE + 4, 'adds r6, r1, #0', 'ldrb r0, [r6]', 'cmp r0, #2',
                 'beq #0x8023fa0', 'cmp r0, #2', 'bgt #0x8023f1a', 'cmp r0, #0', 'beq #0x8023f20',
                 'cmp r0, #1', 'beq #0x8023f28')
    movement.ops(proof.rom, 0x08023FC4, 'strb r0, [r6]')
    movement.ops(proof.rom, INSTALL_CALL, 'bl #0x808f74c', 'movs r0, #2', 'b #0x8023fc4')
    # ANDS changes R0 only. R1 remains four until SUBS produces signed -2.
    movement.ops(proof.rom, 0x08097FD4, 'ldr r0, [r4, #0x30]', 'movs r1, #4', 'ands r0, r1',
                 'cmp r0, #0', 'bne #0x8098008', 'ldr r2, [pc, #0x38]', 'ldr r0, [r4, #0x58]',
                 'subs r1, #6', 'ldr r2, [r2]', 'bl #0x814224c')
    sprite.pinned(proof, sprite.OWNER)
    movement.ops(proof.rom, 0x0809A4FE, 'ldr r0, [pc, #0x28]', 'str r5, [sp]', 'str r0, [sp, #4]',
                 'ldr r0, [r5, #0x10]', 'ldr r1, [pc, #0x24]', 'mov r2, sp', 'bl #0x80c7cc0')
    require((movement.word(proof.rom, 0x0809A528), movement.word(proof.rom, 0x0809A52C)) ==
            (OWNER | 1, sprite.ADAPTER | 1), 'actor visitor registration differs')
    adapter = sprite.adapter.verify(sprite.ADAPTER, 0x080C7B74, proof.rom, proof.mapping,
                                   proof.index, selector=sprite.adapter.SELECTOR)
    return dict(schema='actor-sprite-shadow-v1', partition=partition, search=proof.occupant_search,
                setter=dict(site=SHADOW, phase=INSTALL_PHASE, phase_body_sha256=PHASE_DIGEST,
                            installation_call=INSTALL_CALL, image=image,
                            target=setter, writes=[[0, 0x16, 1, 0xFE]], return_instruction='bx lr'),
                visitor=dict(registration=0x0809A4FE, adapter=adapter, result=1),
                assumptions=['The CpuSet installer ran and the installed bytes remain intact at the call.',
                             'The actor, scene, list nodes, sprites and projection data have the required '
                             'lifetimes and are separate from active frames. The list is finite and stable.'])
