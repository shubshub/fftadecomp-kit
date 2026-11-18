"""The installed zero callback followed by two distinct scheduler descriptor sites."""
import hashlib
import struct
from pathlib import Path

SELECTOR = 'conditional-effect-initialized-scheduler-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
OWNER = 0x0810CC44
INITIALIZE = 0x0810CCC6
FIRST = 0x0810CCE2
SECOND = 0x0810CD90
THUNK = 0x0814224C
SCHEDULER = 0x08005B6C


def require(condition, message):
    if not condition:
        raise ValueError(message)


def block(instructions, start, *expected):
    for operation in expected:
        item = instructions.get(start)
        require(item and f'{item.mnemonic} {item.op_str}' == operation,
                f'expected {operation} at {start:08X}')
        start += item.size
    return start


def getter_footprint(proof, entries, rows):
    """R5 holds the second descriptor while its resource getter runs."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    from software_double_profile import span_record
    results = []
    for start, size, count, calls_expected in ((0x080DD4A4, 14, 6, {0x080DD4AA: 0x080A8810}),
                                               (0x080A8810, 32, 16, {})):
        record = span_record(start, start+size, entries, rows, proof.rom)
        require(record['instrs'] == count, 'resource getter index count changed')
        body = proof.span(start)
        ins, _, branches, calls, words = graph.graph(body, start, owner.refine(body, start, proof.mapping))
        require(not branches and not words and calls == calls_expected and len(ins) == count,
                'resource getter nested call or extent differs')
        checked = match.verify_leaf_instructions(body, start, True, calls)
        require({item.address for item in checked} == set(ins) and
                all(match.ARM_REG_R0+5 not in (*item.regs_access()[0], *item.regs_access()[1])
                    for item in checked), 'resource getter observes the R5 descriptor')
        require(block(ins, start, 'push {lr}') == start+2 and
                block(ins, start+size-4, 'pop {r1}', 'bx r1') == start+size and
                all(item.mnemonic not in ('push', 'pop') and match.ARM_REG_SP not in
                    (*item.regs_access()[0], *item.regs_access()[1])
                    for pc, item in ins.items() if pc not in (start, start+size-4)) and
                not any(item.mnemonic.startswith(('str', 'stm')) for item in checked),
                'resource getter stores or reads an unproved stack location')
        results.append(dict(address=start, bytes=size, instructions=count, calls=sorted(calls.values()),
                            saved_lr_below_sp=4, sha256=hashlib.sha256(body).hexdigest()))
    return results


def bind(proof, data, address, ins, edges, calls):
    import scheduler_zero_descriptor as zero
    from software_double_profile import indices, span_record
    require(address == OWNER and len(data) == 408 and len(ins) == 176 and calls.get(INITIALIZE) == THUNK and
            [pc for pc in sorted(calls) if calls[pc] == SCHEDULER] == [FIRST, SECOND],
            'expected the original indexed effect and its initializer and two scheduler calls')
    entries, rows = indices(proof.mapping, proof.index)
    require(span_record(address, address+len(data), entries, rows, proof.rom)['instrs'] == len(ins),
            'effect scheduler requires the original reached instruction count')
    require(struct.unpack_from('<III', data, 0x0810CCF0-address) == (zero.POINTER, 0x159, 0x080E2399) and
            struct.unpack_from('<I', data, 0x0810CDB4-address)[0] == 0x0810CB69,
            'initializer pointer, effect base or child callback literal differs')
    block(ins, 0x0810CCBE, 'ldr r0, [pc, #0x30]', 'ldr r2, [r0]', 'add r0, sp, #8', 'movs r1, #0x1c',
          'bl #0x814224c', 'add r1, sp, #8', 'ldr r0, [pc, #0x24]', 'adds r0, #0xb2',
          'strh r0, [r1, #0x16]', 'movs r0, #0x51', 'strh r0, [r1, #0x18]', 'ldr r0, [r6, #0x20]',
          'str r0, [sp, #0xc]', 'ldr r0, [pc, #0x1c]', 'movs r1, #0x28', 'add r2, sp, #8',
          'mov r3, sb', 'bl #0x8005b6c')
    block(ins, 0x0810CD76, 'add r5, sp, #0x24', 'ldrh r1, [r6]', 'strh r1, [r5, #0x14]',
          'ldr r0, [r6, #0x20]', 'lsls r1, r1, #0x18', 'lsrs r1, r1, #0x18', 'bl #0x80dd4a4',
          'str r0, [r5, #4]', 'ldr r0, [pc, #0x28]', 'movs r1, #0x20', 'adds r2, r5, #0',
          'mov r3, sb', 'bl #0x8005b6c')
    for begin, end in ((0x0810CCBE, FIRST), (0x0810CD76, SECOND)):
        pc = begin
        while pc != end:
            successor = pc + ins[pc].size
            require([source for source, targets in edges.items() if successor in targets] == [pc],
                    'alternate edge bypasses descriptor setup')
            pc = successor
    proof.effect_initializer = zero.initializer(proof.rom, proof.mapping, proof.index)
    proof.effect_getter = getter_footprint(proof, entries, rows)
    # Every other external call, including any extra or changed thunk, is still
    # checked by the ordinary scheduler-site and buffer rules.
    return {pc: target for pc, target in calls.items() if pc != INITIALIZE}


def check_call(proof, site, aliases, stack, slots, constants, words):
    import match
    offset = 8-4*len(stack)
    require(site == INITIALIZE and len(stack)*4 == 92 and aliases == {match.ARM_REG_R0: offset} and
            (constants or {}).get(match.ARM_REG_R1) == 28 and not slots and not words,
            'installed initializer requires exactly the live 28-byte descriptor at SP+8')
    for byte in range(offset, offset+28):
        proof.access(byte, 1, stack)
    proof.initialized_effect_offset = offset
    # The aligned installed body returns R0=entry LR, R1=0 and R2=one past.
    # The authenticated straight-line continuation does not read the latter
    # before 0810CCDE replaces R2 with the original descriptor address.
    return {}


def check_bindings(bindings):
    require(bindings['functions'] == [[180, 'func_080E2398'], [368, 'func_0810CB68']] and
            bindings['data'] == [[172, 'g_callbacks_0836D4B8', 0], [232, 'data_083A2638', 0]] and
            not bindings['switches'] and [row for row in bindings['calls'] if row[1].startswith('_')] ==
            [[130, '_call_via_r2']], 'effect requires the genuine initializer, child and resource bindings')


def manifest(proof, scheduler):
    import match
    first, second = scheduler['observations']
    offset = getattr(proof, 'initialized_effect_offset', None)
    require(first['site'] == FIRST and second['site'] == SECOND and offset is not None and
            first['descriptor_offset'] == offset and second['descriptor_offset'] == offset+28 and
            first['frame_bytes'] == second['frame_bytes'] == 92 and
            first['aliases'] == [(match.ARM_REG_R2, offset)] and
            second['aliases'] == [(match.ARM_REG_R2, offset+28), (match.ARM_REG_R0+5, offset+28)] and
            all(not obs['other_pointer_words'] and not obs['payload_words'] for obs in (first, second)),
            'effect scheduler descriptor offsets, footprints or payloads differ')
    return dict(scheduler, initializer=proof.effect_initializer, initialized_descriptor=[offset, offset+28],
                second_descriptor=[offset+28, offset+56], initializer_site=INITIALIZE,
                one_past_r2_overwrite=0x0810CCDE, post_zero_field_writes=[[22, 2], [24, 2], [4, 4]],
                second_field_writes=[[20, 2], [4, 4]], getter_while_r5_live=proof.effect_getter,
                composition_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
