"""Replay incoming word ownership for the USA resource-state initializer."""
import hashlib
import json
import struct
from pathlib import Path

from capstone.arm import ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_R0, ARM_REG_SP

import analyze
import installed_zero_effects as zero
import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
import scheduler_zero_descriptor as installed
from effect_scheduler_initializer import block
from software_double_profile import indices, span_record
from transfer_mask_argument import predecessors, references_at

ROOT = 0x08021618
GETTER = 0x08021004
PAIR = 0x08021C84
CLEAR = 0x0802167E
CALLERS = {
    0x0802995C: (0x08029A04,), 0x08029C34: (0x08029CAC,), 0x08029CD8: (0x08029D06,),
    0x0802C0E0: (0x0802C144,), 0x0805C594: (0x0805C8D8,),
    0x0805CA7C: (0x0805CB1A, 0x0805CCDC, 0x0805CEBC),
    0x080717CC: (0x0807183A,), 0x080888B4: (0x0808899A, 0x080889F6, 0x08088AFE,),
    0x080975DC: (0x08097686,), 0x08097704: (0x08097758,),
    0x0809836C: (0x080988DC, 0x08098962), 0x081295C8: (0x08129C4E, 0x08129CBE),
    0x08129D90: (0x08129F46,),
}
CALLS = {
    0x0802162C: GETTER, 0x08021650: PAIR, 0x0802165C: 0x08021C90,
    0x08021670: 0x08007138, CLEAR: installed.THUNK, 0x08021686: 0x080C7A74,
    0x0802168E: 0x080C7A74, 0x0802169C: PAIR,
}
READS = {0x080216C8: (0, 0), 0x080216CE: (1, 4)}
require = installed.require


def frame_layouts(ins, edges, entry):
    """Distinguish newly allocated outgoing words from every callee-save slot."""
    todo = [(entry, ())]
    states = {}
    while todo:
        pc, frame = todo.pop()
        if pc in states:
            require(states[pc] == frame, 'caller frame differs at join')
            continue
        states[pc] = frame
        item = ins[pc]
        ops = item.operands
        if item.mnemonic == 'push':
            frame = ('saved',) * len(ops) + frame
        elif item.mnemonic == 'pop':
            require(frame[:len(ops)] == ('saved',) * len(ops), 'invalid caller pop')
            frame = frame[len(ops):]
        elif item.mnemonic in ('sub', 'add') and ops[0].type == ARM_OP_REG and ops[0].reg == ARM_REG_SP:
            require(ops[-1].type == ARM_OP_IMM and ops[-1].imm > 0 and ops[-1].imm % 4 == 0,
                    'dynamic caller frame')
            count = ops[-1].imm // 4
            if item.mnemonic == 'sub':
                frame = ('local',) * count + frame
            else:
                require(frame[:count] == ('local',) * count, 'caller adjustment crosses a save')
                frame = frame[count:]
        else:
            require(ARM_REG_SP not in item.regs_access()[1], 'untracked caller SP write')
        todo.extend((successor, frame) for successor in edges[pc])
    return states


def argument_stores(ins, pred, states, site):
    frame = states[site]
    require(frame[:3] == ('local',) * 3, 'three private outgoing words required')
    current = site
    seen = set()
    stores = {}
    while len(stores) < 3:
        require(current not in seen and len(pred[current]) == 1,
                'incoming argument writes must dominate the call through a single basic block')
        seen.add(current)
        current, = pred[current]
        item = ins[current]
        require(states[current] == frame and item.mnemonic not in ('bl', 'blx'), 'intervening call or frame')
        if item.mnemonic.startswith(('str', 'stm')) or item.mnemonic == 'push':
            ops = item.operands
            require(item.mnemonic == 'str' and ops[-1].type == ARM_OP_MEM and
                    ops[-1].mem.base == ARM_REG_SP and not ops[-1].mem.index and
                    ops[-1].mem.disp >= 0 and ops[-1].mem.disp % 4 == 0,
                    'intervening unproved write to outgoing arguments')
            if ops[-1].mem.disp in (0, 4, 8):
                stores.setdefault(ops[-1].mem.disp, (current, item.reg_name(ops[0].reg)))
    return dict(site=site, depth=4 * len(frame), stores=[[off, *stores[off]] for off in (0, 4, 8)])


def scalar_definitions(ins, pred, states, entry, use, register, slot=None):
    """Collect the reaching native writes, including caller-local words reloaded for a store."""
    pending = list(pred[use])
    visited = set()
    definitions = {}
    while pending:
        pc = pending.pop()
        if pc in visited:
            continue
        visited.add(pc)
        item = ins[pc]
        ops = item.operands
        if slot is None:
            require(item.mnemonic not in ('bl', 'blx') or register not in match.CALLER_CLOBBERED,
                    'argument value has no defined result across an intervening call')
            if register in item.regs_access()[1]:
                require(item.mnemonic.startswith(('ldr', 'add', 'mov', 'asr', 'lsl', 'lsr')),
                        'unproved argument register producer')
                record = dict(site=pc, instruction=f'{item.mnemonic} {item.op_str}')
                if item.mnemonic.startswith('ldr') and ops[-1].type == ARM_OP_MEM and ops[-1].mem.base == ARM_REG_SP:
                    require(item.mnemonic == 'ldr' and not ops[-1].mem.index and ops[-1].mem.disp % 4 == 0,
                            'source caller-local word must be aligned and directly addressed')
                    location = -4 * len(states[pc]) + ops[-1].mem.disp
                    require(location < 0, 'source is not a caller-local word')
                    record['local_writes'] = scalar_definitions(ins, pred, states, entry, pc, None, location)
                definitions[pc] = record
                continue
        elif item.mnemonic.startswith('str') and ops[-1].type == ARM_OP_MEM and ops[-1].mem.base == ARM_REG_SP:
            target = ops[-1].mem.disp - 4 * len(states[pc])
            width = {'str': 4, 'strh': 2, 'strb': 1}.get(item.mnemonic)
            require(width and not ops[-1].mem.index, 'unproved caller-local store')
            if target < slot + 4 and target + width > slot:
                require(target == slot and width == 4, 'partial caller-local initialization')
                definitions[pc] = dict(site=pc, instruction=f'{item.mnemonic} {item.op_str}')
                continue
        require(pc != entry, 'argument may be reloaded without a reaching initialization')
        pending.extend(pred[pc])
    require(definitions, 'argument has no reaching definition')
    return [definitions[pc] for pc in sorted(definitions)]


def caller_record(buffers, rows, address, sites):
    end = int(next(row["end"] for row in rows if int(row["rom"], 16) == address), 16)
    body = buffers.rom[address-match.ROM_BASE:end-match.ROM_BASE]
    named.validate_owner(body, address, buffers.rom, buffers.mapping, buffers.index)
    options = {'one_object_word_switch': True} if address == 0x0802995C else {}
    refined = analyze.refine_function(body, address, rows, max_bytes=len(body), max_instructions=len(body)//2,
        rom_end=match.ROM_BASE + len(buffers.rom), same_owner_long_branches=True, **options)
    ins, edges, _, calls, _ = graph.graph(body, address, refined, **options)
    require({pc for pc, dest in calls.items() if dest == ROOT} == set(sites), 'caller BL set differs')
    pred = predecessors(edges)
    states = frame_layouts(ins, edges, address)
    records = [argument_stores(ins, pred, states, site) for site in sites]
    for record in records:
        record['sources'] = [scalar_definitions(ins, pred, states, address, store, ins[store].operands[0].reg)
                             for _, store, _ in record['stores']]
    return dict(address=address, end=address+len(body), instructions=len(ins),
                sha256=hashlib.sha256(body).hexdigest(),
                sites=records)


def checked_block(ins, pred, start, *ops):
    end = block(ins, start, *ops)
    pc = start
    while pc + ins[pc].size < end:
        child = pc + ins[pc].size
        require(pred[child] == {pc}, 'alternate entry bypasses the checked instruction')
        pc = child
    return end


def resource_getter(buffers, rows):
    body = buffers.rom[GETTER-match.ROM_BASE:GETTER-match.ROM_BASE+62]
    named.validate_owner(body, GETTER, buffers.rom, buffers.mapping, buffers.index)
    ref = analyze.refine_function(body, GETTER, rows, max_bytes=len(body), max_instructions=len(body)//2,
                                  rom_end=match.ROM_BASE+len(buffers.rom), same_owner_long_branches=True)
    ins, edges, branches, calls, words = graph.graph(body, GETTER, ref)
    require(not branches and not calls and not words and len(ins) == 29 and len(body) == 62 and
            struct.unpack_from('<I', body, 0x28)[0] == 0x08390E44 and
            match.parse_data_symbols(buffers.objects).get('g_table_08390E44') == 0x08390E44,
            'resource lookup requires its genuine category table and exact indexed leaf')
    graph.partition(body, GETTER, ref, ins, words)
    match.verify_leaf_instructions(body, GETTER, True)
    block(ins, GETTER, 'push {lr}', 'adds r2, r1, #0', 'ldr r1, [pc, #0x20]', 'lsls r0, r0, #2',
          'adds r0, r0, r1', 'ldr r3, [r0]', 'movs r0, #3', 'ands r0, r2', 'cmp r0, #2',
          'bgt #0x8021030', 'cmp r0, #1', 'blt #0x8021030')
    group = ('movs r1, #4', 'rsbs r1, r1, #0', 'ands r1, r2', 'lsls r0, r1, #1',
             'adds r0, r0, r1', 'lsls r0, r0, #1')
    block(ins, 0x0802101C, *group, 'adds r0, #0xc', 'b #0x802103c')
    block(ins, 0x08021030, *group, 'adds r0, r3, r0', 'pop {r1}', 'bx r1')
    table = 0x08390E44
    next_table = 0x08391224
    require(match.parse_data_symbols(buffers.objects).get('data_08391224') == next_table,
            'resource category table needs the independently named next object')
    neighbor = 0x08021054
    next_getter = buffers.rom[neighbor-match.ROM_BASE:neighbor-match.ROM_BASE+16]
    named.validate_owner(next_getter, neighbor, buffers.rom, buffers.mapping, buffers.index)
    checked = match.verify_leaf_instructions(next_getter, neighbor, True)
    block({item.address: item for item in checked}, neighbor, 'ldr r1, [pc, #8]', 'lsls r0, r0, #1',
          'adds r0, r0, r1', 'ldrh r0, [r0]', 'bx lr')
    require(len(checked) == 5 and struct.unpack_from('<I', next_getter, 12)[0] == next_table,
            'the following halfword object must have its own genuine native lookup')
    categories = struct.unpack_from('<248I', buffers.rom, table - match.ROM_BASE)
    starts = sorted(set(categories))
    require(list(categories) == sorted(categories) and starts[0] == 0x0836DAA4 and
            all(start % 4 == 0 and (end-start) % 24 == 0 and start < end <= table
                for start, end in zip(starts, starts[1:]+[table])), 'unexpected resource subtable layout')
    pointers = [value for (value,) in struct.iter_unpack('<I', buffers.rom[starts[0]-match.ROM_BASE:table-match.ROM_BASE])]
    require(all(value == 0 or value % 4 == 0 and match.ROM_BASE <= value <= match.ROM_BASE + len(buffers.rom)-4
                for value in pointers), 'resource list contains a misaligned or unreadable descriptor')
    limits = dict(zip(starts, starts[1:]+[table]))
    return dict(address=GETTER, table=table, category_count=len(categories), distinct_subtables=len(starts),
                words_per_category=[(limits[start]-start)//4 for start in categories],
                pointer_words=len(pointers), present=sum(value != 0 for value in pointers),
                next_object=next_table, next_object_reader=neighbor,
                index_contract='0 <= category < 248 and offset/4 + index is within that category without unsigned wrap',
                category_stride=4, group_mask=0xFFFFFFFC,
                group_scale=6, variant_extra=[0,12,12,0], sha256=hashlib.sha256(body).hexdigest())


def clear_effect(buffers):
    installation = installed.initializer(buffers.rom, buffers.mapping, buffers.index)
    image_offset = installed.IMAGE - match.ROM_BASE
    payload = buffers.rom[image_offset:image_offset+installation['copy_plan']['bytes']]
    effect = zero.verify_conditional(payload, installed.DESTINATION, installed.DESTINATION, 72, selector=zero.SELECTOR)
    require(effect['image_sha256'] == installed.IMAGE_SHA256 and len(effect['cases']) == 4 and
            all(case['SP_restored'] and case['protected_return'] for case in effect['cases']),
            'allocator clear requires the installed image and all destination alignments')
    return dict(boot=installation['boot'], installer=installation['installer'], copy_plan=installation['copy_plan'],
                installed_entry=installation['entry'], bios_call=installation['bios_call'],
                wrapper=installation['wrapper'], site=CLEAR, **effect)


class ResourceArguments:
    def __init__(self, buffers, data, address, ins, edges, calls, bindings):
        expected = [[pc-ROOT, '_call_via_r2' if pc == CLEAR else f'func_{target:08X}']
                    for pc, target in sorted(CALLS.items())]
        require(address == ROOT and len(data) == 224 and len(ins) == 102 and calls == CALLS and
                bindings == dict(calls=expected, functions=[], switches=[], data=[[220,'g_callbacks_0836D4B8',0]]) and
                struct.unpack_from('<I', data, 220)[0] == installed.POINTER,
                'expected the exact resource owner, its eight calls and its installed entry table')
        ent, text = indices(buffers.mapping, buffers.index)
        require(span_record(ROOT, ROOT+len(data), ent, text, buffers.rom)['instrs'] == 102,
                'resource initializer requires the genuine reached instruction count')
        pred = predecessors(edges)
        checked_block(ins, pred, ROOT, 'push {r4, r5, r6, r7, lr}', 'mov r7, sb', 'mov r6, r8',
                      'push {r6, r7}', 'adds r6, r0, #0', 'adds r4, r1, #0', 'adds r5, r2, #0',
                      'adds r7, r3, #0', 'ldr r0, [sp, #0x1c]', 'ldr r1, [sp, #0x20]', 'bl #0x8021004',
                      'mov sb, r0', 'ldr r1, [sp, #0x24]', 'lsls r0, r1, #2', 'add r0, sb',
                      'ldr r0, [r0]', 'cmp r0, #0', 'bne #0x8021644')
        checked_block(ins, pred, 0x0802166A, 'ldr r5, [r6, #8]', 'ldr r0, [r5]', 'movs r1, #0x48',
                      'bl #0x8007138', 'adds r4, r0, #0', 'ldr r0, [pc, #0x7c]', 'ldr r2, [r0]',
                      'adds r0, r4, #0', 'movs r1, #0x48', 'bl #0x814224c')
        checked_block(ins, pred, 0x080216A0, 'ldr r1, [sp, #0x24]', 'lsls r0, r1, #2', 'add r0, sb', 'ldr r1, [r0]')
        checked_block(ins, pred, 0x080216C8, 'mov r0, sp', 'ldrh r0, [r0, #0x1c]', 'strh r0, [r4, #6]',
                      'mov r1, sp', 'ldrh r1, [r1, #0x20]', 'strh r1, [r4, #8]', 'movs r0, #3',
                      'ldr r1, [sp, #0x20]', 'ands r0, r1')
        rows = json.loads(buffers.mapping)
        self.data = data
        self.buffers = buffers
        self.reads = set()
        self.references = references_at(buffers.rom, ROOT, CALLERS)
        self.callers = [caller_record(buffers, rows, caller, sites) for caller, sites in CALLERS.items()]
        pair = buffers.rom[PAIR-match.ROM_BASE:PAIR-match.ROM_BASE+6]
        named.validate_owner(pair, PAIR, buffers.rom, buffers.mapping, buffers.index)
        items = match.verify_leaf_instructions(pair, PAIR, True)
        block({item.address: item for item in items}, PAIR,
              'strh r1, [r0, #0x12]', 'strh r2, [r0, #0x16]', 'bx lr')
        checked_block(ins, pred, 0x08021692, 'mov r0, r8', 'lsls r1, r0, #0x10',
                      'lsrs r1, r1, #0x10', 'adds r0, r4, #0', 'adds r2, r7, #0', 'bl #0x8021c84')
        self.getter = resource_getter(buffers, rows)
        self.clear = clear_effect(buffers)

    def read(self, instruction, depth):
        if instruction.address not in READS:
            return None
        reg, offset = READS[instruction.address]
        require(depth == 7 and instruction.mnemonic == 'mov' and instruction.op_str == f'r{reg}, sp',
                'incoming halfword requires the intact seven-word save frame')
        self.reads.add(instruction.address)
        return ARM_REG_R0+reg, offset, 2

    def manifest(self):
        require(self.reads == set(READS), 'both incoming reads must be replayed')
        return dict(references=self.references, callers=self.callers, lookup=self.getter, clear=self.clear,
                    verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    field_setter=dict(address=PAIR, byte_offsets=[18,22], widths=[2,2],
                                      first_explicitly_narrowed_at=0x08021694, third_argument_from_saved_r3=0x0802169A),
                    incoming_halfwords=[[site, offset, 2] for site, (_, offset) in READS.items()],
                    contract='Ordinary returning ARM ABI and aligned initialized argument words. '
                             'Unenumerated computed or external callers must supply the same seven arguments. '
                             'Category, selector and index must select readable table and record storage. '
                             'Owner, lists, optional existing state, successful allocation, and resource objects '
                             'are valid, distinct from active frames, and stable across the helper calls. '
                             'Installation and memory permissions remain conditional as recorded in clear.')
