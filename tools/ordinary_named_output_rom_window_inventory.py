"""Default-off named-output inventory with one explicit bounded ROM-read premise."""
import argparse
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_IMM, ARM_OP_MEM, ARM_REG_R0,
    ARM_REG_R1, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR, ARM_REG_PC,
    ARM_CC_AL, ARM_CC_INVALID)
import ordinary_named_output_leaf_only_inventory as leaf

parent, named = leaf.parent, leaf.named
LEAF = leaf.LEAF
SELECTOR = 'ordinary-named-output-rom-window-inventory-v1'
SCHEMA = 'thumb-ordinary-named-output-rom-window-inventory-v1'
WINDOW_SCHEMA = 'thumb-exact-readonly-ROM-byte-window-v1'
NAME, ANCHOR = 'g_table_083A8190', 0x083A8190
START, END = ANCHOR-1, ANCHOR+255
PREMISE = ('conditional: the exact byte interval [0x083A818F,0x083A828F) is initialized '
    'and readable at the proved byte load; g_table_083A8190 binds only the anchor '
    '0x083A8190 and implies no object extent; all loaded values remain unknown')
sha, text = named.sha, named.text


def window_policy():
    return {'schema': WINDOW_SCHEMA, 'symbol': NAME, 'anchor': ANCHOR,
        'start': START, 'end': END, 'readable': True, 'initialized': True, 'readonly': True}


def validate_window(policy, data_mapping, rom):
    expected = window_policy()
    if type(policy) is not dict or set(policy) != set(expected) or any(
            type(policy[key]) is not type(value) or policy[key] != value
            for key, value in expected.items()) or type(data_mapping) is not bytes or type(rom) is not bytes:
        raise ValueError('ROM byte window requires its exact explicit typed readability premise')
    objects = parent.match.parse_data_symbols(data_mapping)
    if objects.get(NAME) != ANCHOR:
        raise ValueError('ROM byte window requires its exact existing anchor name binding')
    if not parent.match.ROM_BASE <= START < END <= parent.match.ROM_BASE+len(rom) or END-START != 256:
        raise ValueError('ROM byte window leaves the immutable ROM snapshot')
    return {'policy': json.loads(text(policy)), 'premise': PREMISE,
        'snapshot_window_sha256': sha(rom[START-parent.match.ROM_BASE:END-parent.match.ROM_BASE]),
        'object_extent_inferred': False, 'loaded_values': 'unknown scalars'}


def literal_roles(data, address, instructions, partition):
    """Authenticate exactly one anchor and one scalar277, each actually PC-loaded."""
    roles = []
    words = partition['words']
    if len(words) != 2 or sorted(word['value'] for word in words) != [277, ANCHOR]:
        raise ValueError('ROM-window caller requires exactly its anchor and scalar277 literal words')
    for word in words:
        if word['switch_word'] or len(word['load_sites']) != 1:
            raise ValueError('ROM-window caller literal lacks exact single reached ownership')
        site = word['load_sites'][0]
        item = instructions[site]; operands = item.operands; raw = bytes(item.bytes)
        encoded = int.from_bytes(raw, 'little')
        destination = ARM_REG_R0+((encoded >> 8) & 7)
        literal = ((site+4) & ~3)+4*(encoded & 255)
        if item.size != 2 or len(raw) != 2 or encoded & 0xF800 != 0x4800 or item.mnemonic != 'ldr' or \
                item.cc not in (ARM_CC_AL, ARM_CC_INVALID) or len(operands) != 2 or \
                operands[0].type != ARM_OP_REG or operands[0].reg != destination or \
                operands[1].type != ARM_OP_MEM or operands[1].mem.base != ARM_REG_PC or \
                operands[1].mem.index or operands[1].mem.disp != 4*(encoded & 255) or \
                item.writeback or operands[1].subtracted or operands[1].shift.type or operands[1].shift.value or \
                literal != word['address'] or literal % 4 or not address <= literal <= address+len(data)-4 or \
                int.from_bytes(data[literal-address:literal-address+4], 'little') != word['value']:
            raise ValueError('ROM-window caller requires exact raw PC-literal load encoding and value')
        roles.append({'site': site, 'address': literal, 'value': word['value'], 'raw': raw.hex(),
            'register': destination-ARM_REG_R0,
            'role': 'named_anchor' if word['value'] == ANCHOR else 'scalar277'})
    return roles


def complete(data, address, rom, mapping, index):
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('ROM-window inventory requires exact immutable typed inputs')
    parent.owner.validate_span(data, address, rom, mapping, index)
    entries, rows = parent.indices.indices(mapping, index)
    record = parent.indices.span_record(address, address+len(data), entries, rows, rom)
    refinement = parent.owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = parent.graph.graph(data, address, refinement)
    if record['instrs'] != len(instructions) or branches or words or refinement['word_switches'] or any(
            item.mnemonic.startswith(('ldm', 'stm')) for item in instructions.values()):
        raise ValueError('ROM-window inventory requires exact closed caller counts without switches or block transfers')
    parent.operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = parent.graph.partition(data, address, refinement, instructions, words)
    roles = literal_roles(data, address, instructions, partition)
    return instructions, edges, calls, partition, roles


def prove_window(instructions, edges, address, calls, roles):
    """All-predecessor transfer for one byte, SUBS1, anchor ADD and byte read.

    Unsigned byte subtraction is 32-bit modular. Zero maps to 0xffffffff,
    then anchor addition maps it to anchor-1. No result or return facts follow.
    """
    if address not in instructions or set(edges) != set(instructions) or set(calls)-set(instructions):
        raise ValueError('ROM-window provenance requires its exact complete CFG')
    predecessors = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            if successor not in instructions:
                raise ValueError('ROM-window CFG edge escapes decoded instructions')
            predecessors[successor].add(site)
    degree = {site: len(before) for site, before in predecessors.items()}
    pending = [site for site in instructions if degree[site] == 0]
    ordered = []
    while pending:
        site = pending.pop(); ordered.append(site)
        for successor in edges[site]:
            degree[successor] -= 1
            if degree[successor] == 0:
                pending.append(successor)
    if len(ordered) != len(instructions) or ordered[0] != address:
        raise ValueError('ROM-window provenance requires an acyclic entry-reachable caller')
    anchor = next(role for role in roles if role['role'] == 'named_anchor')
    outgoing, events, reads = {}, [], []
    for site in ordered:
        before = [outgoing[predecessor] for predecessor in predecessors[site]]
        incoming = ({ARM_REG_R1: ('entryarg1',)} if site == address else
            {reg: fact for reg, fact in before[0].items() if all(state.get(reg) == fact for state in before[1:])})
        state = dict(incoming); item = instructions[site]; raw = bytes(item.bytes)
        encoded = int.from_bytes(raw, 'little'); ops = item.operands
        if site in calls:
            for reg in (ARM_REG_R0, ARM_REG_R1, ARM_REG_R0+2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR):
                state.pop(reg, None)
            outgoing[site] = state
            continue
        _, written = item.regs_access()
        for reg in written:
            state.pop(reg, None)
        narrow = item.size == len(raw) == 2 and item.cc in (ARM_CC_AL, ARM_CC_INVALID)
        transfer = None
        if site == anchor['site']:
            transfer = (ARM_REG_R0+anchor['register'], ('anchor', anchor['address'], site))
        elif narrow and encoded & 0xFFC0 == 0x1C00 and item.mnemonic == 'adds' and len(ops) == 3 and \
                ops[0].type == ops[1].type == ARM_OP_REG and ops[2].type == ARM_OP_IMM and ops[2].imm == 0 and \
                ops[0].reg == ARM_REG_R0+(encoded & 7) and ops[1].reg == ARM_REG_R0+((encoded >> 3) & 7):
            if ops[1].reg in incoming:
                transfer = (ops[0].reg, incoming[ops[1].reg])
        elif narrow and encoded & 0xFF00 == 0x4600 and item.mnemonic == 'mov' and len(ops) == 2 and \
                ops[0].type == ops[1].type == ARM_OP_REG and \
                ops[0].reg == ARM_REG_R0+(encoded & 7)+((encoded >> 4) & 8) and \
                ops[1].reg == ARM_REG_R0+((encoded >> 3) & 15):
            if ops[1].reg in incoming:
                transfer = (ops[0].reg, incoming[ops[1].reg])
        elif narrow and encoded & 0xF800 == 0x7800 and item.mnemonic == 'ldrb' and len(ops) == 2 and \
                ops[0].type == ARM_OP_REG and ops[0].reg == ARM_REG_R0+(encoded & 7) and \
                ops[1].type == ARM_OP_MEM and ops[1].mem.base == ARM_REG_R0+((encoded >> 3) & 7) and \
                not ops[1].mem.index and ops[1].mem.disp == ((encoded >> 6) & 31) and \
                not item.writeback and not ops[1].subtracted and not ops[1].shift.type and not ops[1].shift.value:
            origin = incoming.get(ops[1].mem.base)
            if origin == ('entryarg1',) and ops[1].mem.disp == 3:
                transfer = (ops[0].reg, ('byte', site))
            elif origin is not None and origin[0] == 'window' and ops[1].mem.disp == 0:
                reads.append({'site': site, 'raw': raw.hex(), 'width': 1,
                    'source_byte_load': origin[1], 'subtract_one': origin[2], 'add_anchor': origin[3],
                    'anchor_literal': origin[4], 'anchor_load': origin[5],
                    'byte_values': [0,255], 'modular_subtract_values': [[0,254],[0xffffffff,0xffffffff]],
                    'signed_anchor_offsets': [-1,254], 'addresses': [START, END], 'values': 'unknown'})
            elif origin is not None and origin[0] in ('anchor', 'window'):
                raise ValueError('ROM-window read differs from its exact derived byte address')
        elif narrow and encoded & 0xF8FF == 0x3801 and item.mnemonic == 'subs' and len(ops) == 2 and \
                ops[0].type == ARM_OP_REG and ops[0].reg == ARM_REG_R0+((encoded >> 8) & 7) and \
                ops[1].type == ARM_OP_IMM and ops[1].imm == 1:
            origin = incoming.get(ops[0].reg)
            if origin is not None and origin[0] == 'byte':
                transfer = (ops[0].reg, ('decrement', origin[1], site))
        elif narrow and encoded & 0xFE00 == 0x1800 and item.mnemonic == 'adds' and len(ops) == 3 and \
                all(op.type == ARM_OP_REG for op in ops) and \
                tuple(op.reg for op in ops) == (ARM_REG_R0+(encoded & 7),
                    ARM_REG_R0+((encoded >> 3) & 7), ARM_REG_R0+((encoded >> 6) & 7)):
            first, second = incoming.get(ops[1].reg), incoming.get(ops[2].reg)
            if first is not None and second is not None and first[0] == 'decrement' and second[0] == 'anchor':
                transfer = (ops[0].reg, ('window', first[1], first[2], site, second[1], second[2]))
        if transfer is not None:
            state[transfer[0]] = transfer[1]
            events.append([site, transfer[0]-ARM_REG_R0, list(transfer[1]), raw.hex()])
        # A tracked ROM pointer may only feed the exact byte read, exact ADD,
        # authenticated copy, or an ordinary call whose effects stay conditional.
        for op in ops:
            if op.type == ARM_OP_MEM:
                origin = incoming.get(op.mem.base)
                if origin is not None and origin[0] in ('anchor','window') and not (
                        reads and reads[-1]['site'] == site):
                    raise ValueError('ROM-window pointer has an unsupported memory use or write')
        outgoing[site] = state
    if len(reads) != 1:
        raise ValueError('ROM-window inventory requires one all-path proved modular byte-index read')
    return {'schema': WINDOW_SCHEMA, 'reads': reads, 'origin_transfers': events,
        'all_predecessor_equal_fact_join': True, 'call_clobbers': ['r0','r1','r2','r3','r12','lr'],
        'ordinary_preserved_origins': 'conditional existing callee-saved ABI only',
        'word_bits': 32, 'byte_nonzero_precondition': False, 'loaded_values': 'unknown scalars',
        'object_extent_inferred': False, 'writes_through_proved_window': []}


def bind_calls(calls, mapping, address, size, rom_size):
    return leaf.bind_calls(calls, mapping, address, size, rom_size)


def verify(data, address, rom, mapping, index, data_mapping, calls, bindings, *, selector,
           readonly_named_buffer_policy=None, readonly_rom_window_policy=None, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('ROM-window inventory requires its explicit default-off selector')
    named.validate_named_policy(readonly_named_buffer_policy, data_mapping)
    window = validate_window(readonly_rom_window_policy, data_mapping, rom)
    instructions, edges, actual_calls, partition, roles = complete(data,address,rom,mapping,index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('ROM-window bindings differ from every actual reached ordinary call')
    provenance = prove_window(instructions,edges,address,calls,roles)
    entries, rows = parent.indices.indices(mapping,index)
    start,end,count,digest = LEAF
    record = parent.indices.span_record(start,end,entries,rows,rom)
    body = rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE]
    if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
        raise ValueError('ROM-window complete named helper body identity/count differs')
    sites = {site:target for site,target in calls.items() if target == start}
    proof = named.NamedReadonlyFormalLeafProof(body,start,rom,mapping,index,data_mapping,sites,readonly_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        local_alias_slot_policy=parent.slots.SELECTOR,zero_index_profile=parent.zero_index.SELECTOR,
        formal_stack_callee_proof=proof)
    modules = (leaf,named,parent,parent.analyze,parent.match,parent.thunks,parent.owner,parent.graph,
        parent.operations,parent.indices,parent.frame,parent.slots,parent.zero_index,parent.incoming)
    source = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema':SCHEMA,'selector':SELECTOR,'inventory_only':True,'address':address,
        'end':address+len(data),'instructions':len(instructions),'body_sha256':sha(data),'ROM_sha256':sha(rom),
        'mapping_sha256':sha(mapping),'index_sha256':sha(index),'data_mapping_sha256':sha(data_mapping),
        'calls':[[s,t,bindings[s]] for s,t in sorted(calls.items())],
        'native_edges':[[s,list(targets)] for s,targets in sorted(edges.items())],
        'frame':restored,'partition':partition,'caller_literal_roles':roles,
        'readonly_named_buffer_policy':json.loads(text(readonly_named_buffer_policy)),
        'named_read_premise':named.READ_PREMISE,'readonly_ROM_window':window,'ROM_window_provenance':provenance,
        'ordinary_call_premise':'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise':'the actual arg3 and initialized outgoing words0/4 contain live local pointers; each freshly proved halfword write is discharged into allocated locals outside outgoing and saved words',
        'component_accounting':{'fresh_named_helper_workflows':1,'fresh_helper_frames':1,'fresh_caller_frames':1,
            'helper_store_events':5,'unique_write_footprints':3,'binding_revalidations':1},
        'complete_native_structural_proof':True,'complete_argument_effect_proof':True,
        'source_or_ELF_admission':False,'arithmetic_C_equivalence':False,'numeric_input_preconditions':[],
        'numeric_return_facts':[],'physical_memory_claim':False,'memory_safety_claim':False,
        'nonescape_claim':False,'universal_termination_claim':False,'producer_source_sha256':source,
        'claim':'complete acyclic CFG/partition and reached-return abstract ABI with fresh named-output leaf, explicit independent named-halfword and ROM-byte readability premises, conditional other ordinary ABI'}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('ROM-window manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    for name in ('rom','mapping','index','data-mapping'):
        parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--readonly-named-buffer-policy',required=True,type=json.loads)
    parser.add_argument('--readonly-rom-window-policy',required=True,type=json.loads)
    parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    rom,mapping,index,data_mapping = (args.rom.read_bytes(),args.mapping.read_bytes(),
        args.index.read_bytes(),args.data_mapping.read_bytes())
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:
        raise ValueError('ROM-window inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(rows[0]['end'],16)-parent.match.ROM_BASE]
    _,_,calls,_,_ = complete(data,args.address,rom,mapping,index)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    result,_ = verify(data,args.address,rom,mapping,index,data_mapping,calls,bindings,selector=args.profile,
        readonly_named_buffer_policy=args.readonly_named_buffer_policy,
        readonly_rom_window_policy=args.readonly_rom_window_policy)
    print(text(result))


if __name__ == '__main__':
    main()
