"""Default-off complete inventory proof for the named halfword r0/r1 output leaf."""
import argparse
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0, ARM_REG_R1,
                          ARM_REG_PC, ARM_CC_AL, ARM_CC_INVALID)
import ordinary_second_formal_output_callees_inventory as second

parent, named = second.parent, second.named
sha, text = second.sha, second.text
SELECTOR = 'formal-r0-r1-named-leaf-inventory-v1'
SCHEMA = 'thumb-formal-r0-r1-named-leaf-inventory-v1'
IDENTITY = (0x0801E6F0, 0x0801E700, 6,
            'ba7fcd94ac95474dc185f09353f3cc26122122112afb4a3819610ffa2580667fb0f')
OUTPUT_SCHEMA = 'thumb-formal-r0-r1-writable-halfwords-v1'
PREMISE = ('conditional: g_state_02007F40+36 and +38 provide initialized readable aligned '
           'halfwords at each reached load; their values remain unknown')
OUTPUT_PREMISE = ('conditional: incoming r0 and r1 designate writable aligned halfwords; '
                  'only their two-byte offset-zero formal footprints are proved; no physical '
                  'extent, separation or nonescape fact follows')


def output_policy():
    return {'schema': OUTPUT_SCHEMA, 'writes': [[0,0,2], [1,0,2]]}


def validate_output(policy):
    expected = output_policy()
    if type(policy) is not dict or set(policy) != set(expected) or \
            type(policy['schema']) is not str or policy['schema'] != OUTPUT_SCHEMA or \
            type(policy['writes']) is not list or len(policy['writes']) != 2 or any(
                type(row) is not list or len(row) != 3 or any(type(v) is not int for v in row)
                for row in policy['writes']) or policy != expected:
        raise ValueError('r0/r1 outputs require their exact explicit writable halfword premise')


def complete(data, address, rom, mapping, index):
    if any(type(value) is not bytes for value in (data,rom,mapping,index)) or type(address) is not int or \
            address != IDENTITY[0] or data != second.exact_body(IDENTITY,rom,mapping,index):
        raise ValueError('r0/r1 leaf requires its exact immutable complete body and dual indexes')
    parent.owner.validate_span(data,address,rom,mapping,index)
    refinement = parent.owner.refine(data,address,mapping)
    instructions,edges,branches,calls,words = parent.graph.graph(data,address,refinement)
    if len(instructions) != 6 or branches or calls or words or refinement['word_switches']:
        raise ValueError('r0/r1 leaf requires its six-instruction call-free CFG')
    parent.operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    partition = parent.graph.partition(data,address,refinement,instructions,words)
    if partition['code_bytes'] != 12 or partition['alignment_bytes'] or \
            partition['literal_and_table_bytes'] != 4 or len(partition['words']) != 1:
        raise ValueError('r0/r1 leaf requires twelve code bytes and one complete literal')
    return instructions,edges,partition


def prove_origins(instructions,edges,address,data,partition):
    literal, = partition['words']
    if literal['address'] != address+12 or literal['value'] != named.GLOBAL or \
            literal['switch_word'] or len(literal['load_sites']) != 1:
        raise ValueError('r0/r1 leaf named literal ownership differs')
    origins = {ARM_REG_R0: ('formal',0), ARM_REG_R1: ('formal',1)}
    reads, stores, loads = [], [], []
    ordered = sorted(instructions)
    for position,site in enumerate(ordered):
        item = instructions[site]
        raw, ops = bytes(item.bytes), item.operands
        encoded = int.from_bytes(raw,'little')
        expected = () if position == 5 else (site+2,)
        if site != address+2*position or item.size != len(raw) or len(raw) != 2 or \
                item.cc not in (ARM_CC_AL,ARM_CC_INVALID) or tuple(edges[site]) != expected:
            raise ValueError('r0/r1 origins require the complete straight-line narrow CFG')
        if item.mnemonic == 'ldr':
            register = ARM_REG_R0+((encoded>>8)&7)
            target = ((site+4)&~3)+4*(encoded&255)
            if encoded & 0xF800 != 0x4800 or len(ops) != 2 or ops[0].type != ARM_OP_REG or \
                    ops[0].reg != register or ops[1].type != ARM_OP_MEM or ops[1].mem.base != ARM_REG_PC or \
                    ops[1].mem.index or ops[1].mem.disp != 4*(encoded&255) or item.writeback or \
                    ops[1].subtracted or ops[1].shift.type or ops[1].shift.value or \
                    target != literal['address'] or literal['load_sites'] != [site] or \
                    int.from_bytes(data[target-address:target-address+4],'little') != named.GLOBAL:
                raise ValueError('r0/r1 leaf requires its exact reached named PC-literal load')
            origins[register] = ('named',named.NAME)
            loads.append([site,target,named.NAME,named.GLOBAL,raw.hex()])
        elif item.mnemonic in ('ldrh','strh'):
            load = item.mnemonic == 'ldrh'
            register, base = ARM_REG_R0+(encoded&7), ARM_REG_R0+((encoded>>3)&7)
            offset = 2*((encoded>>6)&31)
            if encoded & 0xF800 != (0x8800 if load else 0x8000) or len(ops) != 2 or \
                    ops[0].type != ARM_OP_REG or ops[0].reg != register or ops[1].type != ARM_OP_MEM or \
                    ops[1].mem.base != base or ops[1].mem.index or ops[1].mem.disp != offset or \
                    item.writeback or ops[1].subtracted or ops[1].shift.type or ops[1].shift.value:
                raise ValueError('r0/r1 leaf requires exact immediate halfword encodings')
            if load:
                if origins.get(base) != ('named',named.NAME) or offset not in (36,38):
                    raise ValueError('r0/r1 read lacks its exact named origin and halfword offset')
                reads.append([site,named.NAME,offset,2,named.GLOBAL+offset,raw.hex()])
                origins.pop(register,None)
            else:
                origin = origins.get(base)
                if origin not in (('formal',0),('formal',1)) or offset or register in origins:
                    raise ValueError('r0/r1 store lacks its exact formal origin and unknown scalar source')
                stores.append([site,origin[1],0,2,raw.hex()])
        elif item.mnemonic == 'bx' and position == 5 and encoded == 0x4770:
            pass
        else:
            raise ValueError('r0/r1 leaf contains an unsupported operation or return')
    if [[item[2],item[3]] for item in reads] != [[36,2],[38,2]] or \
            [item[1:4] for item in stores] != output_policy()['writes'] or len(loads) != 1:
        raise ValueError('r0/r1 observed reads and writes differ from the explicit footprints')
    return dict(named_reads=reads, store_events=stores, writes=output_policy()['writes'],
                typed_literal_loads=loads, named_writes=[], formal_reads=[], return_argument_facts=[],
                named_loaded_values='unknown scalars', store_event_count=2, unique_write_footprints=2)


def verify(data,address,rom,mapping,index,data_mapping,*,selector,
           readonly_named_buffer_policy=None,formal_output_policy=None,manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('r0/r1 leaf requires its explicit default-off selector')
    second.validate_second_policy(readonly_named_buffer_policy,data_mapping)
    validate_output(formal_output_policy)
    instructions,edges,partition = complete(data,address,rom,mapping,index)
    effects = prove_origins(instructions,edges,address,data,partition)
    restored = parent.frame.prove_frame(instructions,edges,address,{}, {})
    modules = (second,named,parent,parent.analyze,parent.match,parent.thunks,parent.owner,
               parent.graph,parent.operations,parent.indices,parent.frame)
    sources = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    sources[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = dict(schema=SCHEMA,selector=SELECTOR,inventory_only=True,address=address,end=address+len(data),
        instructions=len(instructions),body_sha256=sha(data),ROM_sha256=sha(rom),mapping_sha256=sha(mapping),
        index_sha256=sha(index),data_mapping_sha256=sha(data_mapping),partition=partition,frame=restored,
        native_edges=[[site,list(targets)] for site,targets in sorted(edges.items())],effects=effects,
        readonly_named_buffer_policy=json.loads(text(readonly_named_buffer_policy)),named_read_premise=PREMISE,
        formal_output_policy=json.loads(text(formal_output_policy)),formal_output_premise=OUTPUT_PREMISE,
        complete_native_structural_proof=True,complete_formal_effect_proof=True,source_or_ELF_admission=False,
        arithmetic_C_equivalence=False,numeric_input_preconditions=[],numeric_return_facts=[],
        physical_memory_claim=False,memory_safety_claim=False,nonescape_claim=False,
        universal_termination_claim=False,caller_pointer_discharge=False,producer_source_sha256=sources)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('r0/r1 manifest differs from the fresh native workflow')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    for name in ('rom','mapping','index','data-mapping'):
        parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--readonly-named-buffer-policy',required=True,type=json.loads)
    parser.add_argument('--formal-output-policy',required=True,type=json.loads)
    args = parser.parse_args()
    rom,mapping,index,data_mapping = (args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes(),args.data_mapping.read_bytes())
    start,end,_,_ = IDENTITY
    result,_ = verify(rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE],start,rom,mapping,index,data_mapping,
        selector=args.profile,readonly_named_buffer_policy=args.readonly_named_buffer_policy,
        formal_output_policy=args.formal_output_policy)
    print(text(result))


if __name__ == '__main__':
    main()
