"""Explicit inventory-only MOD with independently proved bounded output calls."""
import argparse
import json
from pathlib import Path

import zero_aware_remainder_ordinary_inventory as ordinary
import zero_aware_remainder_framed_inventory as framed
import zero_aware_remainder_shift_inventory as shift
import zero_aware_remainder_byte_range_inventory as byte_range

SELECTOR = 'zero-aware-remainder-bounded-stack-output-inventory-v1'
SCHEMA = 'thumb-zero-aware-remainder-bounded-stack-output-inventory-v1'
OPERANDS = {ordinary.SELECTOR:ordinary, shift.SELECTOR:shift, byte_range.SELECTOR:byte_range}
bind_calls = ordinary.bind_calls


def prepare(data,address,calls,context):
    if type(context) is not tuple or len(context) != 8 or context[5] != SELECTOR or \
            type(context[7]) is not str or context[7] not in OPERANDS or type(context[6]) is not dict or not context[6]:
        raise ValueError('bounded output requires explicit fresh inventory, operand and call-site selectors')
    outputs = context[6]
    if any(type(site) is not int or type(target) is not int or calls.get(site) != target or
            context[3].get(site) == '__modsi3' for site,target in outputs.items()):
        raise ValueError('bounded output sites differ from centrally bound actual ordinary calls')
    runtime = OPERANDS[context[7]].prepare(data,address,calls,context[:5]+(context[7],))
    context[4].update(schema=SCHEMA,selector=SELECTOR,operand_selector=context[7],
        native_runtime_frames=framed.runtime_frames(context[0],context[1],context[4]),
        marked_output_calls=[[site-address,target] for site,target in sorted(outputs.items())])
    return runtime


def prove_operands(data,address,instructions,edges,sites,observed):
    OPERANDS[observed['operand_selector']].prove_operands(data,address,instructions,edges,sites,observed)


def finish(data,address,calls,context,verified,proof,*,zero_index_profile=None):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refined = owner.refine(data,address,context[1])
    instructions,edges,branches,actual_calls,words = graph.graph(data,address,refined)
    if branches or words or calls != actual_calls or set(instructions) != {item.address for item in verified}:
        raise ValueError('bounded output caller requires its exact complete native CFG')
    if context[3] != bind_calls(calls,context[1],address,len(data),len(context[0])):
        raise ValueError('bounded output final call bindings differ')
    if set(context[6]) != {row[0] for row in proof.call_checks}:
        raise ValueError('bounded output caller did not prove every marked site')
    restored = frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        bounded_output_proof=proof,zero_index_profile=zero_index_profile)
    observed = context[4]
    observed.update(frame=restored,partition=graph.partition(data,address,refined,instructions,words),
        calls=[[site-address,name] for site,name in sorted(context[3].items())],
        ordinary_calls=[[site-address,name] for site,name in sorted(context[3].items()) if name != '__modsi3'],
        runtime_calls=[[site-address,name] for site,name in sorted(context[3].items()) if name == '__modsi3'],
        body_sha256=ordinary.pure.sha(data),mapping_sha256=ordinary.pure.sha(context[1]),
        index_sha256=ordinary.pure.sha(context[2]),ROM_sha256=ordinary.pure.sha(context[0]),
        bounded_output=proof.manifest(),complete_native_proof=True,
        external_call_policy='marked output calls have complete native effect/frame closure; other ordinary calls retain conditional returning-call ABI and reject stack arguments',
        caller_frame_policy='all effect bytes inside allocated locals, disjoint saved slots and other output arguments; SP/r4-r11/entry-LR restored',
        ordinary_call_stack_bound=None,
        maximum_MOD_stack_bytes_below_caller_SP=dict(observed['native_runtime_frames'])[
            ordinary.pure.remainder.ADDRESS]['maximum_additional_stack_bytes'])


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,output_calls,operand_selector,manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('bounded output requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data,address,True,calls,
        bounded_stack_output_inventory_context=(rom,mapping,index,bindings,observed,selector,output_calls,operand_selector))
    if manifest is not None and ordinary.pure.text(manifest) != ordinary.pure.text(observed):
        raise ValueError('bounded output manifest differs from fresh native proof')
    return observed,verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--operand-profile',required=True,choices=tuple(OPERANDS))
    parser.add_argument('--output-call',action='append',required=True,help='exact hexadecimal site:target')
    for name in ('rom','mapping','index'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('address',type=lambda value:int(value,16));args=parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index=args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows=[row for row in json.loads(mapping) if int(row['rom'],16)==args.address]
    if len(rows)!=1:raise ValueError('bounded output requires one exact mapped owner')
    data=rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    _,_,_,calls,_=graph.graph(data,args.address,owner.refine(data,args.address,mapping))
    outputs={}
    for item in args.output_call:
        site,target=(int(value,16) for value in item.split(':'))
        if site in outputs:raise ValueError('duplicate bounded output call site')
        outputs[site]=target
    bindings=bind_calls(calls,mapping,args.address,len(data),len(rom))
    observed,_=verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile,
        output_calls=outputs,operand_selector=args.operand_profile)
    print(ordinary.pure.text(observed))


if __name__=='__main__':main()
