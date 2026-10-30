"""Explicit bounded output inventory plus proven-zero local signed-load indices."""
import argparse
import json
from pathlib import Path

import bounded_stack_output_inventory as bounded
import zero_index_stack_profile as zero

SELECTOR = 'zero-aware-remainder-bounded-output-zero-index-inventory-v1'
SCHEMA = 'thumb-zero-aware-remainder-bounded-output-zero-index-inventory-v1'
bind_calls = bounded.bind_calls
prove_operands = bounded.prove_operands


def prepare(data,address,calls,context):
    if type(context) is not tuple or len(context) != 8 or context[5] != SELECTOR:
        raise ValueError('bounded output zero index requires its explicit fresh inventory context')
    runtime = bounded.prepare(data,address,calls,context[:5]+(bounded.SELECTOR,)+context[6:])
    context[4].update(schema=SCHEMA,selector=SELECTOR,
        local_signed_index_policy='authenticated Thumb LDRSB/LDRSH register-offset loads only, index exact zero on every reaching path')
    return runtime


def finish(data,address,calls,context,verified,proof):
    bounded.finish(data,address,calls,context,verified,proof,zero_index_profile=zero.SELECTOR)
    if not context[4]['frame']['zero_index_signed_loads']:
        raise ValueError('bounded output zero index requires an actual proved local signed indexed load')


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,output_calls,operand_selector,manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('bounded output zero index requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data,address,True,calls,
        bounded_stack_output_zero_index_inventory_context=(rom,mapping,index,bindings,observed,selector,output_calls,operand_selector))
    if manifest is not None and bounded.ordinary.pure.text(manifest) != bounded.ordinary.pure.text(observed):
        raise ValueError('bounded output zero index manifest differs from fresh native proof')
    return observed,verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--operand-profile',required=True,choices=tuple(bounded.OPERANDS))
    parser.add_argument('--output-call',action='append',required=True)
    for name in ('rom','mapping','index'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('address',type=lambda value:int(value,16));args=parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index=args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows=[row for row in json.loads(mapping) if int(row['rom'],16)==args.address]
    if len(rows)!=1:raise ValueError('zero index requires one exact mapped owner')
    data=rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    _,_,_,calls,_=graph.graph(data,args.address,owner.refine(data,args.address,mapping))
    outputs={}
    for item in args.output_call:
        site,target=(int(value,16) for value in item.split(':'))
        if site in outputs:raise ValueError('duplicate bounded output site')
        outputs[site]=target
    bindings=bind_calls(calls,mapping,args.address,len(data),len(rom))
    observed,_=verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile,
        output_calls=outputs,operand_selector=args.operand_profile)
    print(bounded.ordinary.pure.text(observed))


if __name__=='__main__':main()
