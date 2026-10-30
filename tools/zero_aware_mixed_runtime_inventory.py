"""Inventory-only exact zero-aware DIV/MOD closures with bounded shift inputs."""
import argparse
import json
from pathlib import Path

import divsi3_profile as quotient
import zero_aware_remainder_inventory as remainder
import zero_aware_remainder_shift_inventory as shift

SELECTOR = 'zero-aware-mixed-shift-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-mixed-shift-inventory-v1'
OPERATIONS = {'__divsi3':quotient.ADDRESS,'__modsi3':remainder.remainder.ADDRESS}
prove_operands = shift.prove_operands


def bind_calls(calls,mapping,address,size,rom_size):
    if type(calls) is not dict or set(calls.values()) != set(OPERATIONS.values()) or any(
            type(site) is not int or not address <= site <= address+size-4 or site % 2
            for site in calls):
        raise ValueError('zero-aware mixed inventory requires every call to be actual canonical DIV or MOD, including both')
    return {site:next(name for name,value in OPERATIONS.items() if target == value)
        for site,target in sorted(calls.items())}


def prepare(data,address,calls,context):
    import software_double_profile as canonical
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR or \
            type(context[3]) is not dict or type(context[4]) is not dict or context[4]:
        raise ValueError('zero-aware mixed inventory requires a fresh explicit context')
    rom,mapping,index,bindings,observed,_ = context
    if bindings != bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('zero-aware mixed runtime bindings differ from every actual call')
    div = {site:name for site,name in bindings.items() if name == '__divsi3'}
    mod = {site:name for site,name in bindings.items() if name == '__modsi3'}
    remainder.prepare(data,address,{site:calls[site] for site in mod},
        (rom,mapping,index,mod,observed,remainder.SELECTOR))
    quotient.verify_context(data,address,calls,(rom,mapping,div,{}))
    closure = canonical.prove_division_closure(rom,mapping,index)
    zero = 0x0814274C
    if set(closure) != {quotient.ADDRESS,zero} or any(
            proof['writes'] or proof['stack_reads'] for proof in closure.values()) or \
            set(closure[quotient.ADDRESS]['returns']) != {0x0814273E,0x08142748}:
        raise ValueError('zero-aware mixed inventory requires both complete native DIV cases')
    existing = dict(observed['native_runtime_closure'])
    if closure[zero] != existing[zero]:
        raise ValueError('zero-aware mixed runtimes require the same exact zero-hook proof')
    expected = ((0x081426B8,'0029'),(0x081426BA,'41d0'),(0x08142740,'00b5'),
        (0x08142742,'00f003f8'),(zero,'f746'),(0x08142746,'0020'),(0x08142748,'00bd'))
    for site,encoded in expected:
        raw = bytes.fromhex(encoded)
        if rom[site-0x08000000:site-0x08000000+len(raw)] != raw:
            raise ValueError('zero-aware mixed inventory exact DIV entry-to-zero trace differs')
    mod_cases = observed['runtime_cases']
    existing.update(closure)
    observed.update(schema=SCHEMA,selector=SELECTOR,
        dependencies={'quotient':[list(row) for row in canonical.DIVISION_IDENTITIES],
            'remainder':[list(row) for row in remainder.remainder.IDENTITIES]},
        native_runtime_closure=[[site,proof] for site,proof in sorted(existing.items())],
        runtime_cases={'remainder':mod_cases,'quotient':{
            'nonzero':{'component':canonical.DIVISION_RUNTIME,'operands':'exact target entry-register state'},
            'zero':{'guard':'entry r1 == 0','return_r0':0,'maximum_frame_bytes':4,
                'preserved':'r4-r11,sp,entry-lr',
                'trace':[[site,remainder.sha(bytes.fromhex(encoded))] for site,encoded in expected]}}},
        dividend_policy='existing exact ASR16..32 or LSR17..32 signed16 proof at EVERY DIV and MOD site',
        call_clobbers=['r0','r1','r2','r3','r12','lr','flags'],
        caller_facts='every call kills caller-saved facts; no runtime result or flags fact inferred',
        ordinary_calls=[],external_call_policy='complete exact native DIV and MOD closures only')
    return mod


def finish(data,address,calls,context,verified):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm_const import ARM_REG_R4,ARM_REG_R11
    refinement = owner.refine(data,address,context[1])
    instructions,edges,branches,actual_calls,words = graph.graph(data,address,refinement)
    if calls != actual_calls or branches or words or {i.address for i in verified} != set(instructions) or \
            context[3] != bind_calls(calls,context[1],address,len(data),len(context[0])):
        raise ValueError('zero-aware mixed inventory requires its exact closed canonical-call CFG')
    # prepare has freshly proved every canonical target preserves each of these
    # registers, SP and entry LR on every zero/nonzero return alternative.
    preserved = frozenset(range(ARM_REG_R4,ARM_REG_R11+1))
    restored = frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        call_preservation={site:preserved for site in calls})
    context[4].update(frame=restored,partition=graph.partition(data,address,refinement,instructions,words),
        calls=[[site-address,name] for site,name in sorted(context[3].items())],
        runtime_calls=[[site-address,name] for site,name in sorted(context[3].items())],
        body_sha256=remainder.sha(data),mapping_sha256=remainder.sha(context[1]),
        index_sha256=remainder.sha(context[2]),ROM_sha256=remainder.sha(context[0]),complete_native_proof=True)


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None):
    import match
    if selector != SELECTOR:raise ValueError('zero-aware mixed inventory requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data,address,True,calls,
        zero_aware_mixed_inventory_context=(rom,mapping,index,bindings,observed,selector))
    if manifest is not None and remainder.text(manifest) != remainder.text(observed):
        raise ValueError('zero-aware mixed inventory manifest differs from fresh native proof')
    return observed,verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--rom',required=True,type=Path);parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--index',required=True,type=Path);parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index = args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:raise ValueError('inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement = owner.refine(data,args.address,mapping)
    _,_,_,calls,_ = graph.graph(data,args.address,refinement)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    manifest,_ = verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(remainder.text(manifest))


if __name__ == '__main__':main()
