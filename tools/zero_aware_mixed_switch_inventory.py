"""Explicit inventory composition of guarded switches, BYTE and native DIV/MOD."""
import argparse
import json
from pathlib import Path

import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import zero_aware_mixed_runtime_inventory as mixed
import zero_aware_remainder_byte_range_inventory as byte_range
import zero_aware_remainder_ordinary_inventory as ordinary

SELECTOR = 'zero-aware-mixed-byte-switch-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-mixed-byte-switch-inventory-v1'


def bind_calls(calls,mapping,address,size,rom_size):
    """Bind every exact canonical runtime or centrally validated ordinary site."""
    if type(calls) is not dict or any(type(site) is not int or type(target) is not int or
            site % 2 or not address <= site <= address+size-4 for site,target in calls.items()):
        raise ValueError('mixed switch requires exact complete call boundaries')
    runtime = {site:target for site,target in calls.items() if target in mixed.OPERATIONS.values()}
    bindings = mixed.bind_calls(runtime,mapping,address,size,rom_size)
    # The existing ordinary binder supplies target identity, reserved-runtime/
    # thunk exclusions, and unique nonoverlapping complete mapped spans.
    rest = {site:target for site,target in calls.items() if site not in runtime or
        bindings[site] == '__modsi3'}
    bindings.update(ordinary.bind_calls(rest,mapping,address,size,rom_size))
    return dict(sorted(bindings.items()))


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('mixed switch requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data,rom,mapping,index)) or type(address) is not int:
        raise ValueError('mixed switch requires immutable exact ROM and index inputs')
    owner.validate_span(data,address,rom,mapping,index)
    refinement = owner.refine(data,address,mapping)
    instructions,edges,branches,actual_calls,words = graph.graph(data,address,refinement)
    if calls != actual_calls or branches or not refinement['word_switches'] or not words:
        raise ValueError('mixed switch requires its exact guarded word-switch direct-call CFG')
    # Reuse the bounded-output closure's topological criterion. No loop
    # permissions are introduced by composing the existing switch machinery.
    indegree = {site:0 for site in instructions}
    for successors in edges.values():
        for target in successors:indegree[target] += 1
    pending = [site for site in instructions if not indegree[site]]
    reached = 0
    while pending:
        site = pending.pop();reached += 1
        for target in edges[site]:
            indegree[target] -= 1
            if not indegree[target]:pending.append(target)
    if reached != len(instructions):raise ValueError('mixed switch excludes local CFG cycles')
    partition = graph.partition(data,address,refinement,instructions,words)
    operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    expected = bind_calls(calls,mapping,address,len(data),len(rom))
    if type(bindings) is not dict or bindings != expected:
        raise ValueError('mixed switch bindings differ from every actual call')
    runtime = {site:target for site,target in calls.items() if target in mixed.OPERATIONS.values()}
    runtime_bindings = {site:bindings[site] for site in runtime}
    observed = {}
    # The unchanged preparation proves both complete DIV/MOD zero and nonzero
    # closures, their shared zero hook, exact identities and caller ownership.
    mixed.prepare(data,address,runtime,(rom,mapping,index,runtime_bindings,observed,mixed.SELECTOR))
    byte_range.prove_operands(data,address,instructions,edges,runtime,observed)
    # No buffer waiver: local aliases in any caller-clobbered register at ANY
    # call fail. Ordinary callees retain only the existing conditional ABI.
    restored = frame.prove_frame(instructions,edges,address,branches,calls,stack_aliases=True)
    observed.update(schema=SCHEMA,selector=SELECTOR,frame=restored,partition=partition,
        word_switches=refinement['word_switches'],
        instructions=len(instructions),address=address,end=address+len(data),
        calls=[[site-address,name] for site,name in sorted(bindings.items())],
        runtime_calls=[[site-address,name] for site,name in sorted(runtime_bindings.items())],
        ordinary_calls=[[site-address,name] for site,name in sorted(bindings.items()) if site not in runtime],
        ordinary_call_ABI=ordinary.ABI,
        ordinary_call_premise='conditional: each ordinary callee returns and obeys the existing direct-call ABI',
        ordinary_callee_native_proof=False,
        dividend_policy='unchanged BYTE all-path signed16 load/immediate interval at EVERY DIV and MOD site',
        numeric_resource_policy='existing4096 changed proof states; exceeding refuses, never bounds runtime iterations',
        external_call_policy='complete canonical DIV/MOD closures plus conditional ordinary returning-call ABI',
        body_sha256=mixed.remainder.sha(data),mapping_sha256=mixed.remainder.sha(mapping),
        index_sha256=mixed.remainder.sha(index),ROM_sha256=mixed.remainder.sha(rom),complete_native_proof=True)
    if manifest is not None and mixed.remainder.text(manifest) != mixed.remainder.text(observed):
        raise ValueError('mixed switch manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--rom',required=True,type=Path);parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--index',required=True,type=Path);parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    rom,mapping,index = args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:raise ValueError('mixed switch requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'],16)-match.ROM_BASE]
    refinement = owner.refine(data,args.address,mapping)
    _,_,_,calls,_ = graph.graph(data,args.address,refinement)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    observed,_ = verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(mixed.remainder.text(observed))


if __name__ == '__main__':main()
