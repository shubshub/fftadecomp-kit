"""Inventory-only zero-aware MOD composed with conditional ordinary call ABI."""
import argparse
import json
from pathlib import Path

import zero_aware_remainder_inventory as pure

SELECTOR = 'zero-aware-remainder-ordinary-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-remainder-ordinary-inventory-v1'
ABI = 'existing conditional structural returning direct-call ABI; r4-r11 and SP preserved'


def bind_calls(calls, mapping, address, size, rom_size):
    """Validate every actual ordinary target centrally before constructing bindings."""
    import match
    import function_thunk_profile as thunks
    entries = json.loads(mapping)
    bindings = {}
    for site, target in sorted(calls.items()):
        if target == pure.remainder.ADDRESS:
            bindings[site] = '__modsi3'
            continue
        if thunks.reserved(target):
            raise ValueError('ordinary remainder inventory excludes reserved call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'],16) == actual)
        end = int(row['end'],16)
        if not actual < end <= match.ROM_BASE+rom_size or \
                actual < address+size and end > address or any(
                    other is not row and int(other['rom'],16) < end and
                    int(other['end'],16) > actual for other in entries):
            raise ValueError('ordinary call requires a unique nonoverlapping mapped target span')
        bindings[site] = name
    if '__modsi3' not in bindings.values() or not any(name != '__modsi3' for name in bindings.values()):
        raise ValueError('ordinary remainder inventory requires actual MOD and ordinary calls')
    return bindings


def prepare(data, address, calls, context):
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR or \
            type(context[3]) is not dict or not context[3] or \
            type(context[4]) is not dict or context[4]:
        raise ValueError('ordinary remainder requires a fresh explicit inventory context')
    rom, mapping, index, bindings, observed, _ = context
    expected = bind_calls(calls, mapping, address, len(data), len(rom))
    if bindings != expected:
        raise ValueError('ordinary remainder call bindings differ from every validated actual site')
    runtime = {site: name for site,name in bindings.items() if name == '__modsi3'}
    pure.prepare(data, address, {site: calls[site] for site in runtime},
        (rom, mapping, index, runtime, observed, pure.SELECTOR))
    observed.update(schema=SCHEMA, selector=SELECTOR,
        ordinary_call_ABI=ABI,
        ordinary_call_premise='conditional: each ordinary callee returns and obeys the existing direct-call ABI',
        call_clobbers=['r0','r1','r2','r3','r12','lr','flags'],
        caller_facts='caller-saved numeric/address facts cleared at every call; no callee result or flags facts')
    return runtime


def prove_operands(data, address, instructions, edges, sites, observed):
    # The existing worklist clears caller-saved facts for EVERY call instruction,
    # including ordinary sites. Only canonical MOD sites require the dividend.
    pure.prove_operands(data, address, instructions, edges, sites, observed)


def finish(data, address, calls, context, verified):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    refinement = owner.refine(data, address, context[1])
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if calls != actual_calls or branches or words or {i.address for i in verified} != set(instructions):
        raise ValueError('ordinary remainder requires its exact closed direct-call inventory')
    bindings = bind_calls(calls, context[1], address, len(data), len(context[0]))
    if context[3] != bindings:
        raise ValueError('ordinary remainder final call bindings differ')
    # Ordinary targets retain precisely the existing conditional structural ABI
    # premise. They are never labelled as complete native callee proofs.
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
    context[4].update(frame=restored,
        partition=graph.partition(data, address, refinement, instructions, words),
        calls=[[site-address, name] for site,name in sorted(bindings.items())],
        ordinary_calls=[[site-address, name] for site,name in sorted(bindings.items()) if name != '__modsi3'],
        runtime_calls=[[site-address, name] for site,name in sorted(bindings.items()) if name == '__modsi3'],
        body_sha256=pure.sha(data), mapping_sha256=pure.sha(context[1]), index_sha256=pure.sha(context[2]),
        ROM_sha256=pure.sha(context[0]), complete_native_proof=True,
        external_call_policy='complete exact canonical MOD closure plus conditional ordinary returning-call ABI')


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('ordinary remainder requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data, address, True, calls,
        remainder_ordinary_inventory_context=(rom,mapping,index,bindings,observed,selector))
    if manifest is not None and pure.text(manifest) != pure.text(observed):
        raise ValueError('ordinary remainder inventory manifest differs from fresh native proof')
    return observed, verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    parser.add_argument('--rom', required=True, type=Path)
    parser.add_argument('--mapping', required=True, type=Path)
    parser.add_argument('--index', required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value,16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index = args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:
        raise ValueError('inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement = owner.refine(data,args.address,mapping)
    _,_,_,calls,_ = graph.graph(data,args.address,refinement)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    manifest,_ = verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(pure.text(manifest))


if __name__ == '__main__':
    main()
