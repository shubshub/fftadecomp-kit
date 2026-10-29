"""Standalone finite local-word index inventory under conditional ordinary ABI."""
import argparse
import hashlib
import json
from pathlib import Path

import finite_stack_index_profile as finite

SELECTOR = 'finite-stack-index-structural-inventory-v1'
SCHEMA = 'thumb-finite-stack-index-structural-inventory-v1'


def text(value): return json.dumps(value,sort_keys=True,separators=(',',':'))
def sha(value): return hashlib.sha256(value).hexdigest()


def bind_calls(calls,mapping,address,size,rom_size):
    import match
    entries=json.loads(mapping)
    if type(calls) is not dict or not calls:
        raise ValueError('finite index inventory requires actual ordinary direct calls')
    bindings={}
    for site,target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site%2 or not address<=site<=address+size-4:
            raise ValueError('finite index inventory requires exact ordinary call sites')
        if match.function_thunk.reserved(target):
            raise ValueError('finite index inventory excludes reserved call thunks')
        name=f'func_{target:08X}'
        actual=match.function_address_target(name,entries,address,size,rom_size)
        row=next(row for row in entries if int(row['rom'],16)==actual)
        end=int(row['end'],16)
        if not actual<end<=match.ROM_BASE+rom_size or actual<address+size and end>address or any(
                other is not row and int(other['rom'],16)<end and int(other['end'],16)>actual for other in entries):
            raise ValueError('finite index ordinary target requires a unique nonoverlapping mapped span')
        bindings[site]=name
    return bindings


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    if selector!=SELECTOR: raise ValueError('finite index inventory requires its explicit inventory-only selector')
    entries=owner.validate_span(data,address,rom,mapping,index)
    refinement=owner.refine(data,address,mapping)
    instructions,edges,branches,actual_calls,words=graph.graph(data,address,refinement)
    if branches or words or calls!=actual_calls or bindings!=bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('finite index inventory requires exact closed direct-call CFG and bindings')
    selected=next(row for row in entries if int(row['rom'],16)==address)
    rows=[row.split() for row in index.decode().splitlines() if row.split() and row.split()[0]==f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs']!=len(instructions) or \
            len(rows)!=1 or len(rows[0])<4 or int(rows[0][3])!=len(instructions):
        raise ValueError('finite index inventory requires exact dual-index instruction counts')
    operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    if not any((match.thumb_stack_adjustment(item) or 0)<0 for item in instructions.values()):
        raise ValueError('finite index inventory requires actual allocated caller locals')
    partition=graph.partition(data,address,refinement,instructions,words)
    reserved=(match.function_thunk,match.divsi3,match.modsi3,match.umodsi3,
        match.ashldi3,match.software_float,match.software_double)
    for word in partition['words']:
        value=word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(module.reserved(value) for module in reserved):
            raise ValueError('finite index inventory cannot materialize a runtime or thunk address')
    restored=frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        finite_stack_index_policy=finite.SELECTOR)
    proof=restored['finite_stack_indices']
    if not any(len(row[2])==2 for row in proof['SP_additions']) or not any(len(row[2])==2 for row in proof['reads']):
        raise ValueError('finite index inventory requires an actual two-alternative SP addition and local read')
    modules=(match,owner,graph,operations,frame,finite,*reserved)
    pins={Path(module.__file__).name:sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name]=sha(Path(__file__).read_bytes())
    observed={'schema':SCHEMA,'selector':SELECTOR,'inventory_only':True,'source_or_ELF_admission':False,
        'claim':'structural reached-return target state under conditional ordinary returning-call ABI',
        'arithmetic_C_equivalence':False,'numeric_input_assumptions':[],'numeric_return_facts':[],
        'termination_claim':False,'control_flow_guarantee':'every reached CFG region has a path to a checked return; universal termination is not proved',
        'ordinary_call_premise':'conditional: every ordinary callee returns and preserves r4-r11/SP; no complete native ordinary-callee or memory-safety proof',
        'call_facts':'caller-saved numeric/address/flags facts killed at every call; callee-saved constants retained only under the conditional ordinary ABI',
        'caller_frame_policy':'allocated initialized aligned local-word reads on every finite alternative; original saved slots/SP/r4-r11/entry-LR; no alias spills, outgoing SP arguments, buffers or entry words',
        'calls':[[site-address,name] for site,name in sorted(bindings.items())],
        'frame':restored,'partition':partition,'instructions':len(instructions),
        'body_sha256':sha(data),'mapping_sha256':sha(mapping),'index_sha256':sha(index),'ROM_sha256':sha(rom),
        'producer_source_sha256':pins,'complete_native_structural_proof':True}
    if manifest is not None and text(manifest)!=text(observed):
        raise ValueError('finite index inventory manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    parser.add_argument('--rom',required=True,type=Path);parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--index',required=True,type=Path);parser.add_argument('address',type=lambda value:int(value,16))
    args=parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index=args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows=[row for row in json.loads(mapping) if int(row['rom'],16)==args.address]
    if len(rows)!=1: raise ValueError('finite index inventory requires one exact mapped owner')
    data=rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement=owner.refine(data,args.address,mapping)
    _,_,_,calls,_=graph.graph(data,args.address,refinement)
    bindings=bind_calls(calls,mapping,args.address,len(data),len(rom))
    proof,_=verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(text(proof))


if __name__=='__main__':main()
