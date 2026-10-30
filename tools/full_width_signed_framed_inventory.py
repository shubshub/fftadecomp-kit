"""Standalone framed structural target-state inventory, without arithmetic equivalence."""
import argparse
import hashlib
import json
from pathlib import Path

import divsi3_profile as quotient
import modsi3_profile as remainder
import zero_aware_remainder_ordinary_inventory as ordinary
import full_width_signed_runtime_inventory as unframed

SELECTOR = 'full-width-signed-framed-target-state-inventory-v1'
SCHEMA = 'thumb-full-width-signed-framed-target-state-inventory-v1'
OPERATIONS = {'__divsi3':quotient.ADDRESS,'__modsi3':remainder.ADDRESS}


def text(value):return json.dumps(value,sort_keys=True,separators=(',',':'))
def sha(value):return hashlib.sha256(value).hexdigest()


bind_calls = unframed.bind_calls


def runtime_frames(rom,mapping,closure):
    """Prove each exact runtime frame, including its actual dependency call."""
    from capstone.arm_const import ARM_REG_R4,ARM_REG_R11
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    preserved = frozenset(range(ARM_REG_R4,ARM_REG_R11+1))
    proven = {}
    for address,end in ((0x0814274C,0x0814274E),
            (quotient.ADDRESS,0x0814274A),(remainder.ADDRESS,0x08142A1E)):
        data = rom[address-0x08000000:end-0x08000000]
        refinement = owner.refine(data,address,mapping)
        instructions,edges,branches,calls,words = graph.graph(data,address,refinement)
        if branches or words or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads']:
            raise ValueError('full-width framed runtime requires exact dependency and no caller-memory effects')
        restored = frame.prove_frame(instructions,edges,address,{},calls,
            call_preservation={site:preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('full-width framed runtime return alternatives differ')
        nested = max((proven[target]['maximum_additional_stack_bytes']
            for target in calls.values()),default=0)
        proven[address] = {'frame':restored,
            'maximum_additional_stack_bytes':restored['maximum_frame_bytes']+nested,
            'caller_memory_writes':[],'caller_stack_reads':[],
            'restores':'r4-r11,sp,entry-lr'}
    return [[address,proof] for address,proof in sorted(proven.items())]


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    import software_double_profile as canonical
    import software_float_profile as native
    from capstone.arm_const import ARM_REG_R4,ARM_REG_R11
    if selector != SELECTOR:raise ValueError('full-width structural inventory requires its explicit inventory-only selector')
    entries = owner.validate_span(data,address,rom,mapping,index)
    refinement = owner.refine(data,address,mapping)
    instructions,edges,branches,actual_calls,words = graph.graph(data,address,refinement)
    if branches or words or calls != actual_calls or bindings != bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('full-width structural inventory requires its exact closed direct-call CFG and bindings')
    selected = next(row for row in entries if int(row['rom'],16) == address)
    rows = [row.split() for row in index.decode().splitlines() if row.split() and row.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('full-width structural inventory requires exact dual-index reachable instruction counts')
    operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    if not any((match.thumb_stack_adjustment(item) or 0) < 0 for item in instructions.values()):
        raise ValueError('full-width framed inventory requires actual allocated caller locals')
    partition = graph.partition(data,address,refinement,instructions,words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (match.function_thunk,quotient,remainder,
                    match.umodsi3,match.ashldi3,match.software_float,canonical)):
            raise ValueError('full-width structural inventory cannot materialize a runtime or thunk address')
    div = canonical.prove_division_closure(rom,mapping,index)
    mod = canonical.prove_remainder_closure(rom,mapping,index)
    zero = 0x0814274C
    if set(div) != {quotient.ADDRESS,zero} or set(mod) != {remainder.ADDRESS,zero} or div[zero] != mod[zero] or \
            set(div[quotient.ADDRESS]['returns']) != {0x0814273E,0x08142748} or \
            set(mod[remainder.ADDRESS]['returns']) != {0x08142A12,0x08142A1C} or \
            any(proof['writes'] or proof['stack_reads'] for proof in (*div.values(),*mod.values())):
        raise ValueError('full-width structural inventory requires complete exact DIV/MOD/zero native closures')
    closure = div | mod
    native_frames = runtime_frames(rom,mapping,closure)
    ordinary_sites = {site:name for site,name in bindings.items() if name not in OPERATIONS}
    # Both runtime targets have complete native preservation proofs. Ordinary
    # sites retain exactly the existing conditional returning-call ABI premise.
    preserved = frozenset(range(ARM_REG_R4,ARM_REG_R11+1))
    restored = frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        call_preservation=None if ordinary_sites else {site:preserved for site in calls})
    modules = (match,owner,graph,operations,frame,canonical,native,quotient,remainder,ordinary,unframed)
    source_pins = {Path(module.__file__).name:sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema':SCHEMA,'selector':SELECTOR,'inventory_only':True,'source_or_ELF_admission':False,
        'claim':'local structural target-state ABI under exact canonical closures and conditional ordinary returning-call ABI',
        'runtime_entry_domain':'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'arithmetic_C_equivalence':False,'runtime_numeric_return_facts':[],'nonzero_facts':[],
        'termination_claim':False,'control_flow_guarantee':'every reached CFG region has a path to a checked return; universal termination is not proved',
        'runtime_input_semantics':'unchanged native interpreter symbolic entry-register origins; scalar_entries forbids public external writes and imposes no numeric range',
        'dependencies':{'quotient':[list(row) for row in canonical.DIVISION_IDENTITIES],
            'remainder':[list(row) for row in remainder.IDENTITIES]},
        'native_runtime_closure':[[site,proof] for site,proof in sorted(closure.items())],
        'zero_nonzero_control_alternatives':'both exact DIV returns and both exact MOD returns, including shared zero-hook dependency',
        'calls':[[site-address,name] for site,name in sorted(bindings.items())],
        'runtime_calls':[[site-address,name] for site,name in sorted(bindings.items()) if name in OPERATIONS],
        'ordinary_calls':[[site-address,name] for site,name in sorted(ordinary_sites.items())],
        'ordinary_call_premise':'conditional: every ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee proof',
        'caller_facts':'every call clears caller-saved register provenance; no numeric/address/flags result facts are supplied',
        'frame':restored,'native_runtime_frames':native_frames,
        'caller_frame_policy':'exact allocated locals/saved slots/SP/r4-r11/entry-LR; no entry-word or buffer premises',
        'runtime_stack_policy':'each canonical runtime accesses its own proved frame below the current caller SP',
        'ordinary_call_stack_bound':None,
        'partition':partition,'instructions':len(instructions),
        'body_sha256':sha(data),'mapping_sha256':sha(mapping),'index_sha256':sha(index),'ROM_sha256':sha(rom),
        'producer_source_sha256':source_pins,'complete_native_structural_proof':True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('full-width structural inventory manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


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
    if len(rows) != 1:raise ValueError('full-width structural inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement = owner.refine(data,args.address,mapping)
    _,_,_,calls,_ = graph.graph(data,args.address,refinement)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    manifest,_ = verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile)
    print(text(manifest))


if __name__ == '__main__':main()
