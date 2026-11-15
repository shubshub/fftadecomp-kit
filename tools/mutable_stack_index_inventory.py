"""Standalone mutable four-local-word index inventory under conditional ordinary ABI."""
import argparse
import hashlib
import json
from pathlib import Path

import mutable_stack_index_profile as finite

SELECTOR = 'mutable-four-local-index-structural-inventory-v1'
ALIAS_SLOT_SELECTOR = 'mutable-four-local-index-alias-slot-structural-inventory-v1'
LOW_HALFWORD_SELECTOR = 'mutable-four-local-index-alias-slot-low-signed-halfword-read-structural-inventory-v1'
HALFWORD_ACCESS_SELECTOR = 'mutable-four-local-index-alias-slot-halfword-access-structural-inventory-v1'
SCALAR_SLOT_SELECTOR = 'mutable-four-local-index-alias-slot-halfword-scalar-slot-structural-inventory-v1'
CONSUMER_SCRATCH_SELECTOR = 'mutable-four-local-index-alias-slot-halfword-scalar-slot-consumer-scratch-structural-inventory-v1'
LEAF_OVERWRITE_SELECTOR = 'mutable-four-local-index-alias-slot-halfword-scalar-slot-leaf-overwrite-structural-inventory-v1'
THREE_CALL_SELECTOR = 'mutable-four-local-index-three-call-structural-inventory-v1'
SCHEMA = 'thumb-mutable-four-local-index-structural-inventory-v1'


def text(value): return json.dumps(value,sort_keys=True,separators=(',',':'))
def sha(value): return hashlib.sha256(value).hexdigest()


def bind_calls(calls,mapping,address,size,rom_size):
    import match
    entries=json.loads(mapping)
    if type(calls) is not dict or not calls:
        raise ValueError('mutable index inventory requires actual ordinary direct calls')
    bindings={}
    for site,target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site%2 or not address<=site<=address+size-4:
            raise ValueError('mutable index inventory requires exact ordinary call sites')
        if match.function_thunk.reserved(target):
            raise ValueError('mutable index inventory excludes reserved call thunks')
        name=f'func_{target:08X}'
        actual=match.function_address_target(name,entries,address,size,rom_size)
        row=next(row for row in entries if int(row['rom'],16)==actual)
        end=int(row['end'],16)
        if not actual<end<=match.ROM_BASE+rom_size or actual<address+size and end>address or any(
                other is not row and int(other['rom'],16)<end and int(other['end'],16)>actual for other in entries):
            raise ValueError('mutable index ordinary target requires a unique nonoverlapping mapped span')
        bindings[site]=name
    return bindings


def verify(data,address,rom,mapping,index,calls,bindings,*,selector,manifest=None,objects=None,scratch_sites=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    if selector not in (SELECTOR, ALIAS_SLOT_SELECTOR, LOW_HALFWORD_SELECTOR, HALFWORD_ACCESS_SELECTOR, SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR):
        raise ValueError('mutable index inventory requires its explicit inventory-only selector')
    three_call = selector == THREE_CALL_SELECTOR
    if not three_call and scratch_sites is not None:
        raise ValueError('scratch role bindings require the explicit three-call selector')
    leaf_overwrite = selector == LEAF_OVERWRITE_SELECTOR
    consumer_scratch = selector in (CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR)
    scalar_slots = selector in (SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR)
    halfword_array = selector in (HALFWORD_ACCESS_SELECTOR, SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR)
    low_halfword = selector in (LOW_HALFWORD_SELECTOR, HALFWORD_ACCESS_SELECTOR, SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR)
    pointer_slots = selector in (ALIAS_SLOT_SELECTOR, LOW_HALFWORD_SELECTOR, HALFWORD_ACCESS_SELECTOR, SCALAR_SLOT_SELECTOR, CONSUMER_SCRATCH_SELECTOR, LEAF_OVERWRITE_SELECTOR, THREE_CALL_SELECTOR)
    entries=owner.validate_span(data,address,rom,mapping,index)
    refinement=owner.refine(data,address,mapping)
    instructions,edges,branches,actual_calls,words=graph.graph(data,address,refinement)
    if branches or words or calls!=actual_calls or bindings!=bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('mutable index inventory requires exact closed direct-call CFG and bindings')
    selected=next(row for row in entries if int(row['rom'],16)==address)
    rows=[row.split() for row in index.decode().splitlines() if row.split() and row.split()[0]==f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs']!=len(instructions) or \
            len(rows)!=1 or len(rows[0])<4 or int(rows[0][3])!=len(instructions):
        raise ValueError('mutable index inventory requires exact dual-index instruction counts')
    operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    if not any((match.thumb_stack_adjustment(item) or 0)<0 for item in instructions.values()):
        raise ValueError('mutable index inventory requires actual allocated caller locals')
    partition=graph.partition(data,address,refinement,instructions,words)
    reserved=(match.function_thunk,match.divsi3,match.modsi3,match.umodsi3,
        match.ashldi3,match.software_float,match.software_double)
    for word in partition['words']:
        value=word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(module.reserved(value) for module in reserved):
            raise ValueError('mutable index inventory cannot materialize a runtime or thunk address')
    consumer_proof = None
    if consumer_scratch:
        from consumer_scratch_alias_profile import ConsumerScratchAliasProof
        proof_type = ConsumerScratchAliasProof
        if leaf_overwrite:
            from readonly_leaf_overwrite_profile import ReadonlyLeafOverwriteProof
            proof_type = ReadonlyLeafOverwriteProof
        if three_call:
            from three_call_composition_profile import ThreeCallCompositionProof, SELECTOR as policy
            consumer_proof = ThreeCallCompositionProof(rom,mapping,index,objects,address,len(data),calls,
                scratch_sites,policy=policy)
        else:
            consumer_proof = proof_type(rom,mapping,index,objects,address,len(data),calls)
    elif objects is not None:
        raise ValueError('typed consumer objects require the explicit consumer inventory selector')
    restored=frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        consumer_scratch_proof=consumer_proof,
        mutable_stack_index_policy=(finite.THREE_CALL_SELECTOR if three_call
            else finite.LEAF_OVERWRITE_SELECTOR if leaf_overwrite
            else finite.CONSUMER_SCRATCH_SELECTOR if consumer_scratch
            else finite.SCALAR_SLOT_SELECTOR if scalar_slots
            else finite.HALFWORD_ACCESS_SELECTOR if halfword_array
            else finite.LOW_HALFWORD_SELECTOR if low_halfword
            else finite.ALIAS_SLOT_SELECTOR if pointer_slots else finite.SELECTOR))
    if scalar_slots and (not restored['mutable_scalar_word_slots']['stores'] or
            not restored['mutable_scalar_word_slots']['loads']):
        raise ValueError('scalar word inventory requires actual known scalar store and full-word recovery')
    if halfword_array:
        part = restored['mutable_halfword_accesses']
        written = {offset for row in part['writes'] for offset in row['offsets']}
        if not part['reads'] or not any({offset+step for step in (0,2,4,6)} <= written for offset in written):
            raise ValueError('halfword array inventory requires four actual halfword writes and a read')
    if low_halfword and not halfword_array and not restored['mutable_low_signed_halfword_reads']['reads']:
        raise ValueError('low halfword inventory requires an actual authenticated read')
    if pointer_slots and (not restored['mutable_local_pointer_slots']['stores'] or
            not restored['mutable_local_pointer_slots']['loads']):
        raise ValueError('mutable pointer inventory requires actual local pointer spill and reload')
    proof=restored['mutable_stack_indices']
    offsets={row[2] for row in proof['writes'] if row[3]==4}
    if not proof['reads'] or not any({offset+step for step in (0,4,8,12)} <= offsets for offset in offsets):
        raise ValueError('mutable index inventory requires actual four consecutive initialized-word writes and a local read')
    modules=(match, match.armv4t,owner,graph,operations,frame,finite,*reserved)
    if pointer_slots:
        import local_alias_slot_profile as alias_slots
        modules += (alias_slots,)
    if low_halfword:
        import zero_index_stack_profile as zero_index
        modules += (zero_index,)
    if consumer_scratch:
        import consumer_scratch_alias_profile as consumer
        import ignored_leaf_alias_profile as ignored
        modules += (consumer,ignored)
        if leaf_overwrite:
            import readonly_leaf_overwrite_profile as overwrite
            modules += (overwrite,)
    if three_call:
        import three_call_composition_profile as combined
        import readonly_leaf_overwrite_profile as overwrite
        import incoming_scratch_overwrite_profile as ordinary
        modules += (combined,overwrite,ordinary)
    pins={Path(module.__file__).name:sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name]=sha(Path(__file__).read_bytes())
    observed={'schema':('thumb-mutable-four-local-index-alias-slot-halfword-scalar-slot-structural-inventory-v1' if scalar_slots
            else 'thumb-mutable-four-local-index-alias-slot-halfword-access-structural-inventory-v1' if halfword_array
            else 'thumb-mutable-four-local-index-alias-slot-low-signed-halfword-read-structural-inventory-v1'
            if low_halfword else 'thumb-mutable-four-local-index-alias-slot-structural-inventory-v1'
            if pointer_slots else SCHEMA),'selector':selector,'inventory_only':True,'source_or_ELF_admission':False,
        'claim':'structural reached-return target state and initialized local-word accesses under conditional ordinary returning-call ABI',
        'arithmetic_C_equivalence':False,'numeric_input_assumptions':[],'numeric_return_facts':[],
        'termination_claim':False,'control_flow_guarantee':'every reached CFG region has a path to a checked return; universal termination is not proved',
        'ordinary_call_premise':'conditional: every ordinary callee returns and preserves r4-r11/SP; no complete native ordinary-callee or memory-safety proof',
        'call_facts':'caller-saved numeric/address/flags facts killed at every call; callee-saved constants retained only under the conditional ordinary ABI',
        'caller_frame_policy':('allocated aligned mutable local words and halfwords with exact byte coverage and direct-SP pointer slots; no byte accesses, outgoing SP arguments, buffers or entry words' if halfword_array else 'allocated aligned mutable local words with direct-SP pointer slots and exact zero-index low signed halfword reads of initialized nonpointer words; no halfword stores/upper lanes, outgoing SP arguments, buffers or entry words' if low_halfword else 'allocated aligned mutable local words with explicit direct-SP pointer slots; all-path initialized word reads; saved SP/r4-r11/entry-LR; no halfwords, outgoing SP arguments, buffers or entry words' if pointer_slots else 'allocated aligned mutable local words; every read initialized on every exact path context; original saved slots/SP/r4-r11/entry-LR; no alias spills, halfwords, outgoing SP arguments, buffers or entry words'),
        'calls':[[site-address,name] for site,name in sorted(bindings.items())],
        'frame':restored,'partition':partition,'instructions':len(instructions),
        'body_sha256':sha(data),'mapping_sha256':sha(mapping),'index_sha256':sha(index),'ROM_sha256':sha(rom),
        'producer_source_sha256':pins,'complete_native_structural_proof':True,'path_state_resource_limit':finite.MAX_UPDATES}
    if consumer_scratch:
        observed['schema']='thumb-mutable-four-local-index-consumer-scratch-structural-inventory-v1'
        observed['objects_sha256']=sha(objects)
        observed['consumer_scratch_contract']=('existing complete leaf overwrite-before-use proof for every incoming scratch alias; all local memory provenance retained' if leaf_overwrite else 'readonly complete ignored incoming R2 leaf; every caller successor path kills R2 before use/forward/return; all local memory provenance retained')
        if leaf_overwrite:
            observed['schema']='thumb-mutable-four-local-index-leaf-overwrite-structural-inventory-v1'
    if three_call:
        observed['schema']='thumb-mutable-four-local-index-three-call-structural-inventory-v1'
        observed.pop('consumer_scratch_contract')
        observed['scratch_contract']='three explicitly selected disjoint original calls; each independent authenticated policy required; all local frame state retained'
    if scalar_slots:
        observed['scalar_word_facts'] = 'exact authenticated allocated scalar-word spill/reload only; no incoming/partial-memory inference or numeric callee theorem'
    if manifest is not None and text(manifest)!=text(observed):
        raise ValueError('mutable index inventory manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,ALIAS_SLOT_SELECTOR,LOW_HALFWORD_SELECTOR,HALFWORD_ACCESS_SELECTOR,SCALAR_SLOT_SELECTOR,CONSUMER_SCRATCH_SELECTOR,LEAF_OVERWRITE_SELECTOR,THREE_CALL_SELECTOR))
    parser.add_argument('--rom',required=True,type=Path);parser.add_argument('--mapping',required=True,type=Path)
    parser.add_argument('--objects',type=Path)
    parser.add_argument('--scratch-sites',type=Path,help='exact role-to-[site,target] JSON for explicit three-call inventory only')
    parser.add_argument('--index',required=True,type=Path);parser.add_argument('address',type=lambda value:int(value,16))
    args=parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom,mapping,index=args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes()
    rows=[row for row in json.loads(mapping) if int(row['rom'],16)==args.address]
    if len(rows)!=1: raise ValueError('mutable index inventory requires one exact mapped owner')
    data=rom[args.address-0x08000000:int(rows[0]['end'],16)-0x08000000]
    refinement=owner.refine(data,args.address,mapping)
    _,_,_,calls,_=graph.graph(data,args.address,refinement)
    bindings=bind_calls(calls,mapping,args.address,len(data),len(rom))
    proof,_=verify(data,args.address,rom,mapping,index,calls,bindings,selector=args.profile,objects=None if args.objects is None else args.objects.read_bytes(),scratch_sites=None if args.scratch_sites is None else json.loads(args.scratch_sites.read_bytes()))
    print(text(proof))


if __name__=='__main__':main()
