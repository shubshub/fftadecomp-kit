"""Initialized local descriptors through two complete read-only tree iterators.

The unknown final callback retains the explicit compatible returning ABI and
ordinary memory noninterference premises. No iteration bound is assumed.
"""
import hashlib
import json
from pathlib import Path
import struct

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import function_thunk_profile as thunk
import local_long_branch_profile as frame
import scalar_callback_adapter_inventory as scalar
from software_double_profile import indices, span_record

SELECTOR = 'conditional-two-word-tree-callback-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-two-word-tree-callback-closure-v1'
CONTROL_FLOW = 'complete initialized descriptor, read-only tree iterator and two-output local callback adapter; compatible returning indirect ABI and memory noninterference conditional; termination unproved'



def sha(data):return hashlib.sha256(data).hexdigest()


def complete(address,size,count,rom,mapping,index):
    data=rom[address-match.ROM_BASE:address-match.ROM_BASE+size]
    owner.validate_span(data,address,rom,mapping,index)
    entries,rows=indices(mapping,index)
    identity=span_record(address,address+size,entries,rows,rom)
    refinement=owner.refine(data,address,mapping)
    ins,edges,branches,calls,words=graph.graph(data,address,refinement)
    partition=graph.partition(data,address,refinement,ins,words)
    if branches or words or len(ins)!=count or identity['instrs']!=count:
        raise ValueError('two-word closure requires exact complete owner/count')
    return data,ins,edges,calls,partition


def prove(data,address,rom,mapping,index,*,selector):
    # Owner dispatch can initialize while the shared callback policy is loading.
    import two_output_callback_adapter_inventory as adapter
    from two_word_callback_closure_profile import _ContextRead, PRESERVED
    if type(selector)is not str or selector!=SELECTOR or type(address)is not int or \
            any(type(v)is not bytes for v in(data,rom,mapping,index)):
        raise ValueError('two-word closure requires its exact explicit policy and immutable inputs')
    body,ins,edges,calls,partition=complete(address,28,11,rom,mapping,index)
    if data!=body or sorted(ins)!=[address+v for v in(0,2,4,6,8,10,12,14,18,20,22)] or \
            len(calls)!=1 or list(calls)!=[address+14] or \
            body[:8]!=bytes.fromhex('00b582b000920191') or \
            body[12:14]!=bytes.fromhex('6a46') or body[18:24]!=bytes.fromhex('02b001bc0047'):
        raise ValueError('two-word closure requires complete natural initialized descriptor wrapper')
    r0,r1=match.ARM_REG_R0,match.ARM_REG_R0+1
    source=ins[address+8]
    if len(source.operands)!=2 or source.operands[1].type!=match.ARM_OP_MEM or \
            not scalar.load(source,r0,r0,source.operands[1].mem.disp) or \
            source.operands[1].mem.disp<0 or source.operands[1].mem.disp%4:
        raise ValueError('two-word closure requires an aligned incoming object word load')
    literal=ins[address+10];ops=literal.operands
    if literal.mnemonic!='ldr' or len(ops)!=2 or ops[0].type!=match.ARM_OP_REG or \
            ops[0].reg!=r1 or ops[1].type!=match.ARM_OP_MEM or \
            ops[1].mem.base!=match.ARM_REG_PC or ops[1].mem.index or \
            ((literal.address+4)&~3)+ops[1].mem.disp!=address+24 or \
            partition['literal_and_table_bytes']!=4 or partition['alignment_bytes']:
        raise ValueError('two-word closure requires one complete callback literal')
    value,=struct.unpack_from('<I',body,24)
    if value%2!=1:
        raise ValueError('two-word closure callback literal must be a typed odd Thumb pointer')
    callback=match.function_address_target(f'func_{value&~1:08X}',json.loads(mapping),address,len(data),len(rom))
    iterator=calls[address+14]
    worker,wi,we,wc,wp=complete(iterator,86,42,rom,mapping,index)
    # Both complete tree traversals use the same control and frame structure.
    # Their left/right child loads exchange offsets12 and16 in four places.
    prefix=bytes.fromhex('f0b50f1c161c846801225242251c002c1ed0e168002907d0914205d02069904211d0221c0c1cf2e7206990420bd0201c311c')
    suffix=bytes.fromhex('00280ad02069002802d0221c041ce3e7ac4202d0221ca468dee7f0bc01bc0047')
    template=bytearray(prefix+b'\x00'*4+suffix)
    if len(template)!=86:
        raise ValueError('tree closure internal complete template differs')
    reverse=worker[18:20]==bytes.fromhex('2169')
    if reverse:
        template[18:20]=bytes.fromhex('2169')
        for offset in (28,40,58):template[offset:offset+2]=bytes.fromhex('e068')
    selected=thunk.ALIASES['_call_via_r7']
    if worker[:50]!=template[:50] or worker[54:]!=template[54:] or \
            wc!={iterator+50:selected} or wp['literal_and_table_bytes'] or wp['alignment_bytes']:
        raise ValueError('tree closure requires the complete read-only tree iterator')
    child_offsets=(16,12) if reverse else (12,16)
    if not scalar.load(wi[iterator+18],r1,r0+4,child_offsets[0]) or any(
            not scalar.load(wi[iterator+offset],r0,r0+4,child_offsets[1])
            for offset in (28,40,58)):
        raise ValueError('tree closure requires the exact decoded child-load operands')
    # The adapter preserves the descriptor and callback identities in R6/R7.
    # R2 is caller-clobbered and is not assumed to retain a sentinel or node.
    adata=rom[callback-match.ROM_BASE:callback-match.ROM_BASE+32]
    refinement=owner.refine(adata,callback,mapping)
    ai,ae,ab,ac,aw=graph.graph(adata,callback,refinement)
    if ab or aw or len(ac)!=2 or callback+10 not in ac:
        raise ValueError('tree closure requires a complete two-output local adapter')
    getter=ac[callback+10]
    adapter_proof=adapter.verify(callback,getter,rom,mapping,index,selector=adapter.SELECTOR)
    tdata=rom[selected-match.ROM_BASE:selected-match.ROM_BASE+2]
    owner.validate_span(tdata,selected,rom,mapping,index)
    entries,rows=indices(mapping,index)
    if span_record(selected,selected+2,entries,rows,rom)['instrs']!=1 or any(
            int(row['rom'],16)<selected+4 and int(row['end'],16)>selected+2 for row in entries):
        raise ValueError('tree closure R7 thunk requires separate indexed padding')
    canonical,=thunk.dependencies(['_call_via_r7'],rom)
    addresses=[address,iterator,callback,getter,selected,thunk.ALIASES['_call_via_r2']]
    if len(set(addresses))!=len(addresses):
        raise ValueError('tree closure requires distinct complete dependency owners')
    worker_frame=frame.prove_frame(wi,we,iterator,{},wc,
        call_preservation={site:PRESERVED for site in wc})
    dependencies={iterator:worker,callback:adata,getter:rom[getter-match.ROM_BASE:getter-match.ROM_BASE+10],
        selected:tdata,thunk.ALIASES['_call_via_r2']:rom[thunk.ALIASES['_call_via_r2']-match.ROM_BASE:thunk.ALIASES['_call_via_r2']-match.ROM_BASE+2]}
    context=_ContextRead(rom,mapping,address+14,iterator,dependencies,ins,edges)
    verified=match.verify_leaf_instructions(data,address,True,calls,buffer_proof=context)
    root_frame=frame.prove_frame(ins,edges,address,{},calls,
        call_preservation={site:PRESERVED for site in calls},stack_aliases=True,buffer_proof=context)
    if {item.address for item in verified}!=set(ins) or not context.observed:
        raise ValueError('tree closure requires exact root descriptor access evidence')
    return dict(schema=SCHEMA,instructions=len(ins),calls=[[14,f'func_{iterator:08X}']],
        runtime_calls=[],partition=partition,frame=root_frame,
        callback_closure=dict(schema=SELECTOR,root_descriptor=dict(offset=-12,width=8,
            initialized_words=[dict(site=address+4,offset=0,entry_register=2),
                               dict(site=address+6,offset=4,entry_register=1)],
            actual_buffer_checks=context.observed),
            iterator=dict(address=iterator,end=iterator+86,instructions=42,body_sha256=sha(worker),
                partition=wp,frame=worker_frame,thunk=canonical,reverse_child_order=reverse,
                loop_invariant='R7 is the exact adapter Thumb pointer; R6 is the original initialized descriptor; R4/R5 are ordinary node values. Every reached load retains its explicit validity/provenance condition. R2 is arbitrary after a returning callback and has no retained sentinel or previous-node theorem.',
                caller_clobbered_R2_preservation_assumed=False,
                iteration_bound_assumed=False,termination_proved=False),
            adapter=adapter_proof,
            external_read_obligations=[dict(base='root entry R0',offset=source.operands[1].mem.disp,width=4),
                dict(base='loaded tree object',offset=8,width=4),
                dict(base='each reached current node',offsets=[8,12,16],width=4),
                dict(base='each node passed to getter',offsets=[4,0],width=4,ordered=True)],
            explicit_conditions=adapter_proof['explicit_conditions']+[
                'Every reached tree/node load is aligned, live, initialized and physically readable at its recorded width, including paths selected by arbitrary caller-clobbered R2 values.',
                'All private root, iterator, adapter and callback frames and continuation code satisfy compatible returning ABI validity and noninterference; external values carry no private-frame/saved-return provenance.'],
            source_sha256={**{Path(module.__file__).name:sha(Path(module.__file__).read_bytes())
                for module in(match, match.armv4t,owner,graph,thunk,frame,adapter,scalar)},
                'two_word_callback_closure_profile.py':sha((Path(__file__).parent/'two_word_callback_closure_profile.py').read_bytes()),
                Path(__file__).name:sha(Path(__file__).read_bytes())},
            physical_memory_permission=False,numeric_nonalias_proved=False,
            actual_callback_ABI_established=False,termination_proved=False))
