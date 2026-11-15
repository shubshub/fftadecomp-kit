"""Initialized local callback descriptors through a complete read-only iterator.

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
import scalar_callback_adapter_inventory as adapter
from software_double_profile import indices, span_record

SELECTOR = 'conditional-two-word-callback-closure-v1'
SCHEMA = 'elf-symbol-thumb-conditional-two-word-callback-closure-v1'
CONTROL_FLOW = 'complete initialized two-word local descriptor and read-only callback iterator; compatible returning indirect ABI and memory noninterference conditional; termination unproved'
PRESERVED = adapter.PRESERVED


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


class _ContextRead(match.BufferCallProof):
    def __init__(self,rom,mapping,site,target,dependencies,root_instructions,root_edges):
        super().__init__(rom,mapping,stack_arguments=True)
        self.site,self.call_target=site,target
        self.dependencies=dict(dependencies)
        self.root_instructions={point:bytes(item.bytes)for point,item in root_instructions.items()}
        self.root_edges=dict(root_edges)
        self.observed=[]

    def validate_frame(self,instructions,edges,address,branches,calls,preservation,scratch):
        if address!=self.site-14 or branches or calls!={self.site:self.call_target} or \
                edges!=self.root_edges or {point:bytes(item.bytes)for point,item in instructions.items()}!=self.root_instructions or \
                preservation!={self.site:PRESERVED} or scratch is not None:
            raise ValueError('two-word closure frame differs from its exact complete root')

    def check_call(self,address,aliases,stack,slots=None,*,site=None,words=None,**kwargs):
        r2=match.ARM_REG_R0+2
        if site!=self.site or address!=self.call_target or slots or words or \
                aliases!={r2:-12} or len(stack)!=3:
            raise ValueError('two-word closure call differs from its complete initialized root context')
        self.access(-12,4,stack)
        self.access(-8,4,stack)
        self.observed.append(dict(site=site,target=address,descriptor_offset=-12,width=8))
        return {}


def prove(data,address,rom,mapping,index,*,selector):
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
            not adapter.load(source,r0,r0,source.operands[1].mem.disp) or \
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
    worker,wi,we,wc,wp=complete(iterator,34,16,rom,mapping,index)
    expected=bytes.fromhex('70b50e1c151c446800e0a468002c05d0201c291c')
    ending=bytes.fromhex('0028f6d170bc01bc0047')
    selected=thunk.ALIASES['_call_via_r6']
    if worker[:20]!=expected or worker[24:]!=ending or wc!={iterator+20:selected} or \
            wp['literal_and_table_bytes'] or wp['alignment_bytes']:
        raise ValueError('two-word closure requires the complete read-only node iterator')
    # These exact instruction roles establish the loop invariant: R6 retains
    # entry callback, R5 retains descriptor address, and R4 is the current node.
    # The complete adapter restores R4-R11 under its explicit callback premise.
    adapter_data=rom[callback-match.ROM_BASE:callback-match.ROM_BASE+22]
    refinement=owner.refine(adapter_data,callback,mapping)
    ai,ae,ab,ac,aw=graph.graph(adapter_data,callback,refinement)
    if ab or aw or len(ac)!=2 or callback+4 not in ac:
        raise ValueError('two-word closure requires its complete two-call scalar adapter')
    getter=ac[callback+4]
    adapter_proof=adapter.verify(callback,getter,rom,mapping,index,selector=adapter.SELECTOR)
    tdata=rom[selected-match.ROM_BASE:selected-match.ROM_BASE+2]
    owner.validate_span(tdata,selected,rom,mapping,index)
    entries,rows=indices(mapping,index)
    if span_record(selected,selected+2,entries,rows,rom)['instrs']!=1 or any(
            int(row['rom'],16)<selected+4 and int(row['end'],16)>selected+2 for row in entries):
        raise ValueError('two-word closure R6 thunk requires separate indexed padding')
    canonical,=thunk.dependencies(['_call_via_r6'],rom)
    addresses=[address,iterator,callback,getter,selected,thunk.ALIASES['_call_via_r2']]
    if len(set(addresses))!=len(addresses):
        raise ValueError('two-word closure requires distinct complete dependency owners')
    worker_frame=frame.prove_frame(wi,we,iterator,{},wc,
        call_preservation={site:PRESERVED for site in wc})
    dependencies={iterator:worker,callback:adapter_data,getter:rom[getter-match.ROM_BASE:getter-match.ROM_BASE+4],
        selected:tdata,thunk.ALIASES['_call_via_r2']:rom[thunk.ALIASES['_call_via_r2']-match.ROM_BASE:thunk.ALIASES['_call_via_r2']-match.ROM_BASE+2]}
    context=_ContextRead(rom,mapping,address+14,iterator,dependencies,ins,edges)
    verified=match.verify_leaf_instructions(data,address,True,calls,buffer_proof=context)
    root_frame=frame.prove_frame(ins,edges,address,{},calls,
        call_preservation={site:PRESERVED for site in calls},stack_aliases=True,buffer_proof=context)
    if {item.address for item in verified}!=set(ins) or not context.observed:
        raise ValueError('two-word closure requires exact native root and descriptor access evidence')
    return dict(schema=SCHEMA,instructions=len(ins),calls=[[14,f'func_{iterator:08X}']],
        runtime_calls=[],partition=partition,frame=root_frame,
        callback_closure=dict(schema=SELECTOR,root_descriptor=dict(offset=-12,width=8,
            initialized_words=[dict(site=address+4,offset=0,entry_register=2),
                               dict(site=address+6,offset=4,entry_register=1)],
            actual_buffer_checks=context.observed),
            iterator=dict(address=iterator,end=iterator+34,instructions=16,body_sha256=sha(worker),
                partition=wp,frame=worker_frame,thunk=canonical,
                loop_invariant='R6 is the exact adapter Thumb pointer; R5 is the original initialized descriptor; R4 is null or the current ordinary node. Each returning adapter preserves R4-R11/SP. Only node+8 advances the loop; callback R0 remains unknown.',
                iteration_bound_assumed=False,termination_proved=False),
            adapter=adapter_proof,
            external_read_obligations=[dict(base='root entry R0',offset=source.operands[1].mem.disp,width=4),
                dict(base='loaded list object',offset=4,width=4),
                dict(base='each nonnull current node passed to getter',offset=0,width=4),
                dict(base='each current node followed after nonzero callback result',offset=8,width=4)],
            explicit_conditions=adapter_proof['explicit_conditions']+[
                'Every reached list/node load is aligned, live, initialized and physically readable at its recorded width; null is tested only as a word value.',
                'All private root, iterator, adapter and callback frames and continuation code satisfy compatible returning ABI validity and noninterference; external values carry no private-frame/saved-return provenance.'],
            source_sha256={**{Path(module.__file__).name:sha(Path(module.__file__).read_bytes())
                for module in(match, match.armv4t,owner,graph,thunk,frame,adapter)},
                Path(__file__).name:sha(Path(__file__).read_bytes())},
            physical_memory_permission=False,numeric_nonalias_proved=False,
            actual_callback_ABI_established=False,termination_proved=False))
