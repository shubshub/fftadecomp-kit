"""Default-off inventory with freshly proved C918 and two-register C960 outputs."""
import argparse
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0, ARM_REG_R2,
    ARM_REG_R3, ARM_REG_R12, ARM_REG_SP, ARM_REG_PC, ARM_REG_LR, ARM_CC_AL, ARM_CC_INVALID)
import ordinary_named_output_leaf_only_inventory as leaf

parent,named = leaf.parent,leaf.named
FIRST = leaf.LEAF
SECOND = (0x0801C960,0x0801C984,15,
    '7571d680a715ff36444c951cbd8f92b3692eb982961f7428e55dbab9e103a2a3')
SELECTOR = 'ordinary-second-formal-output-callees-inventory-v1'
SCHEMA = 'thumb-ordinary-second-formal-output-callees-inventory-v1'
SECOND_SCHEMA = 'thumb-second-formal-output-leaf-v1'
POLICY_SCHEMA = 'thumb-second-formal-output-readonly-named-buffer-v1'
EFFECTS = [[2,0,2],[3,0,2]]
READS = [[36,2],[38,2]]
PREMISE = ('conditional: the named halfwords g_state_02007F40+0x24 and +0x26 are '
    'initialized, aligned and readable at each reached C960 load; values remain unknown; '
    'the leaf has no stores through the named origin; no physical nonalias claim')
sha,text = named.sha,named.text


def second_named_policy():
    return {'schema':POLICY_SCHEMA,'symbol':named.NAME,'reads':[[36,2],[38,2]],
        'readable':True,'initialized':True}


def validate_second_policy(policy,data_mapping):
    if type(policy) is not dict or set(policy) != set(second_named_policy()) or \
            type(policy['schema']) is not str or policy['schema'] != POLICY_SCHEMA or \
            type(policy['symbol']) is not str or policy['symbol'] != named.NAME or \
            type(policy['reads']) is not list or policy['reads'] != READS or any(
                type(row) is not list or any(type(value) is not int for value in row) for row in policy['reads']) or \
            policy['readable'] is not True or policy['initialized'] is not True or type(data_mapping) is not bytes:
        raise ValueError('second output leaf requires its distinct exact typed named-read premise')
    objects = parent.match.parse_data_symbols(data_mapping)
    if objects.get(named.NAME) != named.GLOBAL:
        raise ValueError('second output leaf requires the exact existing named data binding')


def exact_body(identity,rom,mapping,index):
    start,end,count,digest = identity
    entries,rows = parent.indices.indices(mapping,index)
    record = parent.indices.span_record(start,end,entries,rows,rom)
    data = rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE]
    if record['instrs'] != count or sha(data) != digest:
        raise ValueError('second output complete helper body identity/count differs')
    return data


def complete_second(data,address,rom,mapping,index):
    if any(type(value) is not bytes for value in (data,rom,mapping,index)) or type(address) is not int:
        raise ValueError('second output leaf requires exact immutable native inputs')
    if address != SECOND[0] or data != exact_body(SECOND,rom,mapping,index):
        raise ValueError('second output leaf requires its actual complete mapped body')
    parent.owner.validate_span(data,address,rom,mapping,index)
    refinement = parent.owner.refine(data,address,mapping)
    instructions,edges,branches,calls,words = parent.graph.graph(data,address,refinement)
    if len(instructions) != 15 or branches or calls or words or refinement['word_switches'] or any(
            item.mnemonic.startswith(('ldm','stm')) for item in instructions.values()):
        raise ValueError('second output requires its complete call-free leaf CFG')
    parent.operations.verify_operations(instructions,edges,address,branches,calls,refinement)
    partition = parent.graph.partition(data,address,refinement,instructions,words)
    if partition['code_bytes'] != 30 or partition['literal_and_table_bytes'] != 4 or \
            partition['alignment_bytes'] != 2 or partition['alignment'] != [[address+30,address+32]] or \
            len(partition['words']) != 1:
        raise ValueError('second output leaf requires its exact code/literal/zero-alignment partition')
    return instructions,edges,partition


def prove_second_origins(instructions,edges,address,data,partition,data_mapping,policy):
    validate_second_policy(policy,data_mapping)
    literal = partition['words'][0]
    if literal['value'] != named.GLOBAL or literal['address'] != address+32 or \
            literal['switch_word'] or len(literal['load_sites']) != 1:
        raise ValueError('second output named literal ownership/value differs')
    origins = {ARM_REG_R2:('formal',2),ARM_REG_R3:('formal',3)}
    ordered,depth = sorted(instructions),0
    reads,stores,loads = [],[],[]
    for position,site in enumerate(ordered):
        item = instructions[site];raw = bytes(item.bytes);encoded = int.from_bytes(raw,'little');ops = item.operands
        regs = tuple(op.reg for op in ops if op.type == ARM_OP_REG)
        expected = () if position == len(ordered)-1 else (site+2,)
        if item.size != len(raw) or len(raw) != 2 or item.cc not in (ARM_CC_AL,ARM_CC_INVALID) or \
                tuple(edges[site]) != expected or position+1 < len(ordered) and ordered[position+1] != site+2:
            raise ValueError('second output origins require the full straight-line narrow CFG')
        if item.mnemonic in ('push','pop'):
            push = item.mnemonic == 'push'
            actual = tuple(ARM_REG_R0+n for n in range(8) if encoded & (1<<n)) + \
                (((ARM_REG_LR if push else ARM_REG_PC),) if encoded & 0x100 else ())
            if encoded & 0xFE00 != (0xB400 if push else 0xBC00) or regs != actual or \
                    push and any(register in origins for register in regs) or not push and len(regs) > depth:
                raise ValueError('second output cannot spill formal origins or forge frame operations')
            depth += len(regs) if push else -len(regs)
            if not push:
                for register in regs:origins.pop(register,None)
        elif item.mnemonic == 'ldr':
            destination = ARM_REG_R0+((encoded>>8)&7);target = ((site+4)&~3)+4*(encoded&255)
            if encoded & 0xF800 != 0x4800 or len(ops) != 2 or ops[0].type != ARM_OP_REG or \
                    ops[0].reg != destination or ops[1].type != ARM_OP_MEM or ops[1].mem.base != ARM_REG_PC or \
                    ops[1].mem.index or ops[1].mem.disp != 4*(encoded&255) or item.writeback or \
                    ops[1].subtracted or ops[1].shift.type or ops[1].shift.value or \
                    target != literal['address'] or literal['load_sites'] != [site] or \
                    int.from_bytes(data[target-address:target-address+4],'little') != named.GLOBAL:
                raise ValueError('second output requires its exact reached raw named-literal load')
            origins[destination] = ('named',named.NAME)
            loads.append([site,target,named.NAME,named.GLOBAL,raw.hex()])
        elif item.mnemonic in ('ldrh','strh'):
            load = item.mnemonic == 'ldrh'
            register,base = ARM_REG_R0+(encoded&7),ARM_REG_R0+((encoded>>3)&7)
            offset = 2*((encoded>>6)&31)
            if encoded & 0xF800 != (0x8800 if load else 0x8000) or len(ops) != 2 or \
                    ops[0].type != ARM_OP_REG or ops[0].reg != register or ops[1].type != ARM_OP_MEM or \
                    ops[1].mem.base != base or ops[1].mem.index or ops[1].mem.disp != offset or \
                    item.writeback or ops[1].subtracted or ops[1].shift.type or ops[1].shift.value:
                raise ValueError('second output requires exact immediate halfword read/write encodings')
            if load:
                if origins.get(base) != ('named',named.NAME) or [offset,2] not in READS:
                    raise ValueError('second output read lacks its exact named origin/offset/width')
                reads.append([site,named.NAME,offset,2,named.GLOBAL+offset,raw.hex()]);origins.pop(register,None)
            else:
                origin = origins.get(base)
                if origin not in (('formal',2),('formal',3)) or offset or register in origins:
                    raise ValueError('second output write lacks its exact formal origin/scalar source')
                stores.append([site,origin[1],0,2,raw.hex()])
        elif item.mnemonic == 'bx':
            if position != len(ordered)-1 or encoded & 0xFF87 != 0x4700 or not regs or regs[0] in origins:
                raise ValueError('second output requires its restored entry-LR terminal return')
        else:
            allowed = item.mnemonic in ('lsls','asrs') and encoded & 0xF800 in (0x0000,0x1000)
            if item.mnemonic == 'subs' and encoded & 0xFE00 == 0x1A00:
                allowed = len(ops) == 3 and all(op.type == ARM_OP_REG for op in ops) and regs == (
                    ARM_REG_R0+(encoded&7),ARM_REG_R0+((encoded>>3)&7),ARM_REG_R0+((encoded>>6)&7))
            read,written = item.regs_access()
            if not allowed or any(register in origins for register in read) or \
                    set(written)&{ARM_REG_SP,ARM_REG_LR,ARM_REG_PC}:
                raise ValueError('second output has unsupported formal/named/scalar operation')
            for register in written:origins.pop(register,None)
    if depth or [[r[2],r[3]] for r in reads] != READS or [row[1:4] for row in stores] != EFFECTS or len(loads) != 1:
        raise ValueError('second output observed frame, reads or writes differ from the exact policy')
    return {'schema':SECOND_SCHEMA,'reads':[],'writes':[list(row) for row in EFFECTS],
        'store_events':stores,'store_event_count':2,'unique_write_footprints':2,
        'named_reads':reads,'typed_literal_loads':loads,'incoming_word_reads':[],
        'readonly_named_buffer_policy':json.loads(text(policy)),'named_read_premise':PREMISE,
        'named_loaded_values':'unknown scalars','named_writes':[],'return_argument_facts':[],
        'residual_machine_pointers':'r2/r3 may retain passed pointers; caller-clobber abstraction grants no nonescape claim'}


class SecondFormalOutputLeafProof:
    def __init__(self,data,address,rom,mapping,index,data_mapping,sites,policy):
        if type(sites) is not dict or len(sites) != 1 or any(type(site) is not int or site%2 or \
                type(target) is not int or target != address for site,target in sites.items()):
            raise ValueError('second output proof requires its one exact actual call site')
        instructions,edges,partition = complete_second(data,address,rom,mapping,index)
        effects = prove_second_origins(instructions,edges,address,data,partition,data_mapping,policy)
        restored = parent.frame.prove_frame(instructions,edges,address,{}, {})
        self.sites = dict(sites);self._sites = text(sorted(sites.items()));self._observations = {}
        self._record = {'schema':SECOND_SCHEMA,'address':address,'end':address+len(data),'instructions':len(instructions),
            'body_sha256':sha(data),'ROM_sha256':sha(rom),'mapping_sha256':sha(mapping),'index_sha256':sha(index),
            'data_mapping_sha256':sha(data_mapping),'native_edges':[[s,list(targets)] for s,targets in sorted(edges.items())],
            'frame':restored,'partition':partition,'effects':effects}
        self._seal = sha(text(self._record).encode())

    def validate_calls(self,calls):
        if type(calls) is not dict or text(sorted(self.sites.items())) != self._sites or any(
                calls.get(site) != target for site,target in self.sites.items()) or \
                sha(text(self._record).encode()) != self._seal or self._record['effects']['writes'] != EFFECTS:
            raise ValueError('second output descriptor differs from its fresh body/site/effect proof')

    def check_call(self,site,target,aliases,stack,pointer_slots):
        self.validate_calls({site:target})
        if self.sites.get(site) != target or type(stack) is not list or not stack:
            raise ValueError('unmarked second output call or absent live caller frame')
        clobbered = {*range(ARM_REG_R0,ARM_REG_R0+4),ARM_REG_R12,ARM_REG_LR}
        if set(aliases)&clobbered != {ARM_REG_R2,ARM_REG_R3}:
            raise ValueError('second output call requires exactly arg2/arg3 local pointers and scalar arg0/arg1')
        base = -4*len(stack);writes = []
        for formal,offset,width in self._record['effects']['writes']:
            values = aliases[ARM_REG_R0+formal]
            if type(values) is not frozenset or len(values) != 1:
                raise ValueError('second output pointer needs one all-path live local origin')
            origin,live = next(iter(values))
            if type(origin) is not int or live is not True:
                raise ValueError('second output pointer has missing or expired local origin')
            position = origin+offset-base
            if (origin+offset)%width or position < 8 or \
                    origin+offset+width > 0 or any(stack[number][0] != 'local' for number in
                        range(position//4,(position+width-1)//4+1)):
                raise ValueError('second output leaves aligned live locals or overlaps outgoing/saved words')
            writes.append((origin+offset,width))
        if set(range(writes[0][0],writes[0][0]+writes[0][1]))&set(range(writes[1][0],writes[1][0]+writes[1][1])):
            raise ValueError('second output actual halfword domains overlap')
        self._observations[site] = {'site':site,'target':target,'caller_SP_entry_offset':base,
            'argument_entry_SP_offsets':[[2,writes[0][0]],[3,writes[1][0]]],
            'writes_entry_SP_offsets':[list(row) for row in writes],
            'callee_stack_separation':'fresh strict saved-only frame below call SP; formal writes in caller locals above outgoing words',
            'physical_nonalias_claim':False}
        return writes

    def fingerprint(self):
        self.validate_calls(self.sites)
        if set(self._observations) != set(self.sites):
            raise ValueError('second output fresh proof did not cover every marked call')
        return {'schema':SECOND_SCHEMA,'native_leaf':json.loads(text(self._record)),
            'calls':[self._observations[site] for site in sorted(self._observations)]}


class SecondFormalOutputCalleesProof:
    def __init__(self,first_data,second_data,rom,mapping,index,data_mapping,calls,first_policy,second_policy):
        if first_data != exact_body(FIRST,rom,mapping,index) or second_data != exact_body(SECOND,rom,mapping,index):
            raise ValueError('second-output pair requires both actual canonical mapped helper bodies')
        first_sites = {site:target for site,target in calls.items() if target == FIRST[0]}
        second_sites = {site:target for site,target in calls.items() if target == SECOND[0]}
        if len(first_sites) != 1 or len(second_sites) != 1:
            raise ValueError('second-output pair requires exactly one call to each fresh leaf')
        self._first = named.NamedReadonlyFormalLeafProof(first_data,FIRST[0],rom,mapping,index,data_mapping,first_sites,first_policy)
        self._second = SecondFormalOutputLeafProof(second_data,SECOND[0],rom,mapping,index,data_mapping,second_sites,second_policy)
        self.sites = first_sites|second_sites;self._sites = text(sorted(self.sites.items()))

    def validate_calls(self,calls):
        if type(self._first) is not named.NamedReadonlyFormalLeafProof or type(self._second) is not SecondFormalOutputLeafProof or \
                text(sorted(self.sites.items())) != self._sites or set(self.sites) != set(self._first.sites)|set(self._second.sites):
            raise ValueError('second-output pair differs from its exact freshly proved children')
        self._first.validate_calls(calls);self._second.validate_calls(calls)

    def check_call(self,site,target,aliases,stack,pointer_slots):
        self.validate_calls(self.sites)
        if self.sites.get(site) != target:raise ValueError('unmarked second-output pair call or target')
        child = self._first if site in self._first.sites else self._second
        return child.check_call(site,target,aliases,stack,pointer_slots)

    def fingerprint(self):
        self.validate_calls(self.sites)
        return {'schema':SCHEMA,'callees':[self._first.fingerprint(),self._second.fingerprint()],
            'store_events':7,'unique_write_footprints_per_callee':[3,2],
            'written_abstract_word_facts':'existing frame invalidates every overlapping local scalar/alias-slot fact',
            'physical_nonalias_claim':False}


def bind_calls(calls,mapping,address,size,rom_size):
    bound = leaf.bind_calls(calls,mapping,address,size,rom_size)
    if list(calls.values()).count(SECOND[0]) != 1:
        raise ValueError('second-output inventory requires one actual second leaf call')
    return bound


def verify(data,address,rom,mapping,index,data_mapping,calls,bindings,*,selector,
           readonly_named_buffer_policy=None,readonly_second_named_buffer_policy=None,manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('second-output inventory requires its explicit default-off selector')
    named.validate_named_policy(readonly_named_buffer_policy,data_mapping)
    validate_second_policy(readonly_second_named_buffer_policy,data_mapping)
    instructions,edges,actual_calls,partition = parent.complete(data,address,rom,mapping,index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('second-output bindings differ from all actual reached calls')
    bodies = {}
    for identity in (FIRST,SECOND):
        start,end,_,_ = identity
        if start < address+len(data) and end > address:raise ValueError('second-output helper overlaps caller')
        bodies[start] = exact_body(identity,rom,mapping,index)
    proof = SecondFormalOutputCalleesProof(bodies[FIRST[0]],bodies[SECOND[0]],rom,mapping,index,data_mapping,calls,
        readonly_named_buffer_policy,readonly_second_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        local_alias_slot_policy=parent.slots.SELECTOR,zero_index_profile=parent.zero_index.SELECTOR,
        formal_stack_callee_proof=proof)
    modules = (leaf,named,parent,parent.analyze,parent.match,parent.thunks,parent.owner,parent.graph,
        parent.operations,parent.indices,parent.frame,parent.slots,parent.zero_index,parent.incoming)
    source = {Path(module.__file__).name:sha(Path(module.__file__).read_bytes()) for module in modules}
    source[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema':SCHEMA,'selector':SELECTOR,'inventory_only':True,'address':address,'end':address+len(data),
        'instructions':len(instructions),'body_sha256':sha(data),'ROM_sha256':sha(rom),'mapping_sha256':sha(mapping),
        'index_sha256':sha(index),'data_mapping_sha256':sha(data_mapping),
        'calls':[[s,t,bindings[s]] for s,t in sorted(calls.items())],'frame':restored,'partition':partition,
        'readonly_named_buffer_policy':json.loads(text(readonly_named_buffer_policy)),
        'readonly_second_named_buffer_policy':json.loads(text(readonly_second_named_buffer_policy)),
        'named_read_premises':[named.READ_PREMISE,PREMISE],'named_loaded_values':'unknown scalars',
        'ordinary_call_premise':'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving ABI; its body and memory effects remain unproved',
        'component_accounting':{'fresh_helper_workflows':2,'fresh_helper_frames':2,'fresh_caller_frames':1,
            'helper_store_events':[5,2],'unique_write_footprints_per_callee':[3,2]},
        'complete_native_structural_proof':True,'complete_argument_effect_proof':True,
        'source_or_ELF_admission':False,'numeric_input_preconditions':[],'numeric_return_facts':[],
        'arithmetic_C_equivalence':False,'physical_memory_claim':False,'memory_safety_claim':False,
        'nonescape_claim':False,'universal_termination_claim':False,'producer_source_sha256':source,
        'claim':'complete CFG/partition and strict reached-return abstract ABI with fresh C918/C960 formal write proofs, distinct explicit named-read premises and conditional other ordinary ABI'}
    if manifest is not None and text(manifest) != text(observed):raise ValueError('second-output manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    for name in ('rom','mapping','index','data-mapping'):parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--readonly-named-buffer-policy',required=True,type=json.loads)
    parser.add_argument('--readonly-second-named-buffer-policy',required=True,type=json.loads)
    parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    rom,mapping,index,data_mapping = (args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes(),args.data_mapping.read_bytes())
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:raise ValueError('second-output inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(rows[0]['end'],16)-parent.match.ROM_BASE]
    _,_,calls,_ = parent.complete(data,args.address,rom,mapping,index)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    result,_ = verify(data,args.address,rom,mapping,index,data_mapping,calls,bindings,selector=args.profile,
        readonly_named_buffer_policy=args.readonly_named_buffer_policy,
        readonly_second_named_buffer_policy=args.readonly_second_named_buffer_policy)
    print(text(result))


if __name__ == '__main__':main()
