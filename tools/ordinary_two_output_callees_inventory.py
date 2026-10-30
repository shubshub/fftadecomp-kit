"""Default-off two-output-leaf inventory with two explicitly premised named reads."""
import argparse
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0, ARM_REG_R3,
    ARM_REG_SP, ARM_REG_PC, ARM_REG_LR, ARM_CC_AL, ARM_CC_INVALID)
import ordinary_formal_stack_callee_inventory as parent

SELECTOR = 'ordinary-two-output-callees-inventory-v1'
SCHEMA = 'thumb-ordinary-two-output-callees-inventory-v1'
NAMED_SCHEMA = 'thumb-formal-output-readonly-named-buffer-v1'
PAIR_SCHEMA = 'thumb-two-fresh-formal-output-leaves-v1'
FIRST = parent.LEAF
SECOND = (0x0801C918, 0x0801C960, 34,
    '691a3b26d9786d76f850b2cab1e5999bac35af0524a17a4f82f8f0f7ea379fcf')
NAME, GLOBAL = 'g_state_02007F40', 0x02007F40
READS = [[32, 2], [34, 2]]
STORE_FORMALS = [3, 3, 4, 4, 5]
READ_PREMISE = ('conditional: the named halfwords at g_state_02007F40+0x20 and +0x22 '
    'are initialized, aligned and readable at each reached load; values remain unknown; '
    'the proved leaf performs no writes through the named object')
sha, text = parent.sha, parent.text


def named_policy():
    return {'schema': NAMED_SCHEMA, 'symbol': NAME, 'reads': [[32, 2], [34, 2]], 'readable': True}


def validate_named_policy(policy, data_mapping):
    if type(policy) is not dict or set(policy) != {'schema', 'symbol', 'reads', 'readable'} or \
            type(policy['schema']) is not str or policy['schema'] != NAMED_SCHEMA or \
            type(policy['symbol']) is not str or policy['symbol'] != NAME or \
            type(policy['reads']) is not list or policy['reads'] != READS or \
            any(type(row) is not list or any(type(value) is not int for value in row) for row in policy['reads']) or \
            policy['readable'] is not True or type(data_mapping) is not bytes:
        raise ValueError('two-output named reads require their exact explicit typed readability premise')
    objects = parent.match.parse_data_symbols(data_mapping)
    if objects.get(NAME) != GLOBAL:
        raise ValueError('two-output named reads require the exact existing typed data binding')
    return objects


def complete_named(data, address, rom, mapping, index):
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('named output leaf requires exact immutable typed inputs')
    parent.owner.validate_span(data, address, rom, mapping, index)
    entries, rows = parent.indices.indices(mapping, index)
    record = parent.indices.span_record(address, address+len(data), entries, rows, rom)
    refinement = parent.owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = parent.graph.graph(data, address, refinement)
    if record['instrs'] != len(instructions) or branches or calls or words or refinement['word_switches'] or any(
            item.mnemonic.startswith(('ldm', 'stm')) for item in instructions.values()):
        raise ValueError('named output leaf requires a closed complete leaf CFG with no calls/block transfers')
    parent.operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = parent.graph.partition(data, address, refinement, instructions, words)
    if partition['code_bytes'] != 68 or partition['literal_and_table_bytes'] != 4 or \
            partition['alignment_bytes'] or len(partition['words']) != 1:
        raise ValueError('named output leaf requires exactly its complete 68-byte code and one read literal')
    return instructions, edges, partition


def prove_named_origins(instructions, edges, address, data, partition, data_mapping, policy):
    """Finite straight-line origin transfer, never a numerical value interpreter."""
    validate_named_policy(policy, data_mapping)
    literal = partition['words'][0]
    if literal['value'] != GLOBAL or literal['switch_word'] or len(literal['load_sites']) != 1 or \
            literal['address'] != address+len(data)-4:
        raise ValueError('named output literal ownership/value/reached-load binding differs')
    origins = {ARM_REG_R3: ('formal', 3)}
    ordered, depth = sorted(instructions), 0
    incoming_reads, named_reads, stores, transfers, literal_loads = [], [], [], [], []
    if not ordered or ordered[0] != address or set(instructions) != set(edges):
        raise ValueError('named output leaf requires its complete entry CFG')
    for position, site in enumerate(ordered):
        item = instructions[site]; raw = bytes(item.bytes); encoded = int.from_bytes(raw, 'little')
        operands = item.operands
        regs = tuple(op.reg for op in operands if op.type == ARM_OP_REG)
        expected = () if position == len(ordered)-1 else (site+2,)
        if item.size != 2 or len(raw) != 2 or item.cc not in (ARM_CC_AL, ARM_CC_INVALID) or \
                tuple(edges[site]) != expected or position+1 < len(ordered) and ordered[position+1] != site+2:
            raise ValueError('named output leaf requires its exact straight-line narrow CFG')
        if item.mnemonic in ('push', 'pop'):
            push = item.mnemonic == 'push'
            actual = tuple(ARM_REG_R0+n for n in range(8) if encoded & (1 << n)) + \
                (((ARM_REG_LR if push else ARM_REG_PC),) if encoded & 0x100 else ())
            if encoded & 0xFE00 != (0xB400 if push else 0xBC00) or regs != actual or \
                    push and any(register in origins for register in regs) or not push and len(regs) > depth:
                raise ValueError('named output leaf cannot spill pointer origins or forge saved frame operations')
            depth += len(regs) if push else -len(regs)
            if not push:
                for register in regs: origins.pop(register, None)
        elif item.mnemonic == 'ldr' and encoded & 0xF800 == 0x9800:
            offset = parent.incoming.read_word(item, depth, parent.ENTRY_POLICY)
            register = ARM_REG_R0+((encoded >> 8) & 7)
            origins[register] = ('formal', 4+offset//4)
            incoming_reads.append([site, offset, 4, register-ARM_REG_R0, raw.hex()])
            transfers.append([site, register-ARM_REG_R0, 'formal', 4+offset//4])
        elif item.mnemonic == 'ldr' and encoded & 0xF800 == 0x4800:
            register = ARM_REG_R0+((encoded >> 8) & 7)
            destination = ((site+4) & ~3)+4*(encoded & 255)
            if len(operands) != 2 or operands[0].type != ARM_OP_REG or operands[0].reg != register or \
                    operands[1].type != ARM_OP_MEM or operands[1].mem.base != ARM_REG_PC or \
                    operands[1].mem.index or operands[1].mem.disp != 4*(encoded & 255) or \
                    item.writeback or operands[1].subtracted or operands[1].shift.type or operands[1].shift.value or \
                    destination != literal['address'] or literal['load_sites'] != [site] or \
                    int.from_bytes(data[destination-address:destination-address+4], 'little') != GLOBAL:
                raise ValueError('named output leaf requires exact reached typed PC-literal encoding')
            origins[register] = ('named', NAME)
            literal_loads.append([site, destination, NAME, GLOBAL, raw.hex()])
            transfers.append([site, register-ARM_REG_R0, 'named', NAME])
        elif item.mnemonic in ('strh', 'ldrh'):
            load = item.mnemonic == 'ldrh'
            register, base = ARM_REG_R0+(encoded & 7), ARM_REG_R0+((encoded >> 3) & 7)
            offset = 2*((encoded >> 6) & 31)
            if encoded & 0xF800 != (0x8800 if load else 0x8000) or len(operands) != 2 or \
                    operands[0].type != ARM_OP_REG or operands[0].reg != register or \
                    operands[1].type != ARM_OP_MEM or operands[1].mem.base != base or \
                    operands[1].mem.index or operands[1].mem.disp != offset or item.writeback or \
                    operands[1].subtracted or operands[1].shift.type or operands[1].shift.value:
                raise ValueError('named output leaf requires exact immediate halfword access encoding')
            if load:
                if origins.get(base) != ('named', NAME) or [offset, 2] not in READS:
                    raise ValueError('named output read leaves its exact symbol/offset/width policy')
                named_reads.append([site, NAME, offset, 2, GLOBAL+offset, raw.hex()])
                origins.pop(register, None)
            else:
                origin = origins.get(base)
                if origin not in (('formal', 3), ('formal', 4), ('formal', 5)) or offset or register in origins:
                    raise ValueError('named output store lacks its exact formal origin/scalar source')
                stores.append([site, origin[1], offset, 2, raw.hex()])
        elif item.mnemonic in ('mov', 'movs') and encoded & 0xFC00 == 0x4400 and (encoded >> 8) & 3 == 2:
            destination = ARM_REG_R0+(encoded & 7)+((encoded >> 4) & 8)
            source = ARM_REG_R0+((encoded >> 3) & 15)
            if regs != (destination, source) or any(register in (ARM_REG_SP, ARM_REG_PC, ARM_REG_LR) for register in regs):
                raise ValueError('named output copy cannot materialize SP/control provenance')
            origin = origins.get(source); origins.pop(destination, None)
            if origin is not None:
                origins[destination] = origin
                transfers.append([site, destination-ARM_REG_R0, *origin])
        elif item.mnemonic == 'bx':
            if position != len(ordered)-1 or encoded & 0xFF87 != 0x4700 or not regs or regs[0] in origins:
                raise ValueError('named output leaf requires its checked entry-LR return')
        else:
            # Exact Thumb immediate shifts and ADD/SUB scalar forms only. All
            # values, including named loads, stay unknown after these writes.
            allowed = (encoded & 0xF800 in (0x0000, 0x1000, 0x1800, 0x3000, 0x3800) and
                       item.mnemonic in ('lsls', 'asrs', 'adds', 'subs'))
            read, written = item.regs_access()
            if not allowed or any(register in origins for register in read) or \
                    set(written) & {ARM_REG_SP, ARM_REG_PC, ARM_REG_LR}:
                raise ValueError('named output leaf has unsupported origin/arithmetic/memory operation')
            for register in written: origins.pop(register, None)
    parent.incoming.validate_reads((row[1] for row in incoming_reads), parent.ENTRY_POLICY)
    if depth or [row[1] for row in stores] != STORE_FORMALS or \
            sorted({tuple(row[1:4]) for row in stores}) != [tuple(row) for row in parent.EFFECTS] or \
            [[row[2],row[3]] for row in named_reads] != READS or len(literal_loads) != 1:
        raise ValueError('named output observed stores/reads/frame differ from the exact finite policy')
    return {'schema': NAMED_SCHEMA, 'reads': [], 'writes': [list(row) for row in parent.EFFECTS],
        'store_events': stores, 'store_event_count': 5, 'unique_write_footprints': 3,
        'incoming_pointer_word_reads': incoming_reads, 'observed_origin_transfers': transfers,
        'named_reads': named_reads, 'typed_literal_loads': literal_loads,
        'readonly_named_buffer_policy': json.loads(text(policy)), 'named_read_premise': READ_PREMISE,
        'named_loaded_values': 'unknown scalars; no constant, arithmetic or return facts',
        'return_argument_facts': [], 'named_writes': []}


class NamedReadonlyFormalLeafProof(parent.FormalStackCalleeProof):
    """Reuse only the parent's exact three-local-footprint call application."""
    def __init__(self, data, address, rom, mapping, index, data_mapping, sites, policy):
        validate_named_policy(policy, data_mapping)
        if type(sites) is not dict or len(sites) != 1 or any(type(site) is not int or site % 2 or
                type(target) is not int or target != address for site,target in sites.items()):
            raise ValueError('named output proof requires its exact one marked site and target')
        instructions, edges, partition = complete_named(data, address, rom, mapping, index)
        effects = prove_named_origins(instructions, edges, address, data, partition, data_mapping, policy)
        restored = parent.frame.prove_frame(instructions, edges, address, {}, {}, entry_stack_policy=parent.ENTRY_POLICY)
        self.sites = dict(sites); self._sites = text(sorted(sites.items()))
        self._record = {'schema': NAMED_SCHEMA, 'address': address, 'end': address+len(data),
            'instructions': len(instructions), 'body_sha256': sha(data), 'ROM_sha256': sha(rom),
            'mapping_sha256': sha(mapping), 'index_sha256': sha(index), 'data_mapping_sha256': sha(data_mapping),
            'native_edges': [[site,list(targets)] for site,targets in sorted(edges.items())],
            'effects': effects, 'frame': restored, 'partition': partition}
        self._seal = sha(text(self._record).encode()); self._observations = {}


class TwoOutputCalleesProof:
    """Closed pair of independently fresh full native effects/frame proofs."""
    def __init__(self, first_data, second_data, rom, mapping, index, data_mapping, calls, policy):
        first_sites = {site:target for site,target in calls.items() if target == FIRST[0]}
        second_sites = {site:target for site,target in calls.items() if target == SECOND[0]}
        if len(first_sites) != 1 or len(second_sites) != 1:
            raise ValueError('two-output proof requires both exact one-time actual leaf calls')
        self._first = parent.FormalStackCalleeProof(first_data, FIRST[0], rom, mapping, index, first_sites)
        self._second = NamedReadonlyFormalLeafProof(second_data, SECOND[0], rom, mapping, index,
            data_mapping, second_sites, policy)
        self.sites = first_sites | second_sites
        self._sites = text(sorted(self.sites.items()))

    def validate_calls(self, calls):
        if type(self._first) is not parent.FormalStackCalleeProof or type(self._second) is not NamedReadonlyFormalLeafProof or \
                text(sorted(self.sites.items())) != self._sites or set(self.sites) != set(self._first.sites) | set(self._second.sites):
            raise ValueError('two-output descriptor differs from its freshly proved pair')
        self._first.validate_calls(calls); self._second.validate_calls(calls)

    def check_call(self, site, target, aliases, stack, pointer_slots):
        self.validate_calls(self.sites)
        if self.sites.get(site) != target:
            raise ValueError('unmarked two-output callee or site')
        child = self._first if site in self._first.sites else self._second
        return child.check_call(site, target, aliases, stack, pointer_slots)

    def fingerprint(self):
        self.validate_calls(self.sites)
        return {'schema': PAIR_SCHEMA, 'callees': [self._first.fingerprint(), self._second.fingerprint()],
            'store_events': 8, 'unique_write_footprints_per_callee': [3, 3],
            'named_read_premise': READ_PREMISE, 'physical_nonalias_claim': False}


def bind_calls(calls, mapping, address, size, rom_size):
    if type(calls) is not dict or not calls or type(mapping) is not bytes or \
            any(type(value) is not int for value in (address, size, rom_size)) or address % 2 or size <= 0 or \
            not parent.match.ROM_BASE <= address < address+size <= parent.match.ROM_BASE+rom_size:
        raise ValueError('two-output inventory requires exact immutable ordinary call inputs')
    entries = json.loads(mapping); bound = {}
    for site,target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site % 2 or \
                not address <= site <= address+size-4 or parent.thunks.reserved(target):
            raise ValueError('two-output inventory excludes thunks and malformed calls')
        name = f'func_{target:08X}'
        actual = parent.match.function_address_target(name, entries, address, size, rom_size)
        rows = [row for row in entries if int(row['rom'],16) == actual]; end = int(rows[0]['end'],16)
        if not actual < end <= parent.match.ROM_BASE+rom_size or actual < address+size and end > address or any(
                row is not rows[0] and int(row['rom'],16) < end and int(row['end'],16) > actual for row in entries):
            raise ValueError('two-output target requires unique nonoverlapping complete ownership')
        bound[site] = name
    if any(list(calls.values()).count(identity[0]) != 1 for identity in (FIRST,SECOND)):
        raise ValueError('two-output inventory requires exactly one call to each output leaf')
    return bound


def verify(data, address, rom, mapping, index, data_mapping, calls, bindings, *, selector,
           readonly_named_buffer_policy=None, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('two-output inventory requires its explicit default-off selector')
    validate_named_policy(readonly_named_buffer_policy, data_mapping)
    instructions, edges, actual_calls, partition = parent.complete(data,address,rom,mapping,index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls,mapping,address,len(data),len(rom)):
        raise ValueError('two-output bindings differ from every actual reached call')
    entries, rows = parent.indices.indices(mapping,index); bodies = {}
    for start,end,count,digest in (FIRST,SECOND):
        record = parent.indices.span_record(start,end,entries,rows,rom)
        body = rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE]
        if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
            raise ValueError('two-output complete helper body identity/count differs')
        bodies[start] = body
    proof = TwoOutputCalleesProof(bodies[FIRST[0]],bodies[SECOND[0]],rom,mapping,index,data_mapping,calls,readonly_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions,edges,address,{},calls,stack_aliases=True,
        local_alias_slot_policy=parent.slots.SELECTOR,zero_index_profile=parent.zero_index.SELECTOR,
        formal_stack_callee_proof=proof,formal_stack_alias_constant_policy=parent.slots.FORMAL_MOVS10_POLICY)
    additions = [row for row in restored['local_alias_slots']['small_SP_additions'] if row[2] == 10]
    if not additions:
        raise ValueError('two-output inventory requires an actual exact MOVS10/SP constructor')
    modules = (parent,parent.analyze,parent.match,parent.thunks,parent.owner,parent.graph,parent.operations,
        parent.indices,parent.frame,parent.slots,parent.zero_index,parent.incoming)
    source = {Path(module.__file__).name:sha(Path(module.__file__).read_bytes()) for module in modules}
    source[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema':SCHEMA,'selector':SELECTOR,'inventory_only':True,'address':address,'end':address+len(data),
        'instructions':len(instructions),'body_sha256':sha(data),'ROM_sha256':sha(rom),
        'mapping_sha256':sha(mapping),'index_sha256':sha(index),'data_mapping_sha256':sha(data_mapping),
        'calls':[[site,target,bindings[site]] for site,target in sorted(calls.items())],
        'frame':restored,'partition':partition,'exact_MOVS10_SP_constructors':additions,
        'readonly_named_buffer_policy':json.loads(text(readonly_named_buffer_policy)),'named_read_premise':READ_PREMISE,
        'component_accounting':{'fresh_helper_workflows':2,'fresh_helper_frames':2,'fresh_caller_frames':1,
            'noop_workflows':0,'helper_store_events':[3,5],'unique_write_footprints':[3,3]},
        'ordinary_call_premise':'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise':'each call passes arg3 plus actual initialized outgoing local-pointer words0/4; the freshly observed three halfword footprints are discharged into live caller locals',
        'named_loaded_values':'unknown scalars; no numeric or return facts',
        'complete_native_structural_proof':True,'complete_argument_effect_proof':True,
        'source_or_ELF_admission':False,'arithmetic_C_equivalence':False,'numeric_input_preconditions':[],
        'numeric_return_facts':[],'physical_memory_claim':False,'memory_safety_claim':False,
        'nonescape_claim':False,'universal_termination_claim':False,'producer_source_sha256':source,
        'claim':'complete CFG/partition and reached-return abstract ABI restoration with two independently proved output leaves, explicit typed named-read premise and conditional other ordinary ABI'}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('two-output manifest differs from fresh native proof')
    return observed,[instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',required=True,choices=(SELECTOR,))
    for name in ('rom','mapping','index','data-mapping'):
        parser.add_argument('--'+name,required=True,type=Path)
    parser.add_argument('--readonly-named-buffer-policy',required=True,type=json.loads)
    parser.add_argument('address',type=lambda value:int(value,16))
    args = parser.parse_args()
    rom,mapping,index,data_mapping = (args.rom.read_bytes(),args.mapping.read_bytes(),args.index.read_bytes(),args.data_mapping.read_bytes())
    selected = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(selected) != 1: raise ValueError('two-output inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(selected[0]['end'],16)-parent.match.ROM_BASE]
    _,_,calls,_ = parent.complete(data,args.address,rom,mapping,index)
    bindings = bind_calls(calls,mapping,args.address,len(data),len(rom))
    result,_ = verify(data,args.address,rom,mapping,index,data_mapping,calls,bindings,selector=args.profile,
        readonly_named_buffer_policy=args.readonly_named_buffer_policy)
    print(text(result))


if __name__ == '__main__': main()
