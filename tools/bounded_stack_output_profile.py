"""Finite native callee closure with argument-relative local-buffer effects."""
import hashlib
import json

import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import local_long_branch_profile as frame
import function_thunk_profile as thunks
from capstone.arm_const import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_R0, ARM_REG_R1,
    ARM_REG_R3, ARM_REG_R4, ARM_REG_R11, ARM_REG_R12, ARM_REG_LR, ARM_REG_SP, ARM_REG_PC)

SCHEMA = 'thumb-bounded-stack-output-callee-closure-v1'
MAX_DEPENDENCIES, MAX_BYTES = 8, 4096
UNKNOWN = (-1, 0)
WIDTHS = {'ldr':4, 'str':4, 'ldrh':2, 'strh':2, 'ldrb':1, 'strb':1, 'ldrsb':1, 'ldrsh':2}


class BoundedOutputProof:
    """No address list grants effects: each exact context gets a complete proof."""

    def __init__(self, rom, mapping, index, output_calls):
        self.rom, self.mapping, self.index = rom, mapping, index
        self.output_calls = dict(output_calls)
        self.entries = json.loads(mapping)
        self.cache, self.active, self.dependencies, self.call_checks = {}, set(), {}, set()

    def target(self, address):
        if thunks.reserved(address):
            raise ValueError('bounded output closure excludes reserved call thunks')
        # This central resolver also rejects canonical runtimes and their aliases.
        actual = match.function_address_target(f'func_{address:08X}', self.entries,
            0, 0, len(self.rom))
        if actual != address:
            raise ValueError('bounded output target binding differs')
        data = match.BufferCallProof(self.rom, self.mapping).span(address)
        if len(data) > MAX_BYTES:
            raise ValueError('bounded output callee exceeds its native byte budget')
        owner.validate_span(data, address, self.rom, self.mapping, self.index)
        if address not in self.dependencies and len(self.dependencies) >= MAX_DEPENDENCIES:
            raise ValueError('bounded output closure exceeds its dependency budget')
        self.dependencies[address] = data
        return data

    def prove(self, address, arguments):
        """Prove all paths, effects and native frames, including every nested call."""
        arguments = tuple(sorted(arguments))
        if any(not ARM_REG_R0 <= register <= ARM_REG_R3 for register in arguments):
            raise ValueError('bounded output pointers require ordinary register arguments')
        key = address, arguments
        if key in self.cache:
            return self.cache[key]
        if address in self.active:
            raise ValueError('bounded output closure excludes recursive calls')
        self.active.add(address)
        try:
            data = self.target(address)
            refined = owner.refine(data, address, self.mapping)
            instructions, edges, branches, calls, words = graph.graph(data, address, refined)
            if branches or words:
                raise ValueError('bounded output closure requires direct finite native CFGs')
            partition = graph.partition(data, address, refined, instructions, words)
            # A topological order proves termination of every local path, rather
            # than using an iteration cap as an assumed runtime bound.
            indegree = {site:0 for site in instructions}
            for successors in edges.values():
                for successor in successors:indegree[successor] += 1
            pending = [site for site in instructions if not indegree[site]]
            ordered = []
            while pending:
                site = pending.pop();ordered.append(site)
                for successor in edges[site]:
                    indegree[successor] -= 1
                    if not indegree[successor]:pending.append(successor)
            if len(ordered) != len(instructions):
                raise ValueError('bounded output closure excludes unbounded local cycles')
            states = {address:{register:frozenset(((register,0),)) for register in arguments}}
            effects, children = set(), {}
            clobbered = set(match.CALLER_CLOBBERED)
            for site in ordered:
                instruction = instructions[site]
                incoming = states[site];aliases = dict(incoming)
                operands = instruction.operands
                read, written = instruction.regs_access()
                if instruction.mnemonic == 'push':
                    if any(op.reg in aliases for op in operands):
                        raise ValueError('bounded output pointer cannot be pushed or spilled')
                elif instruction.mnemonic == 'pop':
                    for operand in operands:aliases.pop(operand.reg,None)
                elif site in calls:
                    passed = {register for register in aliases if register in clobbered}
                    if any(UNKNOWN in aliases[register] for register in passed):
                        raise ValueError('bounded output call has an ambiguous pointer argument')
                    child = self.prove(calls[site], passed)
                    children[site] = child
                    for mode,register,low,high in child['effects']:
                        for root,offset in aliases[register]:
                            effects.add((mode,root,offset+low,offset+high))
                    for register in clobbered:aliases.pop(register,None)
                else:
                    # Reuse authenticated Thumb pointer move/immediate arithmetic.
                    assignment = match.register_alias_assignment(instruction,
                        {register:0 for register in aliases})
                    allowed = {assignment[2]} if assignment is not None else set()
                    if instruction.mnemonic.startswith(('stm','ldm')):
                        raise ValueError('bounded output closure excludes block memory effects')
                    for operand in operands:
                        if operand.type != ARM_OP_MEM:continue
                        if operand.mem.index or instruction.writeback or instruction.mnemonic not in WIDTHS:
                            raise ValueError('bounded output requires exact immediate memory effects')
                        width = WIDTHS[instruction.mnemonic]
                        base = operand.mem.base
                        if base in aliases:
                            if UNKNOWN in aliases[base]:
                                raise ValueError('bounded output memory base has an ambiguous alias join')
                            for root,offset in aliases[base]:
                                low = offset + operand.mem.disp
                                if not -MAX_BYTES <= low < low+width <= MAX_BYTES:
                                    raise ValueError('bounded output effect exceeds its range budget')
                                effects.add(('write' if instruction.mnemonic.startswith('str') else 'read',
                                    root,low,low+width))
                            allowed.add(base)
                        elif base == ARM_REG_SP:
                            # The independent native frame proof below bounds
                            # every local access and excludes saved-slot writes.
                            pass
                        elif base == ARM_REG_PC and instruction.mnemonic == 'ldr':
                            pass
                        else:
                            raise ValueError('bounded output closure has unknown/global memory effects')
                        if instruction.mnemonic.startswith('str') and operands[0].reg in aliases:
                            raise ValueError('bounded output pointer cannot escape through memory')
                    if set(read) & aliases.keys() - allowed:
                        raise ValueError('bounded output pointer has an unsupported use or escape')
                    for register in written:aliases.pop(register,None)
                    if assignment is not None:
                        destination,delta,source = assignment
                        if destination in (ARM_REG_SP,ARM_REG_PC,ARM_REG_LR):
                            raise ValueError('bounded output pointer overwrites a control register')
                        aliases[destination] = frozenset((root,offset+delta) if root >= 0 else UNKNOWN
                            for root,offset in incoming[source])
                if not edges[site] and (ARM_REG_R0 in aliases or ARM_REG_R1 in aliases):
                    raise ValueError('bounded output pointer escapes through an ABI result register')
                for successor in edges[site]:
                    previous = states.get(successor)
                    states[successor] = dict(aliases) if previous is None else {
                        register:previous.get(register,frozenset((UNKNOWN,))) |
                            aliases.get(register,frozenset((UNKNOWN,)))
                        for register in previous.keys() | aliases.keys()}
            # Native instruction/stack/entry-LR proof is independent of the
            # effect interpreter. Every internal ABI premise is discharged by
            # the child's complete frame proof, including a call-free leaf.
            verified = match.verify_leaf_instructions(data,address,True,calls)
            if {item.address for item in verified} != set(instructions):
                raise ValueError('bounded output native CFG differs from effect coverage')
            preserved = frozenset(range(ARM_REG_R4,ARM_REG_R11+1))
            restored = frame.prove_frame(instructions,edges,address,{},calls,
                call_preservation={site:preserved for site in calls})
            result = {'schema':SCHEMA,'address':address,'end':address+len(data),
                'argument_registers':list(arguments),'effects':[list(row) for row in sorted(effects)],
                'body_sha256':hashlib.sha256(data).hexdigest(),'partition':partition,'frame':restored,
                'calls':[[site,target] for site,target in sorted(calls.items())],
                'complete_native_proof':True,'conditional_internal_ABI':False,
                'effect_policy':'exact decoded argument-relative accesses, union over every retained CFG alternative',
                'maximum_stack_bytes':restored['maximum_frame_bytes'] +
                    max((child['maximum_stack_bytes'] for child in children.values()),default=0),
                'scratch_pointer_policy':'r0/r1 pointer results rejected; r2/r3/r12 are ABI scratch, cleared at caller',
                'global_or_unknown_effects':[],
                'frame_memory_separation_contract':{
                    'argument_effect_windows':'entirely at or above callee entry SP',
                    'return_preservation':'proved under this explicit memory separation contract, not for arbitrary pointer numerics',
                    'own_and_nested_frames':'strictly below callee entry SP, bounded by maximum_stack_bytes',
                    'discharge':'caller checks each effect byte lies in its live allocated local words at/above call SP',
                    'arbitrary_pointer_ABI_claim':False}}
            self.cache[key] = result
            return result
        finally:
            self.active.remove(address)

    def check_call(self, address, aliases, stack, slots=None, *, site=None, words=None, **kwargs):
        if self.output_calls.get(site) != address:
            raise ValueError('unmarked ordinary/runtime calls reject stack arguments')
        if slots or words or any(register in aliases for register in (ARM_REG_R12,ARM_REG_LR)):
            raise ValueError('bounded output excludes stack-passed, spilled or scratch pointer arguments')
        arguments = {register:offset for register,offset in aliases.items() if register in match.CALLER_CLOBBERED}
        if not arguments:
            raise ValueError('bounded output site requires actual allocated-local pointer arguments')
        proof = self.prove(address, arguments)
        if not any(row[0] == 'write' for row in proof['effects']):
            raise ValueError('bounded output site requires a proved argument-relative write')
        resolved = []
        for mode,register,low,high in proof['effects']:
            offset = arguments[register]+low
            width = high-low
            match.BufferCallProof.access(offset,width,stack)
            resolved.append((mode,register,offset,offset+width))
        for mode,register,low,high in resolved:
            if any(other != register and (mode == 'write' or access == 'write') and low < end and high > start
                    for access,other,start,end in resolved):
                raise ValueError('bounded output argument effects overlap')
        self.call_checks.add((site,address,tuple(sorted(arguments.items())),tuple(resolved)))
        return {}

    def fingerprint(self):
        digest = hashlib.sha256()
        for address,data in sorted(self.dependencies.items()):
            digest.update(address.to_bytes(4,'little'));digest.update(len(data).to_bytes(4,'little'));digest.update(data)
        return digest.hexdigest()

    def manifest(self):
        return {'schema':SCHEMA,'dependencies':[self.cache[key] for key in sorted(self.cache)],
            'calls':[[site,address,list(arguments),list(effects)]
                for site,address,arguments,effects in sorted(self.call_checks)],
            'frame_memory_separation':'every checked output window lies at/above call SP; closure own/nested frames are below it',
            'fingerprint':self.fingerprint(),'rom_sha256':hashlib.sha256(self.rom).hexdigest(),
            'mapping_sha256':hashlib.sha256(self.mapping).hexdigest(),
            'index_sha256':hashlib.sha256(self.index).hexdigest()}
