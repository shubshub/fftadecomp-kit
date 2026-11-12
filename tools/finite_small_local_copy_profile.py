"""Exact bounded halfword cursor replay after a selected small local copy.

Only one straight-line bottom-tested signed counter loop is supported. This
context retains exact native alias states and selects the branch using its
authenticated counter, never by widening or deleting a cursor alias.
"""
import json

import match
import owner_graph_profile as graph
import small_local_copy_caller_profile as caller
from local_rom_halfword_table_profile import require

SELECTOR = 'conditional-finite-small-local-copy-caller-v1'
SCHEMA = 'native-thumb-finite-small-local-copy-caller-v1'
MAX_STATES = 4096


class LoopProof(caller.SmallLocalCopyProof):
    def __init__(self, data, address, rom, mapping, index, objects, *, selector):
        require(type(selector) is str and selector == SELECTOR, 'explicit finite small-copy selector required')
        super().__init__(data, address, rom, mapping, index, objects, selector=caller.SELECTOR)
        import owner_admission_profile as owner
        ins, edges, branches, calls, words = graph.graph(data, address, owner.refine(data, address, mapping))
        require(not branches and not words and calls == {self.copy['call_site']:self.copy['target']},
                'finite small copy requires only its exact helper call')
        controls = [item for item in ins.values() if item.id == match.ARM_INS_B]
        require(len(controls) == 1 and controls[0].mnemonic == 'ble' and controls[0].size == 2,
                'one signed bottom-tested BLE loop required')
        branch = controls[0]
        header, latch = branch.operands[0].imm, branch.address
        require(self.copy['call_site']+4 < header < latch, 'loop must follow the actual copy')
        body = list(range(header, latch+2, 2))
        require(all(node in ins and ins[node].size == 2 for node in body), 'straight Thumb16 loop body required')
        require(all(edges[node] == (node+2,) for node in body[:-1]) and
                set(edges[latch]) == {header, latch+2}, 'loop body has alternative control')
        predecessors = {node:set() for node in ins}
        for node, successors in edges.items():
            for successor in successors:
                predecessors[successor].add(node)
        require(all(predecessors[node] == {node-2} for node in body[1:]) and
                predecessors[header] == {header-2,latch}, 'loop has an alternative interior entry')
        comparison, update = ins[latch-2], ins[latch-4]
        op = comparison.operands
        require(comparison.mnemonic == 'cmp' and len(op) == 2 and
                op[0].type == match.ARM_OP_REG and op[1].type == match.ARM_OP_IMM,
                'loop requires adjacent scalar immediate comparison')
        self.counter, self.bound = op[0].reg, op[1].imm
        require(0 <= self.bound <= 4 and 2*(self.bound+1) == self.copy['count'],
                'loop bound must exhaust exactly the authenticated copied halfwords')
        require(bytes(update.bytes) == bytes((1, 0x30+self.counter-match.ARM_REG_R0)) and
                match.ARM_REG_R0 <= self.counter <= match.ARM_REG_R0+7 and update.mnemonic == 'adds',
                'loop counter must increment by one immediately before CMP')
        require(all(self.counter not in ins[node].regs_access()[1] for node in body if node != latch-4),
                'loop body overwrites the authenticated counter')
        pre = []
        node = self.copy['call_site']+4
        while node != header:
            require(node in ins and node not in pre and edges[node] == (node+ins[node].size,),
                    'copy-to-loop prefix must be straight control')
            pre.append(node); node += ins[node].size
        writers = [ins[node] for node in pre if self.counter in ins[node].regs_access()[1]]
        require(writers and bytes(writers[-1].bytes) == bytes((0,0x20+self.counter-match.ARM_REG_R0)),
                'loop counter must be initialized to zero after copy')
        increments = [ins[node] for node in body if ins[node].mnemonic == 'adds' and
                      len(ins[node].operands) == 2 and ins[node].operands[1].type == match.ARM_OP_IMM and
                      ins[node].operands[1].imm == 2]
        candidates = []
        for item in increments:
            cursor = item.operands[0].reg
            definitions = [ins[node] for node in pre if cursor in ins[node].regs_access()[1]]
            if definitions and definitions[-1].mnemonic == 'mov' and \
                    len(definitions[-1].operands) == 2 and definitions[-1].operands[1].type == match.ARM_OP_REG and \
                    definitions[-1].operands[1].reg == match.ARM_REG_SP:
                candidates.append((cursor,item.address))
        require(len(candidates) == 1, 'one actual SP-derived halfword cursor required')
        self.cursor, self.cursor_update = candidates[0]
        require(self.cursor != self.counter and self.copy['destination_entry_sp_offset'] == self.copy['caller_sp_offset'],
                'loop cursor must begin at the actual copy destination')
        reads = []
        for node in body:
            item = ins[node]
            read, written = item.regs_access()
            if self.cursor in written:
                require(node == self.cursor_update, 'loop cursor has an unexpected write')
            if self.cursor in read and node != self.cursor_update:
                op = item.operands
                require(node < self.cursor_update and item.mnemonic == 'ldrh' and len(op) == 2 and
                        op[1].type == match.ARM_OP_MEM and op[1].mem.base == self.cursor and
                        not op[1].mem.index and op[1].mem.disp == 0 and not item.writeback,
                        'loop cursor use must be an unindexed pre-increment halfword load')
                reads.append(node)
        require(reads, 'loop must read actual initialized copied halfwords')
        self.data, self.address, self.calls = data, address, calls
        self.native_sites = frozenset(ins)
        self.header, self.latch = header, latch
        self.counter_update = latch-4
        self.loop_reads = reads
        self.branch_observations = set()

    def extra_constant(self, instruction, data, address, constants):
        if instruction.address == self.counter_update:
            value = constants.get(self.counter)
            require(type(value) is int and 0 <= value <= self.bound,
                    'finite loop counter lost its exact authenticated value')
            return value+1
        return super().extra_constant(instruction, data, address, constants)

    def successors(self, current, constants, aliases):
        value = constants.get(self.counter)
        require(current == self.latch and type(value) is int and 1 <= value <= self.bound+1,
                'finite branch lacks exact bounded counter')
        require(aliases.get(self.cursor) == self.copy['caller_sp_offset']+2*value,
                'finite cursor differs from exact counter-derived copy extent')
        target = self.header if value <= self.bound else self.latch+2
        self.branch_observations.add((current,value,target))
        return (target,)


def validate_context(context, buffer_proof, data, address, calls, thumb, others):
    require(type(context) is LoopProof and context is buffer_proof and thumb and
            context.data == data and context.address == address and context.calls == dict(calls or {}) and
            not any(value is not None and value is not False for value in others),
            'finite small-copy replay requires its isolated fresh exact native context')
    # Bind cached producer/input facts afresh, preventing stale mutated objects
    # from granting branch filtering independently of their original proof.
    fresh = LoopProof(data,address,context.rom,context.mapping,context.index,context.objects,selector=SELECTOR)
    require(context.copy == fresh.copy and all(getattr(context,key) == getattr(fresh,key)
            for key in ('header','latch','counter','bound','cursor','cursor_update','counter_update','loop_reads','native_sites')),
            'finite small-copy context is stale')


def verify(data, address, rom, mapping, index, objects, *, selector, manifest=None):
    proof = LoopProof(data,address,rom,mapping,index,objects,selector=selector)
    instructions = match.verify_leaf_instructions(data,address,True,proof.calls,
        buffer_proof=proof,finite_small_copy_context=proof)
    require({item.address for item in instructions} == proof.native_sites,
            'finite native replay does not cover the complete authenticated owner')
    expected = {(proof.latch,value,proof.header if value <= proof.bound else proof.latch+2)
                for value in range(1,proof.bound+2)}
    require(proof.branch_observations == expected and proof.copy_observations,
            'finite copy replay did not cover every exact bounded iteration')
    observed = dict(schema=SCHEMA,selector=SELECTOR,caller=proof.copy,native_instructions=len(instructions),
        loop=dict(header=proof.header,latch=proof.latch,counter=proof.counter-match.ARM_REG_R0,
            cursor=proof.cursor-match.ARM_REG_R0,iterations=proof.bound+1,
            branch_observations=sorted(proof.branch_observations),
            initialized_halfword_reads=[[site,proof.copy['caller_sp_offset']+2*i,2]
                for i in range(proof.bound+1) for site in proof.loop_reads]),
        native_frame_alias_replay=True,source_or_ELF_admission=False,physical_access_proved=False,
        suffix_initialization_proved=False,buffer_fingerprint=proof.fingerprint())
    observed['conditions'] = proof.copy['conditions'] + [
        'ordinary external suffix stores do not alias the active copied local bytes, active saves or code; loaded scalar table values and external accesses retain ordinary memory validity premises',
        'halfword read values retain copied initialization only under the external-store nonalias premise; no physical nonalias or table-extent fact is proved']
    require(manifest is None or json.dumps(manifest,sort_keys=True) == json.dumps(observed,sort_keys=True),
            'finite small-copy manifest is stale')
    return observed,instructions
