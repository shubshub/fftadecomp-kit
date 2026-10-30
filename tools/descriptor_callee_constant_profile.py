"""Exact callee-saved constants require complete native register-origin proofs."""
import hashlib
import json

import match
import function_thunk_profile as thunk
import local_long_branch_profile as frame
import descriptor_disjunctive_alias_profile as alternatives

SELECTOR = 'descriptor-callee-constant-v1'
SCHEMA = 'elf-symbol-thumb-descriptor-callee-constant-v1'
CONTROL_FLOW = 'complete Thumb owner with exact alternatives and native-proved callee-saved constants'
MAX_DEPENDENCIES = alternatives.MAX_DEPENDENCIES
MAX_STACK_BYTES = alternatives.MAX_STACK_BYTES
MAX_PATH_STATES = alternatives.MAX_PATH_STATES
PRESERVED = frozenset(range(match.ARM_REG_R0+4, match.ARM_REG_R0+12))


def _sha(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


class DescriptorCalleeConstantProof(alternatives.DescriptorDisjunctiveAliasProof):
    def __init__(self, *args):
        super().__init__(*args)
        self.preservation_graphs = {}
        self.preserved_frames = {}
        self.preservation_failures = {}
        self.preserved_calls = {}
        self.call_proofs = {}
        self.constant_results = {}
        self.constant_transfers = {}

    def inspect(self, address, data):
        instructions,finite = super().inspect(address,data)
        self.preservation_graphs[address] = (instructions,finite)
        return instructions,finite

    def complete_frame(self, address, data, instructions):
        super().complete_frame(address,data,instructions)
        verified,finite = self.preservation_graphs[address]
        reached = {item.address:item for item in verified}
        edges,calls = {},{}
        for site,item in reached.items():
            operands=item.operands
            registers=tuple(operand.reg for operand in operands if operand.type==match.ARM_OP_REG)
            if site in finite:
                successors=finite[site]
            elif item.mnemonic=='bx' or item.mnemonic=='pop' and match.ARM_REG_PC in registers or \
                    item.mnemonic=='mov' and registers and registers[0]==match.ARM_REG_PC:
                successors=()
            elif item.id==match.ARM_INS_B:
                successors=(operands[0].imm,)
                if item.cc not in (match.ARM_CC_AL,match.ARM_CC_INVALID):
                    successors+=(site+item.size,)
            else:
                successors=(site+item.size,)
            edges[site]=successors
            if match.CS_GRP_CALL in item.groups:
                calls[site]=operands[0].imm
        branches={}
        self.preserved_frames.pop(address,None)
        summaries = self.preserved_calls.get(address,{})
        try:
            if any(summaries.get(site)!=PRESERVED for site in calls):
                raise ValueError('constant preservation requires completed actual callee proofs at every call')
            proof = frame.prove_frame(reached,edges,address,branches,calls,
                call_preservation={site:summaries.get(site,frozenset()) for site in calls})
        except ValueError as error:
            # This optional proof exports no constant when its stronger contract
            # fails. The independent actual effects and native frame gates passed.
            self.preservation_failures[address] = str(error)
            return
        self.preservation_failures.pop(address,None)
        self.preserved_frames[address] = {'address':address,
            'body_sha256':hashlib.sha256(data).hexdigest(), **self.identities,
            'frame':proof, 'calls':[{'site':site,'proofs':[row for _,row in
                sorted(self.call_proofs[address][site].items())]} for site in sorted(calls)]}

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **word_context):
        resolved = address
        if address in thunk.ALIASES.values():
            register=match.ARM_REG_R0+(address-thunk.START)//4
            value=(constants or {}).get(register)
            if type(value) is int:
                resolved=value & ~1
        before = self.native_frames.get(resolved,0)
        result = super().check_arguments(address,arguments,stack,incoming,protected,
            constants=constants,site=site,**word_context)
        token = None
        record = self.preserved_frames.get(resolved)
        if self.native_frames.get(resolved,0)>before and record is not None:
            identity=_sha(record)
            if resolved!=address:
                # The thunk authenticates this transfer only. Preservation comes
                # from the independently completed actual target above.
                identity=_sha([self.records[address],identity])
            token = {'result':result,'address':address,'site':site,'preserved':PRESERVED,
                     'proof_sha256':identity,'resolved_address':resolved}
            self.constant_results[id(result)] = token
        if site is not None:
            parents = [row for row in self.entries
                       if int(row['rom'],16)<=site<int(row['end'],16)]
            decoder=match.Cs(match.CS_ARCH_ARM,match.CS_MODE_THUMB);decoder.detail=True
            instruction=next(decoder.disasm(self.rom[site-match.ROM_BASE:site-match.ROM_BASE+4],site),None)
            if len(parents)==1 and instruction is not None and instruction.mnemonic=='bl' and \
                    len(instruction.operands)==1 and instruction.operands[0].type==match.ARM_OP_IMM and \
                    instruction.operands[0].imm==address:
                parent=int(parents[0]['rom'],16)
                proved=token['preserved'] if token is not None else frozenset()
                old=self.preserved_calls.setdefault(parent,{}).get(site,PRESERVED)
                self.preserved_calls[parent][site]=old & proved
                call_record={'site':site,'target':address,
                    'preserved':sorted(self.preserved_calls[parent][site]),
                    'resolved_address':None if token is None else token['resolved_address'],
                    'proof_sha256':None if token is None else token['proof_sha256']}
                self.call_proofs.setdefault(parent,{}).setdefault(site,{})[_sha(call_record)]=call_record
        return result

    def finish_call_constants(self, constants, result, *, site=None, target=None):
        before=dict(constants)
        super().finish_call_constants(constants,result,site=site,target=target)
        token=self.constant_results.get(id(result))
        if token is None or token['result'] is not result or token['site']!=site or token['address']!=target:
            return
        constants.update((register,value) for register,value in before.items()
                         if register in token['preserved'])
        if constants:
            row={'site':site,'target':target,'resolved_address':token['resolved_address'],
                 'before':sorted(before.items()),'kept':sorted(constants.items()),
                 'proof_sha256':token['proof_sha256']}
            self.constant_transfers[_sha(row)]=row

    def constant_observations(self):
        return {'frames':[row for _,row in sorted(self.preserved_frames.items())],
                'refused_frames':[{'address':address,'reason':reason}
                                  for address,reason in sorted(self.preservation_failures.items())],
                'transfers':[row for _,row in sorted(self.constant_transfers.items())]}
