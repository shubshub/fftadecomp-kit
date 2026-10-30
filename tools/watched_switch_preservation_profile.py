"""Existing complete guarded switches replayed for watched buffer preservation."""
import hashlib
import json

import match
import owner_graph_profile as graph
import protected_descriptor_word_profile as descriptor

SELECTOR = 'watched-switch-preservation-v1'
SCHEMA = 'elf-symbol-thumb-watched-switch-preservation-v1'
CONTROL_FLOW = 'complete Thumb owner with exact watched aliases across complete read-only guarded switch callees'
MAX_DEPENDENCIES = 14


class WatchedSwitchPreservationProof(descriptor.ProtectedDescriptorWordProof):
    dependency_budget = MAX_DEPENDENCIES

    def __init__(self, *args):
        super().__init__(*args)
        self.switches = set()
        self.switch_reads = {}
        self.switch_contexts = {}

    def inspect(self, address, data):
        import owner_admission_profile as owner
        refinement = owner.refine(data, address, self.mapping)
        if not refinement['word_switches']:
            return super().inspect(address, data)
        instructions, _, branches, calls, words = graph.graph(data, address, refinement)
        if len(refinement['word_switches']) != 1 or branches or calls:
            raise ValueError('watched switch requires one complete call-free guarded switch')
        partition = graph.partition(data, address, refinement, instructions, words)
        switch = match.switch_layout(data, address, words)
        verified = match.verify_leaf_instructions(data, address, True, switch_relocations=words)
        if set(instructions) != {item.address for item in verified}:
            raise ValueError('watched switch differs from complete native CFG')
        # This extension proves no unknown memory effects. Push/pop control words
        # retain the native frame proof; watched-register writes are checked by
        # the existing alias engine on every finite successor and actual context.
        for item in verified:
            if item.size != 2 or item.writeback and item.mnemonic not in ('push', 'pop') or \
                    item.mnemonic.startswith(('str', 'stm', 'swp', 'vstr')) or any(
                        operand.type == match.ARM_OP_MEM and operand.access & match.CS_AC_WRITE
                        for operand in item.operands):
                raise ValueError('watched switch requires read-only narrow Thumb effects')
        transfer = address + switch['dispatch'] + 8
        finite = {transfer: tuple(sorted({address + target for offset, target in words.items()
                                         if offset != switch['literal']}))}
        self.check_lifetime(data, address, verified, finite)
        self.switches.add(address)
        self.switch_reads[address] = {register for item in verified for register in item.regs_access()[0]}
        self.records[address] = {'address': address, 'end': address+len(data), 'bytes': len(data),
            'body_sha256': hashlib.sha256(data).hexdigest(), **self.identities,
            'structure': {'kind': 'existing-complete-read-only-guarded-switch-v1',
                'instructions': len(verified), 'cases': switch['bound']+1,
                'transfer': transfer, 'targets': len(finite[transfer]),
                'partition': {key: partition[key] for key in
                              ('code_bytes', 'literal_and_table_bytes', 'alignment_bytes')},
                'table_sha256': hashlib.sha256(data[switch['literal']:
                    switch['table']+4*(switch['bound']+1)]).hexdigest()}}
        return verified, finite

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **word_context):
        result = super().check_arguments(address, arguments, stack, incoming, protected,
                                        constants=constants, site=site, **word_context)
        if address in self.switches and word_context.get('watched'):
            # Watched registers are caller-held aliases, not callee arguments.
            # This narrow proof requires them to be entirely unobserved; it
            # cannot grant bounds or escape permission to an implicit argument.
            if set(word_context['watched']) & self.switch_reads[address]:
                raise ValueError('watched switch cannot read an unpassed live alias register')
            observation = {'address': address, 'site': site,
                'arguments': [list(pair) for pair in sorted(arguments.items())],
                'incoming': [list(pair) for pair in sorted(incoming.items())],
                'stack': [list(word) for word in stack], 'protected': sorted(protected),
                'constants': [list(pair) for pair in sorted((constants or {}).items())],
                'words': [[slot, list(value)] for slot, value in sorted(word_context['words'].items())],
                'frame_base': word_context['frame_base'], 'root_frame': word_context['root_frame'],
                'watched': sorted(word_context['watched'])}
            self.switch_contexts[json.dumps(observation, sort_keys=True)] = observation
        return result

    def switch_observations(self):
        return [self.switch_contexts[key] for key in sorted(self.switch_contexts)]
