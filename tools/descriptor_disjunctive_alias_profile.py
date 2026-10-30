"""Bounded exact stack-alias alternatives with complete per-path effect replay."""
import hashlib
import json

import descriptor_single_store_profile as store
from protected_descriptor_word_profile import WordResult

SELECTOR = 'descriptor-disjunctive-alias-v1'
SCHEMA = 'elf-symbol-thumb-descriptor-disjunctive-alias-v1'
CONTROL_FLOW = 'complete Thumb owner with bounded exact stack-alias alternatives and mandatory context/frame replay'
MAX_DEPENDENCIES = store.MAX_DEPENDENCIES
MAX_STACK_BYTES = store.MAX_STACK_BYTES
MAX_PATH_STATES = 4096


def _text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


class _AlternativeResult(WordResult):
    def __init__(self, alternatives):
        # No arm is selected or merged. Both caller engines expand every result.
        super().__init__({}, {})
        self.alternatives = tuple(alternatives)


class _DisjunctiveStructuralFrame(store._SingleStoreStructuralFrame):
    callee_frames = True
    exact_alias_state_budget = MAX_PATH_STATES


class DescriptorDisjunctiveAliasProof(store.DescriptorSingleStoreProof):
    exact_alias_state_budget = MAX_PATH_STATES
    structural_frame_type = _DisjunctiveStructuralFrame

    def __init__(self, *args):
        super().__init__(*args)
        self.alias_paths = {}

    def alias_path_context(self, address, arguments, stack, incoming, protected,
                           constants, words, frame_base, root_frame, watched, site):
        context = {'address':address, 'call_site':site, 'arguments':sorted(arguments.items()),
            'stack':list(stack), 'incoming':sorted(incoming.items()), 'protected':sorted(protected),
            'constants':sorted(constants.items()), 'words':sorted(words.items()),
            'frame_base':frame_base, 'root_frame':root_frame, 'watched':sorted(watched)}
        key = hashlib.sha256(_text(context).encode()).hexdigest()
        if key not in self.alias_paths:
            self.alias_paths[key] = {'context':context, 'states':{}, 'edges':set(), 'returns':{}}
        return key

    def observe_alias_state(self, context, site, state, predecessor=None, previous=None):
        row = self.alias_paths[context]
        key = hashlib.sha256(_text([site,state]).encode()).hexdigest()
        row['states'][key] = {'id':key, 'site':site, 'state':state}
        if predecessor is not None:
            origin = hashlib.sha256(_text([predecessor,previous]).encode()).hexdigest()
            row['edges'].add((origin,key))

    def alternative_result(self, alternatives):
        return _AlternativeResult(alternatives)

    def observe_alias_return(self, context, site, state, result):
        key = hashlib.sha256(_text([site,state]).encode()).hexdigest()
        self.alias_paths[context]['returns'][key] = result

    def alias_observations(self):
        return [{'id':key, 'context':row['context'],
                 'states':[row['states'][state] for state in sorted(row['states'])],
                 'edges':[list(edge) for edge in sorted(row['edges'])],
                 'returns':[{'state':state, 'effects':result}
                            for state,result in sorted(row['returns'].items())]}
                for key,row in sorted(self.alias_paths.items())]
