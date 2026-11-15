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
RESTORING_SELECTOR = 'descriptor-disjunctive-restoring-leaf-alias-v1'
RESTORING_SCHEMA = 'elf-symbol-thumb-descriptor-disjunctive-restoring-leaf-alias-v1'
CALLEE_SELECTOR = 'descriptor-disjunctive-restoring-callee-alias-v1'
CALLEE_SCHEMA = 'elf-symbol-thumb-descriptor-disjunctive-restoring-callee-alias-v1'
BOUNDED_SELECTOR = 'bounded-disjunctive-restoring-callee-scratch-v1'
BOUNDED_SCHEMA = 'elf-symbol-thumb-bounded-disjunctive-restoring-callee-scratch-v1'
PROFILES = {SELECTOR: SCHEMA, RESTORING_SELECTOR: RESTORING_SCHEMA,
            CALLEE_SELECTOR: CALLEE_SCHEMA, BOUNDED_SELECTOR: BOUNDED_SCHEMA}


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


class RestoringLeafDisjunctiveProof(DescriptorDisjunctiveAliasProof):
    """Replay every effect after proving opaque saved entry values unobserved."""

    _leaf_alias_policy = True
    restoration_schema = RESTORING_SCHEMA

    def _restore_aliases(self,address,watched,arguments):
        import static_callback_r6_frame_profile as restoring
        return restoring.R6FrameCallbackProof._restore_leaf_aliases(
            self,address,watched,arguments)

    def __init__(self, *args):
        super().__init__(*args)
        self.leaf_restorations = {}

    def _graph(self, address):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        data = self.span(address)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data,address,refinement)
        if branches or words:
            raise ValueError('restoring descriptor leaf excludes local BL and switches')
        return data,ins,edges,calls,graph.partition(data,address,refinement,ins,words)

    def check_arguments(self,address,arguments,stack,incoming,protected,*,
                        constants=None,site=None,**context):
        watched = tuple(context.get('watched', ()))
        reduced, record = watched, None
        if watched:
            reduced, record = self._restore_aliases(address,watched,arguments)
        result = super().check_arguments(address,arguments,stack,incoming,protected,
            constants=constants,site=site,**dict(context,watched=reduced))
        if record is not None:
            observation = dict(site=site,watched=sorted(watched),
                retained_watched=sorted(reduced),restoration=record)
            self.leaf_restorations[_text(observation)] = observation
        return result

    def restoring_leaf_manifest(self):
        from pathlib import Path
        import importlib
        if not self.leaf_restorations:
            raise ValueError('restoring descriptor policy requires an actual checked leaf restoration')
        producers = ('descriptor_disjunctive_alias_profile','static_callback_r6_frame_profile',
                     'local_long_branch_profile','owner_graph_profile','owner_admission_profile',
                     'analyze','match', 'armv4t')
        if self.restoration_schema in (CALLEE_SCHEMA,BOUNDED_SCHEMA):
            producers += ('callee_saved_alias_restoration',)
        return dict(schema=self.restoration_schema,
            source_sha256={name+'.py':hashlib.sha256(
                Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                for name in producers},
            observations=[self.leaf_restorations[key] for key in sorted(self.leaf_restorations)])


class RestoringCalleeDisjunctiveProof(RestoringLeafDisjunctiveProof):
    restoration_schema = CALLEE_SCHEMA

    def _restore_aliases(self,address,watched,arguments):
        import callee_saved_alias_restoration as restoring
        data,ins,edges,calls,partition=self._graph(address)
        return restoring.prove(data,ins,edges,calls,partition,address,watched,arguments)


class BoundedRestoringScratchProof(RestoringCalleeDisjunctiveProof):
    """Ordinary bounded outputs need no descriptor or STMIA existence premise."""

    restoration_schema = BOUNDED_SCHEMA

    def __init__(self,*args):
        super().__init__(*args)
        self._root_return_context = None
        self._root_scratch = set()

    def bind_root(self,address,data):
        if self._root_return_context is not None or self.span(address)!=data:
            raise ValueError('bounded scratch root requires its exact unique complete body')
        actual,ins,edges,calls,partition=self._graph(address)
        self._root_return_context=(address,data,frozenset(site for site in edges if not edges[site]))

    def root_scratch_manifest(self):
        import local_long_branch_profile as frame
        if self._root_return_context is None or not self._root_scratch:
            raise ValueError('bounded scratch requires an actual checked root return projection')
        address,data,returns=self._root_return_context
        return dict(schema=frame.DISCARDED_SCRATCH_SCHEMA,
            contract=frame.DISCARDED_SCRATCH_CONTRACT,registers=[2,3],
            address=address,body_sha256=hashlib.sha256(data).hexdigest(),
            observations=sorted(self._root_scratch),
            limits='Only R2/R3 at the exact root normal return are discarded under '
                'the existing explicit external-return ABI contract. All preceding '
                'uses, effects, bounds, path alternatives and frame returns replay. '
                'R0/R1 and nested returns retain their existing escape checks.')


def root_return_aliases(proof,data,address,site,aliases):
    """Closed root-only hook; arbitrary subclasses receive no projection."""
    if type(proof) is not BoundedRestoringScratchProof:
        return aliases
    if proof._root_return_context is None:
        raise ValueError('bounded scratch requires its bound root context')
    root,body,returns=proof._root_return_context
    if address!=root or data!=body or site not in returns or proof.active:
        raise ValueError('bounded scratch differs from its exact normal root return')
    import match
    scratch={match.ARM_REG_R0+2,match.ARM_REG_R0+3}
    proof._root_scratch.update((site,reg-match.ARM_REG_R0,offset)
        for reg,offset in aliases.items() if reg in scratch)
    return {reg:offset for reg,offset in aliases.items() if reg not in scratch}
