"""Explicit R6 constants through replayed frames and selected R6/R7 callbacks.

No ABI declaration grants preservation. Each ordinary call restores its entry
frame under certificates for all nested calls, and independently replays the
existing alias/effect checks. Callback certificates require complete no-call
owners leaving every callee-saved register unwritten. Normal return and the
existing ordinary memory/ABI boundary remain conditional.
"""
import hashlib
import importlib
import json
from pathlib import Path

import match
import owner_graph_profile as graph
import local_long_branch_profile as frame
import static_callback_target_preservation_profile as r7
import named_data_buffer_profile as named

SELECTOR = 'static-callback-restoring-r6-v1'
SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-v1'
CONTROL_FLOW = 'complete ordinary frames with authenticated R6 restoration and bounded leaf R7 callbacks'
TARGET_SELECTOR = 'static-callback-restoring-r6-target-v1'
TARGET_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-v1'
TARGET_CONTROL_FLOW = 'complete ordinary and R6 callback frames with authenticated restoration and bounded effects'
ALIGNED_TARGET_SELECTOR = 'static-callback-restoring-r6-target-aligned-v1'
ALIGNED_TARGET_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-aligned-v1'
LEAF_ALIAS_SELECTOR = 'static-callback-restoring-r6-target-leaf-alias-aligned-v1'
LEAF_ALIAS_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-leaf-alias-aligned-v1'
LOCAL_SCRATCH_SELECTOR = 'static-callback-restoring-r6-target-leaf-alias-local-scratch-aligned-v1'
LOCAL_SCRATCH_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-leaf-alias-local-scratch-aligned-v1'
QUARANTINE_SELECTOR = 'static-callback-restoring-r6-target-leaf-alias-scratch-leaf-kill-aligned-v1'
QUARANTINE_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-leaf-alias-scratch-leaf-kill-aligned-v1'
MOVS_FRAME_SELECTOR = 'static-callback-restoring-r6-target-movs-frame-aligned-v1'
MOVS_FRAME_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-movs-frame-aligned-v1'
OPTIONAL_LOCAL_FRAME_SELECTOR = 'static-callback-restoring-r6-target-optional-local-frame-aligned-v1'
OPTIONAL_LOCAL_FRAME_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-optional-local-frame-aligned-v1'
COMPACT_CLOSURE_SELECTOR = 'static-callback-restoring-r6-target-compact-closure-aligned-v1'
COMPACT_CLOSURE_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-r6-target-compact-closure-aligned-v1'
ENTRY_ALIAS_SELECTOR = 'static-callback-restoring-entry-aliases-aligned-v1'
ENTRY_ALIAS_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-entry-aliases-aligned-v1'
SCRATCH_PREFIX_SELECTOR = 'static-callback-restoring-scratch-prefix-aligned-v1'
SCRATCH_PREFIX_SCHEMA = 'elf-symbol-thumb-static-callback-restoring-scratch-prefix-aligned-v1'
ENTRY_ALIAS_POLICIES = (ENTRY_ALIAS_SELECTOR, SCRATCH_PREFIX_SELECTOR)
COMPACT_CLOSURE_POLICIES = (COMPACT_CLOSURE_SELECTOR, *ENTRY_ALIAS_POLICIES)
OPTIONAL_LOCAL_FRAME_POLICIES = (OPTIONAL_LOCAL_FRAME_SELECTOR, *COMPACT_CLOSURE_POLICIES)
SMALL_CONSTANT_FRAME_POLICIES = (MOVS_FRAME_SELECTOR, *OPTIONAL_LOCAL_FRAME_POLICIES)
QUARANTINE_POLICIES = (QUARANTINE_SELECTOR, *SMALL_CONSTANT_FRAME_POLICIES)
LOCAL_SCRATCH_POLICIES = (LOCAL_SCRATCH_SELECTOR, *QUARANTINE_POLICIES)
LEAF_ALIAS_POLICIES = (LEAF_ALIAS_SELECTOR, *LOCAL_SCRATCH_POLICIES)
TARGET_POLICIES = (TARGET_SELECTOR, ALIGNED_TARGET_SELECTOR, *LEAF_ALIAS_POLICIES)
ALIGNED_POLICIES = (ALIGNED_TARGET_SELECTOR, *LEAF_ALIAS_POLICIES)
PROFILES = {SELECTOR: (SCHEMA, CONTROL_FLOW), TARGET_SELECTOR: (TARGET_SCHEMA, TARGET_CONTROL_FLOW),
            ALIGNED_TARGET_SELECTOR: (ALIGNED_TARGET_SCHEMA, TARGET_CONTROL_FLOW),
            LEAF_ALIAS_SELECTOR: (LEAF_ALIAS_SCHEMA, TARGET_CONTROL_FLOW),
            LOCAL_SCRATCH_SELECTOR: (LOCAL_SCRATCH_SCHEMA, TARGET_CONTROL_FLOW),
            QUARANTINE_SELECTOR: (QUARANTINE_SCHEMA, TARGET_CONTROL_FLOW),
            MOVS_FRAME_SELECTOR: (MOVS_FRAME_SCHEMA, TARGET_CONTROL_FLOW),
            OPTIONAL_LOCAL_FRAME_SELECTOR: (OPTIONAL_LOCAL_FRAME_SCHEMA, TARGET_CONTROL_FLOW),
            COMPACT_CLOSURE_SELECTOR: (COMPACT_CLOSURE_SCHEMA, TARGET_CONTROL_FLOW),
            ENTRY_ALIAS_SELECTOR: (ENTRY_ALIAS_SCHEMA, TARGET_CONTROL_FLOW),
            SCRATCH_PREFIX_SELECTOR: (SCRATCH_PREFIX_SCHEMA, TARGET_CONTROL_FLOW)}
SCHEMAS = (SCHEMA, TARGET_SCHEMA, ALIGNED_TARGET_SCHEMA, LEAF_ALIAS_SCHEMA,
           LOCAL_SCRATCH_SCHEMA, QUARANTINE_SCHEMA, MOVS_FRAME_SCHEMA, OPTIONAL_LOCAL_FRAME_SCHEMA,
           COMPACT_CLOSURE_SCHEMA, ENTRY_ALIAS_SCHEMA, SCRATCH_PREFIX_SCHEMA)
MAX_DEPENDENCIES = r7.MAX_DEPENDENCIES
REGISTER = match.ARM_REG_R0 + 6
PRESERVED = frozenset(range(match.ARM_REG_R0 + 4, match.ARM_REG_R0 + 12))
REPLAY_GUARD = match.ARM_REG_R0 + 11


def policy_manifest(policy=SELECTOR):
    if policy not in PROFILES:
        raise ValueError('unknown R6 restoration policy')
    target = policy in TARGET_POLICIES
    modules = ('static_callback_r6_frame_profile', 'static_callback_target_preservation_profile',
               'static_callback_buffer_profile', 'named_data_buffer_profile',
               'local_long_branch_profile', 'owner_graph_profile', 'owner_admission_profile',
               'function_thunk_profile', 'analyze', 'inert_spin_profile', 'match')
    result = dict(schema='thumb-static-callback-restoring-r6-target-policy-v1' if target else 'thumb-static-callback-restoring-r6-policy-v1', selector=policy,
        register=6, callbacks='exact canonical R6, complete restoring frames, R6/R11 unwritten' if target else 'exact canonical R7, complete leaf, R4-R11 and SP unwritten',
        ordinary_calls='complete existing restoring frame with exact completed nested call certificates',
        replay='fresh existing buffer alias/effect replay; R11 unwritten guard',
        attestation='same proof instance, result identity and aliases, site, target and incoming R6; once',
        returning='conditional compatible normal return only', descriptor_words=False,
        source_sha256={name+'.py': hashlib.sha256(Path(importlib.import_module(name).__file__).read_bytes()).hexdigest()
                       for name in modules})
    if target:
        result['normal_return_scratch'] = dict(schema=frame.DISCARDED_SCRATCH_SCHEMA,
            registers=[2, 3], contract=frame.DISCARDED_SCRATCH_CONTRACT)
    if policy in ALIGNED_POLICIES:
        import addressed_signed_runtime_profile as alignment
        result['schema'] = 'thumb-static-callback-restoring-r6-target-aligned-policy-v1'
        result['terminal_alignment'] = dict(
            schema='canonical-external-two-byte-thumb-nop-v1',
            scope='unowned external assembler alignment only; complete sized FUNC remains unchanged',
            producer_sha256=hashlib.sha256(Path(alignment.__file__).read_bytes()).hexdigest())
    if policy in LEAF_ALIAS_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-r6-target-leaf-alias-aligned-policy-v1'
        result['leaf_alias_restoration'] = dict(
            schema='complete-no-call-unobserved-entry-alias-restoration-v1',
            registers='watched callee-saved registers except R6 and R11',
            effects='same complete fresh bounded-buffer replay',
            preservation='complete native restoring frame; initial opaque register values cannot be observed except by private PUSH and checked return restoration',
            state_budget=4096, private_saved_words=64, nested_calls=False)
    if policy in LOCAL_SCRATCH_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-r6-target-leaf-alias-local-scratch-aligned-policy-v1'
        result['local_return_scratch'] = dict(schema=frame.DISCARDED_SCRATCH_SCHEMA,
            registers=[2, 3], contract=frame.DISCARDED_SCRATCH_CONTRACT,
            scope='exact active ordinary callee only; complete actual consumer kills each alias before observation or compatible normal return; fresh bounded effects and native restoring frame required')
    if policy in QUARANTINE_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-r6-target-leaf-alias-scratch-leaf-kill-aligned-policy-v1'
        result['scratch_leaf_kill'] = dict(schema='complete-unobserving-scratch-leaf-kill-v1',
            registers=[2, 3], scope='complete no-call no-frame leaf kills every incoming scratch alias before any read and before every return; no callee-saved, SP or LR writes', state_budget=4096)
    if policy in SMALL_CONSTANT_FRAME_POLICIES:
        import local_alias_slot_profile as small
        result['schema'] = 'thumb-static-callback-restoring-r6-target-movs-frame-aligned-policy-v1'
        result['frame_small_constants'] = dict(values=[1, 2, 3],
            scope='existing exact reaching MOVS intersection; all calls erase facts; native SP-add recognizer and bounds unchanged',
            producer_sha256=hashlib.sha256(Path(small.__file__).read_bytes()).hexdigest())
    if policy in OPTIONAL_LOCAL_FRAME_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-r6-target-optional-local-frame-aligned-policy-v1'
        result['optional_local_exit_scratch'] = dict(
            registers=[2, 3], exact_local_offsets=1,
            absent_local_alias=[0, False],
            scope='exit only; one established negative local offset optionally joined with no local alias; actual consumer remains unobserving; no scalar or nonescape theorem')
    if policy in COMPACT_CLOSURE_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-r6-target-compact-closure-aligned-policy-v1'
        result['compact_dependency_closure'] = dict(
            owners=named.GUARDED_ALIAS_MAX_DEPENDENCIES,
            aggregate_body_bytes=named.MAX_BYTES,
            scope='all unique requested complete bodies, including consumers and canonical thunks; every actual effect context still replays independently')
    if policy in ENTRY_ALIAS_POLICIES:
        result['schema'] = 'thumb-static-callback-restoring-entry-aliases-aligned-policy-v1'
        result['entry_alias_restoration'] = dict(
            registers='written watched R4-R10, including R6; R11 remains unwritten',
            entry_values='opaque until killed; private PUSH/POP only; no reads, copies, stack addressing or calls while any relaxed entry value is live',
            restoration='same completed fresh bounded effects and complete native frame with authenticated nested call certificates; every returning path restores all saved registers',
            state_budget=4096, private_saved_words=64)
    if policy == SCRATCH_PREFIX_SELECTOR:
        result['schema'] = 'thumb-static-callback-restoring-scratch-prefix-aligned-policy-v1'
        result['scratch_prefix_kill'] = dict(registers=[2, 3], state_budget=4096,
            prefix='all paths kill every incoming scratch value at actual unconditional writes before any read, copy, save, call or return; non-killing cycles rejected',
            completion='exact consumer owner/site/target and complete target bytes; same proof instance must complete fresh effects and authenticated native frame replay at that actual call; completion digest binds the ordinary restoration evidence')
    return result


class _Result(dict):
    pass


class RestoringLocalBufferProof(match.BufferCallProof):
    """Bind frame-local calls to this same completed ordinary effects replay.

    This object grants no new memory premise. The original replay has already
    visited the exact complete body and every nested call. The separate frame
    verifier still tracks local bounds, saved words and all register origins.
    """

    def __init__(self, proof, active):
        if type(proof) is not R6FrameCallbackProof or not proof._local_scratch_policy or \
                not proof._frames or proof._frames[-1] is not active or \
                not active.get('effects_complete'):
            raise ValueError('local frame requires its same completed effects replay')
        super().__init__(proof.rom, proof.mapping)
        self.proof, self.context = proof, active

    def validate_frame(self, instructions, edges, address, branches, calls, preservation, scratch):
        active = self.context
        if not self.proof._frames or self.proof._frames[-1] is not active or \
                not active.get('effects_complete') or address != active['address']:
            raise ValueError('local frame completion context is no longer active')
        data, actual, successors, actual_calls, partition = self.proof._graph(address)
        if branches or calls != actual_calls or edges != successors or \
                {site: bytes(item.bytes) for site, item in instructions.items()} != \
                {site: bytes(item.bytes) for site, item in actual.items()} or \
                calls != {site: row['target'] for site, row in active['calls'].items()} or \
                preservation != {site: PRESERVED for site in calls}:
            raise ValueError('local frame differs from its complete fresh effects body')
        frame.validate_discarded_exit_scratch(scratch)
        self.record = dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
            partition=partition, calls=[[site, active['calls'][site]] for site in sorted(calls)],
            scope='same completed fresh bounded effects; conditional returning ABI only')
        self.constant_states = None
        if self.proof._small_constant_frame_policy:
            import local_alias_slot_profile as small
            self.constant_states = small.prove_constants(instructions, edges, address)
            self.record['reaching_movs'] = dict(
                producer_sha256=hashlib.sha256(Path(small.__file__).read_bytes()).hexdigest(),
                states=[[site, [[register, value, sorted(origins)]
                    for register, (value, origins) in sorted(state.items())]]
                    for site, state in sorted(self.constant_states.items())])

    def check_call(self, address, aliases, stack, slots=None, *, site=None, **context):
        if not hasattr(self, 'record') or not self.proof._frames or \
                self.proof._frames[-1] is not self.context:
            raise ValueError('local frame call requires its active authenticated completion')
        row = self.context['calls'].get(site)
        if row is None or row['target'] != address or slots or context or row['return_aliases']:
            raise ValueError('local frame call differs from its exact completed buffer effects')
        return {}

    def fingerprint(self):
        return hashlib.sha256(json.dumps(self.record, sort_keys=True).encode()).hexdigest()


class R6FrameCallbackProof(r7.StaticCallbackTargetPreservationProof):
    def __init__(self, rom, mapping, index, objects, *, policy):
        if policy not in PROFILES:
            raise ValueError('R6 restoration requires its exact explicit policy')
        super().__init__(rom, mapping, index, objects, policy=r7.SELECTOR)
        self._restoring_target = policy in TARGET_POLICIES
        self._leaf_alias_policy = policy in LEAF_ALIAS_POLICIES
        self._local_scratch_policy = policy in LOCAL_SCRATCH_POLICIES
        self._scratch_leaf_kill_policy = policy in QUARANTINE_POLICIES
        self._small_constant_frame_policy = policy in SMALL_CONSTANT_FRAME_POLICIES
        self._optional_local_frame_policy = policy in OPTIONAL_LOCAL_FRAME_POLICIES
        self._compact_closure_policy = policy in COMPACT_CLOSURE_POLICIES
        self._entry_alias_policy = policy in ENTRY_ALIAS_POLICIES
        self._scratch_prefix_policy = policy == SCRATCH_PREFIX_SELECTOR
        self._compact_spans = {}
        if self._compact_closure_policy:
            self.dependency_budget = named.GUARDED_ALIAS_MAX_DEPENDENCIES
        if self._restoring_target:
            self._target_register = REGISTER
            self._target_thunk = r7.thunk.ALIASES['_call_via_r6']
        self._frames = []
        self._structure_only = False
        self._restorations = {}
        self._ordinary_completed = {}
        self._leaf_completed = {}
        self._scratch_returns = {}
        self._scratch_prefix_obligations = {}
        self._scratch_prefix_completions = {}

    def span(self, address):
        data = super().span(address)
        if self._compact_closure_policy:
            total = sum(row['bytes'] for target, row in self._compact_spans.items()
                        if target != address) + len(data)
            if total > named.MAX_BYTES:
                raise ValueError('compact dependency aggregate body budget exceeded')
            self._compact_spans[address] = dict(address=address, bytes=len(data),
                body_sha256=hashlib.sha256(data).hexdigest())
        return data

    def compact_dependency_closure(self):
        if not self._compact_closure_policy or set(self._compact_spans) != self.requested:
            raise ValueError('compact closure requires every requested complete body')
        rows = [self._compact_spans[address] for address in sorted(self._compact_spans)]
        return dict(owners=len(rows), aggregate_body_bytes=sum(row['bytes'] for row in rows),
                    bodies=rows)

    def normal_return_aliases(self, address, site, aliases):
        if not self._restoring_target:
            return super().normal_return_aliases(address, site, aliases)
        # This selector explicitly assumes R2/R3 are discarded at compatible
        # normal returns. The actual complete consumer must also leave those
        # aliases unobserved until a write or normal return kills them.
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3}
        projected = {register: offset for register, offset in aliases.items() if register in scratch}
        if projected:
            if not self._frames or self._frames[-1]['address'] != address:
                raise ValueError('scratch projection requires its active exact callee')
            active = self._frames[-1]
            call_site = active['site']
            owners = [row for row in self.entries if int(row['rom'],16) <= call_site < int(row['end'],16)]
            if len(owners) != 1:
                raise ValueError('scratch projection requires one complete consumer owner')
            consumer = int(owners[0]['rom'],16)
            data, ins, edges, calls, partition = self._graph(consumer)
            if calls.get(call_site) != active['call_target']:
                raise ValueError('scratch projection differs from the actual consumer call')
            pending = [(call_site+ins[call_site].size, frozenset(projected))]
            seen = set()
            quarantined = {}
            while pending:
                current, live = pending.pop()
                if (current, live) in seen:
                    continue
                seen.add((current, live))
                instruction = ins[current]
                read, written = instruction.regs_access()
                if set(read) & live:
                    raise ValueError('consumer observes projected return scratch before a killing write')
                if current in calls and live:
                    if not self._scratch_leaf_kill_policy:
                        raise ValueError('consumer observes projected return scratch before a killing write')
                    quarantined[current] = (self._scratch_prefix_kill(calls[current], live,
                        consumer=consumer, site=current) if self._scratch_prefix_policy else
                        self._scratch_leaf_kill(calls[current], live))
                    live = frozenset()
                live -= set(written)
                pending.extend((target, live) for target in edges[current] if live)
            receipt = dict(address=address, site=site, consumer=consumer,
                call_site=call_site, call_target=active['call_target'],
                consumer_sha256=hashlib.sha256(data).hexdigest(), partition=partition,
                projected=[[register-match.ARM_REG_R0, offset]
                           for register, offset in sorted(projected.items())],
                continuation_states=len(seen))
            if quarantined:
                receipt['scratch_prefix_kills' if self._scratch_prefix_policy else 'scratch_leaf_kills'] = [
                    dict(quarantined[current], site=current) for current in sorted(quarantined)]
            self._scratch_returns[json.dumps(receipt, sort_keys=True)] = receipt
        return {register: offset for register, offset in aliases.items() if register not in scratch}

    def _scratch_leaf_kill(self, address, registers):
        """Require actual killing writes, rather than an ABI clobber assumption."""
        if not self._scratch_leaf_kill_policy or not registers or \
                set(registers) - {match.ARM_REG_R0+2, match.ARM_REG_R0+3}:
            raise ValueError('scratch leaf kill requires its explicit R2/R3 policy')
        data, ins, edges, calls, partition = self._graph(address)
        guards = PRESERVED | {match.ARM_REG_SP, match.ARM_REG_LR}
        if calls or any(set(item.regs_access()[1]) & guards for item in ins.values()) or \
                any(match.ARM_REG_SP in item.regs_access()[0] for item in ins.values()):
            raise ValueError('scratch leaf kill requires a complete no-call no-frame leaf')
        start = (address, frozenset(registers))
        pending, transitions, safe = [start], {}, set()
        while pending:
            state = pending.pop()
            if state in transitions or state in safe:
                continue
            site, live = state
            read, written = ins[site].regs_access()
            if set(read) & live:
                raise ValueError('scratch leaf reads an incoming alias before a killing write')
            following = live - set(written)
            if not following:
                safe.add(state)
                continue
            if not edges[site]:
                raise ValueError('scratch leaf returns without killing every incoming alias')
            transitions[state] = [(target, frozenset(following)) for target in edges[site]]
            pending.extend(transitions[state])
            if len(transitions) + len(safe) > 4096:
                raise ValueError('scratch leaf kill state budget exceeded')
        while True:
            added = {state for state, successors in transitions.items()
                     if state not in safe and all(target in safe for target in successors)}
            if not added:
                break
            safe.update(added)
        if start not in safe:
            raise ValueError('scratch leaf has a path without a proved killing write')
        return dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
                    partition=partition, registers=sorted(r-match.ARM_REG_R0 for r in registers),
                    states=len(safe), killed_before_observation=True)

    def scratch_return_observations(self):
        return [self._scratch_returns[key] for key in sorted(self._scratch_returns)]

    def _scratch_prefix_kill(self, address, registers, *, consumer, site):
        """Prove actual killing writes; completion remains a separate obligation."""
        if type(self) is not R6FrameCallbackProof or not self._scratch_prefix_policy or not registers or \
                set(registers) - {match.ARM_REG_R0+2, match.ARM_REG_R0+3}:
            raise ValueError('scratch prefix requires its exact explicit R2/R3 policy')
        caller, _, _, calls, caller_partition = self._graph(consumer)
        if calls.get(site) != address:
            raise ValueError('scratch prefix differs from its exact consumer call')
        data, ins, edges, calls, partition = self._graph(address)
        start = (address, frozenset(registers))
        pending, transitions, safe, kills = [start], {}, set(), set()
        while pending:
            state = pending.pop()
            if state in transitions or state in safe:
                continue
            current, live = state
            item = ins[current]
            read, written = map(set, item.regs_access())
            if read & live:
                raise ValueError('scratch prefix observes or saves an incoming value before its killing write')
            if current in calls:
                raise ValueError('scratch prefix calls before killing every incoming value')
            if written & live and item.cc not in (match.ARM_CC_AL, match.ARM_CC_INVALID):
                raise ValueError('scratch prefix killing write is conditional')
            kills.update((current, register-match.ARM_REG_R0) for register in written & live)
            following = live - written
            if not following:
                safe.add(state)
                continue
            if not edges[current]:
                raise ValueError('scratch prefix returns without killing every incoming value')
            transitions[state] = [(target, frozenset(following)) for target in edges[current]]
            pending.extend(transitions[state])
            if len(transitions) + len(safe) > 4096:
                raise ValueError('scratch prefix kill state budget exceeded')
        while True:
            added = {state for state, successors in transitions.items()
                     if state not in safe and all(target in safe for target in successors)}
            if not added:
                break
            safe.update(added)
        if start not in safe:
            raise ValueError('scratch prefix has a path without eventual killing writes')
        record = dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
            partition=partition, consumer=consumer, consumer_sha256=hashlib.sha256(caller).hexdigest(),
            consumer_partition=caller_partition, site=site,
            registers=sorted(register-match.ARM_REG_R0 for register in registers),
            states=len(safe), killing_writes=[list(row) for row in sorted(kills)])
        self._scratch_prefix_obligations[json.dumps(record, sort_keys=True)] = record
        return record

    def scratch_prefix_observations(self):
        """A prefix alone cannot authorize a report without its actual replay."""
        if type(self) is not R6FrameCallbackProof or not self._scratch_prefix_policy:
            raise ValueError('scratch prefix evidence requires its exact native proof instance')
        observations = []
        for key in sorted(self._scratch_prefix_obligations):
            row = self._scratch_prefix_obligations[key]
            identity = (row['consumer'], row['site'], row['address'],
                        row['consumer_sha256'], row['body_sha256'])
            completions = self._scratch_prefix_completions.get(identity)
            if not completions:
                raise ValueError('scratch prefix lacks its same-instance fresh complete effects and frame replay')
            observations.append(dict(row, complete_effects_and_frames=sorted(completions)))
        return observations

    def inspect(self, address, data):
        # The inherited preliminary instruction check has no entry constants.
        # Keep its existing checks, then replay effects with the real context in
        # check_arguments. Only the new unconditional-call hook is suspended.
        previous = self._structure_only
        self._structure_only = True
        try:
            return super().inspect(address, data)
        finally:
            self._structure_only = previous

    def _graph(self, address):
        import owner_admission_profile as owner
        data = self.span(address)
        refinement = owner.refine(data, address, self.mapping)
        ins, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words:
            raise ValueError('R6 restoration excludes local long branches and switches')
        partition = graph.partition(data, address, refinement, ins, words)
        return data, ins, edges, calls, partition

    def _leaf(self, value):
        if type(value) is not int or value % 2 != 1:
            raise ValueError('callback requires an exact odd Thumb target')
        address = match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                                               self._target_thunk, 2, len(self.rom))
        data, ins, edges, calls, partition = self._graph(address)
        if calls:
            raise ValueError('R6 restoration requires a complete no-call callback')
        for instruction in ins.values():
            _, written = instruction.regs_access()
            if set(written) & (PRESERVED | {match.ARM_REG_SP}):
                raise ValueError('callback writes a required unwritten register or SP')
        certificate = frame.prove_frame(ins, edges, address, {}, {}, call_preservation={})
        return dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
                    partition=partition, frame=certificate)

    def _restoring_frame(self, address, active):
        data, ins, edges, calls, partition = self._graph(address)
        if calls != {site: row['target'] for site, row in active['calls'].items()}:
            raise ValueError('ordinary frame has an unbound or incomplete nested call certificate')
        leaf = active.get('leaf_alias_restoration')
        if leaf is not None:
            if calls or leaf['body_sha256'] != hashlib.sha256(data).hexdigest() or leaf['partition'] != partition:
                raise ValueError('leaf alias restoration differs from its exact completed body')
            certificate = leaf['frame']
        else:
            options = {}
            if self._local_scratch_policy:
                options['discarded_exit_scratch'] = dict(schema=frame.DISCARDED_SCRATCH_SCHEMA,
                    registers=[2, 3])
                options['stack_aliases'] = True
                options['buffer_proof'] = RestoringLocalBufferProof(self, active)
            certificate = frame.prove_frame(ins, edges, address, {}, calls,
                call_preservation={site: PRESERVED for site in calls}, **options)
        result = dict(body_sha256=hashlib.sha256(data).hexdigest(), partition=partition,
                    frame=certificate, calls=[dict(site=site, **active['calls'][site])
                                             for site in sorted(active['calls'])])
        if leaf is not None:
            result['leaf_alias_restoration'] = leaf
        entry_aliases = active.get('entry_alias_restoration')
        if entry_aliases is not None:
            if entry_aliases['body_sha256'] != hashlib.sha256(data).hexdigest() or \
                    entry_aliases['partition'] != partition:
                raise ValueError('entry alias restoration differs from its exact completed body')
            result['entry_alias_restoration'] = entry_aliases
        return result

    def _restore_entry_aliases(self, address, watched, arguments):
        """Discharge opaque watches only within a separately proved saving frame.

        This pass proves non-observation, not restoration. The same ordinary
        check_arguments invocation must still complete every nested effect and
        _restoring_frame before it can return an authenticated receipt. Calls
        are allowed only after killing every relaxed entry register value and
        before restoring one. Saved values permit PUSH/POP only; no addressed
        stack access can read, modify or expose their private slots.
        """
        if not self._entry_alias_policy:
            return self._restore_leaf_aliases(address, watched, arguments)
        data, ins, edges, calls, partition = self._graph(address)
        written = set().union(*(set(item.regs_access()[1]) for item in ins.values()))
        relaxed = (set(watched) & PRESERVED & written) - {REPLAY_GUARD}
        if not relaxed:
            return tuple(watched), None
        if relaxed & set(arguments):
            raise ValueError('entry alias restoration cannot hide an explicit pointer argument')
        pending = [(address, frozenset(relaxed), ())]
        seen = set()
        while pending:
            site, opaque, saved = pending.pop()
            state = site, opaque, saved
            if state in seen:
                continue
            seen.add(state)
            if len(seen) > 4096:
                raise ValueError('entry alias restoration state budget exceeded')
            instruction = ins[site]
            read, changed = map(set, instruction.regs_access())
            registers = tuple(operand.reg for operand in instruction.operands
                              if operand.type == match.ARM_OP_REG)
            following_saved = saved
            if instruction.mnemonic == 'push':
                following = opaque
                following_saved = tuple(register in opaque for register in registers) + saved
                if len(following_saved) > 64:
                    raise ValueError('entry alias private save-word budget exceeded')
            elif instruction.mnemonic == 'pop':
                if len(saved) < len(registers):
                    raise ValueError('entry alias pop exceeds its private saved words')
                following = (opaque-set(registers)) | {
                    register for register, tainted in zip(registers, saved) if tainted}
                following_saved = saved[len(registers):]
            else:
                if match.ARM_REG_SP in read or match.ARM_REG_SP in changed:
                    raise ValueError('entry alias saves permit only private PUSH/POP stack access')
                if read & opaque:
                    raise ValueError('callee observes an opaque live entry alias')
                if site in calls and opaque:
                    raise ValueError('nested call crosses an opaque live entry alias')
                following = opaque - changed
            if not edges[site] and following - relaxed:
                raise ValueError('opaque entry alias escapes through a return register')
            pending.extend((target, frozenset(following), following_saved) for target in edges[site])
        record = dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
            partition=partition, registers=sorted(register-match.ARM_REG_R0 for register in relaxed),
            unobserved_entry_states=len(seen), calls_with_live_entry_values=[],
            nested_calls=sorted(calls))
        return tuple(sorted(set(watched)-relaxed)), record

    def _restore_leaf_aliases(self, address, watched, arguments):
        """Restore opaque caller aliases only after a complete no-call proof.

        Entry values may be privately saved and restored, but may not be read
        as addresses, copied, used as scalars, or observed by another call.
        The ordinary effects replay still runs over every reached instruction.
        """
        if not self._leaf_alias_policy:
            return tuple(watched), None
        data, ins, edges, calls, partition = self._graph(address)
        if calls:
            return tuple(watched), None
        written = set().union(*(set(item.regs_access()[1]) for item in ins.values()))
        relaxed = (set(watched) & PRESERVED & written) - {REGISTER, REPLAY_GUARD}
        if not relaxed:
            return tuple(watched), None
        if relaxed & set(arguments):
            raise ValueError('leaf alias restoration cannot hide an explicit pointer argument')
        pending = [(address, frozenset(relaxed), ())]
        seen = set()
        while pending:
            site, opaque, saved = pending.pop()
            state = site, opaque, saved
            if state in seen:
                continue
            seen.add(state)
            if len(seen) > 4096:
                raise ValueError('leaf alias restoration state budget exceeded')
            instruction = ins[site]
            read, changed = map(set, instruction.regs_access())
            registers = tuple(operand.reg for operand in instruction.operands
                              if operand.type == match.ARM_OP_REG)
            following_saved = saved
            if instruction.mnemonic == 'push':
                following = opaque
                following_saved = tuple(register in opaque for register in registers) + saved
                if len(following_saved) > 64:
                    raise ValueError('leaf alias private save-word budget exceeded')
            elif instruction.mnemonic == 'pop':
                if len(saved) < len(registers):
                    raise ValueError('leaf alias pop exceeds its private saved words')
                following = (opaque-set(registers)) | {
                    register for register, tainted in zip(registers,saved) if tainted}
                following_saved = saved[len(registers):]
            else:
                if match.ARM_REG_SP in read or match.ARM_REG_SP in changed:
                    raise ValueError('leaf alias saves permit only private PUSH/POP stack access')
                if read & opaque:
                    raise ValueError('leaf callee observes an opaque live entry alias')
                following = opaque - changed
            pending.extend((target, frozenset(following), following_saved) for target in edges[site])
        certificate = frame.prove_frame(ins, edges, address, {}, {}, call_preservation={})
        record = dict(address=address, body_sha256=hashlib.sha256(data).hexdigest(),
            partition=partition, frame=certificate,
            registers=sorted(register-match.ARM_REG_R0 for register in relaxed),
            unobserved_entry_states=len(seen), nested_calls=False)
        return tuple(sorted(set(watched)-relaxed)), record

    def check_arguments(self, address, arguments, stack, incoming, protected, *,
                        constants=None, site=None, **context):
        if type(site) is not int or context.get('words'):
            raise ValueError('R6 restoration requires exact sites without descriptor words')
        facts = dict(constants or {})
        context = dict(words={}, frame_base=context.get('frame_base'),
                       root_frame=context.get('root_frame'), **{key: value for key, value in context.items()
                       if key not in ('words', 'frame_base', 'root_frame')})
        if address == self._target_thunk:
            if not self._frames:
                raise ValueError('R6 callback certificate requires an active ordinary caller')
            if self._restoring_target:
                value = facts.get(self._target_register)
                if type(value) is not int or value % 2 != 1:
                    raise ValueError('callback requires an exact odd Thumb target')
                target = match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                    self._target_thunk, 2, len(self.rom))
                _, ins, _, _, _ = self._graph(target)
                guards = {REGISTER, REPLAY_GUARD}
                for instruction in ins.values():
                    if set(instruction.regs_access()[1]) & guards:
                        raise ValueError('callback writes a required unwritten target or replay guard')
                watched = tuple(sorted(set(context.get('watched', ())) | guards))
                active = dict(address=target, site=site, call_target=address, calls={})
                self._frames.append(active)
                try:
                    result = super().check_arguments(address, arguments, stack, incoming, protected,
                        constants=facts, site=site, **dict(context, watched=watched))
                    active['effects_complete'] = True
                    certificate = dict(address=target, **self._restoring_frame(target, active))
                finally:
                    self._frames.pop()
            else:
                certificate = self._leaf(facts.get(self._target_register))
                watched = tuple(sorted(set(context.get('watched', ())) | PRESERVED))
                result = super().check_arguments(address, arguments, stack, incoming, protected,
                    constants=facts, site=site, **dict(context, watched=watched))
            self._leaf_completed[id(result)] = (result, tuple(sorted(result.items())),
                                                site, certificate)
            return result
        # The extra unwritten watch forces complete effect replay even for a
        # no-buffer call; it does not infer callee-saved restoration itself.
        watched = tuple(sorted(set(context.get('watched', ())) | {REPLAY_GUARD}))
        active = dict(address=address, site=site, call_target=address, calls={})
        watched, restoration = self._restore_entry_aliases(address, watched, arguments)
        if restoration is not None:
            active['entry_alias_restoration' if self._entry_alias_policy else 'leaf_alias_restoration'] = restoration
        self._frames.append(active)
        try:
            aliases = super().check_arguments(address, arguments, stack, incoming, protected,
                constants=facts, site=site, **dict(context, watched=watched))
            active['effects_complete'] = True
            # Every nested site has independently completed its effects and a
            # frame or no-write callback proof. No arbitrary preserved set enters.
            receipt = dict(site=site, target=address, value=facts.get(REGISTER),
                           **self._restoring_frame(address, active))
            result = _Result(aliases)
            self._ordinary_completed[id(result)] = (result, tuple(sorted(result.items())), receipt)
            return result
        finally:
            self._frames.pop()

    def finish_call_constants(self, constants, result, *, site=None, target=None):
        if self._structure_only:
            return super().finish_call_constants(constants, result, site=site, target=target)
        incoming = dict(constants)
        ordinary = self._ordinary_completed.pop(id(result), None)
        leaf = self._leaf_completed.pop(id(result), None)
        super().finish_call_constants(constants, result, site=site, target=target)
        if leaf is not None:
            original, aliases, call_site, certificate = leaf
            if original is not result or aliases != tuple(sorted(result.items())) or \
                    site != call_site or target != self._target_thunk or not self._frames:
                raise ValueError('callback frame certificate differs from completed call')
            self._record_call(site, target, certificate, result)
        elif ordinary is not None:
            original, aliases, receipt = ordinary
            if original is not result or aliases != tuple(sorted(result.items())) or \
                    receipt['site'] != site or receipt['target'] != target or \
                    incoming.get(REGISTER) != receipt['value']:
                raise ValueError('R6 frame attestation differs from completed call')
            value = receipt['value']
            if value is not None:
                # Only actual mapped Thumb callback identities are retained.
                if type(value) is not int or value % 2 != 1:
                    raise ValueError('preserved R6 is not a typed Thumb callback identity')
                match.function_address_target(f'func_{value & ~1:08X}', self.entries,
                                              target, len(self.span(target)), len(self.rom))
                constants[REGISTER] = value
            key = json.dumps(receipt, sort_keys=True, separators=(',', ':'))
            self._restorations[key] = receipt
            if self._scratch_prefix_policy:
                owners = [row for row in self.entries if int(row['rom'], 16) <= site < int(row['end'], 16)]
                if len(owners) != 1:
                    raise ValueError('scratch prefix completion requires one exact consumer owner')
                consumer = int(owners[0]['rom'], 16)
                data, _, _, calls, _ = self._graph(consumer)
                if calls.get(site) != target or self._frames and self._frames[-1]['address'] != consumer:
                    raise ValueError('scratch prefix completion differs from its actual consumer call')
                identity = (consumer, site, target, hashlib.sha256(data).hexdigest(), receipt['body_sha256'])
                self._scratch_prefix_completions.setdefault(identity, set()).add(
                    hashlib.sha256(key.encode()).hexdigest())
            if self._frames:
                self._record_call(site, target, receipt, result)
        elif self._frames:
            raise ValueError('nested call lacks its exact completed preservation certificate')

    def _record_call(self, site, target, certificate, result):
        row = dict(target=target, certificate=certificate)
        if self._local_scratch_policy:
            row['return_aliases'] = [[register, offset] for register, offset in sorted(result.items())]
        calls = self._frames[-1]['calls']
        if site in calls and calls[site] != row:
            raise ValueError('nested call preservation context changed within one ordinary replay')
        calls[site] = row

    def restoration_observations(self):
        return [self._restorations[key] for key in sorted(self._restorations)]


def requires_replay(proof):
    # Closed native type hook. Existing defaults and arbitrary subclasses do
    # not acquire the all-ordinary-call replay or constant-restoration policy.
    return type(proof) is R6FrameCallbackProof and not proof._structure_only


def structural_return_aliases(proof, data, address, site, aliases):
    """Closed opt-in for the same exact consumer check during local replay.

    Only preliminary validation of an active ordinary callee can use this.
    Its full effect replay and restoring-frame certificate remain mandatory.
    Existing policies and arbitrary proof subclasses retain the old refusal.
    """
    if type(proof) is not R6FrameCallbackProof or not proof._local_scratch_policy:
        return aliases
    if not proof._structure_only or not proof._frames or \
            proof._frames[-1]['address'] != address or proof.span(address) != data:
        raise ValueError('local scratch requires its exact active preliminary callee')
    return proof.normal_return_aliases(address, site, aliases)
