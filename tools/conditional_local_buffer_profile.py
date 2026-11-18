"""Opt-in local-buffer call contracts for the issue #73, #81 and #82 interfaces.

These are conditional ABI/effect contracts, not inferred callback effects.
In particular a length argument does not prove a write bound, the scheduler
copy does not prove nonescape, and the indexed output callee's stores are not
alias-analysed. Defaults retain the ordinary buffer verifier.
"""
import hashlib
from pathlib import Path
import struct

import match
import scene_scheduler_cpufill as scene_fill
import effect_scheduler_initializer as effect_init
import menu_palette_scheduler as menu_palette
import named_data_buffer_profile as named
import owner_graph_profile as graph
import function_thunk_profile as thunk

SCHEDULER = 'conditional-scheduler-descriptor-calls-v1'
SCHEDULER_BRANCH = 'conditional-scheduler-branch-descriptor-calls-v1'
SCHEDULER_FOLLOWING = 'conditional-scheduler-following-call-v1'
SCHEDULER_SEQUENTIAL = 'conditional-scheduler-three-per-path-calls-v1'
SCHEDULER_KILLED_ALIAS = 'conditional-scheduler-sequential-killed-alias-calls-v1'
SCHEDULER_LEAF_OUTPUT = 'conditional-scheduler-sequential-leaf-output-calls-v1'
SCHEDULER_24_FOLLOWING = 'conditional-scheduler-twenty-four-target-following-calls-v1'
SCHEDULER_24 = 'conditional-scheduler-twenty-four-target-branches-v1'
SCHEDULER_LIVE_ALIAS = 'conditional-scheduler-live-local-alias-calls-v1'
SCHEDULER_LIVE_ALIAS_PAYLOAD = 'conditional-scheduler-live-local-alias-payload-calls-v1'
SCHEDULER_EVENT = 'conditional-scheduler-event-definition-v1'
LIVE_ALIAS = (SCHEDULER_LIVE_ALIAS, SCHEDULER_LIVE_ALIAS_PAYLOAD, SCHEDULER_EVENT)
SCHEDULER_WIDE = 'conditional-scheduler-eight-target-branches-v1'
SCHEDULER_LOOP = 'conditional-scheduler-u16-counted-loop-v1'
SCHEDULER_LOOP_LIVE_ALIAS = 'conditional-scheduler-sequential-live-alias-counted-loops-v1'
SCHEDULER_WIDE_LIVE_ALIAS = 'conditional-scheduler-three-per-path-live-alias-v1'
LOOP_LIVE_ALIAS = (SCHEDULER_LOOP_LIVE_ALIAS, SCHEDULER_WIDE_LIVE_ALIAS)
SCHEDULER_PROJECTED = 'conditional-scheduler-projected-outputs-v1'
SCHEDULER_GUARDED = 'conditional-scheduler-guarded-descriptor-calls-v1'
SCHEDULER_PAYLOAD = 'conditional-scheduler-descriptor-payload-calls-v1'
SCHEDULER_PAYLOAD8 = 'conditional-scheduler-descriptor-payload8-calls-v1'
SCHEDULER_HALFWORD_PAYLOAD = 'conditional-scheduler-halfword-output-payload-v1'
SCHEDULER_TWO_PAYLOAD = 'conditional-scheduler-two-payload-calls-v1'
SCENE_SCRIPT = 'conditional-scene-mode6-position-v1'
SCHEDULER_ZERO_DESCRIPTOR = 'conditional-scheduler-zero-descriptor-v1'
SCHEDULER_ENTRY = 'conditional-scheduler-entry-descriptor-calls-v1'
SCHEDULER_ENTRY_BRANCH = 'conditional-scheduler-entry-branch-descriptor-calls-v1'
SCHEDULER_MANAGER_FIELD = 'conditional-scheduler-indirect-manager-v1'
SCHEDULER_MANAGER_OFFSET = 'conditional-scheduler-manager-offset-v1'
SCHEDULER_MANAGER_PATHS = 'conditional-scheduler-manager-paths-v1'
SCHEDULER_CALL_SITES = 'conditional-scheduler-call-site-summaries-v1'
SCHEDULER_CALL_SITES_V2 = 'conditional-scheduler-call-site-summaries-v2'
CALL_SITE_POLICIES = (SCHEDULER_CALL_SITES, SCHEDULER_CALL_SITES_V2, scene_fill.SELECTOR, effect_init.SELECTOR, menu_palette.SELECTOR)
PAYLOAD_FIELDS = {SCHEDULER_PAYLOAD: 4, SCHEDULER_PAYLOAD8: 8, SCHEDULER_HALFWORD_PAYLOAD: 4, SCHEDULER_TWO_PAYLOAD: (4, 8), SCHEDULER_LIVE_ALIAS_PAYLOAD: 4, SCHEDULER_EVENT: 4}
STATE = 'conditional-local-state-iterator-v1'
FLAGGED_STATE = 'conditional-flagged-local-state-iterator-v1'
OUTPUT = 'conditional-local-output-word-call-v1'
SCHEMAS = {
    'conditional-cone-tile-stack-footprint-v1': 'elf-symbol-thumb-conditional-cone-tile-stack-footprint-v1',
    SCHEDULER_PROJECTED: 'elf-symbol-thumb-conditional-scheduler-projected-outputs-v1',
    SCHEDULER: 'elf-symbol-thumb-conditional-scheduler-descriptor-calls-v1',
    SCHEDULER_BRANCH: 'elf-symbol-thumb-conditional-scheduler-branch-descriptor-calls-v1',
    SCHEDULER_FOLLOWING: 'elf-symbol-thumb-conditional-scheduler-following-call-v1',
    SCHEDULER_SEQUENTIAL: 'elf-symbol-thumb-' + SCHEDULER_SEQUENTIAL,
    SCHEDULER_LEAF_OUTPUT: 'elf-symbol-thumb-' + SCHEDULER_LEAF_OUTPUT,
    SCHEDULER_KILLED_ALIAS: 'elf-symbol-thumb-' + SCHEDULER_KILLED_ALIAS,
    SCHEDULER_24_FOLLOWING: 'elf-symbol-thumb-' + SCHEDULER_24_FOLLOWING,
    SCHEDULER_24: 'elf-symbol-thumb-' + SCHEDULER_24,
    SCHEDULER_LIVE_ALIAS: 'elf-symbol-thumb-' + SCHEDULER_LIVE_ALIAS,
    SCHEDULER_EVENT: 'elf-symbol-thumb-' + SCHEDULER_EVENT,
    SCHEDULER_LIVE_ALIAS_PAYLOAD: 'elf-symbol-thumb-' + SCHEDULER_LIVE_ALIAS_PAYLOAD,
    SCHEDULER_WIDE: 'elf-symbol-thumb-conditional-scheduler-eight-target-branches-v1',
    SCHEDULER_LOOP: 'elf-symbol-thumb-conditional-scheduler-u16-counted-loop-v1',
    SCHEDULER_LOOP_LIVE_ALIAS: 'elf-symbol-thumb-' + SCHEDULER_LOOP_LIVE_ALIAS,
    SCHEDULER_WIDE_LIVE_ALIAS: 'elf-symbol-thumb-' + SCHEDULER_WIDE_LIVE_ALIAS,
    SCHEDULER_GUARDED: 'elf-symbol-thumb-conditional-scheduler-guarded-descriptor-calls-v1',
    SCHEDULER_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-descriptor-payload-calls-v1',
    SCHEDULER_PAYLOAD8: 'elf-symbol-thumb-conditional-scheduler-descriptor-payload8-calls-v1',
    SCHEDULER_HALFWORD_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-halfword-output-payload-v1',
    SCHEDULER_TWO_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-two-payload-calls-v1',
    SCENE_SCRIPT: 'elf-symbol-thumb-' + SCENE_SCRIPT,
    SCHEDULER_ZERO_DESCRIPTOR: 'elf-symbol-thumb-' + SCHEDULER_ZERO_DESCRIPTOR,
    SCHEDULER_ENTRY: 'elf-symbol-thumb-conditional-scheduler-entry-descriptor-calls-v1',
    SCHEDULER_ENTRY_BRANCH: 'elf-symbol-thumb-' + SCHEDULER_ENTRY_BRANCH,
    SCHEDULER_MANAGER_FIELD: 'elf-symbol-thumb-conditional-scheduler-indirect-manager-v1',
    SCHEDULER_MANAGER_OFFSET: 'elf-symbol-thumb-' + SCHEDULER_MANAGER_OFFSET,
    SCHEDULER_MANAGER_PATHS: 'elf-symbol-thumb-' + SCHEDULER_MANAGER_PATHS,
    scene_fill.SELECTOR: scene_fill.SCHEMA,
    effect_init.SELECTOR: effect_init.SCHEMA,
    menu_palette.SELECTOR: menu_palette.SCHEMA,
    SCHEDULER_CALL_SITES: 'elf-symbol-thumb-' + SCHEDULER_CALL_SITES,
    SCHEDULER_CALL_SITES_V2: 'elf-symbol-thumb-' + SCHEDULER_CALL_SITES_V2,
    STATE: 'elf-symbol-thumb-conditional-local-state-iterator-v1',
    FLAGGED_STATE: 'elf-symbol-thumb-' + FLAGGED_STATE,
    OUTPUT: 'elf-symbol-thumb-conditional-local-output-word-call-v1',
}
SELECTORS = tuple(SCHEMAS)
CONTROL_FLOW = 'complete Thumb caller with bounded local interfaces under explicit returning-call, bounded-effect and nonretention premises; actual callback effects and termination unproved'
# Complete indexed dependency identities, never an address-only exemption.
DEPENDENCIES = {
    0x08005B6C: (60, 'c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475'),
    0x08005954: (206, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    0x08121B8C: (44, '6646f8955088430fdcc363b15cb3555c12a6ae52ec775c4a4aba44e43a7e292f'),
    0x080C7CC0: (34, '47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1'),
    0x0809ABE8: (22, '65ec4ecbbacee97448810c0c4bb966405fc392884ba09795dc94b0b00aeff3d4'),
    0x080C7B74: (4, 'a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da'),
    0x08098BB0: (112, '4b56b7d9e7ba587ee64a6d4da1eb3b51b2e6eb7cfcb989a8534fa86a7602c3cc'),
    0x080799C0: (1748, '5b5e3ab0c848c2b722884b1bd6c337ed967e70c9f04745a093e5ba516a1974de'),
}
# The one indexed callee whose R2 is a caller-owned result word (issue #81).
OUTPUT_CALLEE = 0x080799C0


def require(condition, message):
    if not condition:
        raise ValueError(message)


class ConditionalLocalBufferProof(named.NamedDataBufferProof):
    def __init__(self, rom, mapping, index, objects, *, policy):
        require(policy in SELECTORS, 'explicit local-buffer contract required')
        super().__init__(rom, mapping, index, objects)
        self.policy = policy
        self.observations = {}
        if policy == SCENE_SCRIPT:
            # Mode-six helper, predicate, geometry, callback, three inputs of
            # the shared helper interpreter, direct scheduler and two thunks.
            self.dependency_budget = 10
        if policy in (SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS):
            # Thirty-two ordinary bodies, two scheduler bodies and two thunks.
            self.dependency_budget = 36
        if policy in (SCHEDULER_24, SCHEDULER_24_FOLLOWING):
            # Twenty-four ordinary bodies, two scheduler bodies and two thunks.
            self.dependency_budget = 28
        if policy in (*LIVE_ALIAS, SCHEDULER_LOOP_LIVE_ALIAS):
            # Twenty-four ordinary bodies, two scheduler bodies, two thunks and eight nested callees.
            self.dependency_budget = 36
        if policy == SCHEDULER_WIDE_LIVE_ALIAS:
            # Thirty-two ordinary bodies, two scheduler bodies, two thunks and eight nested callees.
            self.dependency_budget = 44
        if policy in (SCHEDULER_GUARDED, SCHEDULER_WIDE, SCHEDULER_PROJECTED):
            # Eight authenticated helpers plus two scheduler bodies and two thunks.
            self.dependency_budget = 12
        if policy in CALL_SITE_POLICIES:
            import scheduler_call_site_profile as call_sites
            self.dependency_budget = call_sites.DEPENDENCY_BUDGET

    def bind_root(self, data, address, calls):
        import owner_admission_profile as owner
        from known_query_native_closure_profile import environment_fingerprint
        require(not hasattr(self, 'root'), 'local-buffer contract context is single use')
        named.validate_owner(data, address, self.rom, self.mapping, self.index)
        ins, edges, branches, actual, words = graph.graph(data, address, owner.refine(data, address, self.mapping))
        require(not branches and not words and calls == actual,
                'local-buffer contracts exclude local BL and switches')
        self.root, self.calls = (address, bytes(data)), dict(calls)
        self.environment = environment_fingerprint()
        if self.policy == SCHEDULER_EVENT:
            import scheduler_event_definition as event
            self.event_definition = event.bind(self, data, address, ins, edges, calls)
        if self.policy == SCHEDULER_PROJECTED:
            import scheduler_projected_outputs_profile as projected
            self.projected_outputs = projected.bind(self, edges, calls)
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_HALFWORD_PAYLOAD:
            import scheduler_halfword_payload_profile as halfword
            self.halfword_payload = halfword.bind(self, edges, calls)
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_LOOP:
            import scheduler_counted_loop_profile as counted
            self.branch_calls = counted.bind(self, ins, edges, calls, address)
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in LOOP_LIVE_ALIAS:
            import scheduler_loop_composition_profile as composition
            import scheduler_live_alias_profile as live
            self.branch_calls = composition.bind(self, ins, edges, calls, address,
                limits=composition.WIDE_LIMITS if self.policy == SCHEDULER_WIDE_LIVE_ALIAS else None)
            base = ('No tracked local-register alias, pointer word or word-provenance fact may '
                    'enter it. ')
            require(base in self.branch_calls['ordinary_call_contract'],
                    'live-alias contract replaces the ordinary no-alias sentence')
            self.branch_calls['ordinary_call_contract'] = self.branch_calls['ordinary_call_contract'].replace(base,
                'No pointer word or word-provenance fact may enter it; live private-local aliases may, '
                'only under the following contract. ' + live.PREMISE + ' ' +
                (live.ENTRY_LIVENESS_PREMISE + ' ' if self.policy == SCHEDULER_WIDE_LIVE_ALIAS else ''))
            self.branch_calls['live_alias_source_sha256'] = hashlib.sha256(Path(live.__file__).read_bytes()).hexdigest()
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_24, *LIVE_ALIAS, SCHEDULER_24_FOLLOWING, SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS):
            import scheduler_branch_profile as branch
            self.branch_calls = branch.bind(self, edges, calls, following_calls=self.policy == SCHEDULER_FOLLOWING, wide_targets=self.policy == SCHEDULER_WIDE, twenty_four_targets=self.policy in (SCHEDULER_24, *LIVE_ALIAS), twenty_four_following_calls=self.policy == SCHEDULER_24_FOLLOWING, three_per_path_calls=self.policy in (SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS))
            if self.policy == SCHEDULER_KILLED_ALIAS:
                self.branch_calls['ordinary_call_contract'] += (
                    ' This explicit profile additionally admits complete leaf alias replay or '
                    'incoming caller-clobbered aliases fully overwritten by a closed straight-line '
                    'entry prefix before any observation. Only after that prefix do the ordinary '
                    'returning-ABI premises apply; nested effects remain unproved.')
            if self.policy in LIVE_ALIAS:
                import scheduler_live_alias_profile as live
                base = ('No tracked local-register alias, pointer word or word-provenance fact may '
                        'enter it. ')
                require(base in self.branch_calls['ordinary_call_contract'],
                        'live-alias contract replaces the ordinary no-alias sentence')
                self.branch_calls['ordinary_call_contract'] = self.branch_calls['ordinary_call_contract'].replace(base,
                    'No pointer word or word-provenance fact may enter it; live private-local aliases may, '
                    'only under the following contract. ' + live.PREMISE + ' ')
                self.branch_calls['live_alias_source_sha256'] = hashlib.sha256(Path(live.__file__).read_bytes()).hexdigest()
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_GUARDED:
            import scheduler_predicate_profile as predicates
            predicates.phases(edges, calls)
            self.predicates = predicates.close(self, set(calls.values()) - {0x08005B6C})
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in CALL_SITE_POLICIES:
            import scheduler_call_site_profile as call_sites
            if self.policy == menu_palette.SELECTOR:
                self.scheduler_call_sites = menu_palette.bind(self, data, address, ins, edges, calls)
            else:
                scheduler_calls = effect_init.bind(self, data, address, ins, edges, calls) if self.policy == effect_init.SELECTOR else calls
                self.scheduler_call_sites = call_sites.bind(data, address, ins, edges, scheduler_calls)
            if self.policy == scene_fill.SELECTOR:
                scene_fill.bind(self, data, address, edges, calls)
            call_sites.bind_forwarding(self, edges)
            dependencies = tuple(self.scheduler_call_sites['dependencies'])
            runtime_names = call_sites.RUNTIME_NAMES
        elif self.policy == SCENE_SCRIPT:
            import scene_script_position as scene
            scene.bind(self, data, address, calls)
            dependencies = (0x08005954,)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_ZERO_DESCRIPTOR:
            import scheduler_zero_descriptor as descriptor
            descriptor.bind(self, data, address, ins, edges, calls)
            dependencies = self.scheduler_entry['dependencies']
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_ENTRY_BRANCH:
            import scheduler_entry_branch_profile as entry_branch
            self.scheduler_entry, self.scheduler_entry_branches = entry_branch.bind(data, address, ins, edges, calls)
            dependencies = self.scheduler_entry['dependencies']
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in (SCHEDULER_ENTRY, SCHEDULER_MANAGER_FIELD, SCHEDULER_MANAGER_OFFSET, SCHEDULER_MANAGER_PATHS):
            if self.policy == SCHEDULER_MANAGER_PATHS:
                import scheduler_manager_paths_profile as entry
            elif self.policy == SCHEDULER_MANAGER_OFFSET:
                import scheduler_manager_offset_profile as entry
            elif self.policy == SCHEDULER_MANAGER_FIELD:
                import scheduler_manager_field_profile as entry
            else:
                import scheduler_entry_profile as entry
            self.scheduler_entry = entry.bind(data, address, ins, edges, calls)
            dependencies = self.scheduler_entry['dependencies']
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in (SCHEDULER, *PAYLOAD_FIELDS):
            require(len(calls) == 1 and set(calls.values()) == {0x08005B6C},
                    'scheduler contract requires one actual scheduler call')
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == OUTPUT:
            require(len(calls) == 1 and set(calls.values()) == {OUTPUT_CALLEE},
                    'output-word contract requires one actual indexed output-word call')
            dependencies = (OUTPUT_CALLEE,)
            runtime_names = ()
        elif self.policy == FLAGGED_STATE:
            # MOV R4,SP precedes the initializer. The only post-call access
            # through that alias is flags |= mask on state byte 1.
            require(len(data) == 72 and calls == {address+16: 0x0814224C, address+42: 0x080C7CC0}
                    and data[:16] == bytes.fromhex('30b583b0051c0d486c46026868460421')
                    and data[20:22] == bytes.fromhex('6178')
                    and data[23:38] == bytes.fromhex('200843607008486946019101aa5060')
                    and data[40:42] == bytes.fromhex('0649')
                    and data[46:60] == bytes.fromhex('6846007803b030bc02bc08470000')
                    and struct.unpack_from('<III', data, 60) == (0x0836D4B8, 0x08098BB1, 0x0809ABE9),
                    'flagged state contract requires its exact state update and visitor interface')
            load = struct.unpack_from('<H', data, 38)[0]
            mask = data[22]
            require((load, mask) in ((0x6968, 1), (0x69A8, 1), (0x69A8, 2)),
                    'flagged state contract requires a supported owner list and flag mask')
            self.owner_list_load = dict(site=address+38, base_register=5, destination_register=0,
                                        offset=4*((load >> 6) & 31), width=4)
            self.state_update = dict(load=address+20, store=address+26, state_byte=1,
                                     operation='or', mask=mask, base_register=4)
            dependencies = (0x080C7CC0, 0x0809ABE8, 0x080C7B74, 0x08098BB0)
            runtime_names = ('_call_via_r2', '_call_via_r6')
        else:
            # The one owner-list load at +28 is LDR R0,[R4,#imm5*4]; every other
            # code byte is fixed and the word offset is bound in the report.
            load = struct.unpack_from('<H', data, 28)[0] if len(data) == 60 else None
            require(len(data) == 60 and calls == {address+14: 0x0814224C, address+32: 0x080C7CC0}
                    and data[:14] == bytes.fromhex('10b583b0041c0a48026868460421')
                    and data[18:28] == bytes.fromhex('08486946019101aa5060')
                    and load & 0xF83F == 0x6820
                    and data[30:32] == bytes.fromhex('0649')
                    and data[36:48] == bytes.fromhex('6846007803b010bc02bc0847')
                    and struct.unpack_from('<III', data, 48) == (0x0836D4B8, 0x08098BB1, 0x0809ABE9),
                    'state contract requires the exact four-byte state and initialized visitor interface')
            self.owner_list_load = dict(site=address+28, base_register=4, destination_register=0,
                                        offset=4*((load >> 6) & 31), width=4)
            dependencies = (0x080C7CC0, 0x0809ABE8, 0x080C7B74, 0x08098BB0)
            runtime_names = ('_call_via_r2', '_call_via_r6')
        for target in dependencies:
            body = self.span(target)
            size, digest = DEPENDENCIES[target]
            require(len(body) == size and hashlib.sha256(body).hexdigest() == digest,
                    'local-buffer contract dependency identity differs')
            self.dependencies[target] = body
            self.records[target] = dict(address=target, end=target+size, bytes=size,
                body_sha256=digest, structure={'kind': 'conditional-local-buffer-interface'}, **self.identities)
        self.runtime_dependencies = thunk.dependencies(runtime_names, self.rom)
        for name in runtime_names:
            target = thunk.ALIASES[name]
            body = self.span(target)
            require(len(body) == 2 and not any(int(row['rom'], 16) < target+4 and
                    int(row['end'], 16) > target+2 for row in self.entries),
                    'local-buffer contract thunk requires separately unowned padding')

    def access(self, offset, width, stack):
        log = getattr(self, '_live_log', None)
        if log is not None:
            log['access'].append((offset, width))
        return super().access(offset, width, stack)

    def check_arguments(self, address, *args, **kwargs):
        # Every call the live-alias replay reaches, at any depth, aliases or not.
        log = getattr(self, '_live_log', None)
        if log is not None:
            log['calls'].append(address)
        return super().check_arguments(address, *args, **kwargs)

    def check_indirect_target(self, address, aliases, returns, *, site):
        if not thunk.reserved(address):
            return
        if self.policy == menu_palette.SELECTOR:
            return menu_palette.check_indirect(self, site, address, aliases, returns)
        require(self.policy in (STATE, FLAGGED_STATE, SCHEDULER_ZERO_DESCRIPTOR, effect_init.SELECTOR) and self.calls.get(site) == address == 0x0814224C,
                'local-buffer indirect call differs from authenticated root')
        require(match.ARM_REG_R0+2 not in aliases and
                not set(returns) & (set(match.CALLER_CLOBBERED) - {match.ARM_REG_LR}),
                'local-buffer indirect target carries pointer or return provenance')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if getattr(self, '_live_log', None) is not None:
            # Inside a replayed callee body: the ordinary buffer-call rules apply to its own calls.
            return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)
        if self.policy in CALL_SITE_POLICIES and self.active:
            # Inside an inspected buffer callee: its own calls keep the ordinary buffer rules,
            # including a call to a scheduler entry, which is then walked like any callee.
            # They carry the callee's own frame, never the owner's, so forwarding stays off:
            # a slot or released word there would not be in owner terms.
            forwarding, self.forwarded_stack_arguments = self.forwarded_stack_arguments, False
            try:
                return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)
            finally:
                self.forwarded_stack_arguments = forwarding
        require(self.calls.get(site) == address and not words,
                'local-buffer call differs from its authenticated interface')
        if self.policy == SCENE_SCRIPT:
            import scene_script_position as scene
            return scene.check_call(self, address, aliases, stack, slots, constants, site)
        if self.policy == SCHEDULER_ZERO_DESCRIPTOR:
            import scheduler_zero_descriptor as descriptor
            return descriptor.check_call(self, address, aliases, stack, slots, constants, site)
        if self.policy in CALL_SITE_POLICIES:
            import scheduler_call_site_profile as call_sites
            if self.policy == menu_palette.SELECTOR and site in (menu_palette.SETUP_SITE, menu_palette.COPY_SITE):
                return menu_palette.check_call(self, site, aliases, stack, slots, constants)
            if self.policy == effect_init.SELECTOR and address == effect_init.THUNK:
                return effect_init.check_call(self, site, aliases, stack, slots, constants, words)
            if self.policy == scene_fill.SELECTOR and address == scene_fill.bios.ADDRESS:
                return scene_fill.check_fill(self, address, aliases, stack, slots, site, words)
            if address in call_sites.ENTRIES:
                return call_sites.check_call(self, address, aliases, stack, slots, site=site)
            # Every other root call keeps the unchanged named-data buffer rules.
            result = super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)
            return call_sites.walked_call(self, result, stack, site=site)
        if self.policy == SCHEDULER_KILLED_ALIAS and address != 0x08005B6C:
            import scheduler_killed_alias_profile as killed
            return killed.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy == SCHEDULER_LEAF_OUTPUT and address != 0x08005B6C:
            import scheduler_leaf_output_profile as output
            return output.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy == SCHEDULER_PROJECTED:
            import scheduler_projected_outputs_profile as projected
            return projected.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy in (SCHEDULER_ENTRY, SCHEDULER_ENTRY_BRANCH, SCHEDULER_MANAGER_FIELD, SCHEDULER_MANAGER_OFFSET, SCHEDULER_MANAGER_PATHS):
            if self.policy == SCHEDULER_MANAGER_PATHS:
                import scheduler_manager_paths_profile as entry
            elif self.policy == SCHEDULER_MANAGER_OFFSET:
                import scheduler_manager_offset_profile as entry
            elif self.policy == SCHEDULER_MANAGER_FIELD:
                import scheduler_manager_field_profile as entry
            else:
                import scheduler_entry_profile as entry
            return entry.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy == SCHEDULER_TWO_PAYLOAD:
            import scheduler_two_payload_profile as two
            return two.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy == SCHEDULER_HALFWORD_PAYLOAD:
            import scheduler_halfword_payload_profile as halfword
            return halfword.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy == SCHEDULER_EVENT and address == 0x08005B6C:
            import scheduler_event_definition as event
            return event.check_call(self, aliases, stack, slots, site)
        if self.policy in (*LIVE_ALIAS, *LOOP_LIVE_ALIAS) and address != 0x08005B6C:
            import scheduler_live_alias_profile as live
            return live.check_call(self, address, aliases, stack, slots, constants=constants, site=site, words=words,
                                   entry_liveness=self.policy == SCHEDULER_WIDE_LIVE_ALIAS)
        if self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_24, *LIVE_ALIAS, SCHEDULER_24_FOLLOWING, SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS, SCHEDULER_LOOP) and address != 0x08005B6C:
            require(address in self.branch_calls['ordinary_targets'] and not aliases and not slots,
                    'ordinary branch calls exclude every live local alias and pointer word')
            self.observations[site] = dict(site=site, target=address, kind='conditional-ordinary-ABI-call')
            return {}
        if self.policy == SCHEDULER_GUARDED and address != 0x08005B6C:
            require(address in self.predicates['helpers'] and not aliases and not slots,
                    'predicate calls exclude every live local alias and pointer word')
            self.observations[site] = dict(site=site, target=address, kind='closed-read-only-predicate')
            return {}
        r0, r2 = match.ARM_REG_R0, match.ARM_REG_R0+2
        payload = None
        if self.policy in (SCHEDULER, SCHEDULER_GUARDED, SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_24, SCHEDULER_LIVE_ALIAS, SCHEDULER_24_FOLLOWING, SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS, SCHEDULER_LOOP, *LOOP_LIVE_ALIAS):
            require({reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2} and not slots,
                    'scheduler contract excludes additional register or pointer-word aliases')
            offset, width = aliases[r2], 28
            if self.policy in LOOP_LIVE_ALIAS and site in self.branch_calls['looped_scheduler_sites']:
                # The scheduler and its callback are never walked. Outside loops the
                # existing descriptor premise admits recorded preserved-register
                # aliases. A repeated invocation inside a loop admits only R4-R7
                # holding the descriptor's own address: R2 already hands every
                # invocation that address, and the loop bound already rests on
                # R4-R7 surviving each call.
                require(all(match.ARM_REG_R0+4 <= reg <= match.ARM_REG_R0+7 and value == offset
                            for reg, value in aliases.items() if reg != r2),
                        'looped scheduler calls exclude every local alias other than the R2 descriptor '
                        'and R4-R7 copies of its address')
        elif self.policy == OUTPUT:
            base = -4*len(stack)
            require(aliases == {r2: base} and not slots and sum(1 for word in stack if word[2]) == 1,
                    'output-word contract requires its single local word as the only R2 pointer')
            offset, width = base, 4
        elif self.policy in PAYLOAD_FIELDS:
            require({reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2},
                    'scheduler contract excludes additional register aliases')
            offset, width = aliases[r2], 28
            # The private frame is exactly two adjacent objects: the descriptor
            # and one nonempty payload, in either order. The payload extent is
            # every private word outside the descriptor.
            base = -4*len(stack)
            local = [index for index, word in enumerate(stack) if word[2]]
            first, end = (offset-base)//4, len(local)
            require(offset % 4 == 0 and local == list(range(end)) and 0 <= first and first+7 <= end,
                    'scheduler payload contract requires a contiguous private frame from SP holding the complete aligned descriptor')
            if first == 0 and end > 7:
                payload = (offset+28, 4*end+base-offset-28)
            elif first > 0 and first+7 == end:
                payload = (base, offset-base)
            else:
                require(False, 'scheduler payload contract requires a frame of exactly the descriptor and one adjacent nonempty payload')
            # Each explicit profile selects exactly one descriptor field.
            pointer_field = PAYLOAD_FIELDS[self.policy]
            require(slots == {offset+pointer_field: payload[0]},
                    f'scheduler payload contract requires one descriptor+{pointer_field} word addressing the payload')
        else:
            base = -4*len(stack)
            state_alias = {r0+4: base} if self.policy == FLAGGED_STATE else {}
            if address == 0x0814224C:
                require(aliases == {r0: base, **state_alias} and not slots and (constants or {}).get(r0+1) == 4,
                        'state callback requires its actual local pointer and constant four-byte size')
                offset, width = base, 4
            else:
                require(aliases == {r2: base+4, **state_alias} and slots == {base+4: base},
                        'visitor call requires its exact initialized state-pointer word')
                offset, width = base, 12
        for start, size in ((offset, width),) + ((payload,) if payload else ()):
            for byte in range(start, start+size):
                self.access(byte, 1, stack)
        observation = dict(site=site, target=address, local_offset=offset, bytes=width,
                           aliases=sorted(aliases.items()), pointer_words=sorted((slots or {}).items()))
        if self.policy == OUTPUT:
            observation['observed_store_bytes'] = 2  # ROM inspection only; see assumptions.
        if payload:
            observation.update(payload_offset=payload[0], payload_frame_bytes=payload[1],
                               payload_extent='remaining-private-frame')
            if self.policy == SCHEDULER_PAYLOAD8:
                observation['payload_pointer_word_offset'] = 8
        require(site not in self.observations or self.observations[site] == observation,
                'local-buffer contract differs across incoming paths')
        self.observations[site] = observation
        return {}

    def contract_manifest(self):
        if self.policy == SCENE_SCRIPT:
            import scene_script_position as scene
            return scene.manifest(self)
        if self.policy == SCHEDULER_ZERO_DESCRIPTOR:
            import scheduler_zero_descriptor as descriptor
            return descriptor.manifest(self)
        if self.policy in CALL_SITE_POLICIES:
            import scheduler_call_site_profile as call_sites
            if self.policy == menu_palette.SELECTOR:
                return menu_palette.manifest(self)
            scheduler = call_sites.manifest(self)
            if self.policy == effect_init.SELECTOR:
                return effect_init.manifest(self, scheduler)
            return scene_fill.manifest(self, scheduler) if self.policy == scene_fill.SELECTOR else scheduler
        if self.policy == SCHEDULER_ENTRY_BRANCH:
            import scheduler_entry_branch_profile as entry_branch
            return entry_branch.manifest(self)
        if self.policy == SCHEDULER_PROJECTED:
            import scheduler_projected_outputs_profile as projected
            return projected.manifest(self)
        if self.policy in (SCHEDULER_ENTRY, SCHEDULER_ENTRY_BRANCH, SCHEDULER_MANAGER_FIELD, SCHEDULER_MANAGER_OFFSET, SCHEDULER_MANAGER_PATHS):
            if self.policy == SCHEDULER_MANAGER_PATHS:
                import scheduler_manager_paths_profile as entry
            elif self.policy == SCHEDULER_MANAGER_OFFSET:
                import scheduler_manager_offset_profile as entry
            elif self.policy == SCHEDULER_MANAGER_FIELD:
                import scheduler_manager_field_profile as entry
            else:
                import scheduler_entry_profile as entry
            return entry.manifest(self)
        if self.policy == SCHEDULER_TWO_PAYLOAD:
            import scheduler_two_payload_profile as two
            return two.manifest(self)
        if self.policy == SCHEDULER_HALFWORD_PAYLOAD:
            import scheduler_halfword_payload_profile as halfword
            return halfword.manifest(self)
        require(set(self.observations) == set(self.calls), 'every conditional local-buffer call must be observed')
        return dict(schema=SCHEMAS[self.policy], runtime_dependencies=self.runtime_dependencies,
            environment=self.environment,
            **({'event_definition': self.event_definition} if self.policy == SCHEDULER_EVENT else {}),
            **({'predicates': self.predicates} if self.policy == SCHEDULER_GUARDED else {}),
            **({'owner_list_load': self.owner_list_load} if self.policy in (STATE, FLAGGED_STATE) else {}),
            **({'state_flag_update': self.state_update} if self.policy == FLAGGED_STATE else {}),
            **({'branch_calls': self.branch_calls} if self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_24, *LIVE_ALIAS, SCHEDULER_24_FOLLOWING, SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS, SCHEDULER_LOOP, *LOOP_LIVE_ALIAS) else {}),
            observations=[self.observations[s] for s in sorted(self.observations)],
            assumptions=[
                'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved.',
                'No local pointer is retained for later use or returned through caller-clobbered registers.',
                ('Scheduler allocator/zero/list prefix and callback obey frame noninterference; the 28-byte '
                 'descriptor is readable as representation bytes, its copied pointer values remain conditional, '
                 'and the returned allocation is separate from all caller stack words. Both the copied R1 '
                 'descriptor and ambient original R9 pointer are exposed to the callback; copying does not prove nonescape.'
                 if self.policy in (SCHEDULER, SCHEDULER_GUARDED, SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_24, *LIVE_ALIAS, SCHEDULER_24_FOLLOWING, SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS, SCHEDULER_LOOP, *LOOP_LIVE_ALIAS, *PAYLOAD_FIELDS) else
                 'The indexed output callee writes at most the single four-byte local result word through R2 and '
                 'accesses no other private/saved caller word. Its body identity is checked, but its stores are '
                 'not alias-analysed; ROM inspection shows two 16-bit stores at R2+0 (0x0807A046, 0x0807A05C). '
                 'The word\'s value after the call is conditional; R0/R1 carry no caller-frame pointer.'
                 if self.policy == OUTPUT else
                 'The installed initial callback initializes exactly the four state bytes without accessing other '
                 'private/saved words. Constant n=4 is an interface argument, not a proof of callback behavior. '
                 'Iterator objects and scalar-query callees are valid and separate from the caller frame; '
                 'the visitor record remains unchanged and the known callback accesses only state bytes 0 and 1.')]
                + (['R4 retains the same private state pointer from before the initializer through the iterator. '
                    'Both calls preserve R4 and their ambient R4 alias obeys the same bounded state access '
                    'and nonretention premises. Caller-clobbered pointer values do not survive either call.']
                   if self.policy == FLAGGED_STATE else [])
                + ([(f'The descriptor+{PAYLOAD_FIELDS[self.policy]} word is the only local pointer word; it addresses the payload adjacent to the '
                     'descriptor, whose extent is bounded above by the rest of the private frame, recorded as payload_frame_bytes '
                     '(an upper bound, not the payload type size). Payload initialization is not checked. The callback reads '
                     'the payload only through that word, only within that extent and only before the scheduler call '
                     'returns; caller-initialized members are values and padding bytes are representation only. '
                     'The pinned scheduler body copies the descriptor into its own frame, not the allocation, and makes '
                     'one synchronous phase-0 callback call; the callback copies payload values instead of retaining the '
                     'pointer. The payload size within '
                     'that bound, its initialization and the callback read bound are premises, not proofs. Callee-saved '
                     'register aliases to the descriptor or payload are admitted and recorded, as in the descriptor '
                     f'profile; the read-through-descriptor+{PAYLOAD_FIELDS[self.policy]} premise covers them.')]
                   if self.policy in PAYLOAD_FIELDS and self.policy != SCHEDULER_EVENT else [])
                + (['Every sequential scheduler invocation separately requires compatible return, exact SP and '
                    'protected caller/saved words, readable descriptor representation, allocation separation, '
                    'callback frame noninterference and nonretention. The copied R1 descriptor and original '
                    'R9 exposure remain conditional at each invocation. No actual callee/callback effects, '
                    'physical safety, allocation lifetime or termination theorem is established.']
                   if self.policy in (SCHEDULER_SEQUENTIAL, SCHEDULER_LEAF_OUTPUT, SCHEDULER_KILLED_ALIAS, *LOOP_LIVE_ALIAS) else [])
                + (['Scheduler sites inside a counted loop are invoked at most once per iteration (a site may '
                    'sit on a conditional arm), at most '
                    'counted_loops[].maximum_scheduler_calls times per loop entry; each invocation separately '
                    'requires every per-invocation premise above, including that no earlier invocation or '
                    'callback retains the reused descriptor or any local pointer. The iteration bound is '
                    'conditional on the counter register surviving each call. Every invocation of a looped '
                    'scheduler site is passed the same 28-byte descriptor frame; the owner may store to it '
                    'between invocations, and those stores are checked by the frame and alias replay like any '
                    'other store through a local alias. Its contents and nonretention remain stated premises, '
                    'as for the non-loop selectors. The only local aliases admitted across a looped scheduler '
                    'call are R2 and copies of the descriptor address in R4-R7, recorded in the site aliases; '
                    'a copy names no storage the invocation is not already handed in R2, and its value after '
                    'the call is conditional on R4-R7 surviving each call, as the counter is.']
                   if self.policy in LOOP_LIVE_ALIAS else []),
            actual_callback_effects_proved=False, nonescape_proved=False, termination_proved=False,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
