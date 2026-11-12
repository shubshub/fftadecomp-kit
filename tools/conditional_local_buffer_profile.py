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
import named_data_buffer_profile as named
import owner_graph_profile as graph
import function_thunk_profile as thunk

SCHEDULER = 'conditional-scheduler-descriptor-calls-v1'
SCHEDULER_BRANCH = 'conditional-scheduler-branch-descriptor-calls-v1'
SCHEDULER_FOLLOWING = 'conditional-scheduler-following-call-v1'
SCHEDULER_WIDE = 'conditional-scheduler-eight-target-branches-v1'
SCHEDULER_LOOP = 'conditional-scheduler-u16-counted-loop-v1'
SCHEDULER_PROJECTED = 'conditional-scheduler-projected-outputs-v1'
SCHEDULER_GUARDED = 'conditional-scheduler-guarded-descriptor-calls-v1'
SCHEDULER_PAYLOAD = 'conditional-scheduler-descriptor-payload-calls-v1'
SCHEDULER_PAYLOAD8 = 'conditional-scheduler-descriptor-payload8-calls-v1'
SCHEDULER_HALFWORD_PAYLOAD = 'conditional-scheduler-halfword-output-payload-v1'
SCHEDULER_TWO_PAYLOAD = 'conditional-scheduler-two-payload-calls-v1'
SCHEDULER_ENTRY = 'conditional-scheduler-entry-descriptor-calls-v1'
SCHEDULER_ENTRY_BRANCH = 'conditional-scheduler-entry-branch-descriptor-calls-v1'
SCHEDULER_MANAGER_FIELD = 'conditional-scheduler-indirect-manager-v1'
PAYLOAD_FIELDS = {SCHEDULER_PAYLOAD: 4, SCHEDULER_PAYLOAD8: 8, SCHEDULER_HALFWORD_PAYLOAD: 4, SCHEDULER_TWO_PAYLOAD: (4, 8)}
STATE = 'conditional-local-state-iterator-v1'
OUTPUT = 'conditional-local-output-word-call-v1'
SCHEMAS = {
    SCHEDULER_PROJECTED: 'elf-symbol-thumb-conditional-scheduler-projected-outputs-v1',
    SCHEDULER: 'elf-symbol-thumb-conditional-scheduler-descriptor-calls-v1',
    SCHEDULER_BRANCH: 'elf-symbol-thumb-conditional-scheduler-branch-descriptor-calls-v1',
    SCHEDULER_FOLLOWING: 'elf-symbol-thumb-conditional-scheduler-following-call-v1',
    SCHEDULER_WIDE: 'elf-symbol-thumb-conditional-scheduler-eight-target-branches-v1',
    SCHEDULER_LOOP: 'elf-symbol-thumb-conditional-scheduler-u16-counted-loop-v1',
    SCHEDULER_GUARDED: 'elf-symbol-thumb-conditional-scheduler-guarded-descriptor-calls-v1',
    SCHEDULER_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-descriptor-payload-calls-v1',
    SCHEDULER_PAYLOAD8: 'elf-symbol-thumb-conditional-scheduler-descriptor-payload8-calls-v1',
    SCHEDULER_HALFWORD_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-halfword-output-payload-v1',
    SCHEDULER_TWO_PAYLOAD: 'elf-symbol-thumb-conditional-scheduler-two-payload-calls-v1',
    SCHEDULER_ENTRY: 'elf-symbol-thumb-conditional-scheduler-entry-descriptor-calls-v1',
    SCHEDULER_ENTRY_BRANCH: 'elf-symbol-thumb-' + SCHEDULER_ENTRY_BRANCH,
    SCHEDULER_MANAGER_FIELD: 'elf-symbol-thumb-conditional-scheduler-indirect-manager-v1',
    STATE: 'elf-symbol-thumb-conditional-local-state-iterator-v1',
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
        if policy in (SCHEDULER_GUARDED, SCHEDULER_WIDE, SCHEDULER_PROJECTED):
            # Eight authenticated helpers plus two scheduler bodies and two thunks.
            self.dependency_budget = 12

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
        elif self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE):
            import scheduler_branch_profile as branch
            self.branch_calls = branch.bind(self, edges, calls, following_calls=self.policy == SCHEDULER_FOLLOWING, wide_targets=self.policy == SCHEDULER_WIDE)
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_GUARDED:
            import scheduler_predicate_profile as predicates
            predicates.phases(edges, calls)
            self.predicates = predicates.close(self, set(calls.values()) - {0x08005B6C})
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy == SCHEDULER_ENTRY_BRANCH:
            import scheduler_entry_branch_profile as entry_branch
            self.scheduler_entry, self.scheduler_entry_branches = entry_branch.bind(data, address, ins, edges, calls)
            dependencies = self.scheduler_entry['dependencies']
            runtime_names = ('_call_via_r2', '_call_via_r3')
        elif self.policy in (SCHEDULER_ENTRY, SCHEDULER_MANAGER_FIELD):
            if self.policy == SCHEDULER_MANAGER_FIELD:
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

    def check_indirect_target(self, address, aliases, returns, *, site):
        if not thunk.reserved(address):
            return
        require(self.policy == STATE and self.calls.get(site) == address == 0x0814224C,
                'local-buffer indirect call differs from authenticated root')
        require(match.ARM_REG_R0+2 not in aliases and
                not set(returns) & (set(match.CALLER_CLOBBERED) - {match.ARM_REG_LR}),
                'local-buffer indirect target carries pointer or return provenance')

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        require(self.calls.get(site) == address and not words,
                'local-buffer call differs from its authenticated interface')
        if self.policy == SCHEDULER_PROJECTED:
            import scheduler_projected_outputs_profile as projected
            return projected.check_call(self, address, aliases, stack, slots, site=site)
        if self.policy in (SCHEDULER_ENTRY, SCHEDULER_ENTRY_BRANCH, SCHEDULER_MANAGER_FIELD):
            if self.policy == SCHEDULER_MANAGER_FIELD:
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
        if self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_LOOP) and address != 0x08005B6C:
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
        if self.policy in (SCHEDULER, SCHEDULER_GUARDED, SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_LOOP):
            require({reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2} and not slots,
                    'scheduler contract excludes additional register or pointer-word aliases')
            offset, width = aliases[r2], 28
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
            if address == 0x0814224C:
                require(aliases == {r0: base} and not slots and (constants or {}).get(r0+1) == 4,
                        'state callback requires its actual local pointer and constant four-byte size')
                offset, width = base, 4
            else:
                require(aliases == {r2: base+4} and slots == {base+4: base},
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
        if self.policy == SCHEDULER_ENTRY_BRANCH:
            import scheduler_entry_branch_profile as entry_branch
            return entry_branch.manifest(self)
        if self.policy == SCHEDULER_PROJECTED:
            import scheduler_projected_outputs_profile as projected
            return projected.manifest(self)
        if self.policy in (SCHEDULER_ENTRY, SCHEDULER_ENTRY_BRANCH, SCHEDULER_MANAGER_FIELD):
            if self.policy == SCHEDULER_MANAGER_FIELD:
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
            **({'predicates': self.predicates} if self.policy == SCHEDULER_GUARDED else {}),
            **({'owner_list_load': self.owner_list_load} if self.policy == STATE else {}),
            **({'branch_calls': self.branch_calls} if self.policy in (SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_LOOP) else {}),
            observations=[self.observations[s] for s in sorted(self.observations)],
            assumptions=[
                'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved.',
                'No local pointer is retained for later use or returned through caller-clobbered registers.',
                ('Scheduler allocator/zero/list prefix and callback obey frame noninterference; the 28-byte '
                 'descriptor is readable as representation bytes, its copied pointer values remain conditional, '
                 'and the returned allocation is separate from all caller stack words. Both the copied R1 '
                 'descriptor and ambient original R9 pointer are exposed to the callback; copying does not prove nonescape.'
                 if self.policy in (SCHEDULER, SCHEDULER_GUARDED, SCHEDULER_BRANCH, SCHEDULER_FOLLOWING, SCHEDULER_WIDE, SCHEDULER_LOOP, *PAYLOAD_FIELDS) else
                 'The indexed output callee writes at most the single four-byte local result word through R2 and '
                 'accesses no other private/saved caller word. Its body identity is checked, but its stores are '
                 'not alias-analysed; ROM inspection shows two 16-bit stores at R2+0 (0x0807A046, 0x0807A05C). '
                 'The word\'s value after the call is conditional; R0/R1 carry no caller-frame pointer.'
                 if self.policy == OUTPUT else
                 'The installed initial callback initializes exactly the four state bytes without accessing other '
                 'private/saved words. Constant n=4 is an interface argument, not a proof of callback behavior. '
                 'Iterator objects and scalar-query callees are valid and separate from the caller frame; '
                 'the visitor record remains unchanged and the known callback accesses only state bytes 0 and 1.')]
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
                   if self.policy in PAYLOAD_FIELDS else []),
            actual_callback_effects_proved=False, nonescape_proved=False, termination_proved=False,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
