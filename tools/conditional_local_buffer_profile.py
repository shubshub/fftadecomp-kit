"""Opt-in local-buffer call contracts for the two issue #73 interfaces.

These are conditional ABI/effect contracts, not inferred callback effects.
In particular a length argument does not prove a write bound, and the scheduler
copy does not prove nonescape. Defaults retain the ordinary buffer verifier.
"""
import hashlib
from pathlib import Path
import struct

import match
import named_data_buffer_profile as named
import owner_graph_profile as graph
import function_thunk_profile as thunk

SCHEDULER = 'conditional-scheduler-descriptor-calls-v1'
STATE = 'conditional-local-state-iterator-v1'
SCHEMAS = {
    SCHEDULER: 'elf-symbol-thumb-conditional-scheduler-descriptor-calls-v1',
    STATE: 'elf-symbol-thumb-conditional-local-state-iterator-v1',
}
SELECTORS = tuple(SCHEMAS)
CONTROL_FLOW = 'complete Thumb caller with bounded local interfaces under explicit returning-call, bounded-effect and nonretention premises; actual callback effects and termination unproved'
# Complete indexed dependency identities, never an address-only exemption.
DEPENDENCIES = {
    0x08005B6C: (60, 'c6a20896e48a2d20f9a4e9d59b780095f5e082b65619a2a96cee0ebc26e8c475'),
    0x08005954: (206, '4e3fba4f8cb6ee77b2d0251866e2f85338ab5550832ce8fc0807b3835b0c677e'),
    0x080C7CC0: (34, '47422d610f242091222c8c8e303ea235eede92f9a9c9cc40cd8552e8f44f45d1'),
    0x0809ABE8: (22, '65ec4ecbbacee97448810c0c4bb966405fc392884ba09795dc94b0b00aeff3d4'),
    0x080C7B74: (4, 'a89b85f8bccd76763270edbe8d4a9000e557118189ef0a663b750b93593d16da'),
    0x08098BB0: (112, '4b56b7d9e7ba587ee64a6d4da1eb3b51b2e6eb7cfcb989a8534fa86a7602c3cc'),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class ConditionalLocalBufferProof(named.NamedDataBufferProof):
    def __init__(self, rom, mapping, index, objects, *, policy):
        require(policy in SELECTORS, 'explicit local-buffer contract required')
        super().__init__(rom, mapping, index, objects)
        self.policy = policy
        self.observations = {}

    def bind_root(self, data, address, calls):
        import owner_admission_profile as owner
        from known_query_native_closure_profile import environment_fingerprint
        require(not hasattr(self, 'root'), 'local-buffer contract context is single use')
        named.validate_owner(data, address, self.rom, self.mapping, self.index)
        ins, _, branches, actual, words = graph.graph(data, address, owner.refine(data, address, self.mapping))
        require(not branches and not words and calls == actual,
                'local-buffer contracts exclude local BL and switches')
        self.root, self.calls = (address, bytes(data)), dict(calls)
        self.environment = environment_fingerprint()
        if self.policy == SCHEDULER:
            require(len(calls) == 1 and set(calls.values()) == {0x08005B6C},
                    'scheduler contract requires one actual scheduler call')
            dependencies = (0x08005B6C, 0x08005954)
            runtime_names = ('_call_via_r2', '_call_via_r3')
        else:
            require(len(data) == 60 and calls == {address+14: 0x0814224C, address+32: 0x080C7CC0}
                    and data[:14] == bytes.fromhex('10b583b0041c0a48026868460421')
                    and data[18:32] == bytes.fromhex('08486946019101aa5060a0690649')
                    and data[36:48] == bytes.fromhex('6846007803b010bc02bc0847')
                    and struct.unpack_from('<III', data, 48) == (0x0836D4B8, 0x08098BB1, 0x0809ABE9),
                    'state contract requires the exact four-byte state and initialized visitor interface')
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
        r0, r2 = match.ARM_REG_R0, match.ARM_REG_R0+2
        if self.policy == SCHEDULER:
            require({reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {r2} and not slots,
                    'scheduler contract excludes additional register or pointer-word aliases')
            offset, width = aliases[r2], 28
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
        for byte in range(offset, offset+width):
            self.access(byte, 1, stack)
        observation = dict(site=site, target=address, local_offset=offset, bytes=width,
                           aliases=sorted(aliases.items()), pointer_words=sorted((slots or {}).items()))
        require(site not in self.observations or self.observations[site] == observation,
                'local-buffer contract differs across incoming paths')
        self.observations[site] = observation
        return {}

    def contract_manifest(self):
        require(set(self.observations) == set(self.calls), 'every conditional local-buffer call must be observed')
        return dict(schema=SCHEMAS[self.policy], runtime_dependencies=self.runtime_dependencies,
            environment=self.environment,
            observations=[self.observations[s] for s in sorted(self.observations)],
            assumptions=[
                'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved.',
                'No local pointer is retained for later use or returned through caller-clobbered registers.',
                ('Scheduler allocator/zero/list prefix and callback obey frame noninterference; the 28-byte '
                 'descriptor is readable as representation bytes, its copied pointer values remain conditional, '
                 'and the returned allocation is separate from all caller stack words. Both the copied R1 '
                 'descriptor and ambient original R9 pointer are exposed to the callback; copying does not prove nonescape.'
                 if self.policy == SCHEDULER else
                 'The installed initial callback initializes exactly the four state bytes without accessing other '
                 'private/saved words. Constant n=4 is an interface argument, not a proof of callback behavior. '
                 'Iterator objects and scalar-query callees are valid and separate from the caller frame; '
                 'the visitor record remains unchanged and the known callback accesses only state bytes 0 and 1.')],
            actual_callback_effects_proved=False, nonescape_proved=False, termination_proved=False,
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
