"""Selected native local-copy composition, without compiler/source admission.

The prefix is acyclic and contains no other calls or ordinary memory accesses.
Initialized-byte facts describe the copy's normal return, not arbitrary suffix
states. Physical memory, immutable ROM, and returning ABI premises stay explicit.
"""
import hashlib
import json
from pathlib import Path

import compiler_copy80_caller_prerequisite as prefix
import compiler_small_local_copy_prerequisite as helper
import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
from local_rom_halfword_table_profile import require

SELECTOR = 'conditional-small-local-copy-caller-v1'
SCHEMA = 'native-thumb-small-local-copy-caller-v1'


def _equal_manifest(manifest, observed):
    require(manifest is None or json.dumps(manifest, sort_keys=True) ==
            json.dumps(observed, sort_keys=True), 'small-copy caller manifest is stale')


def prerequisite(data, address, rom, mapping, index, objects, *, selector, manifest=None):
    import owner_admission_profile as owner
    require(type(selector) is str and selector == SELECTOR, 'explicit small-copy caller selector required')
    require(type(address) is int and all(type(raw) is bytes for raw in
            (data, rom, mapping, index, objects)), 'immutable original caller inputs required')
    buffers.validate_owner(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    require(not branches and not words, 'small-copy caller excludes local BL and switch words')
    candidates = [(site, target) for site, target in calls.items() if
        hashlib.sha256(rom[target-match.ROM_BASE:target-match.ROM_BASE+98]).hexdigest() ==
        helper.copy80.COPY_SHA256]
    require(len(candidates) == 1, 'one actual canonical small-copy call required')
    site, target = candidates[0]
    predecessors = {node: set() for node in instructions}
    for node, successors in edges.items():
        for successor in successors:
            if successor in predecessors:
                predecessors[successor].add(node)
    ancestors, pending = set(), [site]
    while pending:
        node = pending.pop()
        if node not in ancestors:
            ancestors.add(node)
            pending.extend(predecessors[node])
    require(address in ancestors and len(ancestors) <= 256, 'bounded reachable small-copy prefix required')
    require(not (set(calls) & (ancestors-{site})), 'small-copy prefix cannot cross another call')
    order, remaining = [], set(ancestors)
    while remaining:
        ready = sorted(node for node in remaining if not (predecessors[node] & remaining))
        require(ready, 'cyclic small-copy prefix requires a separate proof')
        order.extend(ready)
        remaining.difference_update(ready)
    registers = tuple(('entry', r, 0) for r in range(13)) + (('stack', 0), ('entry_return',), None)
    states = {address: {(registers, (), ())}}
    for node in order:
        require(node in states and len(states[node]) <= 128, 'small-copy prefix state budget exceeded')
        if node == site:
            break
        for state in states[node]:
            after = prefix.advance(instructions[node], state, data, address)
            require(not after[2], 'small-copy prefix excludes ordinary memory accesses')
            require(after[0][13][1] <= state[0][13][1], 'small-copy prefix cannot deallocate its frame')
            require(all(value is None or value[0] != 'stack' for _, value in after[1]),
                    'small-copy prefix cannot save or spill local aliases')
            for successor in edges[node]:
                if successor in ancestors:
                    states.setdefault(successor, set()).add(after)
    names = match.parse_data_symbols(objects)
    summaries = set()
    for registers, saves, memory in states[site]:
        destination, source, count = registers[:3]
        require(destination is not None and destination[0] == 'stack', 'actual local destination required')
        require(count is not None and count[0] == 'constant', 'actual constant copy count required')
        helper.count_value(count[1])
        low, high = registers[13][1], min((offset for offset, _ in saves), default=0)
        require(low <= destination[1] and destination[1]+count[1] <= high and low < high,
                'copy destination crosses its allocated local window or saved words')
        require(source is not None and source[0] == 'literal' and source[3] == 0,
                'copy source requires an unchanged PC-relative literal')
        require(match.ROM_BASE <= source[1] and source[1]+count[1] <= match.ROM_BASE+len(rom),
                'complete immutable source must lie in supplied ROM')
        identities = [name for name, point in names.items() if point == source[1]]
        require(len(identities) == 1, 'small-copy source requires one named ROM point')
        require(all(low <= offset and offset+4 <= 0 for offset, _ in saves), 'caller saves leave frame')
        require(all(source[1]+count[1] <= base or base+size <= source[1]
                    for base, size in ((address, len(data)), (target, 98))),
                'source overlaps complete participating code')
        summaries.add((destination[1], source, count[1], low, high, saves, identities[0]))
    require(len(summaries) == 1, 'small-copy prefix paths disagree on arguments or local frame')
    destination, source, count, low, high, saves, identity = summaries.pop()
    proof = helper.verify_helper(target, rom, mapping, index, count=count, selector=helper.SELECTOR)
    values = rom[source[1]-match.ROM_BASE:source[1]-match.ROM_BASE+count]
    effects = helper.relation(values)
    observed = dict(schema=SELECTOR, address=address, complete_bytes=len(data),
        native_instructions=len(instructions), partition=partition, call_site=site, target=target,
        destination_entry_sp_offset=destination, caller_sp_offset=low,
        local_window_entry_sp=[low, high], caller_saves=list(saves), count=count,
        source_point=source[1], source_identity=identity, source_literal_offset=source[2],
        source_bytes_sha256=hashlib.sha256(values).hexdigest(),
        initialized_bytes_at_copy_return=[[destination+i, value] for i, value in enumerate(effects['destination_bytes'])],
        helper=proof, helper_effects=effects,
        conditions=[
            'caller entry SP is aligned; complete caller frame and twelve additional helper save bytes are live ordinary readable/writable memory and do not wrap',
            'the complete active caller/helper frame is disjoint from immutable ROM and participating complete code',
            'supplied ROM bytes equal immutable ordinary runtime source bytes during the prefix and copy',
            'code and active memory are not modified asynchronously',
            'actual Thumb call/return and ordinary ABI compatibility hold; physical memory permissions and C compatibility remain external',
            'initialized-byte values apply at the actual helper normal return only; suffix writes, aliases, observations and memory permissions remain separate'],
        input_pins={name: hashlib.sha256(raw).hexdigest() for name, raw in
            (('owner', data), ('rom', rom), ('mapping', mapping), ('index', index), ('objects', objects))},
        producer_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in Path(__file__).parent.glob('*.py')},
        caller_arguments_proved=True, local_window_proved=True,
        complete_caller_admission=False, physical_access_proved=False, source_or_ELF_admission=False)
    _equal_manifest(manifest, observed)
    return observed


def concrete_domain(data, address, rom, mapping, index, objects, *, selector, entry_sp):
    """Check numeric entry-SP premises against a freshly authenticated window.

    This does not establish the machine's actual SP or grant memory permissions.
    """
    proof = prerequisite(data, address, rom, mapping, index, objects, selector=selector)
    require(type(entry_sp) is int and 0 <= entry_sp <= 0xFFFFFFFF and entry_sp % 4 == 0,
            'aligned supplied u32 caller entry SP required')
    low, high = proof['local_window_entry_sp']
    require(entry_sp+low >= 12, 'combined caller/helper frame wraps')
    result = helper.concrete_domain(count=proof['count'], helper_sp=entry_sp+low,
        source=proof['source_point'], destination=entry_sp+proof['destination_entry_sp_offset'],
        destination_window=(entry_sp+low, high-low), caller_code=(address, len(data)),
        helper_code=(proof['target'], 98))
    frame = (entry_sp+low-12, entry_sp)
    for base, size in ((proof['source_point'], proof['count']),
                       (address, len(data)), (proof['target'], 98)):
        require(frame[1] <= base or base+size <= frame[0],
                'complete active frame overlaps source or participating code')
    return dict(caller=proof, checked_numeric_domain=result,
        complete_frame_range=list(frame), actual_entry_sp_proved=False,
        caller_window_authenticated=True, physical_access_proved=False)


class SmallLocalCopyProof(buffers.NamedDataBufferProof):
    """Exact root copy summary; every other call retains existing buffer rules."""

    def __init__(self, data, address, rom, mapping, index, objects, *, selector):
        super().__init__(rom, mapping, index, objects)
        self.copy = prerequisite(data, address, rom, mapping, index, objects, selector=selector)
        self.copy_observations = set()

    def check_call(self, address, aliases, stack, slots=None, *, constants=None, site=None, words=None):
        if address != self.copy['target']:
            return super().check_call(address, aliases, stack, slots, constants=constants, site=site, words=words)
        require(site == self.copy['call_site'] and not slots and not words,
                'small copy requires its actual root site without pointer slots or word contexts')
        arguments = {reg: value for reg, value in aliases.items() if reg in match.CALLER_CLOBBERED}
        destination = self.copy['destination_entry_sp_offset']
        require(arguments == {match.ARM_REG_R0: destination} and
                -4*len(stack) == self.copy['caller_sp_offset'],
                'small-copy native arguments or live frame differ from authenticated prefix')
        for offset in range(destination, destination+self.copy['count']):
            self.access(offset, 1, stack)
        for offset, _ in self.copy['caller_saves']:
            require(not stack[(offset+4*len(stack))//4][2], 'saved word became a local window')
        data = self.span(address)
        self.dependencies[address] = data
        self.copy_observations.add((site, destination, len(stack)))
        # Exact helper retains R0's destination alias; R1 and R3 point outside
        # the caller stack under recorded ROM/frame separation premises.
        return {match.ARM_REG_R0: destination}


def verify(data, address, rom, mapping, index, objects, *, selector, manifest=None):
    """Replay the complete unchanged native frame/alias verifier, explicitly."""
    proof = SmallLocalCopyProof(data, address, rom, mapping, index, objects, selector=selector)
    import owner_admission_profile as owner
    refinement = owner.refine(data, address, mapping)
    native, _, branches, calls, words = graph.graph(data, address, refinement)
    require(not branches and not words, 'small-copy native profile excludes local BL and switches')
    instructions = match.verify_leaf_instructions(data, address, True, calls, buffer_proof=proof)
    require(set(native) == {item.address for item in instructions} and proof.copy_observations,
            'small-copy native replay differs from complete owner or omitted actual copy')
    observed = dict(schema=SCHEMA, selector=SELECTOR, caller=proof.copy,
        native_instructions=len(instructions), copy_observations=sorted(proof.copy_observations),
        dependencies=proof.records, buffer_fingerprint=proof.fingerprint(),
        native_frame_alias_replay=True, suffix_initialization_proved=False,
        source_or_ELF_admission=False, physical_access_proved=False)
    _equal_manifest(manifest, observed)
    return observed, instructions
