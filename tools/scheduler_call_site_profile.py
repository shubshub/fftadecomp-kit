"""Scheduler descriptor calls as per-site summaries in the ordinary owner walk.

Explicit opt-in owner selector (issue #237). The earlier conditional-scheduler
selectors apply the 28-byte descriptor contract at a scheduler call and also
bound the shape of the whole caller: one scheduler call, at most N sites or
targets, no CFG cycle, no call after a scheduler return. Those bounds limit the
cost of each selector's whole-owner proof; they are not part of the frame
argument. This selector keeps the per-site contract and drops the shape bounds.
The complete owner CFG is replayed by the existing named-data buffer walk
(joins, saved slots, returns, loops and every other call under the unchanged
buffer rules), and every direct call to one of three pinned entries is
discharged on its own:

* func_08005B6C and func_08121B8C: callback R0, size R1, descriptor R2,
  parent R3;
* func_08005954 called directly: manager R0, callback R1, size R2,
  descriptor R3, parent in the caller's outgoing word at SP.

Obligations at each site, all checked against the walk's state there:

1. the descriptor register is the only caller-clobbered alias (no alias in
   R0-R3, R12 or LR besides it);
2. the descriptor is word aligned and its 28 bytes are allocated local words,
   never a saved slot;
3. direct entry: the outgoing word at SP is an allocated local word below the
   descriptor and holds no tracked local pointer; every definition of R0 that
   reaches the site is a load chain rooted at a PC literal: a zero-offset word
   load, then at most one word load at an aligned field offset 0-124, through
   exact copies, the shapes of the existing direct-entry selectors.
   check_bindings requires each literal to be a typed zero-addend named data
   binding;
4. a pointer-bearing word inside the descriptor is admitted only at
   descriptor+4 or descriptor+8, must address an allocated local word outside
   the descriptor, and is recorded with its extent: from its target to the end
   of that contiguous run of allocated local words, or to the descriptor if
   that comes first. The extent must contain no pointer-bearing word and, at a
   direct site, not the outgoing argument word. Other pointer-bearing words are
   recorded and keep their facts; no pinned body reads them;
5. callee-saved aliases are recorded. At a site inside a CFG cycle only R4-R7
   copies of the descriptor address are admitted, and no pointer-bearing word;
6. the call hands back no alias; the walk then clobbers R0-R3, R12 and LR as at
   any call. The direct entry's outgoing word holds no pointer fact to drop;
7. every definition of the callback register that reaches the site is a
   PC-relative load of an owner literal word, directly or through exact
   register copies; check_bindings requires each such word to be a typed
   function binding.

The scheduler bodies, the allocator and the callbacks are never walked. Their
effects are the descriptor selectors' premises, stated per invocation.

conditional-scheduler-call-site-summaries-v2 (issue #238) is the same contract
with the forwarded callee stack arguments of issue #183, the rule
named-data-buffer-stack-index-v2 already applies (match.BufferCallProof,
forwarded_slot_step and forwarded_frame_change, unchanged), so that v1 reports
keep their meaning:

8. an inspected buffer callee may store a tracked owner-frame pointer into an
   aligned word of its own frame as its own callee's outgoing stack argument,
   only if its every SP use is PUSH, POP, ADD/SUB SP,#imm or an immediate
   [sp,#imm] access; the next callee is walked with that word as an incoming
   stack argument, so every access through it is still bounded against the
   owner's frame. A call an inspected callee makes with its own frame keeps
   v1's buffer rules, with no forwarding, since a slot there would not be in
   owner terms;
9. a slot released by ADD SP still holds the pointer: it is tracked until
   written, walked code that reads it refuses, walked callees inherit it, and
   calls trusted while it lies below SP are recorded;
10. at the owner, the words a walked root call's callee released are recorded
    and removed from its result. On every owner CFG path after such a call the
    owner may not move SP down (SUB SP,#imm; the core walk already refuses
    ADD/MOV SP,Rm), nor make any call the walk inspects: one that receives a
    stack pointer in R0-R3, R12 or LR or while a frame word holds one, and
    every scheduler site, none of which is told about the word. Every later
    call is trusted under the recorded FORWARD_PREMISE of
    stack_index_precondition_profile;
11. at least one forwarded slot is recorded, so v1 and v2 admit disjoint sets.

This proof never replays loops (a callee that needs replay refuses as under
v1), so forwarding never meets replay.
"""
import hashlib
from pathlib import Path
import struct

import match
import function_thunk_profile as thunk
from scheduler_loop_composition_profile import components

SELECTOR = 'conditional-scheduler-call-site-summaries-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
SELECTOR_V2 = 'conditional-scheduler-call-site-summaries-v2'
SCHEMA_V2 = 'elf-symbol-thumb-' + SELECTOR_V2
SCHEMAS = {SELECTOR: SCHEMA, SELECTOR_V2: SCHEMA_V2,
           'conditional-effect-initialized-scheduler-v1': 'elf-symbol-thumb-conditional-effect-initialized-scheduler-v1',
           'conditional-scheduler-sdk-halfword-fill-v1': 'elf-symbol-thumb-conditional-scheduler-sdk-halfword-fill-v1'}
SCHEDULER, POOL, DIRECT = 0x08005B6C, 0x08121B8C, 0x08005954
# Closed entry table; every listed body is pinned by size and SHA-256 in
# conditional_local_buffer_profile.DEPENDENCIES.
ENTRIES = {
    SCHEDULER: dict(kind='scheduler', callback_register=0, descriptor_register=2,
                    dependencies=(SCHEDULER, DIRECT)),
    POOL: dict(kind='pool-manager-wrapper', callback_register=0, descriptor_register=2,
               dependencies=(POOL, DIRECT)),
    DIRECT: dict(kind='direct-entry', callback_register=1, descriptor_register=3,
                 dependencies=(DIRECT,)),
}
RUNTIME_NAMES = ('_call_via_r2', '_call_via_r3')
DESCRIPTOR_BYTES = 28
PAYLOAD_FIELDS = (4, 8)
# Three pinned entry bodies, two canonical thunks and the eight inspected
# callees the named-data buffer proof admits on its own.
DEPENDENCY_BUDGET = 13


def require(condition, message):
    if not condition:
        raise ValueError(message)


def looped_sites(edges, sites):
    """Scheduler sites inside a CFG cycle: a nontrivial component or a self loop."""
    component = components(edges)
    members = {}
    for site, root in component.items():
        members.setdefault(root, set()).add(site)
    return sorted(site for site in sites
                  if len(members[component[site]]) > 1 or site in edges[site])


def register_copy(instruction):
    """(destination, source) register numbers of an exact Thumb register copy, else None.

    `adds rd,rs,#0`, `lsls rd,rs,#0` (movs) and the high-register `mov rd,rs`,
    with both registers in R0-R12.
    """
    if instruction.size != 2:
        return None
    raw = int.from_bytes(instruction.bytes, 'little')
    if raw & 0xFFC0 in (0x1C00, 0x0000):
        destination, source = raw & 7, raw >> 3 & 7
    elif raw & 0xFF00 == 0x4600:
        destination, source = (raw & 7) | (raw >> 4 & 8), raw >> 3 & 15
    else:
        return None
    return (destination, source) if destination <= 12 and source <= 12 else None


def reaching_definitions(ins, edges, calls, address, site, register, message):
    """(site, register) of every definition of `register` that reaches `site`.

    Exact register copies are followed to their source's definitions. A call
    that clobbers the register, an interrupt, an unvalidated call or reaching
    the owner entry without a definition refuses with `message`. A value in
    R4-R11 followed across a call rests on the returning ARM ABI premise, as
    every preserved-register fact does.
    """
    predecessors = {s: [] for s in edges}
    for source, targets in edges.items():
        for target in targets:
            require(target in predecessors, 'scheduler register search leaves the complete owner')
            predecessors[target].append(source)
    clobbered = set(match.CALLER_CLOBBERED)
    definitions, seen, pending = set(), set(), [(site, register)]
    while pending:
        current, wanted = pending.pop()
        require(current != address, message)
        for previous in predecessors[current]:
            if (previous, wanted) in seen:
                continue
            seen.add((previous, wanted))
            instruction = ins[previous]
            # The owner walk refuses interrupts and every call but a validated BL on its own;
            # refusing them here keeps this search independent of that order.
            require(match.CS_GRP_INT not in instruction.groups and
                    (match.CS_GRP_CALL not in instruction.groups or previous in calls),
                    'scheduler register search reaches an interrupt or unvalidated call')
            if previous in calls:
                require(wanted not in clobbered, message)
                pending.append((previous, wanted))
                continue
            if wanted not in instruction.regs_access()[1]:
                pending.append((previous, wanted))
                continue
            copy = register_copy(instruction)
            if copy is not None and match.ARM_REG_R0 + copy[0] == wanted:
                pending.append((previous, match.ARM_REG_R0 + copy[1]))
                continue
            definitions.add((previous, wanted))
    require(definitions, message)
    return sorted(definitions)


def pc_literal(data, address, instruction, register):
    """Owner offset of the word an exact `ldr register,[pc,#imm]` loads, else None."""
    raw = int.from_bytes(instruction.bytes, 'little')
    if instruction.size != 2 or raw & 0xF800 != 0x4800 or match.ARM_REG_R0 + (raw >> 8 & 7) != register:
        return None
    offset = ((instruction.address + 4) & ~3) + 4 * (raw & 0xFF) - address
    require(0 <= offset and offset + 4 <= len(data),
            'scheduler literal is not a complete owner word')
    return offset


def word_load(instruction, register):
    """(base register, offset) of an exact `ldr register,[rn,#imm5*4]`, else None."""
    raw = int.from_bytes(instruction.bytes, 'little')
    if instruction.size != 2 or raw & 0xF800 != 0x6800 or match.ARM_REG_R0 + (raw & 7) != register:
        return None
    return match.ARM_REG_R0 + (raw >> 3 & 7), 4 * (raw >> 6 & 31)


CALLBACK_REFUSAL = 'scheduler callback register is not a function literal on every path'
MANAGER_REFUSAL = ('direct scheduler manager requires a typed named literal and a zero-offset '
                   'word load, then at most one aligned field load, on every path')


def callback_literals(data, address, ins, edges, calls, site, register):
    """Owner literal offsets of every definition of `register` reaching `site`.

    Each reaching definition must be `ldr rC,[pc,#imm]`, directly or through
    exact register copies.
    """
    literals = set()
    for definition, wanted in reaching_definitions(ins, edges, calls, address, site, register,
                                                   CALLBACK_REFUSAL):
        offset = pc_literal(data, address, ins[definition], wanted)
        require(offset is not None, CALLBACK_REFUSAL)
        literals.add(offset)
    return sorted(literals)


def manager_chains(data, address, ins, edges, calls, site):
    """Every load chain that defines R0 at a direct func_08005954 site.

    The shapes are those of the existing direct-entry selectors: a typed named
    literal, one word load at offset 0 (entry selector), and optionally a
    second word load at an aligned field offset 0-124 (indirect-manager,
    manager-offset and manager-paths). Register copies and joins are followed
    as in the callback search.
    """
    chains = set()
    for final, final_register in reaching_definitions(ins, edges, calls, address, site,
                                                      match.ARM_REG_R0, MANAGER_REFUSAL):
        load = word_load(ins[final], final_register)
        require(load is not None, MANAGER_REFUSAL)
        base, field = load
        for inner, inner_register in reaching_definitions(ins, edges, calls, address, final, base,
                                                          MANAGER_REFUSAL):
            literal = pc_literal(data, address, ins[inner], inner_register)
            if literal is not None:
                require(field == 0, MANAGER_REFUSAL)
                chains.add((literal, inner, None, final, 0, 1))
                continue
            first = word_load(ins[inner], inner_register)
            require(first is not None and first[1] == 0, MANAGER_REFUSAL)
            for origin, origin_register in reaching_definitions(ins, edges, calls, address, inner,
                                                                first[0], MANAGER_REFUSAL):
                literal = pc_literal(data, address, ins[origin], origin_register)
                require(literal is not None, MANAGER_REFUSAL)
                chains.add((literal, origin, inner, final, field, 2))
    return [dict(literal_offset=literal, literal_load_site=literal_site, pointer_load_site=pointer,
                 dereference_site=final, field_offset=field, dereference_count=count)
            for literal, literal_site, pointer, final, field, count in
            sorted(chains, key=lambda chain: (chain[0], chain[1], chain[2] or 0, chain[3]))]


def bind(data, address, ins, edges, calls):
    sites = {site: target for site, target in calls.items() if target in ENTRIES}
    require(sites, 'call-site summaries require a direct call to a pinned scheduler entry')
    require(not any(thunk.reserved(target) or target in match.RUNTIME_HELPERS.values()
                    for target in calls.values()),
            'call-site summaries exclude root calls through runtime thunks')
    looped = looped_sites(edges, sites)
    records = []
    for site, target in sorted(sites.items()):
        entry = ENTRIES[target]
        offsets = callback_literals(data, address, ins, edges, calls, site,
                                    match.ARM_REG_R0 + entry['callback_register'])
        record = dict(site=site, target=target, scheduler_entry=entry['kind'],
            callback_register=entry['callback_register'],
            descriptor_register=entry['descriptor_register'],
            callback_literal_offsets=offsets, looped=site in looped)
        if target == DIRECT:
            record['manager_chains'] = manager_chains(data, address, ins, edges, calls, site)
        records.append(record)
    dependencies = sorted({body for target in sites.values() for body in ENTRIES[target]['dependencies']})
    return dict(sites=records, looped_sites=looped, dependencies=dependencies,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def bind_forwarding(proof, edges):
    """v2: turn on issue #183's forwarded slots for every callee the walk inspects."""
    if proof.policy != SELECTOR_V2:
        return
    proof.forwarded_stack_arguments = True
    proof.forward_slot_records = set()   # (callee, store site, callee entry-SP offset, owner offset)
    proof.forward_trusted_calls = set()  # (caller, site, target) trusted inside a walked callee
    proof.forward_releases = {}          # owner call site -> owner entry-SP offsets released
    proof.walked_sites = set()           # owner call sites checked by the buffer rules
    proof.owner_edges = dict(edges)


def walked_call(proof, result, stack, *, site):
    """An owner call checked by the buffer rules: under v2, record the site and remove the
    released words its callee hands back (they lie below the owner's SP; see forwarding)."""
    if proof.policy != SELECTOR_V2:
        return result
    proof.walked_sites.add(site)
    stale = match.stale_words(result)
    if not stale:
        return result
    proof.forward_releases.setdefault(site, set()).update(position - 4 * len(stack) for position in stale)
    return type(result)({key: value for key, value in result.items() if key not in stale.values()})


SP_DOWN_REFUSAL = 'the owner moves SP down after a callee released a forwarded pointer word'
STACK_POINTER_REFUSAL = ('the owner passes stack pointers to a callee after a callee released a '
                         'forwarded pointer word')


def forwarding(proof):
    """The v2 record: every forwarded slot and released word, and the owner rules after a release.

    A released word still holds a pointer into the owner's frame, below the owner's SP. The
    owner reaches memory below SP only by moving SP down, and a callee reaches it below its
    entry SP; a walked callee or a scheduler site would not be told about the word. So on
    every owner path after the release both are refused, and every other call is trusted
    under FORWARD_PREMISE, as named-data-buffer-stack-index-v2 does.
    """
    from stack_index_precondition_profile import FORWARD_PREMISE, moves_sp_down
    require(proof.forward_slot_records,
            'forwarded call-site summaries require a forwarded callee stack argument')
    address, data = proof.root
    edges = proof.owner_edges
    releases = [[site, sorted(positions)] for site, positions in sorted(proof.forward_releases.items())]
    after, pending = set(), [successor for site, _ in releases for successor in edges[site]]
    while pending:
        site = pending.pop()
        if site not in after:
            after.add(site)
            pending.extend(edges[site])
    handed = proof.walked_sites | set(proof.observations)
    trusted = []
    for site in sorted(after):
        require(not moves_sp_down(struct.unpack_from('<H', data, site - address)[0]), SP_DOWN_REFUSAL)
        require(site not in handed, STACK_POINTER_REFUSAL)
        if site in proof.calls:
            trusted.append([site, proof.calls[site]])
    return dict(slots=sorted(list(record) for record in proof.forward_slot_records),
                released=releases, trusted_calls=trusted,
                trusted_callee_calls=sorted(list(record) for record in proof.forward_trusted_calls),
                premise=FORWARD_PREMISE if releases else None, premise_proved=False)


def payload_extent(value, stack, descriptor):
    """End (entry-SP-relative) of a payload at `value`: the end of the run of
    allocated local words holding it, or the descriptor if that comes first."""
    index = (value + 4 * len(stack)) // 4
    while index < len(stack) and stack[index][2]:
        index += 1
    end = -4 * len(stack) + 4 * index
    return min(end, descriptor) if value < descriptor else end


def check_call(proof, address, aliases, stack, slots, *, site):
    record = next((item for item in proof.scheduler_call_sites['sites'] if item['site'] == site), None)
    require(record is not None and record['target'] == address,
            'scheduler call site differs from its authenticated interface')
    register = match.ARM_REG_R0 + record['descriptor_register']
    slots = slots or {}
    require({reg for reg in aliases if reg in match.CALLER_CLOBBERED} == {register},
            'scheduler call site admits only the descriptor register as a caller-clobbered alias')
    require(all(type(reg) is int and match.ARM_REG_R0 <= reg <= match.ARM_REG_R0 + 12 or
                reg == match.ARM_REG_LR for reg in aliases),
            'scheduler call site aliases must be registers')
    offset = aliases[register]
    # func_08005954 copies the descriptor with LDM, which ignores address bits [1:0].
    require(offset % 4 == 0, 'scheduler descriptor must be word-aligned')
    for word in range(offset, offset + DESCRIPTOR_BYTES, 4):
        proof.access(word, 4, stack)
    observation = dict(site=site, target=address, scheduler_entry=record['scheduler_entry'],
                       descriptor_offset=offset, descriptor_bytes=DESCRIPTOR_BYTES,
                       frame_bytes=4 * len(stack), looped=record['looped'],
                       aliases=sorted(aliases.items()))
    if address == DIRECT:
        # The fifth argument is the caller's outgoing word at SP; the callee
        # reads it as the parent and may overwrite it (it owns the word).
        base = -4 * len(stack)
        require(offset >= base + 4, 'direct scheduler descriptor overlaps the outgoing argument word')
        proof.access(base, 4, stack)
        require(base not in slots, 'direct scheduler parent word holds a local pointer')
        observation['outgoing_argument_word'] = base
    inside = {word: value for word, value in slots.items() if offset <= word < offset + DESCRIPTOR_BYTES}
    payloads = []
    for word, value in sorted(inside.items()):
        require(word - offset in PAYLOAD_FIELDS,
                'scheduler descriptor pointer words are admitted only at descriptor+4 and descriptor+8')
        proof.access(value, 1, stack)
        require(not offset <= value < offset + DESCRIPTOR_BYTES,
                'scheduler payload word addresses the descriptor')
        end = payload_extent(value, stack, offset)
        # The extent is the only bound on the callback's payload reads; a pointer
        # word inside it would hand the callback a further caller address.
        require(not any(other < end and other + 4 > value for other in slots),
                'scheduler payload extent contains a pointer-bearing word')
        # The direct entry's outgoing word belongs to the callee, which may overwrite it.
        require(address != DIRECT or not (value < base + 4 and end > base),
                'scheduler payload extent includes the direct entry outgoing argument word')
        payloads.append(dict(descriptor_field=word - offset, offset=value, extent_bytes=end - value))
    observation['payload_words'] = payloads
    observation['other_pointer_words'] = sorted((word, value) for word, value in slots.items()
                                                if word not in inside)
    if record['looped']:
        # A repeated invocation admits only copies of the address it is
        # already handed in the descriptor register (issue #198).
        require(all(match.ARM_REG_R0 + 4 <= reg <= match.ARM_REG_R0 + 7 and value == offset
                    for reg, value in aliases.items() if reg != register),
                'looped scheduler calls exclude every local alias other than the descriptor '
                'register and R4-R7 copies of its address')
        require(not slots, 'looped scheduler calls exclude pointer-bearing local words')
    require(site not in proof.observations or proof.observations[site] == observation,
            'local-buffer contract differs across incoming paths')
    proof.observations[site] = observation
    return {}


def check_bindings(manifest, bindings):
    """Every callback literal is a typed function binding; every manager literal a
    typed zero-addend named data binding."""
    functions = {row[0] for row in bindings['functions']}
    for record in manifest['call_sites']['sites']:
        require(record['callback_literal_offsets'] and
                set(record['callback_literal_offsets']) <= functions,
                'scheduler callback register requires a typed function literal')
        require((record['target'] == DIRECT) == ('manager_chains' in record) and
                (record['target'] != DIRECT or record['manager_chains']),
                'direct scheduler site requires its recorded manager chains')
        for chain in record.get('manager_chains', ()):
            rows = [row for row in bindings['data'] if row[0] == chain['literal_offset']]
            require(len(rows) == 1 and len(rows[0]) == 3 and rows[0][2] == 0,
                    'direct scheduler manager literal requires one typed zero-addend named data relocation')


PREMISES = [
    'Actual calls return with compatible ARM ABI, exact SP and protected saved/caller words preserved.',
    'No local pointer is retained for later use or returned through caller-clobbered registers.',
    'Scheduler allocator/zero/list prefix and callback obey frame noninterference; the 28-byte '
    'descriptor is readable as representation bytes, its copied pointer values remain conditional, '
    'and the returned allocation is separate from all caller stack words. Both the copied R1 '
    'descriptor and ambient original R9 pointer are exposed to the callback; copying does not prove nonescape.',
    'Every recorded preserved-register alias is also exposed; the callback must not access other '
    'private or saved caller bytes through it.',
    'The parent argument is NULL or a valid scheduler node that addresses no caller stack word: '
    'func_08005954 writes through it (str r7,[r6,#0x10] at 0x080059BC) and walks its +8 chain, '
    'storing into the last node (0x080059A6-0x080059B0). Its value is not checked.',
    'At a func_08121B8C site the pinned wrapper forwards R0-R3 unchanged as callback, u16 size, '
    'descriptor and parent to the pinned func_08005954 body, with the manager loaded from the word '
    'addressed by its pool state data_020159CC; that pool word is a valid scheduler manager separate '
    'from every caller stack word. Its own outgoing word is in its frame, not the caller frame.',
    'At a direct func_08005954 site R0 is, on each actual path, the value of a recorded manager chain: '
    'the typed named literal addresses a readable aligned word; for a one-load chain the word read is '
    'the manager; for a two-load chain the pointer read from it plus the recorded field offset '
    'addresses another readable aligned word without address wraparound, and the word read there is '
    'the manager. The storage words are separate from every caller stack word; their values are those '
    'seen by the recorded loads, and no equality of values across paths follows. The manager is a valid '
    'scheduler manager separate from every caller stack word. The pinned body reads its fifth argument '
    'from the caller outgoing word at SP (ROM inspection: ldr r6,[sp,#0x38] at 0x08005966 after its '
    '56-byte frame) as the parent value and may overwrite that word; it holds no tracked local pointer '
    'and its initialization is not checked. No other caller private or saved word is read through SP.',
    'Each recorded payload word (descriptor+4 or descriptor+8) addresses a private payload whose extent is '
    'bounded above by its recorded extent_bytes: from the word\'s target to the end of that contiguous run '
    'of allocated local words or to the descriptor, whichever comes first (an upper bound, not the payload '
    'type size); the extent holds no pointer-bearing word and no direct-entry outgoing argument word. '
    'The callback reads the payload only through that word, only within that extent and only before the scheduler call returns, and '
    'retains no pointer to it. Payload initialization is not checked; caller-initialized members are '
    'values and padding bytes are representation only. Recorded pointer-bearing words outside the '
    'descriptor are not read by the pinned bodies and are covered by frame noninterference.',
    'Every scheduler invocation, at any site, sequential or repeated inside a CFG cycle, separately '
    'requires compatible return, exact SP and protected caller/saved words, readable descriptor '
    'representation, allocation separation, callback frame noninterference and nonretention; no earlier '
    'invocation or callback retains the descriptor, a payload or any local pointer. A site inside a CFG '
    'cycle admits only R4-R7 copies of the descriptor address besides the descriptor register, and their '
    'values after the call rest on the returning-ABI premise. No actual callee/callback effects, physical '
    'safety, allocation lifetime or termination theorem is established.',
    'Every other call is checked by the unchanged named-data buffer rules: a call that receives no local '
    'pointer uses the returning ARM ABI summary, and a call that receives one is inspected as a bounded '
    'buffer callee.',
]
PREMISES_V2 = PREMISES + [
    'An inspected buffer callee may forward a caller-frame pointer as its own callee\'s outgoing stack '
    'argument (issue #183): each recorded slot is a word of that callee\'s own frame, written by an '
    'immediate SP store in a callee whose every SP use is immediate, and the next callee is walked with '
    'it as an incoming stack argument. A released slot still holds the pointer and is tracked until '
    'written. After an owner call whose callee released one, no owner path moves SP down or hands a '
    'callee a stack pointer, and every later call is trusted under the recorded forwarded stack argument '
    'premise.',
]


def manifest(proof):
    sites = proof.scheduler_call_sites
    require(set(proof.observations) == {record['site'] for record in sites['sites']},
            'every scheduler call site must be observed')
    v2 = proof.policy == SELECTOR_V2
    record = dict(schema=SCHEMAS[proof.policy], runtime_dependencies=proof.runtime_dependencies,
        environment=proof.environment, call_sites=sites,
        observations=[proof.observations[site] for site in sorted(proof.observations)],
        assumptions=list(PREMISES_V2 if v2 else PREMISES),
        actual_callback_effects_proved=False, nonescape_proved=False, termination_proved=False,
        manager_memory_access_proved=False, caller_shape_bounds=False,
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if v2:
        record['forwarded_stack_arguments'] = forwarding(proof)
    return record
