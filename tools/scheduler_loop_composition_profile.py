"""Sequential scheduler compositions with live-alias calls and counted loops.

Explicit opt-in selector. It composes three existing contracts and adds one
new proof obligation:

* the three-per-path phase rule (at most four scheduler sites, at most three
  scheduler invocations on any path outside loops, ordinary calls after a
  scheduler return admitted under the per-call returning ABI premise);
* the live private-local alias rule for ordinary calls, applied exactly as in
  scheduler_live_alias_profile (preserved-register walk, passed-alias replay);
* the unchanged 28-byte scheduler descriptor contract at every scheduler call;
  a scheduler site inside a loop additionally admits no local alias other
  than the R2 descriptor, not even one in a preserved register, because the
  scheduler and its callback are never walked and the call repeats;
* new: CFG cycles, admitted only as narrowed counted loops (below). A CFG
  without cycles is admitted too; the three-per-path selector itself still
  refuses every cycle and every live alias.

A loop is admitted only in this exact shape:

* its strongly connected component has one entry node (the header), entered
  from outside the component only there; the only edge from inside the
  component into the header is the back edge; removing the back edge leaves
  the component acyclic, so every cycle passes through the back edge;
* the back edge is the taken arm of a conditional branch (the latch) at the
  end of a straight tail in which each instruction is the sole predecessor
  of the next, so no path reaches the latch without executing every tail
  instruction:

      adds  rT, rC, #1
      lsls  rT, rT, #S       S = 32 - W, W in {8, 16}
      lsrs  rC, rT, #S
      ( ldrb|ldrh rL, [..]   zero-extending load, value <= 2**V - 1, V <= W
        cmp   rC, rL
        bcc   header )       back edge iff rC < rL (unsigned)
    | ( cmp   rC, #imm
        bcc   header )       imm <= 2**W - 1
    | ( cmp   rC, #imm
        bls   header )       imm <= 2**W - 2

* rC is R4-R7, distinct from rT and rL, and no instruction of the component
  other than the tail's lsrs writes it.

Rank argument. Let c be rC after the tail's lsrs; c is in [0, 2**W - 1].
In every accepted form, taking the back edge implies c <= 2**W - 2. Between
two consecutive latch tests rC changes only at the tail, so the next value
is (c + 1) mod 2**W = c + 1 (no wrap). The counter therefore strictly
increases across back edges and every back edge has c <= 2**W - 2, so the
back edge is taken at most 2**W - 1 times per loop entry and the header is
entered at most 2**W times. This holds for any incoming counter value: the
first tail narrows it. The argument depends on R4-R7 surviving every call,
which is the existing returning ARM ABI premise; it proves neither
termination of a callee nor any memory property.

Scheduler invocations. Every component other than a counted loop is a
single instruction, and the condensation of the CFG is a DAG, so a
component is entered at most once per execution and a scheduler site
outside a loop runs at most once per path. Those are bounded by the
unchanged three-per-path budget. A loop with k scheduler sites contributes
at most k * 2**W invocations per execution; that bound is recorded per loop.
"""
import hashlib
from pathlib import Path

import match
from scheduler_branch_profile import SCHEDULER

MAX_SCHEDULER_SITES = 4
MAX_ACYCLIC_PER_PATH = 3
MAX_LOOPS = 2
MAX_ORDINARY_TARGETS = 24
MAX_CALL_SITES = 32
# The same complete-owner instruction bound as scheduler_counted_loop_profile.layout.
MAX_INSTRUCTIONS = 256


def require(condition, message):
    if not condition:
        raise ValueError(message)


def components(edges):
    """Tarjan strongly connected components, iterative; returns site -> component id."""
    index, low, stack, on_stack, component = {}, {}, [], set(), {}
    counter = [0]
    for root in sorted(edges):
        if root in index:
            continue
        work = [(root, iter(edges[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on_stack.add(root)
        while work:
            site, successors = work[-1]
            advanced = False
            for target in successors:
                require(target in edges, 'scheduler loop CFG edge leaves the complete owner')
                if target not in index:
                    index[target] = low[target] = counter[0]
                    counter[0] += 1
                    stack.append(target)
                    on_stack.add(target)
                    work.append((target, iter(edges[target])))
                    advanced = True
                    break
                if target in on_stack:
                    low[site] = min(low[site], index[target])
            if advanced:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[site])
            if low[site] == index[site]:
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component[member] = site
                    if member == site:
                        break
    return component


def topological(nodes, successors):
    incoming = dict.fromkeys(nodes, 0)
    for node in nodes:
        for target in successors[node]:
            incoming[target] += 1
    pending = sorted((n for n, count in incoming.items() if not count), reverse=True)
    order = []
    while pending:
        node = pending.pop()
        order.append(node)
        for target in sorted(successors[node], reverse=True):
            incoming[target] -= 1
            if incoming[target] == 0:
                pending.append(target)
    require(len(order) == len(nodes), 'scheduler loop component contains a further cycle')
    return order


def loop(instructions, edges, predecessors, members, address):
    """Authenticate one nontrivial component as a narrowed counted loop."""
    def raw(site):
        require(site in instructions and instructions[site].size == 2 and
                len(instructions[site].bytes) == 2,
                'counted loop control must be exact Thumb16')
        return int.from_bytes(instructions[site].bytes, 'little')

    back = [(s, t) for s in members for t in edges[s] if t in members and t < s and
            instructions[s].size == 2 and raw(s) & 0xF000 == 0xD000]
    require(len(back) == 1, 'counted loop requires exactly one conditional backward edge')
    latch, header = back[0]
    # The owner entry is entered from outside every component.
    entries = {s for s in members if s == address or any(p not in members for p in predecessors[s])}
    require(entries == {header}, 'counted loop has an entry other than its header')
    require({p for p in predecessors[header] if p in members} == {latch},
            'counted loop header has a second internal predecessor')
    inner = {s: tuple(t for t in edges[s] if t in members and (s, t) != (latch, header))
             for s in members}
    topological(sorted(members), inner)

    condition = raw(latch)
    require(condition & 0xFF00 in (0xD300, 0xD900) and edges[latch] and
            set(edges[latch]) == {header, latch + 2} and header != latch + 2,
            'counted loop latch must be an unsigned lower or lower-or-same branch')
    compare = raw(latch - 2)
    if compare & 0xF800 == 0x2800:
        counter, bound = (compare >> 8) & 7, compare & 0xFF
        tail = [latch - 8, latch - 6, latch - 4, latch - 2, latch]
        limit = None
    else:
        require(compare & 0xFFC0 == 0x4280 and condition & 0xFF00 == 0xD300,
                'counted loop latch must compare the counter with a fresh zero-extended limit')
        counter, limit = compare & 7, (compare >> 3) & 7
        tail = [latch - 10, latch - 8, latch - 6, latch - 4, latch - 2, latch]
    for previous, current in zip(tail, tail[1:]):
        require(previous in members and current in members and
                edges[previous] == (current,) and predecessors[current] == {previous},
                'counted loop tail has an alternate entry or exit')
    add, left, right = raw(tail[0]), raw(tail[1]), raw(tail[2])
    require(add & 0xFFC0 == 0x1C40, 'counted loop successor must add exactly one')
    temporary = add & 7
    require((add >> 3) & 7 == counter and temporary != counter and 4 <= counter <= 7,
            'counted loop increments a different or caller-clobbered counter')
    shift = (left >> 6) & 31
    require(left & 0xF800 == 0 and shift in (16, 24) and
            (left >> 3) & 7 == temporary and left & 7 == temporary and
            right & 0xF800 == 0x0800 and (right >> 6) & 31 == shift and
            (right >> 3) & 7 == temporary and right & 7 == counter,
            'counted loop successor lacks an exact u8 or u16 narrowing into its counter')
    width = 32 - shift
    if limit is None:
        maximum = bound if condition & 0xFF00 == 0xD300 else bound + 1
        require(maximum <= (1 << width) - 1,
                'counted loop immediate bound admits counter wrap')
    else:
        load = raw(tail[3])
        loaded = 8 if load & 0xF800 == 0x7800 or load & 0xFE00 == 0x5C00 else \
            16 if load & 0xF800 == 0x8800 or load & 0xFE00 == 0x5A00 else None
        require(loaded is not None and load & 7 == limit and limit != counter,
                'counted loop limit must be a fresh zero-extended byte or halfword load')
        require(loaded <= width, 'counted loop limit is wider than its counter')
        maximum = (1 << loaded) - 1
    writers = [s for s in members if s != tail[2] and
               match.ARM_REG_R0 + counter in instructions[s].regs_access()[1]]
    require(not writers, 'counted loop component writes its counter outside the tail')
    return dict(header=header, latch=latch, tail=tail, exit=latch + 2,
        members=sorted(members), counter_register=counter, counter_bits=width,
        limit_register=limit, limit_maximum=maximum,
        maximum_back_edges=(1 << width) - 1, maximum_header_entries=1 << width,
        rank='2**W - 1 - counter at each latch test; back edge implies counter <= 2**W - 2')


def phases(instructions, edges, calls, address):
    require(0 < len(instructions) <= MAX_INSTRUCTIONS and set(calls) <= set(edges) and
            set(instructions) == set(edges) and address in edges,
            'scheduler loop composition requires a complete bounded instruction graph')
    schedulers = sorted(s for s, t in calls.items() if t == SCHEDULER)
    ordinary = sorted(set(calls.values()) - {SCHEDULER})
    require(1 <= len(schedulers) <= MAX_SCHEDULER_SITES and
            1 <= len(ordinary) <= MAX_ORDINARY_TARGETS and len(calls) <= MAX_CALL_SITES,
            'scheduler loop composition exceeds the explicit call-site or target bounds')
    component = components(edges)
    predecessors = {s: set() for s in edges}
    for s, targets in edges.items():
        for t in targets:
            predecessors[t].add(s)
    groups = {}
    for site, root in component.items():
        groups.setdefault(root, set()).add(site)
    loops = {}
    for root, members in groups.items():
        if len(members) > 1 or root in edges[root]:
            loops[root] = loop(instructions, edges, predecessors, members, address)
    require(len(loops) <= MAX_LOOPS, 'scheduler loop composition exceeds its loop budget')
    condensed = {root: set() for root in groups}
    for s, targets in edges.items():
        for t in targets:
            if component[s] != component[t]:
                condensed[component[s]].add(component[t])
    after = dict.fromkeys(groups, 0)
    looped = dict.fromkeys(groups, False)
    maximum, following = 0, []
    for root in topological(sorted(groups), condensed):
        members = groups[root]
        sites = [s for s in members if calls.get(s) == SCHEDULER]
        if root in loops:
            loops[root]['scheduler_sites'] = sorted(sites)
            loops[root]['maximum_scheduler_calls'] = len(sites) * loops[root]['maximum_header_entries']
        # An ordinary call follows a scheduler return if one completed on an
        # earlier component or, inside a loop, in any iteration.
        prior = after[root] > 0 or looped[root] or (root in loops and sites)
        following += [s for s in members if s in calls and calls[s] != SCHEDULER and prior]
        scheduled = after[root] + (0 if root in loops else len(sites))
        require(scheduled <= MAX_ACYCLIC_PER_PATH,
                'scheduler invocations outside counted loops exceed the explicit per-path bound')
        maximum = max(maximum, scheduled)
        for target in condensed[root]:
            after[target] = max(after[target], scheduled)
            looped[target] = looped[target] or looped[root] or bool(root in loops and sites)
    looped_sites = sorted(s for item in loops.values() for s in item['scheduler_sites'])
    require(set(looped_sites) | {s for s in schedulers if component[s] not in loops} == set(schedulers),
            'scheduler loop composition lost a scheduler site')
    return dict(scheduler_sites=schedulers, ordinary_targets=ordinary,
        scheduler_site_budget=MAX_SCHEDULER_SITES, call_site_budget=MAX_CALL_SITES,
        ordinary_target_budget=MAX_ORDINARY_TARGETS,
        scheduler_calls_per_path_budget=MAX_ACYCLIC_PER_PATH,
        maximum_scheduler_calls_per_path_outside_loops=maximum,
        looped_scheduler_sites=looped_sites,
        counted_loops=[loops[r] for r in sorted(loops, key=lambda r: loops[r]['header'])],
        ordinary_calls_after_scheduler=bool(following),
        following_ordinary_sites=sorted(following),
        loop_budget=MAX_LOOPS, actual_count_or_capacity_proved=False,
        unconditional_termination_proved=False)


def bind(proof, instructions, edges, calls, address):
    result = phases(instructions, edges, calls, address)
    for target in result['ordinary_targets']:
        require(not match.function_thunk.reserved(target) and
                target not in match.RUNTIME_HELPERS.values(),
                'scheduler loop composition requires ordinary indexed Thumb call targets')
        body = proof.span(target)
        proof.dependencies[target] = body
        proof.records[target] = dict(address=target, end=target+len(body), bytes=len(body),
            body_sha256=hashlib.sha256(body).hexdigest(), **proof.identities,
            structure=dict(kind='complete-indexed-body-conditional-ordinary-call',
                callee_effects_proved=False, nested_execution_proved=False))
    result.update(source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        ordinary_call_contract=(
            'Each ordinary indexed call uses the existing returning ARM ABI summary: '
            'compatible registers, exact SP and protected caller/saved words preserved. '
            'No tracked local-register alias, pointer word or word-provenance fact may '
            'enter it. Complete body identity does not prove purity, memory effects, '
            'nested execution, readability, allocation separation or termination.'),
        loop_contract=(
            'Every cycle is a single-entry counted loop with one back edge behind an exact '
            'narrowed +1 counter tail and an unsigned bound no larger than the counter range. '
            'The loop iteration bound depends on the counter register (R4-R7) surviving every '
            'call by the returning ARM ABI premise. Every iteration re-establishes each '
            'per-invocation scheduler and ordinary-call premise; the descriptor is consumed only '
            'during each scheduler invocation, and no earlier invocation retains a local '
            'pointer. The frame and alias replay covers every iteration.'),
        ordinary_callee_effects_proved=False, nested_execution_proved=False)
    return result
