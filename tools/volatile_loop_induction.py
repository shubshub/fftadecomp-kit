"""Relational loop induction for the allowlisted volatile check (kit#137).

volatile_semantics explores every path of the real compile and replays the
stripped and layout-perturbed compiles along it.  A loop whose exit depends on
unknown values has unboundedly many paths, so that exploration stops at its
bound (BoundExceeded) and the source is refused.  This module can turn only
that refusal into an admission, and only for a function whose every loop is
covered by an induction proof over the two compiles together (a product
program).  Anything it cannot prove keeps the refusal, with the bound's own
message first.  POLICY is the one object a maintainer would gate.

Cut points.  Each compile's control-flow graph (jump tables included) is
searched depth first from its entry; the target of every retreating edge is a
cut point, so every cycle passes through one.  The graph must be reducible:
the target of every retreating edge dominates its source, so a cut is the one
entry of its loop [irreducible control flow ...].  A path cuts a loop the first
time it reaches a cut point, and ends there the second time (the back edge).
So each path covers the entry, at most one iteration of each loop it reaches,
and whatever follows an exit; every concrete execution is covered by these
paths, iteration by iteration.

The relation at a cut, over the locations r0-r12, lr, the flags and the frame
slots the loop's strongly connected region stores at `[sp, #imm]`:
* a location the region does not write keeps its value;
* a written location that no path from the cut may read (a static liveness
  pass, counting every unknown instruction as reading everything) is
  poisoned: a value of its own compile that no address may use, so should the
  liveness be wrong a read of it still refuses;
* a live written register whose value carries sp, the object's address or a
  value loaded from the object keeps its exact value (it is never forgotten);
  such a frame slot refuses;
* every other live written location gets a fresh symbol, marked read back from
  memory.  In the stripped and permuted compiles it shares the symbol of a
  live real location that held the same value at the cut (itself when it can,
  modulo the permutation), else it gets a symbol of its own;
* memory outside the frame (and an escaped frame) gets a barrier like a call:
  a load stopped by it reads the memory of the current iteration.  If a store
  the barrier hides (one since the last call, not to the object, or one an
  earlier barrier there hid) may hold a value read from the object, the
  barrier carries the object, and so does every load it stops: such a value
  stays one through memory, as Executor.check_address and the relation's
  plainness test need.

Invariants the proof rests on (each is checked, not assumed, where marked):
I1 every cycle passes through a cut, and a cut is its loop's only entry
   (reducibility, checked);
I2 at a first arrival the relation holds: kept, unwritten and shared locations
   hold the executor's exact values, a symbol stands for any value, and two
   compiles share a symbol only where they held equal values (checked when the
   symbols are assigned);
I3 at every back edge the relation holds again (obligations 4, 5 and 7), so by
   induction the cut's state covers every later iteration of every compile;
I4 memory outside the frame is the same in every compile at a cut: each store
   to it is a trace event, compared in order (the existing rule 1), and only
   loads separate the compiles; the barrier's loads are therefore the same
   symbol in every compile for the same address;
I5 the frame below the escape is exactly what the executor holds: its only
   writes in a loop are the region's `[sp, #imm]` slots (obligation 4), it is
   never accessed at a non-constant offset before it escapes or below sp, sp
   never drops below the frame of the first call or cut, and an access is
   aligned to its width (checked at every access);
I6 a barrier never hides a pinned member's content, and it carries the object
   whenever it hides object content (obligation 7); an escape that would let a
   frame load stop at a barrier hiding object or pinned content refuses;
I7 the bound is the only refusal turned into an admission: any other
   SemanticError, and a bound met again under induction, refuses;
I8 a path runs the code after a cut once per iteration, so every per-path
   list the check compares carries the cuts: the trace (cut and back-edge
   events), the conditions (their counts), rule 3's object-load counterparts
   and the permutation check's object accesses (a "loop cut" marker in
   volatile_semantics), so equal lists mean equal counts per iteration.

Obligations, each refused with the message in brackets:
1. the flags are dead at a cut [flags are live into the loop at ...], and the
   region holds no push, pop, sp write or unknown instruction [an instruction
   the loop cut does not model];
2. the cut and every call see one frame: sp is the same word-aligned frame
   address at every cut and call [sp differs ...], and no frame store lies
   below sp at a call [a frame store below sp at a call];
3. the stripped and permuted compiles cut the same loop at the same point of
   the path: a cut and a back edge are trace events with the decision count,
   so the existing comparison of events and conditions refuses a mismatch,
   and a cut after other decisions than the real compile's refuses [loop cut
   k has no counterpart in the real compile];
4. at every back edge, in each compile: sp, the escape state and the frame base
   are those of the cut [... changes around a loop, the frame escapes inside a
   loop]; a location the region does not write is unchanged [... changes
   although the loop does not write it]; a kept register holds its value and
   its read-back state [... does not keep its value around the loop]; every
   other live written location holds no address, object value or poison [...
   holds an address ... at the back edge]; no frame store lies outside the
   region's slots [a frame store in a loop outside the slots it stores at
   [sp, #imm]] - a store of an unescaped frame at a fixed address through a
   register, outside the push area, marks that slot for the cut and the
   comparison is run again (mark_slots; the marks only grow);
5. at every back edge, each location sharing a symbol holds the value of its
   real counterpart again [back edge k: L differs from the real compile's ...];
6. poison never reaches an address [a memory access through a poisoned
   value]; it differs between the compiles, so in an event or a condition the
   existing comparison refuses it;
7. a pinned member's content (what a load of a pinned member read) is not live
   across a cut in a register or a frame slot, and no store a barrier hides
   holds it, at the cut or at the back edge [the content of a pinned member
   ...]: rule 5 (no self-assignment) compares a store with the member's value
   and would otherwise see a fresh symbol; and a back edge whose hidden stores
   may hold object content needs its cut's barrier to carry the object - if it
   does not, the cut is marked and the comparison is run again (Retaint; the
   marks only grow, so this ends, and past MAX_RERUNS reruns it refuses), and
   the compiles' barriers at the same cut of the same path are marked alike.

Records.  A cut adds a record of kind "loop" that reads and writes nothing (the
iteration's records are those of the first iteration along that path), and a
back edge adds an unconditional branch record that reads the registers live at
the cut point and writes the others and the flags, from a static liveness pass
that counts every unknown instruction as reading everything.  So the existing
classification of object loads sees each loop's first iteration exactly and
never assumes a value dies at a back edge unless it is dead at the loop head.
The cut record is also a marker in the lists of object loads the real and
stripped compiles are compared by (and in the permutation check's), so a
load cannot move across a cut (I8).

Calls are executed as before, never waived, under stricter rules in this run
(it decides functions the bound left undecided, so every gap the executor has
would otherwise become a new admission; see the shelved notes on kit#137):
* every register the callee may read beyond its prototype (its ROM interface,
  else r0-r3) is compared, as part of the call event;
* r12, lr and the flags afterwards differ between the compiles;
* a register the callee's ROM return sites jump through (`pop {rN}; bx rN`)
  holds the call's return address afterwards, named by the call's byte offset
  in its compile (kit#215), and, unless the callee writes it on every path or
  the call compares it, its value before the call too (another return site
  may leave it alone); for a callee whose return form is not known from the
  ROM every r0-r3 depends on that offset, its event and its prior value;
* a register the callee's ROM code does not write on every path keeps a value
  that includes its value before the call; so do r2 and r3 after a runtime
  helper (`__divsi3` and its kin), which is called without a ROM interface:
  in the ROM, `__divsi3`, `__udivsi3` and `__umodsi3` write neither register
  when the divisor is zero, `__umodsi3` leaves r2 alone when the dividend is
  below the divisor, and `__modsi3` leaves r2 alone when the divisor is zero
  or the dividend's magnitude is below the divisor's (its r3, written on
  every path, is kept as well); an SWI compares all of r0-r3 at the call, so
  what it leaves is the same in every compile;
* outgoing stack-argument words belong to the callee afterwards;
* any memory access through a value a call left in r12, lr or a return
  register refuses.
The frame rules are stricter as well: pushes only in the prologue, before any
memory access, call, branch or sp move; no frame access below sp, at a
non-constant offset before the frame escapes, or not aligned to its width; sp
never below the frame of the first call or cut; the saved-register slots join
each escape snapshot; r4-r11 hold their entry values at every return.

Two rules extend the run (kit#137).  Each turns only a refusal of the rules
above into an admission, so a run they would not change takes neither; each is
one switch on the policy object, and neither runs under the escaped-local model
(escaped_local_extents), whose frame they do not model.

Rule A, a loop that escapes the frame.  A back edge that finds the frame
escaped where its cut had it unescaped (obligation 4) marks the cut, alike in
every compile, and the comparison is run again (Retaint).  A marked cut escapes
the frame before anything else: a snapshot event of every frame byte but the
push area, compared between the compiles, anchored at the entry sp.  Every
iteration then runs with the frame escaped, as after any escape: frame stores
are trace events and a frame load stops at the most recent call or barrier.
The snapshot and the events keep the escaped frame the same in every compile
at every barrier (I4 for the frame), so escaping earlier only compares more.
Such a cut havocs no slot (they are escaped memory behind its barrier), and at
its back edge a traced store at a fixed frame address outside the push area is
admitted like a store to memory (for a loop entered escaped before it, too).
Kept closed: a frame address stored in the frame at the cut, or by the loop
[a frame address is stored in the frame a cut is entered with escaped; a loop
entered with the frame escaped stores a frame address], since the barrier
would hand it back as an unknown value; a store overlapping a pushed register
[a frame store in a loop outside the slots ...]; and an access at a variable
frame offset [a frame access at a non-constant offset ...] for the rest of the
path.  Once the frame has escaped this way, a call's barrier also covers its
outgoing argument words.

Rule B, join cuts.  When the loop cuts alone, or a function without a loop,
still meet a bound, paths are also merged where they join.  A join is an
instruction with two or more predecessors that is no loop cut, with dead
flags; its region is every instruction on a path from its immediate dominator
to it, the dominator included (a region holding a push, a pop, an sp move or
an unmodelled instruction has no join).  Arrivals are grouped by the decisions
made before the dominator, so every arrival of a group ran the same code up to
it.  The first arrival of a group opens the join, generalising the state as a
loop cut does over what the region may write (registers, flags, [sp, #imm]
slots), with a barrier when the region may write memory; a value a call left
in a register (a return address, or a value tied to one) is kept exactly, like
an address, since an access through it refuses; it also forgets every branch
outcome learned inside the region, which holds on its own arm only.
Every later arrival of the group ends at the join once the back-edge
obligations hold against the opened state: sp and the escape state, unwritten
locations unchanged, kept ones equal, live written ones plain, the other
compiles' shared locations equal to the real compile's at the same arrival, no
pinned content behind the barrier, object content marking it, frame stores
only to the region's slots (or, escaped, outside the push area), no frame
address behind the barrier.  An arrival whose frame has not escaped where the
opener's has escapes there (a snapshot event); if an arrival escapes where the
opener did not, the group is entered escaped and the run repeated.  Within a
run of this rule every escape is anchored at the entry sp.  The real compile
plans each cut by (decisions so far, joins cut so far) and its trace length;
the others follow the plan.  A join whose obligations fail, that the compiles
meet after different events, that another compile passes without meeting, or
whose dominator lies past the group's decisions in another compile is not cut
in any compile, and the run is repeated (monotone, so it ends; past
MAX_RERUNS + MAX_JOIN_RERUNS reruns it refuses): its paths are enumerated as
before.  Soundness is the induction's, with "iteration" read as "arrival":
each arrival's state in every compile is an instance of the opened one under
one assignment of the shared symbols, so the code after the join, explored once
from that state, covers every arrival.  A join's cut is a trace event and a
record of kind "loop", as a loop cut is (I8).  Known false refusal: a
read-modify-write window across a join (the dead load before it, the store
after it), which rule 3 reads as straight-line code.

Premise, printed in each record that relies on this: callees preserve r4-r11
and sp, and leave their return address only in the register their ROM return
sites jump through.
"""

import re
import types

import volatile_semantics as vs

NAME = "relational-loop-induction-v1"
PREMISE = ("callees preserve r4-r11 and sp, and leave their return address only in the register "
           "their ROM return sites jump through")
REGISTERS = tuple(f"r{n}" for n in range(13)) + ("lr",)
LOW = tuple(f"r{n}" for n in range(8))
ALU = ("mov", "add", "sub", "neg", "mvn", "and", "orr", "eor", "bic", "mul", "lsl", "lsr", "asr", "ror")
ALL_ARGUMENTS = frozenset(vs.ARGUMENT_REGISTERS)
MAX_RERUNS = 16           # comparisons repeated to mark barriers (Retaint)


class Loops(tuple):
    """the 1-based instructions of the real compile where loops were cut; a tagged
    record part (volatile_semantics.record finds it by its attribute)"""
    loop_induction = True

    def __new__(cls, items, joins=(), escaped=()):
        made = super().__new__(cls, items)
        made.joins, made.escaped = list(joins), list(escaped)
        return made

    def __bool__(self):
        return bool(len(self) or self.joins)

    def describe(self):
        # kit#137: the rules a verdict used beyond the loop cuts are named only when used,
        # so a record without them keeps its text
        parts = [f"loops by relational induction at instructions {list(self)}"] if len(self) or not self.joins \
            else []
        parts += [f"paths merged at instructions {self.joins}"] if self.joins else []
        parts += [f"cuts entered with the frame escaped at instructions {self.escaped}"] if self.escaped else []
        return f"{', '.join(parts)} ({NAME}, premise: {PREMISE})"


class Retaint(vs.SemanticError):
    """a loop body leaves object content behind a barrier its cut took for clean: the
    run is repeated with that cut marked (monotone, so it ends)"""


class LoopInduction:
    """The policy: rerun a function the path bound refused under the induction executor.

    Two rules extend it (kit#137), each behind one switch here and each reached only from
    a refusal of the rules before it: escaped_loops (rule A) enters a loop with the frame
    escaped when an iteration escapes it, instead of refusing; join_cuts (rule B) merges
    paths where they join when the loop cuts alone, or an acyclic function, still meet a
    bound.  Neither runs under the escaped-local model (escaped_local_extents).
    register_slots, reached only from the refusal of a frame store outside a loop's
    [sp, #imm] slots, adds the fixed frame slots a loop of an unescaped frame stores
    through a register to its cut (mark_slots)."""

    name, premise = NAME, PREMISE
    escaped_loops = True
    join_cuts = True
    register_slots = True

    def compare(self, bound, real_assembly, stripped_assembly, preprocessed, symbol, declaration,
                perturbed_assembly, interfaces):
        texts = {"real": real_assembly, "stripped": stripped_assembly,
                 "layout-perturbed": perturbed_assembly}
        mapping = vs.perturbed_declaration(declaration)[1] if perturbed_assembly is not None else {}
        contexts = {}
        retry = False
        while True:
            name = getattr(bound, "function", None)
            if not retry:
                if name is None or name in contexts:
                    raise bound
                context = Context(name, texts, symbol, mapping, self)
                if not context.has_loops():
                    if not context.join_cuts:
                        raise bound
                    # rule B: an acyclic function past the bound has only joins to merge
                    context.joining = True
                contexts[name] = context
            retry = False
            joining = any(each.joining for each in contexts.values())
            reruns = MAX_RERUNS + (MAX_JOIN_RERUNS if joining else 0)
            token = vs.LOOP_INDUCTION.set({key: value.executor for key, value in contexts.items()})
            try:
                for _ in range(reruns + 1):
                    for each in contexts.values():
                        each.reset()
                    try:
                        results = vs._compare_compiles(real_assembly, stripped_assembly, preprocessed, symbol,
                                                       declaration, perturbed_assembly, interfaces)
                    except Retaint:
                        continue
                    break
                else:
                    # the marks only grow, so this is a cost bound, never a verdict
                    raise vs.SemanticError(f"marking the loop barriers that hide object content took more "
                                           f"than {MAX_RERUNS} reruns" if not joining else
                                           f"marking the loop and join cuts took more than {reruns} reruns")
            except vs.BoundExceeded as again:
                if again.function in contexts:
                    if contexts[again.function].join_cuts and not contexts[again.function].joining:
                        # rule B: the loop cuts alone still meet a bound: merge paths at joins too
                        contexts[again.function].joining = True
                        retry = True
                        continue
                    raise vs.SemanticError(f"{bound}; relational loop induction (kit#137): {again}") from None
                bound = again
                continue
            except vs.SemanticError as error:
                raise vs.SemanticError(f"{bound}; relational loop induction (kit#137): {error}") from None
            finally:
                vs.LOOP_INDUCTION.reset(token)
            return [result + (Loops(sorted(index + 1 for index in contexts[result[0]].used),
                                    joins=sorted(index + 1 for index in contexts[result[0]].joined),
                                    escaped=sorted(index + 1 for index in contexts[result[0]].entered_escaped)),)
                    if result[0] in contexts else result for result in results]


POLICY = LoopInduction()
MAX_JOIN_RERUNS = 48      # further reruns while join cuts are given up or marked (Retaint)


# ---------------------------------------------------------------- static shape

def normal(mnemonic):
    return mnemonic[:-1] if mnemonic.endswith("s") and mnemonic[:-1] in ALU else mnemonic


def jump_targets(probe, pc):
    """the successors of agbcc's jump-table dispatch at pc, as Executor.jump_table reads them"""
    form = probe.dispatch(pc)
    pool = form[3]
    label, offset = pool if isinstance(pool, tuple) else (pool, 0)
    words = probe.pools.get(label) or []
    word = words[offset // 4] if offset % 4 == 0 and offset // 4 < len(words) else None
    if not (isinstance(word, tuple) and len(word) == 2 and word[0] == "code"):
        return []
    return sorted({probe.labels[entry[1]] for entry in probe.pools.get(word[1]) or []
                   if isinstance(entry, tuple) and len(entry) == 2 and entry[0] == "code" and
                   entry[1] in probe.labels})


def effects(probe, pc, signatures, interfaces, returns):
    """(reads, kills, flags read, flags killed, may write, successors, modelled) of one
    instruction: reads over-approximate and kills under-approximate the executor's"""
    mnemonic, operands, _ = probe.instructions[pc]
    m = normal(mnemonic)
    everything = set(REGISTERS) | {"sp"}
    following = [pc + 1]
    try:
        if m == "lsl" and probe.dispatch(pc) is not None:
            index, destination, table, _ = probe.dispatch(pc)
            return {index}, {destination, table}, False, True, {destination, table}, \
                jump_targets(probe, pc), True
        regs = [vs.register(operand) for operand in operands]
        if m in ALU:
            destination = regs[0]
            if destination == "pc" and m == "mov" and len(operands) == 2:
                return {regs[1]} | ({"r0"} if returns else set()), set(), False, False, set(), [], True
            if destination in (None, "pc") or len(operands) not in (2, 3):
                return everything, set(), True, False, set(REGISTERS), following, False
            sources = operands[1:] if len(operands) == 3 or m in ("mov", "neg", "mvn") else operands
            reads = {vs.register(o) for o in sources if vs.register(o)}
            if "pc" in reads:
                return everything, set(), True, False, set(REGISTERS), following, False
            stack = destination == "sp" or "sp" in reads
            if m == "mov":
                flags = vs.immediate(sources[0]) is not None or \
                    (destination in LOW and vs.register(sources[0]) in LOW)
            elif m in ("add", "sub"):
                high = len(operands) == 2 and vs.register(operands[1]) and \
                    (destination not in LOW or vs.register(operands[1]) not in LOW)
                flags = not stack and not high
            else:
                flags = True
            return reads, {destination}, False, flags, {destination}, following, destination != "sp"
        if m in ("cmp", "cmn", "tst"):
            return {r for r in regs if r}, set(), False, True, set(), following, True
        if m in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh"):
            subject = regs[0]
            if re.fullmatch(r"\.L\w+(?:\s*\+\s*[0-9]+)?", operands[1].strip()):
                return set(), {subject}, False, False, {subject}, following, m == "ldr"
            inner = re.fullmatch(r"\[\s*([^,\]]+?)\s*(?:,\s*([^\]]+?)\s*)?\]", operands[1].strip())
            address = {vs.register(part) for part in inner.groups() if part and vs.register(part)}
            if m.startswith("ldr"):
                return address, {subject}, False, False, {subject}, following, True
            return address | {subject}, set(), False, False, set(), following, True
        if m in ("push", "pop"):
            names = set(vs.register_list(operands[0]))
            if m == "push":
                return names | {"sp"}, {"sp"}, False, False, {"sp"}, following, False
            if "pc" in names:
                return {"sp"} | ({"r0"} if returns else set()), names - {"pc"}, False, False, \
                    names - {"pc"} | {"sp"}, [], False
            return {"sp"}, names | {"sp"}, False, False, names | {"sp"}, following, False
        if m in ("stmia", "stm", "ldmia", "ldm"):
            base, names = vs.register(operands[0].rstrip("!")), set(vs.register_list(operands[1]))
            if m.startswith("stm"):
                return {base} | names, {base}, False, False, {base}, following, True
            return {base}, {base} | names, False, False, {base} | names, following, True
        if m == "b":
            return set(), set(), False, False, set(), [probe.labels[operands[0]]], True
        if m[:1] == "b" and m[1:] in vs.INVERSE:
            return set(), set(), True, False, set(), [probe.labels[operands[0]], pc + 1], True
        if m == "bl" and pc in probe.labels.far:
            # agbcc's far jump: a branch that overwrites lr (Executor.step)
            return set(), {"lr"}, False, False, {"lr"}, [probe.labels[operands[0]]], True
        if m == "bl":
            via = re.fullmatch(r"_call_via_(r[0-9]|r1[0-2]|ip|fp|sl|sb|lr)", operands[0])
            clobbers = {"r0", "r1", "r2", "r3", "r12", "lr"}
            if via:
                return set(ALL_ARGUMENTS) | {vs.register(via[1])}, {"lr", "r12"}, False, True, \
                    clobbers, following, True
            target = operands[0]
            if target in vs.RUNTIME_ARITY:
                # a runtime helper may leave r2 and r3 alone, so it kills neither
                named = {f"r{n}" for n in range(vs.RUNTIME_ARITY[target])}
                return named, clobbers - (ALL_ARGUMENTS - named), False, True, clobbers, following, True
            arity = signatures.get(target, (None, None))[1]
            named = {f"r{n}" for n in range(min(arity, 4))} if arity is not None else set(ALL_ARGUMENTS)
            interface = interfaces(target) if interfaces is not None else None
            if interface is None:
                return named | ALL_ARGUMENTS, {"lr", "r12"}, False, True, clobbers, following, True
            reads, writes = interface
            return named | set(reads), {"lr", "r12"} | set(writes), False, True, clobbers, following, True
        if m in ("swi", "svc"):
            clobbers = {"r0", "r1", "r2", "r3", "r12", "lr"}
            return set(ALL_ARGUMENTS), clobbers, False, True, clobbers, following, True
        if m == "bx":
            return {regs[0]} | ({"r0"} if returns else set()), set(), False, False, set(), [], True
        if m == "nop":
            return set(), set(), False, False, set(), following, True
    except (vs.SemanticError, KeyError, IndexError, TypeError, AttributeError, ValueError):
        pass
    return everything, set(), True, False, set(REGISTERS), following, False


def depth_first_cuts(successors, count):
    """the retreating edges (source, target) of a depth-first search from instruction 0;
    their targets are the cut points, and every cycle passes through one"""
    edges, state, stack = set(), {0: 1}, [(0, iter(successors[0]))] if count else []
    while stack:
        node, children = stack[-1]
        child = next(children, None)
        if child is None:
            state[node] = 2
            stack.pop()
        elif state.get(child) == 1:
            edges.add((node, child))
        elif child not in state:
            state[child] = 1
            stack.append((child, iter(successors[child])))
    return edges


def dominators(successors, count):
    """{instruction reachable from 0: the instructions that dominate it}"""
    predecessors = {pc: set() for pc in range(count)}
    reachable, work = set(), [0] if count else []
    while work:
        pc = work.pop()
        if pc not in reachable:
            reachable.add(pc)
            for successor in successors[pc]:
                predecessors[successor].add(pc)
                work.append(successor)
    dominated = {pc: set(reachable) for pc in reachable}
    if count:
        dominated[0] = {0}
    changed = True
    while changed:
        changed = False
        for pc in sorted(reachable - {0}):
            new = {pc} | set.intersection(*(dominated[p] for p in predecessors[pc] if p in reachable))
            if new != dominated[pc]:
                dominated[pc], changed = new, True
    return dominated


def regions(successors, count):
    """{instruction: its strongly connected component} (iterative Tarjan)"""
    index, low, on, stack, component, counter = {}, {}, set(), [], {}, 0
    for root in range(count):
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            node, position = work.pop()
            if position == 0:
                index[node] = low[node] = counter
                counter += 1
                stack.append(node)
                on.add(node)
            children = successors[node]
            for at in range(position, len(children)):
                child = children[at]
                if child not in index:
                    work += [(node, at + 1), (child, 0)]
                    break
                if child in on:
                    low[node] = min(low[node], index[child])
            else:
                if low[node] == index[node]:
                    members = []
                    while True:
                        member = stack.pop()
                        on.discard(member)
                        members.append(member)
                        if member == node:
                            break
                    for member in members:
                        component[member] = frozenset(members)
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[node])
    return component


def byte_offsets(text, name, count):
    """{instruction index: byte offset in the function} as parse_assembly indexes the
    instructions; None unless every line is understood and the count agrees"""
    if text is None:
        return None
    offsets, offset, inside = {}, 0, False
    for raw in text.splitlines():
        line = raw.split("@", 1)[0].strip()
        if not line:
            continue
        if not inside:
            inside = line == name + ":"
            continue
        if re.match(r"\.size\s+" + re.escape(name) + r"\s*,", line):
            break
        if re.fullmatch(r"[A-Za-z_.$][\w.$]*:", line):
            continue
        if line.startswith(".word"):
            offset += 4
            continue
        if line.startswith("."):
            found = re.fullmatch(r"\.align\s+([0-9]+)(?:\s*,\s*0)?", line)
            if found is None:
                return None
            step = 1 << int(found[1])
            offset = (offset + step - 1) // step * step
            continue
        offsets[len(offsets)] = offset
        offset += 4 if line.split()[0].lower() == "bl" else 2
    return offsets if inside and len(offsets) == count else None


class Shape:
    """one compile of one function: its cut points, loop regions, liveness and byte offsets"""

    def __init__(self, function, name, label, layout, signatures, interfaces, text):
        probe = vs.Executor(name, function, signatures, label, layout, interfaces)
        self.instructions = function[0]
        count = len(function[0])
        returns = signatures.get(name, (True,))[0]
        self.effects = [effects(probe, pc, signatures, interfaces, returns) for pc in range(count)]
        successors = {pc: [s for s in self.effects[pc][5] if 0 <= s < count] for pc in range(count)}
        retreating = depth_first_cuts(successors, count)
        self.cuts = {target for _, target in retreating}
        # a retreating edge whose target does not dominate its source makes the
        # control flow irreducible: a loop entered in more than one place
        dominated = dominators(successors, count)
        self.irreducible = sorted(source for source, target in retreating if target not in dominated[source])
        self.regions = regions(successors, count)
        self.offsets = byte_offsets(text, name, count)
        # backward liveness: registers and "flags"
        live = {pc: set() for pc in range(count)}
        changed = True
        while changed:
            changed = False
            for pc in reversed(range(count)):
                reads, kills, flag_read, flag_kill = self.effects[pc][:4]
                out = set().union(*(live[s] for s in successors[pc])) if successors[pc] else set()
                new = set(reads) | (out - set(kills))
                if flag_read or ("flags" in out and not flag_kill):
                    new.add("flags")
                else:
                    new.discard("flags")
                if new != live[pc]:
                    live[pc], changed = new, True
        self.live = live
        self.successors, self.dominated, self._joins = successors, dominated, None

    @property
    def joins(self):
        """kit#137 rule B: {merge point J: (its immediate dominator, its region, what the
        region may write, whether it may write memory)}.  A merge point is a reachable
        instruction with two or more predecessors that is no loop cut and has dead flags;
        its region is every instruction on a path from its immediate dominator to J, the
        dominator included, and what the region writes is what may differ between the paths
        that meet at J.  A region holding a push, a pop, an sp move or an instruction the
        cuts do not model has no join.  Computed on first use: only rule B reads it."""
        if self._joins is None:
            successors, dominated = self.successors, self.dominated
            reachable = set(dominated)
            predecessors = {pc: set() for pc in range(len(self.instructions))}
            for pc in reachable:
                for successor in successors[pc]:
                    predecessors[successor].add(pc)
            self._joins, self._dominating = {}, {}
            for pc in sorted(reachable):
                if pc in self.cuts or len(predecessors[pc]) < 2 or "flags" in self.live[pc]:
                    continue
                strict = dominated[pc] - {pc}
                idom = next((d for d in strict if dominated[d] == strict), None)
                if idom is None:
                    continue
                forward, work = set(), [s for s in successors[idom] if s != pc]
                while work:
                    at = work.pop()
                    if at in forward or at in (idom, pc):
                        continue
                    forward.add(at)
                    work += successors[at]
                backward, work = set(), [p for p in predecessors[pc] if p != idom]
                while work:
                    at = work.pop()
                    if at in backward or at in (idom, pc):
                        continue
                    backward.add(at)
                    work += predecessors[at]
                region = frozenset((forward & backward) | {idom})
                registers, flags, slots, bad = self.written_over(region)
                if bad is not None:
                    continue
                # a barrier when the region may write memory (a loop cut there adds one too)
                memory = bool(region & self.cuts) or any(
                    normal(self.mnemonic(at)) in ("str", "strb", "strh", "stmia", "stm", "bl", "swi", "svc")
                    for at in region)
                self._joins[pc] = (idom, region, (registers, flags, slots, bad), memory)
                self._dominating.setdefault(idom, []).append(pc)
        return self._joins

    @property
    def dominating(self):
        """{immediate dominator: the merge points it dominates immediately}"""
        self.joins
        return self._dominating

    def written(self, pc):
        """(registers, flags, frame slots (imm, width), the first unmodelled instruction text)"""
        return self.written_over(self.regions.get(pc, frozenset([pc])))

    def written_over(self, nodes):
        registers, flags, slots, bad = set(), False, set(), None
        for at in sorted(nodes):
            reads, kills, _, flag_kill, may, _, modelled = self.effects[at]
            registers |= may
            m = normal(self.mnemonic(at))
            flags = flags or flag_kill or m in ALU or m in ("cmp", "cmn", "tst", "bl", "swi", "svc")
            if not modelled or "sp" in may:
                bad = at if bad is None else bad
            if m in ("str", "strb", "strh"):
                found = re.fullmatch(r"\[\s*sp\s*(?:,\s*#\s*([0-9]+)\s*)?\]", self.operands(at)[1].strip())
                if found:
                    slots.add((int(found[1] or 0), 1 if m.endswith("b") else 2 if m.endswith("h") else 4))
        return registers - {"sp", "pc", None}, flags, slots, bad

    def mnemonic(self, pc):
        return self.instructions[pc][0]

    def operands(self, pc):
        return self.instructions[pc][1]


class Context:
    """everything one induction run of one function shares between its executors"""

    def __init__(self, name, texts, symbol, mapping, policy=None):
        self.name, self.texts, self.atom, self.mapping = name, texts, ("sym", symbol), mapping
        # kit#137 rules A and B, off under the escaped-local model, whose frame they do not model
        plain = vs.FRAME_MODELS.get() is None
        self.escaped_loops = plain and bool(getattr(policy, "escaped_loops", False))
        self.join_cuts = plain and bool(getattr(policy, "join_cuts", False))
        self.register_slots = bool(getattr(policy, "register_slots", False))
        self.shapes, self.cuts, self.backs, self.used, self.returns = {}, {}, {}, set(), {}
        self.loops = None
        # cuts whose barrier is marked as hiding object content: (label, instruction)
        # for every path of a compile, and path keys for every compile at that cut
        self.tainted, self.tainted_keys = set(), set()
        # rule A: cuts entered with the frame escaped because a path through them escapes
        # it: (label, instruction) of a loop or (label, "join", group) for every path of a
        # compile, and path keys (or groups) for every compile at that cut
        self.escaping, self.escaping_keys = set(), set()
        # loop cuts whose loop stores at a fixed frame address through a register, which
        # the [sp, #imm] slots miss: (label, instruction) -> {(offset from the cut's sp,
        # width)}, found at back edges and havocked by the cut from then on
        self.slotted = {}
        # rule B, on once the loop cuts alone meet a bound: the groups (decisions before the
        # join's immediate dominator, real instruction) whose join is not cut
        self.joining, self.uncut = False, set()
        self.reset()

    def reset(self):
        """forget what one run of the comparison recorded (not what it learned)"""
        self.cuts, self.backs, self.used = {}, {}, set()
        # rule B: the real compile's opened joins by group, its plan by arrival (decisions
        # so far, joins cut so far), its states where paths end, the other compiles' opened
        # joins; the real instructions that were cut or entered escaped
        self.join_open, self.join_plan, self.join_backs, self.join_state = {}, {}, {}, {}
        self.joined, self.entered_escaped = set(), set()

    def has_loops(self):
        functions, _ = vs.parse_assembly(self.texts["real"])
        function = functions.get(self.name)
        if function is None:
            return False
        probe = vs.Executor(self.name, function, {}, "real", (None, 0, {}))
        count = len(function[0])
        successors = {}
        for pc in range(count):
            following = effects(probe, pc, {}, None, False)[5]
            successors[pc] = [s for s in following if 0 <= s < count]
        return bool(depth_first_cuts(successors, count))

    def executor(self, name, function, signatures, label, layout, interfaces=None):
        return InductionExecutor(self, name, function, signatures, label, layout, interfaces)

    def shape(self, executor):
        if executor.label not in self.shapes:
            shape = Shape((executor.instructions, executor.labels, executor.pools), executor.name,
                          executor.label, (executor.symbol, executor.size, executor.pinned),
                          executor.signatures, executor.interfaces, self.texts.get(executor.label))
            self.shapes[executor.label] = shape
        return self.shapes[executor.label]

    def same(self, label, real, other):
        if label == "layout-perturbed":
            real = vs.remap(real, self.atom, self.mapping)
        return real == other

    def return_registers(self, target, interfaces):
        """the registers a callee's ROM return sites jump through; all of r0-r3 when unknown"""
        if isinstance(target, str) and target in vs.RUNTIME_ARITY or \
                isinstance(target, tuple) and target[0] == "swi":
            return frozenset()
        found = re.fullmatch(r"func_([0-9A-F]{8})", target) if isinstance(target, str) else None
        rom = interfaces if isinstance(interfaces, vs.RomInterfaces) else \
            getattr(interfaces, "ordinary", None)
        if found is None or not isinstance(rom, vs.RomInterfaces):
            return None
        if target not in self.returns:
            self.returns[target] = popped_return_registers(rom, int(found[1], 16))
        return self.returns[target]


def popped_return_registers(rom, address):
    """the registers the return sites of the Thumb function at address jump through
    (`bx rN` after its pop), or None when a return site is of another form"""
    try:
        from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
        _, _, sites = rom.control_flow(address)
        engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        registers = set()
        for site in sites:
            offset = site - vs.ROM_BASE
            instruction = next(engine.disasm(bytes(rom.rom[offset:offset + 2]), site, count=1), None)
            if instruction is None:
                return None
            if instruction.mnemonic == "bx":
                name = instruction.op_str.strip()
                if name != "lr":
                    if name not in vs.ARGUMENT_REGISTERS:
                        return None
                    registers.add(name)
            elif instruction.mnemonic != "pop" or "pc" not in instruction.op_str:
                return None
        return frozenset(registers)
    except Exception:       # anything unmodelled fails closed
        return None


# ---------------------------------------------------------------- values

def tagged(value, tags):
    if not isinstance(value, tuple) or not value:
        return False
    if value[0] in tags:
        return True
    return any(tagged(part, tags) for part in value[1:])


def poisoned(value):
    return tagged(value, ("poison",))


def left_by_call(value):
    return tagged(value, ("garbage", "retaddr", "unknown-callee"))


class Cut(types.SimpleNamespace):
    """what a path recorded at the first arrival at a loop cut, or at the opening of a join"""


class InductionExecutor(vs.Executor):
    """the executor of an induction run: cuts loops, and models calls and the frame strictly"""

    def __init__(self, context, name, function, signatures, label, layout, interfaces=None):
        super().__init__(name, function, signatures, label, layout, interfaces)
        self.context = context
        self.shape = context.shape(self)
        self.role = "real" if label == "real" else label

    def plain(self, value):
        """holds no frame address, object address, object value or poison"""
        return not vs.carries(value, vs.SP) and not vs.contains(value, self.context.atom) and \
            not poisoned(value)

    def plain_at_join(self, value):
        """plain, and holding nothing a call left (a return address, a value tied to one, a
        register a call leaves as it found it): an access through such a value refuses
        (frame_access), so a join keeps it exactly instead of making it a shared symbol"""
        return self.plain(value) and not left_by_call(value)

    def pinned_content(self, value):
        """does value hold what a load of a pinned member read?"""
        if not isinstance(value, tuple) or not value:
            return False
        if value[0] == "load" and len(value) > 2 and \
                vs.object_offset(value[2], self.symbol, self.size) in self.pinned:
            return True
        return any(self.pinned_content(part) for part in value[1:])

    def behind(self):
        """what the stores a load stopped by a barrier placed now could have forwarded
        hold: (object content, pinned content, object or pinned content in a frame
        store an escape would hide).  A load of other memory, or of an escaped frame,
        stops at the most recent call or barrier (Executor.load), so the stores since
        then are those, plus what an earlier barrier there already hid."""
        atom = self.context.atom
        content = pinned = frame = False
        for entry in reversed(self.memory):
            if entry[0] == "call":
                if isinstance(entry[1], tuple) and entry[1][0] == "loop":
                    loop = self.loops[entry[1][1] - 1]
                    content, frame = content or loop.tainted, frame or loop.hidden_frame
                break
            if entry[0] != "store" or entry[5]:
                continue
            holds = vs.contains(entry[3], atom)
            if vs.carries(entry[2], vs.SP) and not self.escaped:
                # visible through a barrier until the frame escapes
                frame = frame or holds or self.pinned_content(entry[3])
                continue
            pinned = pinned or self.pinned_content(entry[3])
            # a store to the object forwards only to an object load, which carries the atom anyway
            content = content or (holds and not vs.contains(entry[2], atom))
        return content, pinned, frame

    def run(self, decisions, **options):
        self.arrivals, self.loops, self.body_sp, self.opened, self.calling = {}, [], None, False, False
        # kit#137: the cuts this path entered with the frame escaped (rule A), the state
        # at each join's immediate dominator, and the joins cut so far
        self.escaped_cuts, self.pre_escaped, self.marks, self.join_ordinal = set(), False, {}, 0
        return super().run(decisions, **options)

    # frame and calls ---------------------------------------------------------
    def frame_sp(self, text, what):
        sp = self.regs["sp"]
        if not vs.is_stack(sp) or vs.linear(sp)[0] % 4:
            self.fail(text, f"sp is not a word-aligned frame address at {what}")
        if self.body_sp is None:
            self.body_sp = sp
        elif sp != self.body_sp:
            self.fail(text, f"sp differs at {what} from the first call or loop cut")
        return sp

    def frame_access(self, address, text, width):
        if poisoned(address):
            self.fail(text, "a memory access through a poisoned value (relational loop induction)")
        if left_by_call(address):
            self.fail(text, "a memory access through a value a call left in a register")
        if vs.carries(address, vs.SP):
            if not vs.is_stack(address):
                if not self.variable_frame_offsets():
                    self.fail(text, "a frame access at a non-constant offset before the frame escapes")
            elif vs.is_stack(self.regs["sp"]) and \
                    vs.signed32(vs.linear(address)[0]) < vs.signed32(vs.linear(self.regs["sp"])[0]):
                self.fail(text, "a frame access below sp")
            elif vs.linear(address)[0] % width:
                # the processor aligns or rotates it; the executor's bytes would not
                self.fail(text, "a frame access not aligned to its width")

    def variable_frame_offsets(self):
        """may the frame be accessed at a variable offset?  Once it escapes, but not when a
        cut entered it escaped (rule A): such a frame is still read at fixed offsets only, so
        no read below sp or of a pushed word through a computed offset reaches a proof"""
        return self.escaped and not self.pre_escaped

    def step(self, pc, mnemonic, operands, text):
        if not self.context.joining:
            return self.instruction(pc, mnemonic, operands, text)
        for join in self.shape.dominating.get(pc, ()):
            self.marks[join] = (len(self.conditions), frozenset(self.known), len(self.memory))
        if pc in self.shape.joins and self.join(pc, text):
            return "return"
        if self.role == "real":
            return self.instruction(pc, mnemonic, operands, text)
        before = (len(self.conditions), self.join_ordinal)
        result = self.instruction(pc, mnemonic, operands, text)
        plan = self.context.join_plan.get((tuple(self.decisions[:before[0]]), before[1]))
        if plan is not None and self.join_ordinal == before[1] and \
                (len(self.conditions) > before[0] or len(self.trace) > plan[2] or result == "return"):
            # the real compile cut a join at this point of the path and this compile went past it
            self.give_up(plan[1], "another compile does not meet there")
        return result

    def instruction(self, pc, mnemonic, operands, text):
        if pc in self.shape.cuts:
            if pc in self.arrivals:
                return self.back_edge(pc, text)
            self.cut(pc, text)
        m = normal(mnemonic)
        if m == "push":
            if self.opened:
                self.fail(text, "a push outside the prologue")
        elif m in ("stmia", "stm", "ldmia", "ldm") and len(operands) == 2:
            base = vs.register(operands[0].rstrip("!"))
            if base in self.regs:
                self.frame_access(self.regs[base], text, 4)
            self.opened = True
        elif m in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh") and len(operands) == 2 and \
                operands[1].strip().startswith("["):
            address, _ = vs.Executor.memory_operand(self, operands[1], text)
            self.frame_access(address, text, 1 if m.endswith("b") else 2 if m.endswith("h") else 4)
            self.opened = True
        elif not (m in ALU and vs.register(operands[0]) != "sp" or m in ("cmp", "cmn", "tst") or
                  m == "ldr" and len(operands) == 2 and operands[1].startswith(".L")):
            # a memory access, call, branch, pop or sp move ends the prologue
            self.opened = True
        result = super().step(pc, mnemonic, operands, text)
        if result != "return" and self.body_sp is not None:
            sp = self.regs["sp"]
            if not vs.is_stack(sp) or vs.signed32(vs.linear(sp)[0]) < vs.signed32(vs.linear(self.body_sp)[0]):
                # below it lies what the calls made since left behind
                self.fail(text, "sp moves below the frame of the first call or loop cut")
        return result

    def escape(self, values, text):
        if self.context.joining and self.frame_base is None and \
                any(vs.carries(value, vs.SP) for value in values):
            # join cuts: every escape is anchored at the entry sp, so paths that escape
            # at different places observe the frame alike where they meet
            self.frame_base = 0
        if not self.escaped and not self.calling:
            # once escaped, a frame load stops at the most recent call or barrier like
            # any other; an escape through a call puts the call there
            for entry in reversed(self.memory):
                if entry[0] == "call":
                    if isinstance(entry[1], tuple) and entry[1][0] == "loop" and \
                            self.loops[entry[1][1] - 1].hidden_frame:
                        self.fail(text, "the frame escapes after a loop whose barrier hides a frame store "
                                  f"of a value read from {self.symbol}")
                    break
        before = len(self.trace)
        super().escape(values, text)
        if any(event[0] == "escape" for event in self.trace[before:]):
            self.trace.append(("saved", tuple(sorted(
                (vs.signed32(vs.linear(entry[2])[0]) - self.frame_base, entry[1], entry[3])
                for entry in self.memory if entry[0] == "store" and entry[5]))))

    def call(self, target, text, record, via=None):
        sp = self.frame_sp(text, "a call")
        bottom = vs.signed32(vs.linear(sp)[0])
        for entry in self.memory:
            if entry[0] == "store" and vs.is_stack(entry[2]) and vs.signed32(vs.linear(entry[2])[0]) < bottom:
                self.fail(text, "a frame store below sp at a call")
        before = {name: self.regs[name] for name in vs.ARGUMENT_REGISTERS}
        derived = set(self.derived)
        self.calling = True
        try:
            super().call(target, text, record, via)
        finally:
            self.calling = False
        number, event = len(self.trace) - 1, self.trace[-1]
        unnamed = tuple((name, before[name]) for name in sorted(record.guarded))
        if unnamed:
            self.trace[-1] = event + (("unnamed",) + unnamed,)
        offset = self.shape.offsets.get(record.index) if self.shape.offsets is not None else None
        site = ("site", offset) if offset is not None else ("site", self.role, record.index)
        returned = self.context.return_registers(target, self.interfaces)
        interface = getattr(record, "interface", None)
        for name in vs.ARGUMENT_REGISTERS:
            if returned is None:
                # what the callee leaves may hang on its return address
                value = ("unknown-callee", number, name, before[name], site)
            elif name in returned:
                value = ("retaddr", site)
                if (interface is None or name not in interface[1]) and name not in record.reads:
                    # another return site may leave the register alone, so the old value may stay
                    value = ("retaddr", site, ("unwritten", number, name, before[name]))
            elif (interface is None or name not in interface[1]) and name not in record.reads:
                # neither compared at the call nor known to be overwritten on every path (a
                # runtime helper's r2 and r3 are neither): the old value may stay
                value = ("unwritten", number, name, before[name])
            else:
                continue
            self.regs[name] = value
            if name in derived and value[0] != "retaddr":
                self.derived.add(name)
        for name in ("r12", "lr"):
            self.regs[name] = ("garbage", self.role, number, name)
        self.flags, self.flags_derived = ("garbage", self.role, number, "flags"), False
        if not self.escaped or self.pre_escaped or self.context.joining:
            # Executor.call stored the callee's outgoing argument words before an escape;
            # kit#137: once the frame has escaped, the call is a barrier for the whole frame,
            # its outgoing argument words included, so no store stands for them
            return
        for n in range(4, len(event[2])):
            address = vs.add(sp, 4 * (n - 4))
            self.memory.append(("store", 4, address, ("callee-argument", number, n, self.current(4, address)),
                                None, False, True))

    def finish(self, text, record):
        for n in range(4, 12):
            if self.regs[f"r{n}"] != ("entry", f"r{n}"):
                self.fail(text, f"r{n} does not hold its entry value at the return")
        return super().finish(text, record)

    # shared by loop cuts and joins -----------------------------------------
    def enter_escaped(self, where, refuse):
        """kit#137 rule A: the frame escapes here, before a cut, because some path through the
        cut's code escapes it.  The escape is a snapshot event of every frame byte but the
        push area, compared between the compiles, anchored at the entry sp; from here on
        frame stores are events and a frame load stops at the most recent call or barrier.
        A frame address already stored in the frame would then be read back as an unknown
        value, so that refuses."""
        self.escape([vs.SP], where)
        self.pre_escaped = True
        if self.stored_frame_address(self.memory):
            refuse(where, "a frame address is stored in the frame a cut is entered with escaped")

    def stored_frame_address(self, entries):
        """does a store among entries hold a frame address?  Behind a barrier of rule A or B
        a later load would read it back as an unknown value, so it refuses (or the join is
        not cut); a frame address is tracked or refused, never dropped as unknown"""
        return any(entry[0] == "store" and not entry[5] and vs.carries(entry[3], vs.SP) for entry in entries)

    def in_push_area(self, start, width):
        """do the bytes [start, start + width) overlap a pushed register's slot?"""
        return any(entry[0] == "store" and entry[5] and
                   vs.signed32(vs.linear(entry[2])[0]) < start + width and
                   start < vs.signed32(vs.linear(entry[2])[0]) + entry[1] for entry in self.memory)

    def meet_escaped(self, where):
        """a path that meets an opened join escaped while its own frame has not escaped:
        it escapes there, a snapshot event compared between the compiles"""
        self.escape([vs.SP], where)

    def generalise(self, pc, where, written, sp, real, tag, escaped_slots, refuse, plain=None):
        """the state of every path from a cut on: the written live locations become symbols,
        shared with the real compile's where they held its values; dead ones are poisoned
        and those holding an address the checks track are kept.  Returns (entry, written,
        live, poison, kept, pairs, slot addresses, symbol)"""
        registers, flags, slots = written
        base = vs.signed32(vs.linear(sp)[0])
        entry = {name: self.regs[name] for name in REGISTERS}
        entry["flags"] = self.flags
        addresses = {}
        # entered with the frame escaped, the slots are escaped memory behind the barrier
        for imm, width in sorted(slots) if not escaped_slots else ():
            key = ("slot", base + imm, width)
            addresses[key] = (vs.add(sp, imm), width)
            entry[key] = self.current(width, addresses[key][0])
        locations = registers | set(addresses) | ({"flags"} if flags else set())
        # a written location no path from the cut may read is poisoned: should
        # the static liveness be wrong, a read of it still refuses
        live = {location for location in locations - {"flags"}
                if (location in self.shape.live[pc] if isinstance(location, str)
                    else self.live_slot(pc, location, base))}
        poison = locations - live
        # a live location holding an address the checks track is never forgotten
        plain = plain or self.plain
        kept = {location for location in live if not plain(entry[location])}
        for location in kept:
            if not isinstance(location, str):
                refuse(where, f"the frame slot sp{location[1] - base:+#x} holds an address the loop "
                       "rewrites and may read")
        live -= kept
        if real is None:
            pairs = {location: location for location in live}
        else:
            # a live location shares the symbol of a live real location that held the
            # same value at the cut: itself if it can, else the first by name
            pairs = {}
            for location in sorted(live, key=repr):
                matches = [other for other in sorted(real[1], key=repr)
                           if self.context.same(self.label, real[0][other], entry[location])]
                if matches:
                    pairs[location] = location if location in matches else matches[0]

        def label(location):
            return location if isinstance(location, str) else f"slot{location[1]:+#x}/{location[2]}"

        def symbol(location):
            if location in poison:
                return ("poison", self.role, tag, label(location))
            if real is None:
                return ("havoc", tag, label(location))
            if location in pairs:
                return ("havoc", tag, label(pairs[location]))
            return ("havoc", self.role, tag, label(location))

        kept_derived = {name: name in self.derived for name in kept}
        for name in registers - kept:
            self.regs[name] = symbol(name)
            self.derived.add(name)
        if flags:
            self.flags, self.flags_derived = symbol("flags"), True
        return types.SimpleNamespace(entry=entry, written=locations, live=live, kept=kept,
                                     kept_derived=kept_derived, pairs=pairs, slots=addresses, symbol=symbol)

    def havoc_slots(self, state):
        for location in sorted(set(state.slots) - state.kept, key=repr):
            address, width = state.slots[location]
            self.memory.append(("store", width, address, state.symbol(location), None, False, True))

    def current_state(self, opened):
        current = {name: self.regs[name] for name in REGISTERS}
        current["flags"] = self.flags
        for location, (address, width) in opened.slots.items():
            current[location] = self.current(width, address)
        return current

    def check_locations(self, current, opened, where, refuse, says, plain=None):
        """the relation at a cut, again: kept locations keep their values, live written ones
        hold no address, object value or poison, unwritten ones are unchanged"""
        plain = plain or self.plain
        for location, value in current.items():
            name = location if isinstance(location, str) else \
                f"the frame slot sp{location[1] - vs.signed32(vs.linear(opened.sp)[0]):+#x}"
            if location in opened.kept:
                if value != opened.entry[location] or (location in self.derived) != opened.kept_derived[location]:
                    refuse(where, f"{name} {says['kept']}")
            elif location in opened.live:
                if not plain(value):
                    refuse(where, f"{name} holds an address, an object value or a poisoned value "
                           f"{says['live']}({vs.show(value)})")
            elif location in opened.written:
                pass                    # dead at the cut: poisoned there again
            elif value != opened.entry[location]:
                refuse(where, f"{name} {says['unwritten']}")

    def stray_frame_store(self, entries, slots, escaped, snapshot=False):
        """the first store among entries to the frame outside the [sp, #imm] slots a cut
        havocs, or None.  Entered with the frame escaped (and without the escaped-local
        model), a traced store at a fixed frame address outside the push area is escaped
        memory behind the barrier like any other store; the push area stays exact.  With
        snapshot, a path that escapes only where it meets a join, its untraced stores are in
        that escape's snapshot as well."""
        for entry in entries:
            if entry[0] != "store" or not vs.carries(entry[2], vs.SP) or entry[5]:
                continue
            if vs.is_stack(entry[2]) and (vs.signed32(vs.linear(entry[2])[0]), entry[1]) in slots:
                continue
            if escaped and self.frame is None and vs.is_stack(entry[2]) and not self.stored_frame_address([entry]) and \
                    (snapshot or entry[4] is not None or
                     isinstance(entry[3], tuple) and entry[3][0] == "callee-argument") and \
                    not self.in_push_area(vs.signed32(vs.linear(entry[2])[0]), entry[1]):
                continue
            return entry
        return None

    def mark_slots(self, pc, k, loop, slots):
        """a loop of an unescaped frame storing at a fixed frame address through a register
        (outside the push area): mark those slots for the cut and run the comparison again,
        as a hidden object store marks a barrier (the marks only grow).  A store at a
        variable frame offset, or over a pushed register, is left to refuse."""
        if loop.escaped or not self.context.register_slots:
            return
        base = vs.signed32(vs.linear(loop.sp)[0])
        found = set()
        for entry in self.memory[loop.mark:]:
            if entry[0] != "store" or not vs.carries(entry[2], vs.SP) or entry[5]:
                continue
            if not vs.is_stack(entry[2]):
                return
            start = vs.signed32(vs.linear(entry[2])[0])
            if (start, entry[1]) in slots:
                continue
            if self.in_push_area(start, entry[1]):
                return
            found.add((start - base, entry[1]))
        marks = self.context.slotted.setdefault((self.label, pc), set())
        if found and not found <= marks:
            marks |= found
            raise Retaint(f"{self.label}: loop {k} stores at a fixed frame address through a register")

    # loops -------------------------------------------------------------------
    def cut(self, pc, text):
        k = len(self.loops) + 1
        self.arrivals[pc] = k
        where = f"<loop {k} at instruction {pc + 1}>"
        if self.shape.irreducible:
            self.fail(where, "irreducible control flow (a loop entered in more than one place) at instruction "
                      f"{self.shape.irreducible[0] + 1}")
        registers, flags, slots, bad = self.shape.written(pc)
        slots = set(slots) | self.context.slotted.get((self.label, pc), set())
        if bad is not None:
            self.fail(self.instructions[bad][2], "an instruction the loop cut does not model")
        if "flags" in self.shape.live[pc]:
            self.fail(where, f"flags are live into the loop at instruction {pc + 1}")
        sp = self.frame_sp(where, "a loop cut")
        base = vs.signed32(vs.linear(sp)[0])
        # rule 5 (no self-assignment) sees a member's content only until a barrier,
        # so none may be live across the cut, in a register or in the frame
        for name in REGISTERS:
            if name in self.shape.live[pc] and self.pinned_content(self.regs[name]):
                self.fail(where, f"the content of a pinned member is live across the loop in {name}")
        for entry in self.memory:
            if entry[0] == "store" and vs.is_stack(entry[2]) and not entry[5] and \
                    self.pinned_content(entry[3]) and \
                    self.live_slot(pc, ("slot", vs.signed32(vs.linear(entry[2])[0]), entry[1]), base):
                self.fail(where, "the content of a pinned member is live across the loop in the frame")
        path = (tuple(self.decisions[:len(self.conditions)]), k)
        # rule A: a loop some iteration of which escapes the frame is entered with it escaped,
        # as a back edge (below) marks it, and alike in every compile
        escaping = (self.label, pc) in self.context.escaping or path in self.context.escaping_keys
        if self.role != "real":
            counterpart = self.context.cuts.get(path)
            if escaping and counterpart is not None and not counterpart[3]:
                self.context.escaping_keys.add(path)
                raise Retaint(f"{self.label}: loop {k} is entered with the frame escaped, the real compile's is not")
            escaping = counterpart is not None and counterpart[3]
        if escaping and not self.escaped:
            self.enter_escaped(where, self.fail)
            self.escaped_cuts.add(pc)
        content, pinned, hidden_frame = self.behind()
        if pinned:
            self.fail(where, "the content of a pinned member is in memory the loop's barrier would hide")
        tainted = content or (self.label, pc) in self.context.tainted or path in self.context.tainted_keys
        real = None
        if self.role != "real":
            real = self.context.cuts.get(path)
            if real is None:
                self.fail(where, f"loop cut {k} has no counterpart in the real compile")
            if tainted and not real[2]:
                # the compiles mark the barrier alike: mark the real compile's too and rerun
                self.context.tainted_keys.add(path)
                raise Retaint(f"{self.label}: loop {k} hides object content the real compile's does not")
            tainted = real[2]
        state = self.generalise(pc, where, (registers, flags, slots), sp, real, k, pc in self.escaped_cuts,
                                self.fail)
        if self.role == "real":
            self.context.cuts[path] = (state.entry, state.live, tainted, escaping)
            self.context.used.add(pc)
            if pc in self.escaped_cuts:
                self.context.entered_escaped.add(pc)
        # a load stopped by a barrier that may hide object content carries the object
        self.memory.append(("call", ("loop", k, self.context.atom) if tainted else ("loop", k)))
        self.havoc_slots(state)
        self.trace.append(("loop", k, len(self.conditions)))
        self.records.append(vs.Record(pc, where, "loop"))
        self.loops.append(Cut(pc=pc, entry=state.entry, written=state.written, kept=state.kept,
                              kept_derived=state.kept_derived, live=state.live, pairs=state.pairs,
                              mark=len(self.memory), escaped=self.escaped, tainted=tainted,
                              hidden_frame=hidden_frame, frame_base=self.frame_base, sp=sp, slots=state.slots))

    def live_slot(self, pc, location, base):
        """may a path from pc read the frame slot before storing it? (a frame load through
        anything but [sp, #imm], or a call, counts as reading every slot)"""
        seen, work = set(), [pc]
        while work:
            at = work.pop()
            if at in seen or at >= len(self.instructions):
                continue
            seen.add(at)
            mnemonic, operands, _ = self.instructions[at]
            m = normal(mnemonic)
            if m in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh") and \
                    not operands[1].startswith(".L"):
                found = re.fullmatch(r"\[\s*sp\s*(?:,\s*#\s*([0-9]+)\s*)?\]", operands[1].strip())
                width = 1 if m.endswith("b") else 2 if m.endswith("h") else 4
                if found is None:
                    if m.startswith("ldr"):
                        return True
                else:
                    start = base + int(found[1] or 0)
                    if start < location[1] + location[2] and location[1] < start + width:
                        if m.startswith("ldr") or (start, width) != location[1:]:
                            return True
                        continue
            elif m in ("bl", "swi", "svc", "pop", "ldmia", "ldm") or not self.shape.effects[at][6]:
                return True
            work += [s for s in self.shape.effects[at][5] if s < len(self.instructions)]
        return False

    def back_edge(self, pc, text):
        k = self.arrivals[pc]
        loop = self.loops[k - 1]
        where = f"<back edge of loop {k} at instruction {pc + 1}>"
        if self.regs["sp"] != loop.sp:
            self.fail(where, "sp changes around a loop")
        if self.escaped and not loop.escaped and self.context.escaped_loops:
            # rule A: the frame escapes inside the loop: enter the loop with it escaped and rerun
            self.context.escaping.add((self.label, pc))
            self.context.escaping_keys.add((tuple(self.decisions[:len(self.conditions)]), k))
            raise Retaint(f"{self.label}: loop {k} escapes the frame")
        if self.escaped != loop.escaped or self.frame_base != loop.frame_base:
            self.fail(where, "the frame escapes inside a loop")
        current = self.current_state(loop)
        self.check_locations(current, loop, where, self.fail, {
            "kept": "does not keep its value around the loop", "live": "at the back edge ",
            "unwritten": "changes although the loop does not write it"})
        content, pinned, _ = self.behind()
        if pinned:
            self.fail(where, "the loop leaves the content of a pinned member in memory its barrier would hide")
        if content and not loop.tainted:
            # the next iteration's barrier hides object content: mark the cut and rerun
            self.context.tainted.add((self.label, pc))
            self.context.tainted_keys.add((tuple(self.decisions[:len(self.conditions)]), k))
            raise Retaint(f"{self.label}: loop {k} leaves object content behind its barrier")
        if pc in self.escaped_cuts and self.stored_frame_address(self.memory[loop.mark:]):
            # rule A: the barrier would hand a stored frame address back as an unknown value
            self.fail(where, "a loop entered with the frame escaped stores a frame address")
        slots = {(location[1], location[2]) for location in loop.slots}
        if self.stray_frame_store(self.memory[loop.mark:], slots,
                                  loop.escaped and self.context.escaped_loops) is not None:
            self.mark_slots(pc, k, loop, slots)
            self.fail(where, "a frame store in a loop outside the slots it stores at [sp, #imm]")
        key = (tuple(self.decisions[:len(self.conditions)]), k)
        if self.role == "real":
            self.context.backs[key] = current
        else:
            real = self.context.backs.get(key)
            if real is None:
                self.fail(where, f"the back edge of loop {k} has no counterpart in the real compile")
            for location, other in sorted(loop.pairs.items(), key=repr):
                if not self.context.same(self.label, real[other], current[location]):
                    self.fail(where, f"back edge {k}: {location} differs from the real compile's {other} "
                              f"(real {vs.show(real[other])}, {self.label} {vs.show(current[location])})")
        self.trace.append(("back-edge", k, len(self.conditions)))
        live = self.shape.live[pc]
        record = vs.Record(pc, where, "branch", live & set(REGISTERS), set(REGISTERS) - live)
        record.unconditional, record.flags_written = True, True
        self.records.append(record)
        return "return"

    # joins (kit#137 rule B) --------------------------------------------------
    def join(self, pc, text):
        """a merge point the loop cuts left: within a group (the decisions made before its
        immediate dominator, so every path in it ran the same code up to there), the first
        arrival opens it and goes on from a generalised state; every later arrival ends
        there once its state is an instance of that state.  The real compile plans the
        cuts; the others follow the plan.  True when the path ends here."""
        mark = self.marks.get(pc)
        if mark is None:
            return False
        arrival = (tuple(self.decisions[:len(self.conditions)]), self.join_ordinal)
        if self.role == "real":
            group = (tuple(self.decisions[:mark[0]]), pc)
            if group in self.context.uncut:
                return False
            opened = self.context.join_open.get(group)
            action = "end" if opened is not None and opened.arrival != arrival else "open"
            self.context.join_plan[arrival] = (action, group, len(self.trace))
        else:
            plan = self.context.join_plan.get(arrival)
            if plan is None:
                return False
            action, group, events = plan
            if mark[0] > len(group[0]):
                # this compile's region must hold every decision the group's paths differ in
                self.give_up(group, "its dominator in this compile lies past the group's decisions")
            if events != len(self.trace):
                self.give_up(group, "the compiles reach it after different events")
            site = self.context.join_state.setdefault((self.label, group, "site"), pc)
            if site != pc:
                self.give_up(group, "this compile reaches its group at two instructions")
        self.join_ordinal += 1
        if action == "open":
            self.open_join(pc, group, arrival, mark)
            return False
        self.end_join(pc, group, arrival, mark)
        return True

    def give_up(self, group, why, message=None):
        """a join whose obligations fail is not cut, in any compile, and the run repeated:
        its paths are enumerated as before"""
        self.context.uncut.add(group)
        raise Retaint(f"{self.label}: join at instruction {group[1] + 1} not cut: {message or why}")

    def open_join(self, pc, group, arrival, mark):
        k = len(self.loops) + 1
        where = f"<join {self.join_ordinal} at instruction {pc + 1}>"
        _, _, (registers, flags, slots, _), memory = self.shape.joins[pc]

        def refuse(where, why):
            self.give_up(group, why)
        sp = self.regs["sp"]
        if not vs.is_stack(sp) or vs.linear(sp)[0] % 4 or self.body_sp is not None and sp != self.body_sp:
            refuse(where, "sp is not the frame of the first call or cut")
        if self.body_sp is None:
            self.body_sp = sp
        base = vs.signed32(vs.linear(sp)[0])
        real = None
        if self.role != "real":
            real = self.context.join_open.get(group)
            if real is None:
                self.fail(where, "a join with no counterpart in the real compile")
        escaping = (self.label, "join", group) in self.context.escaping or group in self.context.escaping_keys
        if real is not None:
            if escaping and not real.escaping:
                self.context.escaping_keys.add(group)
                raise Retaint(f"{self.label}: a join is entered with the frame escaped, the real compile's is not")
            escaping = real.escaping
        if escaping and not self.escaped:
            self.enter_escaped(where, refuse)
            self.escaped_cuts.add(pc)
        for name in REGISTERS:
            if name in self.shape.live[pc] and self.pinned_content(self.regs[name]):
                refuse(where, f"the content of a pinned member is live across it in {name}")
        for entry in self.memory:
            if entry[0] == "store" and vs.is_stack(entry[2]) and not entry[5] and self.pinned_content(entry[3]) and \
                    self.live_slot(pc, ("slot", vs.signed32(vs.linear(entry[2])[0]), entry[1]), base):
                refuse(where, "the content of a pinned member is live across it in the frame")
        content, pinned, hidden_frame = self.behind() if memory else (False, False, False)
        if pinned:
            refuse(where, "the content of a pinned member is in memory its barrier would hide")
        if self.escaped and self.stored_frame_address(self.memory[mark[2]:]):
            refuse(where, "its barrier would hide a stored frame address")
        if self.stray_frame_store(self.memory[mark[2]:], {(base + imm, width) for imm, width in slots},
                                  self.escaped) is not None:
            refuse(where, "a frame store outside the slots its region stores at [sp, #imm]")
        tainted = memory and (content or group in self.context.tainted_keys)
        if real is not None:
            if tainted and not real.tainted:
                self.context.tainted_keys.add(group)
                raise Retaint(f"{self.label}: a join hides object content the real compile's does not")
            tainted = real.tainted
        state = self.generalise(pc, where, (registers, flags, slots), sp,
                                None if real is None else (real.entry, real.live), ("join", repr(group)),
                                self.escaped, refuse, self.plain_at_join)
        # what the paths that meet here learned about their branches holds on one of them only
        for condition in [condition for condition in self.known if condition not in mark[1]]:
            del self.known[condition]
        if memory:
            self.memory.append(("call", ("loop", k, self.context.atom) if tainted else ("loop", k)))
        self.havoc_slots(state)
        self.trace.append(("join", self.join_ordinal, len(self.conditions)))
        self.records.append(vs.Record(pc, where, "loop"))
        cut = Cut(pc=pc, entry=state.entry, written=state.written, kept=state.kept,
                  kept_derived=state.kept_derived, live=state.live, pairs=state.pairs, mark=len(self.memory),
                  escaped=self.escaped, tainted=tainted, hidden_frame=hidden_frame, frame_base=self.frame_base,
                  sp=sp, slots=state.slots, arrival=arrival, escaping=escaping, memory=memory)
        self.loops.append(cut)
        if self.role == "real":
            self.context.join_open[group] = cut
            self.context.joined.add(pc)
            if pc in self.escaped_cuts:
                self.context.entered_escaped.add(pc)
        else:
            self.context.join_state[(self.label, group)] = cut

    def end_join(self, pc, group, arrival, mark):
        where = f"<join {self.join_ordinal} at instruction {pc + 1}>"
        opened = self.context.join_open.get(group) if self.role == "real" else \
            self.context.join_state.get((self.label, group))
        if opened is None:
            self.fail(where, "a join reached before the arrival that opens it")

        def refuse(where, why):
            self.give_up(group, why)
        if self.regs["sp"] != opened.sp:
            refuse(where, "sp differs between the paths that meet")
        if self.escaped and not opened.escaped:
            # rule A at a join: the group is entered with the frame escaped
            self.context.escaping.add((self.label, "join", group))
            self.context.escaping_keys.add(group)
            raise Retaint(f"{self.label}: a path escapes the frame before join at instruction {pc + 1}")
        met = opened.escaped and not self.escaped
        if met:
            self.meet_escaped(where)
        if self.escaped != opened.escaped or self.frame_base != opened.frame_base:
            self.fail(where, "the frame escapes on one of the paths that meet")
        current = self.current_state(opened)
        # a path whose state is no instance of the opened one does not fail: the join is
        # not cut, and its paths are enumerated
        self.check_locations(current, opened, where, refuse, {
            "kept": "holds another value than on the path that opened the join", "live": "",
            "unwritten": "differs between the paths that meet although the join's region does not write it"},
            self.plain_at_join)
        if opened.memory:
            content, pinned, _ = self.behind()
            if pinned:
                refuse(where, "a path leaves the content of a pinned member behind its barrier")
            if content and not opened.tainted:
                self.context.tainted_keys.add(group)
                raise Retaint(f"{self.label}: a path leaves object content behind the barrier of the join at "
                              f"instruction {pc + 1}")
        elif len(self.memory) != mark[2]:
            self.fail(where, "memory changes in a region that writes none")
        if opened.escaped and self.stored_frame_address(self.memory[mark[2]:]):
            refuse(where, "a path stores a frame address that its barrier would hide")
        slots = {(location[1], location[2]) for location in opened.slots}
        if self.stray_frame_store(self.memory[mark[2]:], slots, opened.escaped, met) is not None:
            refuse(where, "a frame store outside the slots its region stores at [sp, #imm]")
        if self.role == "real":
            self.context.join_backs[arrival] = current
        else:
            real = self.context.join_backs.get(arrival)
            if real is None:
                self.fail(where, "a join end with no counterpart in the real compile")
            for location, other in sorted(opened.pairs.items(), key=repr):
                if not self.context.same(self.label, real[other], current[location]):
                    refuse(where, f"{location} differs from the real compile's {other} where the paths meet "
                           f"(real {vs.show(real[other])}, {self.label} {vs.show(current[location])})")
        self.trace.append(("join-end", self.join_ordinal, len(self.conditions)))
        live = self.shape.live[pc]
        record = vs.Record(pc, where, "branch", live & set(REGISTERS), set(REGISTERS) - live)
        record.unconditional, record.flags_written = True, True
        self.records.append(record)
