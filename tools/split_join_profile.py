"""Disagreeing forward joins of a stack-argument walk, kept apart instead of refused.

The core walk keeps one merged state per instruction.  When two paths reach a
join with one register holding two different stack offsets, the stack-argument
walks refuse (`inconsistent possible pointer offsets at control-flow join`)
unless the register is dead there or a counted stack-cursor loop takes the join:
one offset cannot describe both paths, and dropping the register would turn a
frame address into an unchecked scalar.  This rule keeps both offsets exact.

It acts inside the walk, at the one point where the merged walk would refuse
the join; it is not a second run.  A walk that never reaches such a join is
unchanged.  A buffer callee's inspection is a walk too: where the inspection
refused at a join and the dead-register rule then took the call (the callee
writes its stack-address arguments before reading them), the callee is now
walked apart and inspected, so the owner's proof records a split instead of a
dead-register call.  The rule applies only:

* in a stack-argument walk of the plain or function-buffer proof
  (`BufferCallProof`, `FunctionBufferCallProof`) with ordinary joined states
  (no exact path states, no owner-switch cursor);
* in a walk without a variable stack-index policy (`buffer_proof.index_policy`,
  the default stack-index retry and the opt-in stack-index routes): that
  policy records deferred accesses per instruction and analyses the CFG on its
  own, and was never shown sound over split states, so such a walk keeps the
  join refusal;
* at a forward join (the join lies above the edge's source).  A back edge
  keeps its refusal.  A rotated loop (`b cond; body: ...; cond: ...; bne body`)
  reaches its loop-carried join by two forward edges, so it can split: its
  split states go round the loop on their keys until they converge, or until
  the budget or a frame check refuses;
* for registers whose offsets still disagree after the dead-register rules.

The incoming state goes to the key (join, ((register, offset), ...)) of its
disagreeing registers.  A state stays on a split key while one of those
registers still holds its offset, and returns to the plain key - and to the
unchanged merge there, which refuses or splits again as before - once none
does.  States are merged at a key only when they agree on every disagreeing
register, and every other field is merged by the core walk's own join
(`match.join_walk_state`), so no merge ever joins two offsets of one register:
every access, callee inspection, escape and return check of the walk runs on
each alternative with its exact offsets.  Pointer-bearing frame words are never
split on: two states that meet on one key and disagree on one refuse there,
while split states that never meet again each carry their own words exactly.  A
split register in R0-R3 that still holds a frame address at a return refuses;
R12 keeps its exemption there, as in every stack-argument walk.  A walk that
needs more than BUDGET split keys refuses (`split join budget exhausted`).  A
counted stack-cursor loop does not engage over a split state inside its
region; the join keeps its refusal there.

Every split is recorded in the buffer proof as (walk, join, register, kept
offset, split offset), bound into its fingerprint (registers numbered from r0)
and stated on one `* buffer split join:` line per walk and join; replays
recompute them.  A proof that splits nothing keeps its fingerprint and lines.
`POLICY.enabled` takes the rule off.
"""

from capstone.arm import ARM_REG_R0

SCHEMA = "stack-split-join-v1"
BUDGET = 512


class Policy:
    """The one switch that takes the rule off every stack-argument walk."""
    enabled = True


POLICY = Policy()


class Key(tuple):
    """A walk state key (join, ((register, offset), ...)) that keeps those exact offsets apart.

    A tuple, so the walk unpacks it as it unpacks every keyed state, but never a
    plain tuple: the pass-keyed cursor states test `type(key) is tuple`.
    """


class Conflict(Exception):
    """Two states at one split key still disagree on these registers (never reported)."""

    def __init__(self, conflicts):
        super().__init__(conflicts)
        self.conflicts = conflicts


class SplitJoins:
    """The split joins of one walk; records go to the walk's buffer proof."""

    def __init__(self, proof, address):
        self.proof = proof
        self.address = address
        self.keys = set()

    def follow(self, state_key, successor, outgoing):
        """The key a split state's edge reaches: its split while a split offset survives."""
        aliases = dict(outgoing[2])
        kept = tuple((register, offset) for register, offset in state_key[1] if aliases.get(register) == offset)
        return Key((successor, kept)) if kept else successor

    def applies(self, current, successor, target_key):
        return successor > current and (type(target_key) is int or isinstance(target_key, Key))

    def divert(self, states, pending, target_key, successor, previous, outgoing, conflicts, merge):
        """Send `outgoing` to the split key of its disagreeing registers and merge it there."""
        mark = dict(target_key[1]) if isinstance(target_key, Key) else {}
        for _ in range(16):
            before = dict(previous[2])
            for register in sorted(conflicts):
                self.proof.split_joins[(self.address, successor, register, before[register],
                                        conflicts[register])] = None
            mark.update(conflicts)
            key = Key((successor, tuple(sorted(mark.items()))))
            if key not in self.keys:
                self.keys.add(key)
                if len(self.keys) > BUDGET:
                    raise ValueError("split join budget exhausted")
            previous = states.get(key)
            if previous is None:
                merged = outgoing
                break
            try:
                merged = merge(previous)
                break
            except Conflict as conflict:
                conflicts = conflict.conflicts
        else:
            raise ValueError("split join budget exhausted")
        if previous != merged:
            states[key] = merged
            pending.append(key)


def merge(previous, outgoing, stack, merge_possible_aliases, dead, join):
    """The stack-argument walk's join of two states at one key; Conflict where register offsets still disagree.

    The register aliases are merged as the core join merges them (offsets dead at the join are dropped
    first); every other field goes through ``join``, the core walk's own join of the remaining fields
    (``match.join_walk_state``).
    """
    if len(previous[1]) != len(stack):
        raise ValueError("inconsistent saved stack depth at control-flow join")
    before = dict(previous[2])
    dying = {register for register, offset in outgoing[2]
             if register in before and before[register] != offset and dead(register, before[register], offset)}
    kept = tuple((register, offset) for register, offset in previous[2] if register not in dying)
    incoming = tuple((register, offset) for register, offset in outgoing[2] if register not in dying)
    offsets = dict(kept)
    conflicts = {register: offset for register, offset in incoming
                 if register in offsets and offsets[register] != offset}
    if conflicts:
        raise Conflict(conflicts)
    return join(previous, merge_possible_aliases(kept, incoming))


def records(split_joins):
    """The fingerprint form of a proof's split records: registers numbered from r0, as every record is."""
    return [[walk, join, register - ARM_REG_R0, kept, split]
            for walk, join, register, kept, split in sorted(split_joins)]


def lines(records):
    """One report line per walk and join kept apart (offsets from the walk's entry SP)."""
    grouped = {}
    for walk, join, register, kept, split in sorted(records):
        grouped.setdefault((walk, join), []).append(f"r{register - ARM_REG_R0} {kept:+d}/{split:+d}")
    return [f"* buffer split join: `{SCHEMA}` walk 0x{walk:08X} join 0x{join:08X} keeps "
            f"{', '.join(pairs)} apart (entry-SP offsets, kept/split) until those registers are rewritten; "
            f"each alternative is walked and checked on its own"
            for (walk, join), pairs in sorted(grouped.items())]
