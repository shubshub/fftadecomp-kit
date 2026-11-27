"""A walked callee's released frame address left in R2/R3 at its return (the released scratch).

The default stack-argument buffer proofs (`BufferCallProof` and `FunctionBufferCallProof`) walk a
callee whenever a tracked pointer is live at the call.  A callee that hands one of its own locals to
a further call can return with that local's address still in R2 or R3 (agbcc does not clear scratch
registers): 0x08006EC0 passes `mov r2, sp` to 0x08006C88 and returns with r2 = entry-32.  The
callee's frame is released by that return, so the value is an address below the caller's SP, where
the caller's next callee builds its frame.  The walk refused every such return ("local stack
pointer escapes through a return register"), because the caller could write through it.

The caller is a known, walked function, so this rule checks the caller instead of refusing:

1. at a return of an inspected callee's walk (the proof's `active` set is non-empty), an alias in R2
   or R3 at a negative offset from the callee's entry SP (its own frame) is recorded on the proof
   (callee, return site, register, offset) and removed from the escape check.  R0 and R1, an offset
   at or above the entry SP (a caller's frame) and every return of the owner root keep their
   refusal;
2. after any call to a callee with such a record, both walks of the caller (the core walk and the
   alias-path walk) carry each released register as a marker in their alias state, keyed outside
   the register, slot and released-word key spaces, so the existing joins carry it (released on any
   incoming path is released after the join);
3. an instruction that reads a marked register refuses, a call while R0-R3 holds a marker refuses
   (the callee may take it as an argument), and a write clears the marker (recorded with its site);
4. at a return of a walked caller a marked R2/R3 is recorded for that caller the same way, so the
   release follows the call chain until a write clears it; at the owner root's return it refuses;
5. an inspection that refused with this rule's refusal (the Refusal type), or that met this rule
   at all (recorded a release, a repeat included, or applied a marker), keeps its refusal: the
   dead-register fallback (an alias-free call when the callee overwrites the passed address
   unread) would discard the pass and drop the address, as kit #538 keeps the refusal of a callee
   that returns its own frame;
6. the markers do not depend on the walk's order: a call that marks no R2 (or R3) for its callee,
   because no release of that callee had been recorded yet, notes (callee, register), and a release
   recorded later for a noted pair refuses.  A call in the core walk of an inspected callee is not
   noted: that callee's alias-path walk visits the same call after its core walk.

Nothing is dropped: the value is tracked until a write overwrites it on every path, and every use
refuses.  No premise.  Every record and clearing site is bound into the buffer fingerprint, only
when there is one, and stated on one report line; replay recomputes them.
"""
import hashlib
import json

SCHEMA = 'thumb-released-callee-scratch-v1'
MARK_BASE = 1 << 25
RELEASED = 'released'
FIELD = '* buffer released scratch'
ESCAPE = 'local stack pointer escapes through a return register'


class Refusal(ValueError):
    """Every refusal of this rule.  The dead-register fallback (BufferCallProof.check_arguments)
    never turns one into an alias-free call, whatever its message (rule 5)."""


def _registers():
    import match
    return match.ARM_REG_R0, (match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3)


def applies(proof):
    """Only the default path's two stack-argument proofs, of the match module that defined the proof
    (match.py issues as __main__ and replays as match: call_via_target_profile.kit_match); every
    subclass keeps today's walk."""
    if proof is None:
        return False
    from call_via_target_profile import kit_match
    kit = kit_match(proof)
    return type(proof) in (kit.BufferCallProof, kit.FunctionBufferCallProof) and proof.stack_arguments is True


def mark(register):
    return MARK_BASE + register


def marked(aliases):
    """The registers that hold a released callee frame address."""
    return {key - MARK_BASE for key in aliases if type(key) is int and key >= MARK_BASE}


def callee_return(proof, address, site, aliases, *, own_frame=True):
    """Rule 1 and the return half of rule 4, at a return of the walk of `address`.

    own_frame: the core walk, whose aliases are offsets from the walked function's own entry SP.
    The alias-path walk tracks the owner's pointers (an owner pointer legitimately returned in R2
    stays an alias), so it passes own_frame=False and only its markers are handed on."""
    held = marked(aliases)
    if not applies(proof) or not proof.active:
        return aliases
    r0, scratch = _registers()
    kept = dict(aliases)
    for register in scratch if own_frame else ():
        offset = kept.get(register)
        if type(offset) is int and offset < 0:
            _record(proof, (address, site, register - r0, offset))
            del kept[register]
    for register in held:
        if register not in scratch:
            raise Refusal(f"released callee frame address in r{register - r0} reaches a return")
        _record(proof, (address, site, register - r0, None))
        del kept[mark(register)]
    return kept


def _record(proof, row):
    """Record a release; rule 6 refuses one that an earlier call of the same callee went without.
    The row is recorded first, so the refusal also keeps the dead-register fallback away (rule 5)."""
    proof.released_scratch.add(row)
    proof.released_events += 1
    if (row[0], row[2]) in proof.released_unmarked:
        raise Refusal(f"released callee frame address in r{row[2]}: an earlier call to 0x{row[0]:08X} "
                         "took no marker")


def events(proof):
    """How often the proof has met this rule: each release recorded (a repeated row too) and each
    call that applied a marker.  The count is never rolled back."""
    return proof.released_events


def keeps_refusal(proof, before, error):
    """Rule 5: whether a refused inspection keeps its refusal rather than become the dead-register
    fallback's alias-free call (BufferCallProof.check_arguments).  It does when the refusal is this
    rule's (a Refusal anywhere in its cause chain), or when the pass met this rule at all since
    `events` was `before`: discarding the pass would drop a released address the walk has seen, as
    kit #538 keeps the refusal of a callee that returns its own frame."""
    seen = set()
    while error is not None and id(error) not in seen:
        if isinstance(error, Refusal):
            return True
        seen.add(id(error))
        error = error.__cause__ or error.__context__
    return proof.released_events != before


def released(proof, callee):
    """The registers a callee hands back released (rule 2)."""
    if not applies(proof):
        return ()
    r0, _ = _registers()
    return sorted({r0 + register for function, _, register, _ in proof.released_scratch if function == callee})


def after_call(proof, callee, aliases, *, core=False):
    """Rule 2 after a call to `callee`, and rule 6's ledger: each of R2/R3 the call does not mark is
    noted as (callee, register) in `proof.released_unmarked`.  `core`: the call is in a core walk;
    one inside an inspected callee (proof.active) is exempt, because that callee's alias-path walk
    makes the same call again after it, and marks or notes it then."""
    registers = released(proof, callee)
    for register in registers:
        aliases[mark(register)] = RELEASED
    if registers:
        proof.released_events += 1
    if applies(proof) and not (core and proof.active):
        r0, scratch = _registers()
        proof.released_unmarked.update((callee, register - r0) for register in scratch if register not in registers)


def step(proof, address, site, instruction, aliases, calling):
    """Rule 3 for one instruction of either walk; returns nothing, updates `aliases`."""
    held = marked(aliases)
    if not held:
        return
    import match
    read, written = instruction.regs_access()
    for register in held:
        if register in read:
            raise Refusal(f"released callee frame address in r{register - match.ARM_REG_R0} is read")
    if calling and any(register - match.ARM_REG_R0 < 4 for register in held):
        raise Refusal("released callee frame address reaches a call in R0-R3")
    for register in held & set(written):
        del aliases[mark(register)]
        proof.released_kills.add((address, site, register - match.ARM_REG_R0))


def records(proof):
    return dict(released=[list(row) for row in sorted(proof.released_scratch, key=_key)],
                cleared=[list(row) for row in sorted(proof.released_kills)])


def _key(row):
    return row[0], row[1], row[2], -1 << 40 if row[3] is None else row[3]


def digest(proof):
    if not proof.released_scratch:
        return None
    return json.dumps([SCHEMA, records(proof)], sort_keys=True, separators=(',', ':'))


def lines(proof):
    if not proof.released_scratch:
        return []
    released_rows = ', '.join(
        f"0x{callee:08X} return 0x{site:08X} r{register} " + ("from its callee" if offset is None else f"sp{offset:+d}")
        for callee, site, register, offset in sorted(proof.released_scratch, key=_key))
    cleared = ', '.join(f"0x{function:08X} at 0x{site:08X} r{register}"
                        for function, site, register in sorted(proof.released_kills)) or 'none'
    return [f"{FIELD}: `{SCHEMA}` released {released_rows}; cleared {cleared}"]


def fingerprint_part(proof):
    text = digest(proof)
    return None if text is None else hashlib.sha256(text.encode()).hexdigest()
