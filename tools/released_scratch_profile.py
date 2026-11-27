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
   (the callee may take it as an argument) unless rule 7 proves the callee overwrites it unread, and
   a write clears the marker (recorded with its site);
4. at a return of a walked caller a marked R2/R3 is recorded for that caller the same way, so the
   release follows the call chain until a write clears it; at the owner root's return it refuses;
5. an inspection that refused with this rule's refusal (the Refusal type), or that met this rule
   at all (recorded a release, a repeat included, or applied a marker), keeps its refusal: the
   dead-register fallback (an alias-free call when the callee overwrites the passed address
   unread) would discard the pass and drop the address, as kit #538 keeps the refusal of a callee
   that returns its own frame;
6. a call that marks no R2 (or R3) for its callee, because no release of that callee had been
   recorded yet, notes (callee, register), and a release recorded later for a noted pair refuses,
   so the walk's order does not decide a marker for any callee the walk can name: a direct callee,
   a resolved call-via target, or the target an unresolved call-via call names by its exact
   call-target fact or strict value (call_key): an indexed Thumb ROM entry (a wait-state mirror
   folded) or a routine of the boot IWRAM image (an IWRAM mirror folded,
   iwram_image_profile.name), the only code a release can be recorded for.  Every key is folded
   the same way (`callee_key`).  A call-via target nobody can name, such as a callback loaded
   from memory, is under the ordinary trust in an unwalked indirect call.  A call in the core
   walk of an inspected callee is not noted: that callee's alias-path walk visits the same call
   after its core walk;
7. a call while R0-R3 holds a marker is admitted only when dead_register's version-1 entry walk
   proves that its direct callee writes that register before any read, call, return or other
   transfer on every path (a call counts as a read; no callee is followed); the marker then ends at
   the call, and the proof is recorded (callee, its body's SHA-256, every killing write).

On the walked paths nothing is dropped: a release the walk records is tracked until a write
overwrites it on every path, and every use refuses; the rule adds no premise.  Its reach is the
walk's: a released address forwarded by a callee the walk does not walk (a wrapper reached by an
unresolved call, in ROM or in the image, or the image's ROM source run in place), or left by a
target the walk cannot name, rests on the ordinary trust in unwalked calls, the buffer walk's
standing premise for untracked pointers.  Every record and clearing site is bound into the buffer
fingerprint, only when there is one, and stated on one report line; replay recomputes them.
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


def callee_key(address):
    """The address a release is keyed by: a ROM wait-state mirror or an IWRAM mirror folded (rule 6)."""
    import rom_mirror
    import iwram_image_profile as iwram_image
    return rom_mirror.canonical(iwram_image.canonical(address))


def _record(proof, row):
    """Record a release; rule 6 refuses one that an earlier call of the same callee went without.
    The row is recorded first, so the refusal also keeps the dead-register fallback away (rule 5)."""
    row = (callee_key(row[0]),) + tuple(row[1:])
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
    callee = callee_key(callee)
    return sorted({r0 + register for function, _, register, _ in proof.released_scratch if function == callee})


def call_key(proof, callee, constants, site):
    """The function a call's release is keyed by (rules 2 and 6): `callee`, or, for a call through a
    call-via thunk the walk did not resolve (nothing was passed), the target it can name without
    resolving it: the exact call-target fact in the thunk's register, else the strict value there
    (call_via_target_profile.strict_known), when call_via_target_profile.entry accepts it as an
    indexed Thumb entry or iwram_image_profile.name as a routine of the boot IWRAM image (each folds
    its mirrors).  Those are the targets call_via_target_profile.resolve can answer, from the same
    value.  Nothing is resolved or recorded (resolve and the image resolver write their records), so
    a walk is unchanged by asking.  A target nobody can name, such as a callback loaded from memory,
    stays the thunk: that call keeps the ordinary trust in an unwalked indirect call."""
    import match
    import call_via_target_profile as call_via
    import iwram_image_profile as iwram_image
    if not applies(proof):
        return callee
    name = next((name for name, address in match.RUNTIME_HELPERS.items() if address == callee), "")
    if not name.startswith("_call_via_r") or not name[len("_call_via_r"):].isdigit():
        return callee
    number = int(name[len("_call_via_r"):])
    value = constants.get(match.ARM_REG_R0 + number)
    if not isinstance(value, call_via.CallTarget):
        span = call_via.function_of(proof, site)
        value = call_via.strict_known(proof, span, site).get(number) if span is not None else None
    target = call_via.entry(proof, value) if value is not None else None
    if target is None and value is not None:
        target = iwram_image.name(proof, value)
    return target if target is not None else callee


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
        proof.released_unmarked.update((callee_key(callee), register - r0) for register in scratch if register not in registers)


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
    passed = {register for register in held if register - match.ARM_REG_R0 < 4}
    if calling and passed:
        entry = killing_callee(proof, instruction, passed)
        if entry is None:
            raise Refusal("released callee frame address reaches a call in R0-R3")
        for register in passed:                   # rule 7: the callee overwrites it unread
            del aliases[mark(register)]
        proof.released_calls[(address, site, entry["address"], tuple(entry["registers"]))] = entry
    for register in held & set(written):
        del aliases[mark(register)]
        proof.released_kills.add((address, site, register - match.ARM_REG_R0))


def killing_callee(proof, instruction, registers):
    """Rule 7: the proof that the direct callee of `instruction` writes each of `registers` before any
    read, call, return or other transfer on every path from its entry (dead_register's version-1
    entry walk: a call while a value is live refuses, no callee is followed), as a record; None when
    there is none (the call is no direct BL of a mapped callee, or the walk refuses)."""
    import dead_register
    import match
    operands = instruction.operands
    if instruction.mnemonic != 'bl' or instruction.size != 4 or len(operands) != 1 or \
            operands[0].type != match.ARM_OP_IMM or operands[0].imm in match.RUNTIME_HELPERS.values():
        return None
    callee = operands[0].imm
    try:
        data = proof.span(callee)
        result = dead_register.prove(callee, frozenset(registers), dead_register.thumb_step(callee, data),
                                     end='dead register reaches the end of its callee',
                                     cycle='dead register callee has a path without its killing write',
                                     budget='dead register callee state budget exceeded')
    except ValueError:
        return None
    r0, _ = _registers()
    return dict(address=callee, end=callee + len(data), body_sha256=dead_register.sha(data),
                registers=sorted(register - r0 for register in registers), states=result.states,
                kills=sorted([site, register - r0] for site, register in result.kills))


def records(proof):
    found = dict(released=[list(row) for row in sorted(proof.released_scratch, key=_key)],
                 cleared=[list(row) for row in sorted(proof.released_kills)])
    if proof.released_calls:
        # Only a walk that relied on rule 7 adds this; every other record is unchanged.
        found['killed_by_calls'] = [[function, site, entry] for (function, site, _, _), entry
                                    in sorted(proof.released_calls.items())]
    return found


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
    calls = ''.join(
        f"; call 0x{site:08X} in 0x{function:08X} to 0x{entry['address']:08X} passes "
        f"{' '.join(f'r{register}' for register in entry['registers'])}, which the callee writes before any "
        f"read, call or return on every path ({entry['states']} states; "
        f"{' '.join(f'r{register}@0x{at:08X}' for at, register in entry['kills'])}; "
        f"body {entry['body_sha256'][:16]})"
        for (function, site, _, _), entry in sorted(proof.released_calls.items()))
    return [f"{FIELD}: `{SCHEMA}` released {released_rows}; cleared {cleared}{calls}"]


def fingerprint_part(proof):
    text = digest(proof)
    return None if text is None else hashlib.sha256(text.encode()).hexdigest()
