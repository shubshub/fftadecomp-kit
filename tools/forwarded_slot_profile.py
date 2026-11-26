"""Forwarded buffer pointer slots on the default path.

An inspected callee may store a pointer into the owner's frame in its own frame: as the outgoing
stack argument of its own callee (agbcc's coordinate wrappers pass their output pointers on that
way), or as a spill of an incoming pointer it reloads.  The stack-argument buffer walk already
tracks such a word exactly (``match.BufferCallProof.forwarded_slot_step`` and
``forwarded_frame_change``): a slot is an alias keyed by its negative entry-SP offset, a reload
yields the alias, a partial access refuses, a call with live slots walks the callee with them as
its incoming stack arguments (whose own proof refuses writing them), and releasing the slot's word
with ADD SP turns it into a *released word* that is tracked until it is written: any read of it
refuses.  The opt-in `named-data-buffer-stack-index-v2` proof turned this on; this module turns it
on for the default plain and function-literal stack-argument proofs and carries released words to
the owner:

* a released word that comes back to the owner at a call's return is kept in the owner walk, at
  its owner entry-SP offset (``import_released``);
* a later call the owner walk inspects (it passes stack pointers) inherits every released word, at
  its callee entry-SP offset, so the callee's walk checks it too (``inherited``); a later call it
  does not inspect is trusted under the recorded premise ``PREMISE`` (``trust``);
* a PUSH writes every word it covers, so it ends the released words there (``push``);
* moving SP down over released words without writing them refuses (``sp_down``);
* at the owner's return the released words lie below SP and are dropped (``at_return``).

Every report with a released word states ``PREMISE``: trusted calls, interrupt handlers and the code
after the owner's return are not inspected, and none of them may read the word before writing it.

No value is taken from a frame word across a call: a live slot survives a call only because the
call is walked with it as an incoming argument whose write that walk refuses, and a released word
is never a source of any value (a read refuses); a callee that overwrites one only makes the
record conservative.
"""
import json

SCHEMA = "default-forwarded-buffer-slots-v1"
PREMISE = ("unproved runtime premise: a trusted call (a callee called without stack pointer arguments while "
           "every released word is below the caller's SP, or a summarised BIOS call; it is not inspected), "
           "including everything it calls, does not read a stack word below the trusted callee's entry SP "
           "before writing it, and neither do interrupt handlers or the code that runs after the owner "
           "returns, so no released forwarded pointer word is read")
SLOTS_FIELD = "* buffer forwarded slots: "
PREMISE_FIELD = "* buffer forwarded slot premise: "


def _match():
    import match
    return match


def released(aliases):
    """{owner entry-SP offset: key} of the released words the owner walk holds."""
    return _match().stale_words(aliases)


def inherited(aliases, depth_words):
    """The released words as the next callee's entry-SP-relative stale keys."""
    base = _match().FORWARD_STALE_BASE
    return {base + position + 4 * depth_words: aliases[key] for position, key in released(aliases).items()}


def import_released(proof, aliases, result, depth_words, site, inspected):
    """Move the released words in a call's result into the owner's terms; return the result without them.

    An inspected call hands back every released word it still holds, inherited ones included, so the
    owner's set is replaced by the returned one; a call that was not inspected returns none and the
    owner keeps its words."""
    match = _match()
    stale = match.stale_words(result)
    if inspected:
        for key in list(released(aliases).values()):
            del aliases[key]
    for position, key in stale.items():
        local = match.FORWARD_STALE_BASE + position - 4 * depth_words
        if aliases.setdefault(local, result[key]) != result[key]:
            raise ValueError("inconsistent released forwarded pointer words after a call")
        proof.forward_releases.setdefault(site, set()).add(position - 4 * depth_words)
    if not stale:
        return result
    return type(result)({key: value for key, value in result.items() if key not in stale.values()})


def trust(proof, owner, site, target):
    proof.forward_trusted_calls.add((owner, site, target))


def push(aliases, after_words, before_words):
    """A PUSH writes [entry_SP - 4*after_words, entry_SP - 4*before_words): its released words end."""
    for position, key in released(aliases).items():
        if -4 * after_words <= position < -4 * before_words:
            del aliases[key]


def sp_down(aliases):
    if released(aliases):
        raise ValueError("the owner moves SP down after a callee released a forwarded pointer word")


def at_return(aliases):
    """The owner's return: released words lie below SP and are dropped."""
    keys = set(released(aliases).values())
    return {key: value for key, value in aliases.items() if key not in keys} if keys else aliases


def observed(proof):
    """A default proof (forward_slots=True; the opt-in stack-index v2 proof and the scheduler's v2 policy
    bind their own records) that forwarded, released or trusted anything."""
    if not getattr(proof, "default_forwarding", False):
        return False
    return bool(proof.forward_slot_records or proof.forward_releases or proof.forward_trusted_calls)


def evidence(proof):
    return dict(schema=SCHEMA,
                slots=sorted(list(record) for record in proof.forward_slot_records),
                released=[[site, sorted(positions)] for site, positions in sorted(proof.forward_releases.items())],
                trusted=sorted([owner, site, target] for owner, site, target in proof.forward_trusted_calls),
                premise=PREMISE if proof.forward_releases else None,
                premise_proved=False)


def fingerprint_payload(proof):
    """Bound only when a slot was forwarded: every other fingerprint is unchanged."""
    if not observed(proof):
        return None
    return json.dumps(evidence(proof), sort_keys=True, separators=(",", ":")).encode()


def lines(proof):
    if not observed(proof):
        return []
    found = evidence(proof)
    slots = ", ".join(f"0x{callee:08X} store 0x{site:08X} word entry_SP{position:+#x} = owner entry_SP{target:+#x}"
                      for callee, site, position, target in found["slots"]) or "none"
    released_text = ", ".join(f"call 0x{site:08X}: " + " ".join(f"entry_SP{position:+#x}" for position in positions)
                              for site, positions in found["released"]) or "none"
    trusted = ", ".join(f"0x{site:08X} to 0x{target:08X}" for _, site, target in found["trusted"]) or "none"
    out = [f"{SLOTS_FIELD}`{SCHEMA}` inspected callees store owner frame pointers in their own frames, tracked "
           f"word by word: {slots}; released below the owner's SP after {released_text}; trusted calls "
           f"while released words exist: {trusted}"]
    if found["premise"] is not None:
        out.append(PREMISE_FIELD + found["premise"])
    return out
