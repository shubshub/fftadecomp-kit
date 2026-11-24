"""Variable private-stack-array indices on the default Thumb path, retried after the plain walk refuses.

The default buffer walks (`match.BufferCallProof` with stack arguments: the plain path, the plain
and function-literal data-buffer proofs and the function-buffer proof) represent only exact stack
offsets. A frame address plus a runtime index (`adds Rd, Ralias, Ridx`, `add Rd, sp, Rd` with an
unknown Rd, `ldr Rt, [Ralias, Ridx]`) is refused at its first use:

    unsupported stack-alias use or escape
    unsupported stack-address materialization
    stack-alias index is not a known constant

Those are the only triggers. After such a refusal, and only then, the same walk is run once more
with `stack_index_precondition_profile.Policy` attached (`buffer_proof.index_policy`), as the opt-in
`named-data-buffer-stack-index-v2` route attaches it: the core defers each variable derivation and
access, and the analysis re-decodes the verified body, owns every value derived from a frame
address from the deferral on, and proves each deferred access. Nothing is dropped: an access the
analysis cannot prove refuses, and so does any other use of a ranged address (stored, pushed,
compared, used as an index, passed in R0-R3, R12 or a stack-argument word, returned, or used as a
branch target). Every walk that does not refuse at a trigger is the walk it was before, so no
verdict the default path reaches today changes.

The analysis runs with v2 semantics (sign-extended index congruence, no forwarded stack
arguments), with the #350 callee watch (`callee_saved_watch`) on the retried proof, as the opt-in
route has it, and three differences from the opt-in route:

1. **R4-R11 at calls.** Callee-saved obliges a callee to restore those registers, not to leave their
   values unread. A ranged address live in R4-R11 at a call is admitted only through the watch,
   which walks what the call executes; its premise lines print in the report. A policy without the
   watch refuses it at the call (`carry_callee_saved = False`); the opt-in route carries it.
2. **Premise rows bound loads only.** An access the in-function value ranges do not prove in bounds
   is admitted only under a premise row (`index expression < K whenever the site executes`), and
   only when `config/stack_index_premises.json` holds a reviewed entry for the function that repeats
   every row exactly (`stack_index_precondition_profile.accept`); a missing or differing entry
   refuses and prints the rows to review. A **store** that needs a premise is refused: out-of-range
   writes reach saved registers and the saved LR.
3. **Copy-helper initialisation.** A summarised call to the pinned copy helper 0x081443FC
   (`copy_helper_summary_profile`, which proves its write set `[dst, dst+n)` exactly) with a local
   destination and a non-local source marks those bytes initialised at its site for the analysis's
   load check. A local-to-local copy initialises nothing: its source may be stale.

A walk the retry admits records, in the buffer proof's fingerprint and report lines: the trigger,
the analysis evidence (proved accesses, derivations, premise rows with the accepted reviewed entry,
frame-word records) and the copies used. The premise rows print verbatim, in that report only.
"""
import json
from pathlib import Path

import match
import stack_index_precondition_profile as stack_index

NAME = "default-stack-index-retry-v1"
TRIGGERS = ("unsupported stack-alias use or escape",
            "unsupported stack-address materialization",
            "stack-alias index is not a known constant")
COPY_HELPER = 0x081443FC
SUMMARY = ("variable private-stack-array indices retried after the plain walk refused: every access "
           "proved by in-function value ranges to touch only allocated local words, initialised ones for "
           "a load, or, for a load only, bounded by a reviewed premise row that the proof does not check; "
           "no ranged address stored, pushed, compared, passed or returned, and one held in R4-R11 at "
           "a call only where the callee-saved watch admits that call")


class RetryPolicy:
    """The one policy object of this rule: ``enabled = False`` restores the plain refusals."""

    def __init__(self, enabled):
        self.enabled = enabled

    def triggered(self, error):
        return self.enabled and isinstance(error, ValueError) and str(error) in TRIGGERS


POLICY = RetryPolicy(True)


class IndexPolicy(stack_index.Policy):
    """The opt-in route's policy, with the default path's three differences (module docstring)."""

    carry_callee_saved = False

    def __init__(self, owner, data, premises):
        super().__init__(owner, len(data), stack_index.SELECTOR_V2)
        self.data = bytes(data)
        self.premises = premises

    def applies(self, address, data):
        return address == self.owner and bytes(data) == self.data

    def finish(self, data, address, instructions, copies):
        evidence = super().finish(data, address, instructions, copies)
        for row in evidence["preconditions"]:
            if row["kind"] != "load":
                stack_index.refuse(f"the {row['kind']} at 0x{row['site']:08X} needs a runtime premise "
                                   f"({row['expression']} < {row['bound']}); on the default path premise rows "
                                   f"admit loads only")
        self.evidence = stack_index.accept(evidence, address, stack_index.parse_premises(self.premises))
        return self.evidence


def snapshot(root):
    """The decomp's reviewed premise file, or None."""
    try:
        return (Path(root) / stack_index.PREMISES_PATH).read_bytes()
    except FileNotFoundError:
        return None


def copies(proof):
    """Initialisation for the analysis: {call site: (entry-SP destination, count)} from the summarised
    copy-helper calls of the owner walk whose destination is local and whose source is not."""
    policy = proof.index_policy
    if type(policy) is not IndexPolicy:
        raise ValueError("stack-index copies require the default stack-index retry policy")
    found = {}
    summaries = proof.copy_summaries
    for record in (summaries.observations.values() if summaries is not None else ()):
        site = record["site"]
        if not policy.owner <= site < policy.owner + policy.size or record["destination"] is None or \
                record["source"] is not None:
            continue
        copy = (record["destination"], record["count"])
        if found.setdefault(site, copy) != copy:
            raise ValueError("a copy-helper site copies to more than one local destination")
    return found


def retry(error, walk, make_proof, data, address, premises):
    """Run ``walk(proof)`` once more on a fresh ``make_proof()`` with the policy attached.

    ``error`` is the refusal of the plain walk; anything but a trigger is raised unchanged.
    Returns (instructions, proof); a refused retry raises the plain refusal with its reason."""
    if not POLICY.triggered(error):
        raise error
    proof = make_proof()
    if proof.index_policy is not None or proof.stack_index_retry is not None or not proof.stack_arguments:
        raise ValueError("default stack-index retry requires a fresh stack-argument buffer proof")
    proof.index_policy = IndexPolicy(address, data, premises)
    # The #350 callee walk, with this proof's ROM and mapping, checks every call made while R4-R11
    # hold a ranged address; without it IndexPolicy refuses such a call.
    proof.index_policy.callee_watch = proof
    # The plain mapped span, as the opt-in route's proof gives it: frame words walk callees with it.
    proof.index_policy.callee_span = lambda callee: match.BufferCallProof.span(proof, callee)
    try:
        instructions = walk(proof)
        if proof.index_policy.evidence is None:
            raise ValueError("stack index: the retried walk proved no variable stack index")
    except ValueError as reason:
        raise ValueError(f"{error}; default stack-index retry: {reason}") from reason
    proof.stack_index_retry = {
        "policy": NAME, "address": address, "trigger": str(error),
        "copies": sorted([site, destination, count]
                         for site, (destination, count) in copies(proof).items()),
        "evidence": json.loads(json.dumps(proof.index_policy.evidence, sort_keys=True))}
    return instructions, proof


def lines(record):
    """The report lines of an admitted retry; the replayed report repeats them.

    They are buffer proof lines (`* buffer ` prefix), which the buffer report checks hold to the
    recomputed proof exactly and in order; the opt-in route's premise lines follow verbatim."""
    evidence, address = record["evidence"], record["address"]
    out = [f"* buffer stack index: `{record['policy']}` after `{record['trigger']}`: {SUMMARY}; "
           f"{len(evidence['accesses'])} accesses proved by in-function ranges, "
           f"{len(evidence['preconditions'])} loads under reviewed premise rows, "
           f"{len(evidence['derivations'])} variable derivations"]
    for site, kind, width, low, high, modulus in evidence["accesses"]:
        out.append(f"* buffer stack index access: site 0x{address + site:08X} {kind} width {width} "
                   f"entry_SP{low:+#x}..{high:+#x} step 2^{modulus}, proved")
    for site, destination, count in record["copies"]:
        out.append(f"* buffer stack index initialisation: copy helper 0x{COPY_HELPER:08X} at 0x{site:08X} writes "
                   f"entry_SP{destination:+#x}..{destination + count:+#x} from a non-local source")
    out.extend("* buffer " + line[2:] for line in stack_index.precondition_lines(evidence))
    return out


def walk(make_proof, run, data, address, premises):
    """``run(make_proof())``, and on a trigger the one retry; returns (instructions, proof)."""
    proof = make_proof()
    try:
        return run(proof), proof
    except ValueError as error:
        return retry(error, run, make_proof, data, address, premises)
