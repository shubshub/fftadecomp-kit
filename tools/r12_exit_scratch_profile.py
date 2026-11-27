"""A frame address left in R12 (IP) at a return of a buffer walk (kit #588).

`verify_leaf_instructions` checks what a walk hands back at a return: an own-frame address left
in R0-R3 refuses ("local stack pointer escapes through a return register"), except R2/R3 under
the recorded `thumb-discarded-exit-scratch-v1` premise where a walk states it.  R12 was exempt
at every return, with no report line: IP is call-clobbered scratch, so the kit assumed nobody
reads it after the call.  Two kinds of return relied on that:

* a walked callee's return.  The caller drops IP with the other caller-clobbered registers, so
  if it read IP it would hold an unknown scalar that is really the callee's released frame,
  below the caller's SP, where its next callee builds its frame;
* the root's own return.  The function the report is about hands its own expired frame address
  in IP to its unwalked caller.

The rule, at every return whose aliases hold R12:

1. a walk without a stack-argument proof refuses (the #538 return check covers R0-R3 there; no
   report meets R12 there, so no premise is stated for it);
2. an inspected callee's walk (the stack-argument proof's `active` set is non-empty) refuses, as
   R0-R3 do at a callee return.  The refusal carries `return_scratch_profile.ESCAPE`, so the
   dead-register fallback keeps it (`BufferCallProof.check_arguments`, kit #538);
3. a root walk refuses unless its proof keeps the ledger: only the proofs whose reports print
   and bind it do.  BufferCallProof and FunctionBufferCallProof (exact types, stack arguments)
   keep it from construction: the default path's plain, data and function-literal buffer
   reports print `BufferCallProof.exit_r12_lines` and bind its fingerprint, and every replay of
   them compares both; the complete-owner route (`owner_admission_profile`) enables it on its
   proofs (`enable`) and records the line in its manifest.  With the ledger, an exact
   own-frame offset below the entry SP is recorded (site, offset) and admitted under the
   premise `thumb-discarded-exit-scratch-r12-v1`: no caller reads IP after the call.  agbcc
   output never does (IP is call-clobbered), the premise R2/R3 rest on, but the kit does not
   check its callers, so the premise is printed on one `* buffer exit scratch r12:` line and
   bound into the proof's fingerprint (or owner manifest) only when a site was recorded.  An
   address at or above the entry SP (the caller's own stack) refuses.

A report without such a return keeps its lines and fingerprint.
"""
import json

SCHEMA = 'thumb-discarded-exit-scratch-r12-v1'
CONTRACT = ('r12 (ip) is discarded scratch at external returns; no caller reads it after the call '
            '(a premise about the callers, not checked)')
FIELD = '* buffer exit scratch r12'


def enable(proof):
    """Give `proof` the ledger: its report prints `lines` and binds `payload`.  Returns `proof`."""
    proof.r12_exit_scratch = set()
    return proof


def check(aliases, site, buffer_proof, stack_arguments):
    """The rule at a return `site` of verify_leaf_instructions; `aliases` maps capstone registers to
    entry-SP offsets."""
    from match import ARM_REG_R12
    from return_scratch_profile import ESCAPE
    if ARM_REG_R12 not in aliases:
        return
    offset = aliases[ARM_REG_R12]
    if not stack_arguments:
        raise ValueError(f"{ESCAPE}: r12 at a return of a walk without a stack-argument proof")
    if getattr(buffer_proof, 'active', None):
        raise ValueError(f"{ESCAPE}: r12 at a walked callee's return")
    ledger = getattr(buffer_proof, 'r12_exit_scratch', None)
    if ledger is None:
        raise ValueError(f"{ESCAPE}: r12 at a root return whose report does not state the r12 premise")
    if type(offset) is not int or offset >= 0:
        raise ValueError(f"{ESCAPE}: r12 holds an address at or above the entry SP")
    ledger.add((site, offset))


def sites(proof):
    return sorted(getattr(proof, 'r12_exit_scratch', None) or ())


def lines(proof):
    """The report line, or nothing when no site was recorded."""
    found = sites(proof)
    if not found:
        return []
    return [f"{FIELD}: `{SCHEMA}` {CONTRACT}; " +
            ", ".join(f"`0x{site:08X} r12 {offset:+d}`" for site, offset in found)]


def payload(proof):
    """The fingerprint bytes, or None when no site was recorded."""
    found = sites(proof)
    if not found:
        return None
    return json.dumps([SCHEMA, CONTRACT, [list(row) for row in found]], separators=(',', ':')).encode()
