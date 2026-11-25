"""Own-frame addresses in a return register, in walks without a stack-argument proof (kit #538).

The stack-argument buffer walks refuse a frame address left in R0-R3 at a
return (`local stack pointer escapes through a return register`); the
restoring owner's frame proof refuses it at every exit.  The other walks - the
plain and version-1 walks of the default path, the self-call walk, the
structural walk of a callee a version-1 proof inspects, and every walk made
without a stack-argument proof - never looked at their aliases at a return, so
a function returning the address of its own expired frame was admitted.  A
caller then holds an address below its SP, where its next callee builds its
frame; that callee can be made to write through it into its own saved
registers.

`verify_leaf_instructions` now checks every such return:

* R0 and R1, the result registers, refuse with the stack-argument walks'
  message;
* R2 and R3 refuse unless the walk carries a `ReturnScratch` ledger.  Two
  kinds of root walk carry one, and each states what it admitted:
  * the default path's root walks that write the plain framed schemas
    (`elf-symbol-thumb-frame-v1`, `-frame-calls-v1`, `-frame-data-v1`, no
    buffer calls), whose reports state the premise and every site on their
    own lines;
  * the restoring owner's acyclic and ignored-leaf walks, whose owner proof
    records the sites as `discarded_exit_scratch` (`manifest`), as the
    restoring owner's frame proof records its own, so the owner evidence
    printed on the report carries them and replay rebuilds and compares them.
  The existing `thumb-discarded-exit-scratch-v1` premise applies there - R2/R3
  carry no results under the agbcc Thumb ABI.  It is a premise about the
  callers, which the walks do not check (after a call every walk treats
  R0-R3 as unknown scalars, not as dead), so it is always recorded;
* R12 keeps its exemption (IP is ABI scratch, not a result register), as in
  the stack-argument walks.

A callee walked by a version-1 proof carries no ledger, so it refuses a frame
address in any of R0-R3 at its return: its consumer is a known caller.

Report lines (after the stack-frame line and any DMA fill lines):

    * stack frame exit scratch premise: `thumb-discarded-exit-scratch-v1` r2/r3 are discarded scratch ...
    * stack frame exit scratch: `0x<return site> r<register> <entry-SP offset>`, ...

Replay re-walks with a ledger only when the report states these lines and
requires the recomputed lines to equal them, so a report written without them
no longer replays for a function that needs them, and a report that states
them for a function that does not is refused.
"""
from local_long_branch_profile import DISCARDED_SCRATCH_CONTRACT, DISCARDED_SCRATCH_SCHEMA

MARKER = "* stack frame exit scratch"
PREMISE = f"* stack frame exit scratch premise: `{DISCARDED_SCRATCH_SCHEMA}` {DISCARDED_SCRATCH_CONTRACT}"
SITES = "* stack frame exit scratch: "
ESCAPE = "local stack pointer escapes through a return register"
RESULTS = frozenset((0, 1))
SCRATCH = frozenset((2, 3))


class ReturnScratch:
    """The own-frame addresses one root walk leaves in R2/R3 at its returns."""

    def __init__(self):
        self.sites = set()

    def admit(self, site, held):
        """`held` maps register number (0-3) to entry-SP offset at the return `site`."""
        for register, offset in held.items():
            if register not in SCRATCH or type(offset) is not int or offset >= 0:
                raise ValueError(ESCAPE)
            self.sites.add((site, register, offset))

    def report_lines(self):
        if not self.sites:
            return []
        return [PREMISE, SITES + ", ".join(f"`0x{site:08X} r{register} {offset:+d}`"
                                           for site, register, offset in sorted(self.sites))]


def manifest(ledger):
    """The owner-proof record of a ledger's sites, in the shape the frame proof records its discarded exit
    scratch (`local_long_branch_profile.prove_frame`): rows (site, register, entry-SP offset, live).  Every
    ledger alias is an exact frame address the walk tracked, so each row is live, and the walk proves no
    non-escape: the premise carries it."""
    return {'schema': DISCARDED_SCRATCH_SCHEMA, 'registers': [2, 3], 'contract': DISCARDED_SCRATCH_CONTRACT,
            'residual_aliases': [[site, register, offset, True] for site, register, offset in sorted(ledger.sites)],
            'native_nonescape_proof': False}


def report_fields(lines):
    """The report's exit-scratch lines, in report order."""
    return [line for line in lines if line.lstrip().startswith(MARKER)]


def check_return(aliases, base, site, ledger):
    """The #538 return check for a walk without a stack-argument proof.

    `aliases` maps capstone registers to entry-SP offsets; `base` is ARM_REG_R0.
    """
    held = {register - base: offset for register, offset in aliases.items() if 0 <= register - base <= 3}
    if not held:
        return
    if set(held) & RESULTS or ledger is None:
        raise ValueError(ESCAPE)
    ledger.admit(site, held)
