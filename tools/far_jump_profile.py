"""agbcc far jumps on the default path's walks: a same-function BL pair walked as a jump.

agbcc emits ``bl .Ln`` to a label of the function it is compiling when a branch does not reach
with a Thumb B (its ``far_jump`` pattern, which also makes the prologue save LR).  The pair is then
a jump, not a call: by ARMv4T, BL sets PC to its target and LR to the address after the pair | 1,
and changes nothing else (no argument or scratch register, no flag, no memory).

The default path's walks (`match.verify_leaf_instructions` with no selector context, and a buffer
proof that is none, `match.BufferCallProof` or `match.FunctionBufferCallProof`, including their
stack-index and closure-slot retries and the walks of the callees they inspect) refused every
such pair: "call is not a validated external direct Thumb BL".  With this rule a pair is walked as
a jump when

1. it is the canonical unconditional four-byte pair (`local_long_branch_profile.target`) whose
   target is an even address strictly inside the function (entry < target < end); the walk then
   decodes the target as a reachable instruction of the span, so a target inside another
   instruction or a literal word refuses as before;
2. the site has no call binding (the link's validated calls; a relocated BL stays a call), and
3. the walk's context is a default one: every other context keeps its own local-branch rule (menu
   list, owner switch far default, software double, outgoing-argument switch frame, addressed
   runtime) or its refusal.

The walk takes the single successor (the target), drops LR's return provenance, alias and
constant, and keeps every other register, the flags and the frame.  Two proofs close it:

* LR is dead: after the walk, every path from each far jump's target writes LR (a BL, or a pop,
  load or move into LR) before anything reads it, so no code observes the continuation the pair
  left there (a push of LR, a copy, a ``bx lr`` after the jump refuse);
* the return: the walk's own return proof is unchanged - a return goes only through a register or
  saved word that holds the entry LR, with the frame balanced - exactly as after an external BL,
  which also destroys LR.  No frame value crosses a call (there is none), and no possible frame
  address becomes a scalar (LR's old value is overwritten; the new one is a ROM code address).

There is no premise.  A report whose walk took a far jump states the edges: the root's in a
``* far jumps:`` line re-derived from its verified instructions, an inspected callee's in the buffer
proof's fingerprint and a buffer line.  Every other report is unchanged.
"""
import json

SCHEMA = "thumb-same-owner-far-jump-v1"
SUMMARY = ("same-function Thumb BL pairs walked as jumps (PC := target, LR := continuation, no call ABI), "
           "each with no call binding and a target that is a reachable non-entry instruction of this "
           "function, and LR written before any read on every path from each target")
LINE = "* far jumps: "
BUFFER_LINE = "* buffer far jumps: "
# The parameters of match.verify_leaf_instructions a default walk may set.  Any other one is a
# selector or profile context, which keeps its own rule.
PARAMETERS = frozenset({"data", "address", "thumb", "validated_calls", "call_resolver", "buffer_proof",
                        "incoming_narrow_reads", "dma_fills", "callee_watch", "return_scratch",
                        "entry_constants", "runtime_summaries"})


class Policy:
    """The rule's one switch: a maintainer can turn it off with one line."""
    enabled = True


POLICY = Policy()


def _default_proof_types():
    """The two default proof classes, in the imported match module and in match.py run as
    __main__ (issuance runs it so, and builds proofs with both copies)."""
    import sys
    types = set()
    for name in ("match", "__main__"):
        module = sys.modules.get(name)
        if module is not None and getattr(module, "VERIFY_LEAF_PARAMETERS", None) is not None:
            types.update(getattr(module, kind, None) for kind in ("BufferCallProof", "FunctionBufferCallProof"))
    types.discard(None)
    return types


def default_walk(values, names):
    """Whether a walk whose verify_leaf_instructions arguments (``names``, read from the walk's
    ``values``) are these may take far jumps."""
    parameters = {name: values[name] for name in names}
    if not POLICY.enabled or parameters.get("thumb") is not True:
        return False
    if any(value is not None and value is not False
           for name, value in parameters.items() if name not in PARAMETERS):
        return False
    types = _default_proof_types()
    proof = parameters.get("buffer_proof")
    if proof is not None and type(proof) not in types:
        return False
    # A callee walk resolves its calls through the proof that inspects it: only a default proof's.
    owner = getattr(parameters.get("call_resolver"), "__self__", None)
    return owner is None or type(owner) in types


def target(instruction, address, end, calls):
    """The far jump's target, or None when the instruction is not a candidate.  A candidate that
    is not the canonical pair refuses."""
    from capstone.arm import ARM_OP_IMM
    from local_long_branch_profile import target as local_target
    operands = instruction.operands
    if instruction.mnemonic != "bl" or len(operands) != 1 or operands[0].type != ARM_OP_IMM or \
            not address < operands[0].imm < end or instruction.address in calls:
        return None
    return local_target(instruction, address, end)


def successors(item):
    """Where control goes after a decoded Thumb instruction that is not a branch, a return or a
    switch dispatch (each analysis decides those itself): a far jump the walk took goes to its
    target only; every other instruction, a call included, falls through to the next one.

    This is the one successor rule for every analysis that recomputes control flow over a
    function a default walk may have walked with far jumps.  tests/test_far_jumps.py
    (SuccessorSiteTests) enumerates every kit function that computes successors, classifies each,
    and runs the default routes with far jumps to check that none of the others is reached."""
    target = getattr(item, "far_jump_target", None)
    return (target,) if target is not None else (item.address + item.size,)


def raw_successors(site, far_jumps):
    """The same for a BL pair at ``site`` in a raw-halfword decoder, given the walk's far jumps."""
    target = far_jumps.get(site)
    return (target,) if target is not None else (site + 4,)


def check_dead(instructions, edges, branches):
    """Every path from each far jump's target writes LR before any instruction reads it."""
    from capstone.arm import ARM_REG_LR
    pending, seen = list(branches.values()), set()
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        item = instructions[node]
        read, written = item.regs_access()
        if ARM_REG_LR in read:
            raise ValueError(f"far jump: the continuation in LR is read at 0x{node:08X}")
        if item.mnemonic == "bl" or ARM_REG_LR in written:
            continue
        pending.extend(edges[node])


def mark(instruction):
    """The walk took this decoded BL as a far jump: its instruction says so, wherever the list goes."""
    instruction.far_jump_target = instruction.operands[0].imm


def record(instructions, address):
    """[[site offset, target offset], ...] of the far jumps the walk that verified these
    instructions took (only those: another context's local branches are not this rule's)."""
    return [[item.address - address, item.far_jump_target - address]
            for item in sorted(instructions, key=lambda item: item.address)
            if getattr(item, "far_jump_target", None) is not None]


def edges_text(edges):
    return ", ".join(f"+0x{site:X}->+0x{destination:X}" for site, destination in edges)


def report_line(edges):
    """The root's line: the schema, the summary and its edges as offsets from the entry."""
    return f"{LINE}`{SCHEMA}` {SUMMARY}: {edges_text(edges)}"


def observe(proof, address, instructions):
    """An inspected callee's far jumps, kept on the buffer proof that walked it."""
    edges = record(instructions, address)
    records = proof.far_jumps
    if edges:
        if records.get(address, edges) != edges:
            raise ValueError("far jumps of one callee differ between its walks")
        records[address] = edges


def fingerprint_payload(proof):
    records = getattr(proof, "far_jumps", None)
    if not records:
        return None
    return json.dumps([SCHEMA, sorted([address, edges] for address, edges in records.items())],
                      separators=(",", ":")).encode()


def lines(proof):
    records = getattr(proof, "far_jumps", None)
    if not records:
        return []
    return [f"{BUFFER_LINE}`{SCHEMA}` callee 0x{address:08X}: {edges_text(edges)}"
            for address, edges in sorted(records.items())]
