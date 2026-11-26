"""R2/R3 own-frame addresses at a function-literal owner's normal returns (T3).

On a path that returns, agbcc can leave the address of one of the owner's locals in R2 or R3, the
base it used for that local's stores or the last argument it passed.  The function-literal buffer
proofs (``elf-symbol-thumb-function-buffer-calls-v1`` and
``elf-symbol-thumb-function-data-buffer-calls-v1``) refused that at the return ("local stack
pointer escapes through a return register").

At the owner's own normal returns such an address, one inside the owner's expired frame, is dropped
and recorded under the premise the kit already states at other roots,
``thumb-discarded-exit-scratch-v1``: R2/R3 carry no results under the agbcc Thumb ABI, so the
owner's caller never reads them.  It is a premise about the callers and is not checked; every
report that uses it states it.  The projection is ``RootReturnScratchMixin``'s, unchanged, as
kdes-rem's owner-switch exit scratch binds it: only the bound owner's exact normal returns (whose
returns end the walk), never an inspected callee's return, only R2/R3 and only addresses inside
the expired frame.  R0/R1, every other register, every callee return and a walk that kept any join
apart (``split_join_profile``, on any register) keep the refusal.  The binding is made only for an
exact ``FunctionBufferCallProof`` root walk without a stack-index policy, an owner switch or the menu
list frame, and only when the root has no local BL or switch and every normal return ends the walk;
any other shape stays unbound, so its refusal stands.  It is made lazily, at the first root return
that holds an R2/R3 address, so a walk that never needs it is unchanged.

The sites are bound into the buffer fingerprint only when one exists, and the report states them
on one ``* buffer function-literal exit scratch`` line; replay recomputes both.  ``POLICY``
gates the rule with one line.

The plain frame-buffer owner (``FRAME``) shares the binding and the projection: the default
stack-argument walk of an exact ``BufferCallProof`` (``elf-symbol-thumb-frame-buffer-calls-v2``
and the typed-data buffer proof's plain route), including its stack-index retry, which binds the
retried proof's own root.  Its callers wrap the walk with ``walk(..., kind=FRAME)``: match.py's
default retry, the data-buffer proof and both replays (``match_evidence.buffer_report_matches``
and the legacy thunk-absence replay).  Every other plain proof is never wrapped, so it is never
bound and keeps its refusal.  Its sites are stated on one ``* buffer frame exit scratch`` line and
bound under their own payload tag; ``FRAME_POLICY`` gates it.
"""
import json

import frame_result_r1_profile as frame_r1

LINE = "* buffer function-literal exit scratch"
FRAME_LINE = "* buffer frame exit scratch"
FUNCTION, FRAME = "function-literal", "frame-buffer"
_LINES = {FUNCTION: LINE, FRAME: FRAME_LINE}
_TAGS = {FUNCTION: "function-literal-exit-scratch-v1", FRAME: "frame-buffer-exit-scratch-v1"}


class Policy:
    """The maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()
FRAME_POLICY = Policy()


def eligible(proof, kind=None):
    from call_via_target_profile import kit_match
    kind = kind or getattr(proof, "_function_exit_kind", FUNCTION)
    if kind == FRAME:
        return FRAME_POLICY.enabled and type(proof) is kit_match(proof).BufferCallProof and \
            proof.stack_arguments is True
    return kind == FUNCTION and POLICY.enabled and type(proof) is kit_match(proof).FunctionBufferCallProof and \
        proof.index_policy is None


def walk(proof, data, address, mapping, run, kind=FUNCTION):
    """Run the owner walk ``run()`` with ``proof`` as the bound root's proof when it is eligible.

    The root's normal returns are bound on first need, at the first of its returns that holds an
    R2/R3 frame address (``aliases``), so a walk that never needs the projection is unchanged."""
    if eligible(proof, kind) and getattr(proof, "_return_root", None) is None:
        proof._function_exit_root = (address, bytes(data), mapping)
        proof._function_exit_kind = kind
    result = run()
    if getattr(proof, "_function_exit_bound", False):
        record(proof, address)
    return result


def _bind(proof):
    """The root's exact normal returns, as RootReturnScratchMixin.bind_return_root takes them."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    address, data, mapping = proof._function_exit_root
    try:
        refinement = owner.refine(data, address, mapping)
        _, edges, branches, _, words = graph.graph(data, address, refinement)
    except ValueError:
        return False                    # outside the rule: the escape refusal stands
    returns = frozenset(int(site, 16) for site in refinement["returns"])
    # No local BL and no switch, and every return ends the walk, as bind_return_root requires.
    if branches or words or not returns or any(edges[site] for site in returns):
        return False
    proof._return_root = (address, data, returns)
    proof._return_scratch = {}
    proof._return_scratch_joins = set()
    proof._frame_r1_sites = {}
    proof._function_exit_bound = True
    return True


def aliases(proof, data, address, site, held, split_state=False):
    """The return hook match.py calls at every stack-argument return; unbound proofs keep ``held``.

    ``split_state``: the return is reached in a state the split-join rule keeps apart.  The
    function-literal owner refuses any walk that kept a join apart; the frame-buffer owner refuses
    only a return reached in such a state, so its projections are made from merged states alone."""
    import match
    root = getattr(proof, "_function_exit_root", None)
    frame = getattr(proof, "_function_exit_kind", FUNCTION) == FRAME
    if root is None or not eligible(proof) or address != root[0] or data != root[1] or \
            (split_state if frame else _split(proof, address)):
        return held
    watched = (match.ARM_REG_R0 + 1, match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3) if frame else \
        (match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3)
    if not any(register in watched for register in held):
        return held
    if not getattr(proof, "_function_exit_bound", False):
        if getattr(proof, "_return_root", None) is not None or not _bind(proof):
            proof._function_exit_root = None
            return held
    from named_data_buffer_profile import RootReturnScratchMixin
    projected = RootReturnScratchMixin.root_return_aliases(proof, data, address, site, held)
    # The frame-buffer owner's R1, only on the ROM's caller evidence (frame_result_r1_profile).
    return frame_r1.project(proof, data, address, site, projected, root[2]) if frame else projected


def _split(proof, address):
    from owner_switch_buffer_profile import _split_walk
    return _split_walk(proof, address)


def record(proof, address):
    """After the walk: the final projected sites, kept only when there are any."""
    from local_long_branch_profile import DISCARDED_SCRATCH_SCHEMA, DISCARDED_SCRATCH_CONTRACT
    sites = sorted((site, register, offset)
                   for site, pairs in proof._return_scratch.items() for register, offset in pairs)
    if proof._return_scratch_joins:
        raise ValueError("function-literal exit scratch projects no joins")
    if sites and getattr(proof, "_function_exit_kind", FUNCTION) == FUNCTION and _split(proof, address):
        raise ValueError("function-literal exit scratch refuses a walk that kept a join apart")
    proof.function_exit_scratch = dict(schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
                                       contract=DISCARDED_SCRATCH_CONTRACT, address=address,
                                       sites=[list(site) for site in sites]) if sites else None
    kind = getattr(proof, "_function_exit_kind", FUNCTION)
    if sites and kind != FUNCTION:
        proof.function_exit_scratch["kind"] = kind
    frame_r1.record(proof)


def lines(proof):
    return _scratch_lines(proof) + frame_r1.lines(proof)


def _scratch_lines(proof):
    scratch = getattr(proof, "function_exit_scratch", None)
    if not scratch:
        return []
    sites = ", ".join(f"`0x{site:08X} r{register} {offset:+d}`" for site, register, offset in scratch["sites"])
    # With the frame-buffer owner's R1 rule used, R1 keeps the refusal except as its own line states.
    kept = "R0, R1 (but for the frame result r1 line)" if getattr(proof, "frame_result_r1", None) else "R0/R1"
    return [f"{_LINES[scratch.get('kind', FUNCTION)]}: `{scratch['schema']}` premise, not checked: {scratch['contract']}; own-frame "
            f"addresses dropped at the owner's normal returns: {sites}; {kept} and every callee return keep "
            f"the escape refusal"]


def fingerprint_payload(proof):
    scratch = getattr(proof, "function_exit_scratch", None)
    payload = json.dumps([_TAGS[scratch.get("kind", FUNCTION)], scratch], sort_keys=True,
                         separators=(",", ":")).encode() if scratch else None
    # The frame-buffer owner's R1 evidence (frame_result_r1_profile), only when it dropped one.
    r1 = frame_r1.fingerprint_payload(proof)
    if r1 is None:
        return payload
    return (payload or b"") + len(r1).to_bytes(8, "little") + r1
