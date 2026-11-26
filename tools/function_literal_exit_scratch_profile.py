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
"""
import json

LINE = "* buffer function-literal exit scratch"


class Policy:
    """The maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()


def eligible(proof):
    from call_via_target_profile import kit_match
    return POLICY.enabled and type(proof) is kit_match(proof).FunctionBufferCallProof and \
        proof.index_policy is None


def walk(proof, data, address, mapping, run):
    """Run the owner walk ``run()`` with ``proof`` as the bound root's proof when it is eligible.

    The root's normal returns are bound on first need, at the first of its returns that holds an
    R2/R3 frame address (``aliases``), so a walk that never needs the projection is unchanged."""
    if eligible(proof) and getattr(proof, "_return_root", None) is None:
        proof._function_exit_root = (address, bytes(data), mapping)
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
    proof._function_exit_bound = True
    return True


def aliases(proof, data, address, site, held):
    """The return hook match.py calls at every stack-argument return; unbound proofs keep ``held``."""
    import match
    root = getattr(proof, "_function_exit_root", None)
    if root is None or not eligible(proof) or address != root[0] or data != root[1] or _split(proof, address):
        return held
    if not any(register in (match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3) for register in held):
        return held
    if not getattr(proof, "_function_exit_bound", False):
        if getattr(proof, "_return_root", None) is not None or not _bind(proof):
            proof._function_exit_root = None
            return held
    from named_data_buffer_profile import RootReturnScratchMixin
    return RootReturnScratchMixin.root_return_aliases(proof, data, address, site, held)


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
    if sites and _split(proof, address):
        raise ValueError("function-literal exit scratch refuses a walk that kept a join apart")
    proof.function_exit_scratch = dict(schema=DISCARDED_SCRATCH_SCHEMA, registers=[2, 3],
                                       contract=DISCARDED_SCRATCH_CONTRACT, address=address,
                                       sites=[list(site) for site in sites]) if sites else None


def lines(proof):
    scratch = getattr(proof, "function_exit_scratch", None)
    if not scratch:
        return []
    sites = ", ".join(f"`0x{site:08X} r{register} {offset:+d}`" for site, register, offset in scratch["sites"])
    return [f"{LINE}: `{scratch['schema']}` premise, not checked: {scratch['contract']}; own-frame "
            f"addresses dropped at the owner's normal returns: {sites}; R0/R1 and every callee return keep "
            f"the escape refusal"]


def fingerprint_payload(proof):
    scratch = getattr(proof, "function_exit_scratch", None)
    if not scratch:
        return None
    return json.dumps(["function-literal-exit-scratch-v1", scratch], sort_keys=True,
                      separators=(",", ":")).encode()
