"""Compiler division beside one guarded local jump table.

The positive-constant signed quotient profile (`__divsi3`) and the default
switch profile each excluded the other only because neither manifest
recorded the other's facts.  This composition keeps both proofs whole: the
table is the default path's guarded dispatch, derived from the bytes by
`switch_layout` (forward cases only), the closed CFG includes its case edges,
and the existing constant-divisor checks run over that same CFG.  The
quotient manifest records the switch descriptor beside the divisors, under
its own schemas.  No data, function literal, thunk or other runtime joins it.
A frame still needs the existing framed quotient selector.

Set ``POLICY.enabled`` to False to restore every old refusal.
"""

SUFFIX = " beside one guarded local jump table"


class Policy:
    enabled = True


POLICY = Policy()


def relocations(manifest, data, address):
    """A signed quotient manifest's switch relocations, checked against the bytes; None without a switch."""
    if not isinstance(manifest, dict) or "switch" not in manifest or not POLICY.enabled:
        return None
    from match import switch_layout
    descriptor = manifest["switch"]
    if not isinstance(descriptor, dict) or not isinstance(descriptor.get("relocations"), list) or any(
            not isinstance(record, list) or len(record) != 2 or
            any(type(value) is not int for value in record) for record in descriptor["relocations"]):
        raise ValueError("invalid division switch descriptor")
    result = dict(descriptor["relocations"])
    if switch_layout(data, address, result) != descriptor:
        raise ValueError("division switch descriptor does not match the guarded bytes")
    return result
