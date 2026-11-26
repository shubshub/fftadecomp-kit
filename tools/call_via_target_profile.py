"""Canonical call-via thunks beside function literals on the default path (T1).

A caller with function literals may also call agbcc's ``_call_via_rN`` thunks.  The frameless
function-address proof keeps refusing them (``canonical-thunks-v1`` stays the selector for that
shape); the function-literal buffer proofs (``elf-symbol-thumb-function-buffer-calls-v1`` and
``elf-symbol-thumb-function-data-buffer-calls-v1``) bind each thunk by its canonical ELF name and
``bx rN`` bytes and walk it exactly as the plain ``BufferCallProof`` already does: a thunk call
that passes no frame address is an ordinary call (R4-R11 frame addresses fall under kit #350's
walk and recorded premise), one that passes a frame address is refused as before ("non-leaf
indirect control flow requires linked CFG verification").  Every reached code-valued pool word of
such a caller carries its canonical function relocation, and none names the caller's own bytes.

Only the default route takes it: ``match.default_call_route`` (no selector, control-flow profile
or library unit) links a function-literal caller's thunk calls, and only without a switch.
``POLICY`` gates it with one line.
"""


class Policy:
    """The maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()
