"""Compiler `__modsi3` as a proved leaf call in the default buffer walk.

The default path's generic call binding refuses a compiler signed remainder
next to a jump table, a runtime call thunk, function literals or another
runtime with "signed remainder excludes mixed aliases, addressed calls with
data, and other profiles".  The isolated remainder profile proves only a
frameless caller with register operands, so a framed caller that passes
buffers, reads typed objects or dispatches through its own table stops there,
although the bounded-buffer walk proves every other part of it.

On that refusal only, and only after the compiler-thunk route (kit #134) has
refused too where it applies, a run with no selector, the fixed toolchain, no
library unit and no label, whose original object names `__modsi3` and not its
addressed spelling, is verified once more with this policy active.  Nothing
admitted today reaches the retry, so no existing report changes.  In the retry:

* every `__modsi3` relocation binds to the pinned entry 0x08142950 with the
  existing identity check; the addressed spelling, other runtimes and function
  literals refuse, and so does `__modsi3` or `func_08142950` named in the
  preprocessed C;
* the plain stack-argument buffer proof (the one that carries the copy-helper
  and jump-table callee summaries; never a selector's proof) applies the
  existing runtime_summary_profile leaf contract to a BL to that exact entry:
  native proof of every path of the pinned body and the `__div0` hook, no
  memory operand, R4-R11 and SP restored, R0 an unknown scalar, R1-R3, R12, LR
  and the flags clobbered, no tracked local pointer in R0, R1 or LR, and a dead
  pointer in R3 discarded only because every return overwrites it;
* every summarised call site, in the owner or in an inspected callee, carries a
  numeric operand record from owner_runtime_profile.prove_remainders over that
  walk's CFG: a CFG-constant divisor in 1..0x7FFFFFFF, or a signed16 dividend
  and a nonzero divisor (modsi3_profile.prove_operands).  A site without one
  refuses, so no admitted remainder divides by zero or computes INT_MIN % -1;
* the owner's own jump table may sit beside the summary only through the owner
  switch the data-buffer proof binds (owner_switch_buffer_profile).

The records are stated in `* buffer signed remainder` lines and bound into the
buffer proof fingerprint only when a site was summarised, so every other
fingerprint is unchanged.  Not proved, as for the selector's summary: the
remainder's value, any range for it, or termination.  ``POLICY.enabled =
False`` restores the plain refusal, and a report carrying these lines then
fails replay.
"""
from contextlib import contextmanager
from contextvars import ContextVar
import json
import re

EXCLUSION = "signed remainder excludes mixed aliases, addressed calls with data, and other profiles"
ADDRESS = 0x08142950
NAME = "__modsi3"
ADDRESSED_NAME = "func_08142950"
SUMMARY_SCHEMA = "thumb-compiler-modsi3-numeric-leaf-summary-v1"
FIELD = "* buffer signed remainder"
LINE = FIELD + ": "
ROUTED = "; compiler signed runtime thunks: "
RETRY = "; signed remainder leaf summary: "
CONTRACT = ("compiler __modsi3 at the SHA-pinned entry 0x08142950 with the shared __div0 hook; native proof "
            "of every reachable path: returns to the entry LR with R4-R11 and SP restored, no memory operand "
            "or block transfer; caller summary: R0 unknown scalar, R1-R3/R12/LR/flags clobbered, caller frame "
            "untouched; no tracked local pointer in R0/R1/LR, a pointer in R3 discarded only because every "
            "return overwrites it; every site has a numeric operand record (positive signed32 constant "
            "divisor, or signed16 dividend and nonzero divisor); no remainder value, range or termination theorem")

_ACTIVE = ContextVar("signed_remainder_leaf_active", default=False)
_CLASS = []


class Policy:
    """The default-path retry; ``enabled = False`` keeps the plain refusal."""

    enabled = True

    def applies(self, args, gate, original, error):
        import library_units
        # The refusal may come before compile_object returned a parsed ELF image.
        if not self.enabled or _ACTIVE.get() or gate is not None or type(error) is not ValueError or \
                str(error) != EXCLUSION or not isinstance(original, dict) or \
                type(original.get("symbols")) is not list or args.mode != "thumb" or \
                args.control_flow_profile != "ordinary" or args.label or library_units._selectors(args):
            return False
        names = {item.get("name") for item in original["symbols"] if not item.get("section")}
        return NAME in names and ADDRESSED_NAME not in names

    @staticmethod
    def routed_refusal(stop, error):
        """Whether a SystemExit is the compiler-thunk route refusing this same exclusion."""
        return isinstance(stop.code, str) and \
            stop.code.startswith(f"compile failed:\n{error}{ROUTED}")

    def retry(self, main, refusal):
        """Run main once more with the policy active; a refusal keeps the plain one first."""
        token = _ACTIVE.set(True)
        try:
            return main()
        except SystemExit as stop:
            if stop.code in (None, 0):
                raise
            reason = str(stop.code).removeprefix("compile failed:\n")
            raise SystemExit(f"{refusal}{RETRY}{reason}") from None
        finally:
            _ACTIVE.reset(token)


POLICY = Policy()


def active():
    return POLICY.enabled and _ACTIVE.get()


@contextmanager
def activated():
    token = _ACTIVE.set(True)
    try:
        yield
    finally:
        _ACTIVE.reset(token)


def selected(report):
    return any(line.lstrip().startswith(FIELD) for line in report.splitlines())


def replayable(report):
    """A report carrying the lines replays only under the plain buffer schemas, policy enabled."""
    from data_buffer_profile import SCHEMA as DATA_BUFFER_SCHEMA
    from match_evidence import STACK_BUFFER_SCHEMA
    verdicts = [line for line in report.splitlines() if line.startswith("* verification:")]
    return POLICY.enabled and verdicts in ([f"* verification: `{DATA_BUFFER_SCHEMA}`"],
                                           [f"* verification: `{STACK_BUFFER_SCHEMA}`"])


def namespace(preprocessed):
    from plausible import strip_comments_and_strings
    if {NAME, ADDRESSED_NAME} & set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*",
                                               strip_comments_and_strings(preprocessed))):
        raise ValueError("signed remainder leaf summary requires compiler-emitted __modsi3; "
                         "runtime identifiers cannot occur in preprocessed C")


def summaries_class():
    """RuntimeSummaries restricted to __modsi3, with per-site operand records (built lazily:
    runtime_summary_profile imports modules that import match)."""
    if not _CLASS:
        from runtime_summary_profile import RuntimeSummaries

        class RemainderLeafSummaries(RuntimeSummaries):
            def __init__(self, rom, mapping, index):
                super().__init__(rom, mapping, index)
                self.records = {}

            @staticmethod
            def covers(address):
                return type(address) is int and address == ADDRESS

            def record(self, instructions, edges, address, branches, calls, data):
                """The numeric operand record of every summarised site this walk reached."""
                import owner_runtime_profile as owner
                sites = {site for site, target in calls.items() if target == ADDRESS and site in instructions}
                if not sites:
                    return
                for offset, kind, *value in owner.prove_remainders(instructions, edges, address, branches,
                                                                  calls, sites, data):
                    entry = [address, offset, kind, *value]
                    if self.records.setdefault(address + offset, entry) != entry:
                        raise ValueError("signed remainder leaf operand records differ between walks of one site")

            def complete(self):
                missing = sorted(set(self.sites) - set(self.records))
                if missing:
                    raise ValueError("signed remainder leaf site has no numeric operand record: " +
                                     ", ".join(f"0x{site:08X}" for site in missing))

            def evidence(self):
                self.complete()
                if not self.sites:
                    raise ValueError("signed remainder leaf evidence requires a summarised call")
                return dict(schema=SUMMARY_SCHEMA, contract=CONTRACT,
                            components=[self.components[key] for key in sorted(self.components)],
                            sites=[self.records[site] for site in sorted(self.sites)],
                            observations=[self.observations[key] for key in sorted(self.observations)],
                            caller_clobbers=["r0", "r1", "r2", "r3", "r12", "lr", "flags"],
                            numeric_equivalence_claim=False, termination_claim=False)

            def digest_text(self):
                return json.dumps(self.evidence(), sort_keys=True, separators=(",", ":"))

            def lines(self):
                if not self.sites:
                    return []
                import owner_runtime_profile as owner
                evidence = self.evidence()
                entry = next(row for row in evidence["components"] if row["address"] == ADDRESS)
                lines = [f"{LINE}`{SUMMARY_SCHEMA}` __modsi3 0x{ADDRESS:08X} ({entry['instructions']} "
                         f"instructions, {entry['body_sha256'][:16]}) and __div0 as a native-proved leaf: "
                         "R0 unknown scalar, R1-R3/R12/LR/flags clobbered, R4-R11/SP restored, no memory "
                         "operand; no local pointer in R0/R1/LR; no remainder value or range"]
                discards = {}
                for row in evidence["observations"]:
                    for register, offset in row["discarded_scratch_aliases"]:
                        discards.setdefault(row["site"], set()).add(f"r{register}=sp{offset:+d}")
                for function, offset, kind, *value in evidence["sites"]:
                    site = function + offset
                    operands = (f"divisor {value[0]}" if kind == owner.POSITIVE_DIVISOR else
                                "signed16 dividend, nonzero divisor")
                    lines.append(f"{LINE}call 0x{site:08X} (0x{function:08X}+0x{offset:X}): {operands} "
                                 f"({kind}); dead scratch discarded: "
                                 f"{' '.join(sorted(discards.get(site, ()))) or 'none'}")
                return lines

        _CLASS.append(RemainderLeafSummaries)
    return _CLASS[0]


def is_summaries(value):
    return bool(_CLASS) and type(value) is _CLASS[0]


def summaries(rom, mapping, index):
    if not active() or any(type(value) is not bytes for value in (rom, mapping, index)):
        raise ValueError("signed remainder leaf summaries require the active policy and exact snapshots")
    return summaries_class()(rom, mapping, index)


def require_summarised(proof, calls):
    """The retry's admitted proof summarised every linked __modsi3 site of the owner."""
    owned = {site for site, target in calls.items() if target == ADDRESS}
    summary = getattr(proof, "runtime_summaries", None)
    if not owned or not is_summaries(summary) or not owned <= set(summary.sites):
        raise ValueError("signed remainder leaf summary requires the plain stack-argument buffer proof "
                         "at every compiler __modsi3 call")
    summary.complete()
