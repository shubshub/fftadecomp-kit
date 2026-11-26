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

The same retry covers the other three pinned word runtimes, compiler
`__divsi3` (0x081426B8), `__udivsi3` (0x08142AB0) and `__umodsi3`
(0x08142B28) (``DIVISION``).  It also runs on the three link exclusions that
refuse them beside a table, a thunk, a literal or another runtime, when the
original object names at least one compiler runtime and none of the four
addressed spellings.  In that retry each compiler name binds to its pinned
entry with that runtime's own identity check, and the same leaf contract
summarises it.  Every site carries a numeric operand record from its
function's own walk:
* signed quotient and remainder: a CFG-constant divisor in 1..0x7FFFFFFF, or a
  signed16 dividend and a nonzero divisor;
* unsigned quotient and remainder: a CFG-constant divisor in 1..0xFFFFFFFF.
No admitted site divides by zero or computes INT_MIN / -1.  An owner that
summarises only `__modsi3` keeps exactly the lines, schema and fingerprint
text above.  Any other owner states its sites in `* buffer division runtime`
lines under schema `thumb-compiler-division-numeric-leaf-summary-v1`, each
site naming its runtime.  ``DIVISION.enabled = False`` restores the plain
refusals for the three new exclusions and leaves `__modsi3` alone in the
retry.
"""
from contextlib import contextmanager
from contextvars import ContextVar
import json
import re

EXCLUSION = "signed remainder excludes mixed aliases, addressed calls with data, and other profiles"
ADDRESS = 0x08142950
NAME = "__modsi3"
ADDRESSED_NAME = "func_08142950"
# The other pinned word runtimes (DIVISION) and the link exclusions that refuse them in combinations.
ENTRIES = {"__divsi3": 0x081426B8, NAME: ADDRESS, "__udivsi3": 0x08142AB0, "__umodsi3": 0x08142B28}
ADDRESSED_NAMES = frozenset(f"func_{entry:08X}" for entry in ENTRIES.values())
DIVISION_EXCLUSIONS = ("signed quotient excludes other runtime, literal, switch and thunk profiles",
                       "division evidence excludes literal, switch and thunk combinations",
                       "unsigned remainder excludes other runtime, switch, function and thunk profiles")
SIGNED = frozenset(("__divsi3", NAME))
DIVISION_SUMMARY_SCHEMA = "thumb-compiler-division-numeric-leaf-summary-v1"
DIVISION_FIELD = "* buffer division runtime"
DIVISION_LINE = DIVISION_FIELD + ": "
DIVISION_RETRY = "; division leaf summary: "
NONZERO_DIVISOR = "nonzero-u32-constant-divisor"
DIVISION_CONTRACT = (
    "compiler __divsi3/__modsi3/__udivsi3/__umodsi3 at their SHA-pinned entries 0x081426B8/0x08142950/"
    "0x08142AB0/0x08142B28 with the shared __div0 hook; native proof of every reachable path: returns to the "
    "entry LR with R4-R11 and SP restored, no memory operand or block transfer; caller summary: R0 unknown "
    "scalar, R1-R3/R12/LR/flags clobbered, caller frame untouched; no tracked local pointer in R0/R1/LR, a "
    "pointer in R2/R3/R12 discarded only where every return overwrites it; every site has a numeric operand "
    "record (signed: positive signed32 constant divisor, or signed16 dividend and nonzero divisor; unsigned: "
    "nonzero u32 constant divisor); no quotient or remainder value, range or termination theorem")
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


class DivisionPolicy:
    """The retry's other three runtimes and their exclusions; ``enabled = False`` keeps __modsi3 alone."""

    enabled = True


DIVISION = DivisionPolicy()


def names():
    """The compiler runtime names the retry binds."""
    return frozenset(ENTRIES) if DIVISION.enabled else frozenset((NAME,))


def entries():
    """{pinned entry: compiler name} of the runtimes the retry binds."""
    return {ENTRIES[name]: name for name in names()}


def verify_identity(name, rom, mapping):
    """The bound runtime's existing identity check (pinned bytes, exact unique Thumb spans, hook)."""
    import match
    import divsi3_profile as divsi3
    import modsi3_profile as modsi3
    import umodsi3_profile as umodsi3
    {"__divsi3": divsi3.verify_identity, NAME: modsi3.verify_identity,
     "__udivsi3": match.verify_udivsi3_identity, "__umodsi3": umodsi3.verify_identity}[name](rom, mapping)


class Policy:
    """The default-path retry; ``enabled = False`` keeps the plain refusal."""

    enabled = True

    def applies(self, args, gate, original, error):
        import library_units
        # The refusal may come before compile_object returned a parsed ELF image.
        if not self.enabled or _ACTIVE.get() or gate is not None or type(error) is not ValueError or \
                str(error) not in (EXCLUSION,) + (DIVISION_EXCLUSIONS if DIVISION.enabled else ()) or \
                not isinstance(original, dict) or \
                type(original.get("symbols")) is not list or args.mode != "thumb" or \
                args.control_flow_profile != "ordinary" or args.label or library_units._selectors(args):
            return False
        undefined = {item.get("name") for item in original["symbols"] if not item.get("section")}
        if str(error) == EXCLUSION:
            return NAME in undefined and ADDRESSED_NAME not in undefined
        # A division exclusion: some compiler runtime, and no addressed spelling of any of the four.
        return bool(undefined & set(ENTRIES)) and not undefined & ADDRESSED_NAMES

    @staticmethod
    def routed_refusal(stop, error):
        """Whether a SystemExit is the compiler-thunk route refusing this same exclusion."""
        return isinstance(stop.code, str) and \
            stop.code.startswith(f"compile failed:\n{error}{ROUTED}")

    def retry(self, main, refusal):
        """Run main once more with the policy active; a refusal keeps the plain one first."""
        # The remainder exclusion keeps its own suffix; the three division exclusions name theirs.
        suffix = RETRY if str(refusal).startswith(f"compile failed:\n{EXCLUSION}") else DIVISION_RETRY
        token = _ACTIVE.set(True)
        try:
            return main()
        except SystemExit as stop:
            if stop.code in (None, 0):
                raise
            reason = str(stop.code).removeprefix("compile failed:\n")
            raise SystemExit(f"{refusal}{suffix}{reason}") from None
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
    return any(line.lstrip().startswith((FIELD, DIVISION_FIELD)) for line in report.splitlines())


def replayable(report):
    """A report carrying the lines replays only under the plain buffer schemas, policy enabled."""
    from data_buffer_profile import SCHEMA as DATA_BUFFER_SCHEMA
    from match_evidence import STACK_BUFFER_SCHEMA
    verdicts = [line for line in report.splitlines() if line.startswith("* verification:")]
    return POLICY.enabled and verdicts in ([f"* verification: `{DATA_BUFFER_SCHEMA}`"],
                                           [f"* verification: `{STACK_BUFFER_SCHEMA}`"])


def namespace(preprocessed):
    from plausible import strip_comments_and_strings
    reserved = set(names()) | {f"func_{ENTRIES[name]:08X}" for name in names()}
    found = reserved & set(re.findall(r"[A-Za-z_][A-Za-z_0-9]*", strip_comments_and_strings(preprocessed)))
    if found & {NAME, ADDRESSED_NAME}:
        raise ValueError("signed remainder leaf summary requires compiler-emitted __modsi3; "
                         "runtime identifiers cannot occur in preprocessed C")
    if found:
        raise ValueError("division leaf summary requires compiler-emitted runtimes; "
                         "runtime identifiers cannot occur in preprocessed C")


def summaries_class():
    """RuntimeSummaries restricted to the bound runtimes, with per-site operand records (built lazily:
    runtime_summary_profile imports modules that import match)."""
    if not _CLASS:
        from runtime_summary_profile import RuntimeSummaries

        class RemainderLeafSummaries(RuntimeSummaries):
            def __init__(self, rom, mapping, index):
                super().__init__(rom, mapping, index)
                self.records = {}
                self.bound = entries()

            def covers(self, address):
                return type(address) is int and address in self.bound

            def record(self, instructions, edges, address, branches, calls, data):
                """The numeric operand record of every summarised site this walk reached."""
                import owner_runtime_profile as owner
                reached = {site: target for site, target in calls.items()
                           if target in self.bound and site in instructions}
                rows = []
                remainders = {site for site, target in reached.items() if target == ADDRESS}
                if remainders:
                    # Unchanged from the __modsi3-only retry: its records, its refusals.
                    rows += owner.prove_remainders(instructions, edges, address, branches, calls,
                                                   remainders, data)
                others = {site: target for site, target in reached.items() if target != ADDRESS}
                if others:
                    rows += division_records(instructions, edges, address, branches, calls, others, data)
                for offset, kind, *value in rows:
                    entry = [address, offset, kind, *value]
                    if self.records.setdefault(address + offset, entry) != entry:
                        raise ValueError("signed remainder leaf operand records differ between walks of one site")

            def remainder_only(self):
                return set(self.sites.values()) <= {ADDRESS}

            def complete(self):
                missing = sorted(set(self.sites) - set(self.records))
                if missing:
                    raise ValueError("signed remainder leaf site has no numeric operand record: " +
                                     ", ".join(f"0x{site:08X}" for site in missing))

            def evidence(self):
                self.complete()
                if not self.sites:
                    raise ValueError("signed remainder leaf evidence requires a summarised call")
                common = dict(components=[self.components[key] for key in sorted(self.components)],
                              observations=[self.observations[key] for key in sorted(self.observations)],
                              caller_clobbers=["r0", "r1", "r2", "r3", "r12", "lr", "flags"],
                              numeric_equivalence_claim=False, termination_claim=False)
                if self.remainder_only():
                    return dict(schema=SUMMARY_SCHEMA, contract=CONTRACT,
                                sites=[self.records[site] for site in sorted(self.sites)], **common)
                sites = []
                for site in sorted(self.sites):
                    function, offset, kind, *value = self.records[site]
                    sites.append([function, offset, ENTRY_NAMES[self.sites[site]], kind, *value])
                return dict(schema=DIVISION_SUMMARY_SCHEMA, contract=DIVISION_CONTRACT, sites=sites, **common)

            def digest_text(self):
                return json.dumps(self.evidence(), sort_keys=True, separators=(",", ":"))

            def lines(self):
                if not self.sites:
                    return []
                import owner_runtime_profile as owner
                evidence = self.evidence()
                discards = {}
                for row in evidence["observations"]:
                    for register, offset in row["discarded_scratch_aliases"]:
                        discards.setdefault(row["site"], set()).add(f"r{register}=sp{offset:+d}")
                if self.remainder_only():
                    entry = next(row for row in evidence["components"] if row["address"] == ADDRESS)
                    lines = [f"{LINE}`{SUMMARY_SCHEMA}` __modsi3 0x{ADDRESS:08X} ({entry['instructions']} "
                             f"instructions, {entry['body_sha256'][:16]}) and __div0 as a native-proved leaf: "
                             "R0 unknown scalar, R1-R3/R12/LR/flags clobbered, R4-R11/SP restored, no memory "
                             "operand; no local pointer in R0/R1/LR; no remainder value or range"]
                    for function, offset, kind, *value in evidence["sites"]:
                        site = function + offset
                        operands = (f"divisor {value[0]}" if kind == owner.POSITIVE_DIVISOR else
                                    "signed16 dividend, nonzero divisor")
                        lines.append(f"{LINE}call 0x{site:08X} (0x{function:08X}+0x{offset:X}): {operands} "
                                     f"({kind}); dead scratch discarded: "
                                     f"{' '.join(sorted(discards.get(site, ()))) or 'none'}")
                    return lines
                runtimes = sorted({row[2] for row in evidence["sites"]}, key=lambda name: ENTRIES[name])
                parts = []
                for name in runtimes:
                    entry = next(row for row in evidence["components"] if row["address"] == ENTRIES[name])
                    parts.append(f"{name} 0x{ENTRIES[name]:08X} ({entry['instructions']} instructions, "
                                 f"{entry['body_sha256'][:16]})")
                lines = [f"{DIVISION_LINE}`{DIVISION_SUMMARY_SCHEMA}` {', '.join(parts)} and __div0 as "
                         "native-proved leaves: R0 unknown scalar, R1-R3/R12/LR/flags clobbered, R4-R11/SP "
                         "restored, no memory operand; no local pointer in R0/R1/LR; no quotient or "
                         "remainder value or range"]
                for function, offset, name, kind, *value in evidence["sites"]:
                    site = function + offset
                    lines.append(f"{DIVISION_LINE}call 0x{site:08X} (0x{function:08X}+0x{offset:X}) {name}: "
                                 f"{operand_text(kind, value)} ({kind}); dead scratch discarded: "
                                 f"{' '.join(sorted(discards.get(site, ()))) or 'none'}")
                return lines

        _CLASS.append(RemainderLeafSummaries)
    return _CLASS[0]


ENTRY_NAMES = {entry: name for name, entry in ENTRIES.items()}


def operand_text(kind, value):
    import owner_runtime_profile as owner
    if kind in (owner.POSITIVE_DIVISOR, NONZERO_DIVISOR):
        return f"divisor {value[0]}"
    if kind == owner.SIGNED16_OPERANDS:
        return "signed16 dividend, nonzero divisor"
    raise ValueError("division leaf operand record has an unknown kind")


def constant_states(instructions, edges, address, branches, calls, data):
    """owner_runtime_profile.prove_remainders' constant pass: converged register constants per instruction.

    MOV, ADD/SUB immediate, LSL immediate and PC literals outside the typed domain
    (owner_runtime_profile.constant_result); a fact survives a join only when every
    incoming path agrees; an external call erases r0-r3, r12 and LR, a local BL LR only.
    """
    import owner_runtime_profile as owner
    from capstone.arm import (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    clobbered = (ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    states, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        instruction = instructions[site]
        incoming = states[site]
        outgoing = dict(incoming)
        if site in branches:
            outgoing.pop(ARM_REG_LR, None)
        elif site in calls:
            for register in clobbered:
                outgoing.pop(register, None)
        else:
            _, written = instruction.regs_access()
            for register in written:
                outgoing.pop(register, None)
            value = owner.constant_result(instruction, incoming, address, data)
            if value is not None:
                outgoing[instruction.operands[0].reg] = value
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError("division CFG leaves exact instruction boundaries")
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: value for register, value in previous.items() if outgoing.get(register) == value}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError("division proof does not cover every reached instruction")
    return states


def division_records(instructions, edges, address, branches, calls, sites, data):
    """One operand record per summarised __divsi3, __udivsi3 or __umodsi3 site of this walk.

    __divsi3: a CFG constant in r1 in [1, 0x7FFFFFFF] (no zero divisor, no INT_MIN / -1 for any
    dividend), else modsi3_profile.prove_operands' signed16 r0 and nonzero r1.  __udivsi3 and
    __umodsi3: a CFG constant in r1 in [1, 0xFFFFFFFF].  Anything else refuses.
    """
    import modsi3_profile as modsi3
    import owner_runtime_profile as owner
    from capstone.arm import ARM_REG_R1
    if address not in instructions or set(edges) != set(instructions) or not sites or \
            set(sites) - set(calls) or any(calls[site] != target or ENTRY_NAMES.get(target) not in names()
                                           for site, target in sites.items()):
        raise ValueError("division leaf requires exact reached canonical sites")
    states = constant_states(instructions, edges, address, branches, calls, data)
    records, fallback = {}, set()
    for site, target in sorted(sites.items()):
        value = states[site].get(ARM_REG_R1)
        if ENTRY_NAMES[target] in SIGNED:
            if type(value) is int and 1 <= value <= 0x7FFFFFFF:
                records[site] = [site - address, owner.POSITIVE_DIVISOR, value]
            else:
                fallback.add(site)
        elif type(value) is int and 1 <= value <= 0xFFFFFFFF:
            records[site] = [site - address, NONZERO_DIVISOR, value]
        else:
            raise ValueError(f"unsigned division leaf requires a CFG-proven nonzero constant in r1 at {site:08X}")
    if fallback:
        modsi3.prove_operands(instructions, edges, address, fallback)
        records.update({site: [site - address, owner.SIGNED16_OPERANDS] for site in fallback})
    return [records[site] for site in sorted(records)]


def is_summaries(value):
    return bool(_CLASS) and type(value) is _CLASS[0]


def summaries(rom, mapping, index):
    if not active() or any(type(value) is not bytes for value in (rom, mapping, index)):
        raise ValueError("signed remainder leaf summaries require the active policy and exact snapshots")
    return summaries_class()(rom, mapping, index)


def require_summarised(proof, calls):
    """The retry's admitted proof summarised every linked runtime site of the owner."""
    owned = {site for site, target in calls.items() if target in entries()}
    summary = getattr(proof, "runtime_summaries", None)
    if not owned or not is_summaries(summary) or not owned <= set(summary.sites):
        raise ValueError("signed remainder leaf summary requires the plain stack-argument buffer proof "
                         "at every compiler __modsi3 call")
    summary.complete()
