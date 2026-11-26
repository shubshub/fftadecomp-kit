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
SIGN_GUARDED_DIVISOR = "nonzero-not-minus-one-divisor"
REMAINDER_KINDS = ("positive-signed32-constant-divisor", "signed16-dividend-nonzero-divisor")
DIVISION_CONTRACT = (
    "compiler __divsi3/__modsi3/__udivsi3/__umodsi3 at their SHA-pinned entries 0x081426B8/0x08142950/"
    "0x08142AB0/0x08142B28 with the shared __div0 hook; native proof of every reachable path: returns to the "
    "entry LR with R4-R11 and SP restored, no memory operand or block transfer; caller summary: R0 unknown "
    "scalar, R1-R3/R12/LR/flags clobbered, caller frame untouched; no tracked local pointer in R0/R1/LR, a "
    "pointer in R2/R3/R12 discarded only where every return overwrites it; every site has a numeric operand "
    "record (signed: positive signed32 constant divisor, signed16 dividend and nonzero divisor, or a divisor "
    "proved nonzero and not -1 from zero-compare branches and negation; unsigned: nonzero u32 constant "
    "divisor); no quotient or remainder value, range or termination theorem")
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


class SignPolicy:
    """Signed divisors proved nonzero and not -1 by zero-compare branches and negation
    (``sign_guarded_sites``); ``enabled = False`` drops that record kind."""

    enabled = True


SIGN = SignPolicy()


class EvidencePolicy:
    """A summarised runtime site as the buffer proof's inspected call (``summarised_evidence``)."""

    enabled = True


EVIDENCE = EvidencePolicy()


def summarised_evidence(proof):
    """Whether, inside the retry, the proof summarised a runtime site.

    The buffer proofs' "inspected buffer call" requirement says which schema a report gets and
    turns on the gates keyed on buffer evidence (the complete mapped span, the data-buffer
    composition, DMA fill records, the return-scratch refusal).  It is not what proves the walk:
    the stack-argument proof walks the whole owner either way.  An owner whose only proved callee
    is a summarised runtime therefore has buffer evidence here, and every such gate applies.
    """
    summary = getattr(proof, "runtime_summaries", None)
    return EVIDENCE.enabled and active() and is_summaries(summary) and bool(summary.sites)


def summary_only_evidence(proof):
    """The proof's buffer evidence is a summarised runtime site and nothing else."""
    return summarised_evidence(proof) and not proof.dependencies and proof.stack_index_retry is None


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
                    # The __modsi3-only retry's records and refusals first; a site neither of its
                    # records covers may still have a sign-guarded divisor.
                    try:
                        rows += owner.prove_remainders(instructions, edges, address, branches, calls,
                                                       remainders, data)
                    except ValueError as error:
                        rows += signed_fallback(instructions, edges, address, branches, calls,
                                                remainders, data, error)
                others = {site: target for site, target in reached.items() if target != ADDRESS}
                if others:
                    rows += division_records(instructions, edges, address, branches, calls, others, data)
                for offset, kind, *value in rows:
                    entry = [address, offset, kind, *value]
                    if self.records.setdefault(address + offset, entry) != entry:
                        raise ValueError("signed remainder leaf operand records differ between walks of one site")

            def remainder_only(self):
                return set(self.sites.values()) <= {ADDRESS} and \
                    all(record[2] in REMAINDER_KINDS for record in self.records.values())

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
                        operands = operand_text(kind, value)
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
    if kind == SIGN_GUARDED_DIVISOR:
        return "divisor nonzero and not -1"
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
        try:
            modsi3.prove_operands(instructions, edges, address, fallback)
        except ValueError as error:
            records.update({row[0] + address: row for row in signed_fallback(
                instructions, edges, address, branches, calls, fallback, data, error)})
        else:
            records.update({site: [site - address, owner.SIGNED16_OPERANDS] for site in fallback})
    return [records[site] for site in sorted(records)]


def signed_fallback(instructions, edges, address, branches, calls, sites, data, error):
    """Per-site records for signed sites the all-site proofs refused, or that refusal again.

    A positive constant divisor or a signed16 dividend with a nonzero divisor keeps its record;
    any other site needs a divisor that sign_guarded_sites proves nonzero and not -1.  A site
    with none of the three re-raises the original refusal unchanged.
    """
    import modsi3_profile as modsi3
    import owner_runtime_profile as owner
    from capstone.arm import ARM_REG_R1
    if not (SIGN.enabled and DIVISION.enabled):
        raise error
    try:
        states = constant_states(instructions, edges, address, branches, calls, data)
        guarded = sign_guarded_sites(instructions, edges, address, sites)
    except ValueError:
        raise error from None
    rows = []
    for site in sorted(sites):
        value = states[site].get(ARM_REG_R1)
        if type(value) is int and 1 <= value <= 0x7FFFFFFF:
            rows.append([site - address, owner.POSITIVE_DIVISOR, value])
            continue
        try:
            modsi3.prove_operands(instructions, edges, address, {site})
        except ValueError:
            if site not in guarded:
                raise error from None
            rows.append([site - address, SIGN_GUARDED_DIVISOR])
        else:
            rows.append([site - address, owner.SIGNED16_OPERANDS])
    return rows


def sign_guarded_sites(instructions, edges, address, sites):
    """The sites whose r1 is proved nonzero and not -1 on every path, from the code alone.

    A forward must-analysis over the closed CFG with four register facts: nonzero, >= 0, < 0
    and not -1.  Facts come from immediate moves, from an adjacent `cmp rN, #0` (or a register
    known to be 0) whose conditional branch has it as sole predecessor (EQ/NE give nonzero on
    the unequal edge; GE/LT/GT/LE give the signed facts on each edge; coincident destinations
    give nothing), and from `rsbs rD, rN, #0`: nonzero stays nonzero, and the negation of a
    negative value is not -1 (it is positive, or INT_MIN when rN is INT_MIN).  >= 0 implies not
    -1 and < 0 implies nonzero.  Copies (MOV, ADD #0) keep facts; any other write and every
    call's caller-clobbered registers drop them; joins keep only facts every path has.  No
    range is derived: an rsbs of a value >= 0 may be -1 and gets no such fact.
    """
    from capstone import CS_GRP_CALL
    from capstone.arm import (ARM_CC_AL, ARM_CC_INVALID, ARM_CC_EQ, ARM_CC_NE, ARM_CC_LT, ARM_CC_GE,
                              ARM_CC_GT, ARM_CC_LE, ARM_INS_B, ARM_INS_CMP, ARM_OP_IMM, ARM_OP_REG,
                              ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    clobbered = frozenset((ARM_REG_R0, ARM_REG_R1, ARM_REG_R2, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR))
    if address not in instructions or set(edges) != set(instructions) or set(sites) - set(instructions):
        raise ValueError("sign-guarded divisors require exact reached sites")

    def closed(facts):
        facts = set(facts)
        if "lt0" in facts:
            facts.add("nz")
        if "ge0" in facts:
            facts.add("nm1")
        return frozenset(facts)

    def constant(value):
        value &= 0xFFFFFFFF
        return closed({("const", value)} | ({"nz"} if value else set()) |
                      ({"ge0"} if value < 0x80000000 else {"lt0"}) | ({"nm1"} if value != 0xFFFFFFFF else set()))

    predecessors = {current: set() for current in instructions}
    for current, successors in edges.items():
        for successor in successors:
            predecessors[successor].add(current)
    states, pending = {address: {}}, [address]
    while pending:
        current = pending.pop()
        instruction = instructions[current]
        incoming = states[current]
        outgoing = dict(incoming)
        operands = instruction.operands
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        if CS_GRP_CALL in instruction.groups:
            outgoing = {register: facts for register, facts in outgoing.items() if register not in clobbered}
        else:
            _, written = instruction.regs_access()
            outgoing = {register: facts for register, facts in outgoing.items() if register not in written}
            if unconditional and instruction.size == 2 and operands and operands[0].type == ARM_OP_REG:
                destination, mnemonic = operands[0].reg, instruction.mnemonic
                source = None
                if mnemonic in ("mov", "movs") and len(operands) == 2:
                    if operands[1].type == ARM_OP_REG:
                        source = operands[1].reg
                    elif operands[1].type == ARM_OP_IMM:
                        outgoing[destination] = constant(operands[1].imm)
                elif mnemonic in ("add", "adds") and len(operands) == 3 and operands[1].type == ARM_OP_REG and \
                        operands[2].type == ARM_OP_IMM and operands[2].imm == 0:
                    source = operands[1].reg
                elif mnemonic in ("rsbs", "negs") and operands[1].type == ARM_OP_REG and (
                        len(operands) == 2 or len(operands) == 3 and operands[2].type == ARM_OP_IMM and
                        operands[2].imm == 0):
                    before = incoming.get(operands[1].reg, frozenset())
                    known = [fact[1] for fact in before if isinstance(fact, tuple)]
                    if known:
                        outgoing[destination] = constant(-known[0])
                    else:
                        facts = ({"nz"} if "nz" in before else set()) | ({"nm1"} if "lt0" in before else set())
                        if facts:
                            outgoing[destination] = closed(facts)
                if source is not None and source in incoming:
                    outgoing[destination] = incoming[source]
        guarded, taken_facts, fallthrough_facts = None, set(), set()
        if instruction.id == ARM_INS_B and instruction.size == 2 and \
                instruction.cc in (ARM_CC_EQ, ARM_CC_NE, ARM_CC_LT, ARM_CC_GE, ARM_CC_GT, ARM_CC_LE) and \
                predecessors[current] == {current - 2} and current - 2 in instructions:
            comparison = instructions[current - 2]
            compared = comparison.operands
            if comparison.id == ARM_INS_CMP and comparison.size == 2 and \
                    comparison.cc in (ARM_CC_AL, ARM_CC_INVALID) and len(compared) == 2 and \
                    compared[0].type == ARM_OP_REG and (
                        compared[1].type == ARM_OP_IMM and compared[1].imm == 0 or
                        compared[1].type == ARM_OP_REG and
                        ("const", 0) in states[current - 2].get(compared[1].reg, frozenset())):
                guarded = compared[0].reg
                taken_facts, fallthrough_facts = {
                    ARM_CC_EQ: (set(), {"nz"}), ARM_CC_NE: ({"nz"}, set()),
                    ARM_CC_GE: ({"ge0"}, {"lt0"}), ARM_CC_LT: ({"lt0"}, {"ge0"}),
                    ARM_CC_GT: ({"ge0", "nz"}, set()), ARM_CC_LE: (set(), {"ge0", "nz"})}[instruction.cc]
        target = operands[0].imm if guarded is not None else None
        fallthrough = current + instruction.size
        for successor in edges[current]:
            facts = dict(outgoing)
            if guarded is not None and target != fallthrough:
                extra = taken_facts if successor == target else fallthrough_facts
                if extra:
                    facts[guarded] = closed(facts.get(guarded, frozenset()) | extra)
            previous = states.get(successor)
            merged = facts if previous is None else {
                register: previous[register] & facts[register] for register in previous
                if register in facts and previous[register] & facts[register]}
            if merged != previous:
                states[successor] = merged
                pending.append(successor)
    return {site for site in sites if {"nz", "nm1"} <= states.get(site, {}).get(ARM_REG_R1, frozenset())}


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
