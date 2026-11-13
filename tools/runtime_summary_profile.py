"""Canonical division runtimes as summarised leaf calls in bounded-buffer walks.

The selector `bounded-buffer-runtime-summaries-v1` keeps every existing
named-data bounded-buffer rule and adds one thing: a direct Thumb BL to the
exact entry of a pinned canonical division runtime is treated as a leaf with a
proved effect, instead of being refused as an unproved buffer callee.

What is proved here, freshly on every run, from the ROM and both indexes:

* identity: the complete spans of `__divsi3` (0x081426B8), `__modsi3`
  (0x08142950), `__udivsi3` (0x08142AB0), `__umodsi3` (0x08142B28) and the
  shared divide-by-zero hook `__div0` (0x0814274C) are SHA-256 pinned, exactly
  and uniquely mapped Thumb spans (the existing per-runtime identity checks);
* closure: the existing native ABI interpreter walks every reachable path of
  each runtime, including the zero-divisor path through `__div0` (a bare
  `mov pc, lr`); every path returns to the entry LR with R4-R11 and SP
  restored, the only call is that hook, and there is no external write or
  incoming stack read;
* no memory access at all: every decoded instruction of every component is
  checked to have no memory operand and no LDM/STM; PUSH/POP of the runtime's
  own balanced frame below the caller's SP is the only memory traffic.

The summary the caller walk applies at such a call:

* R0 returns an unconstrained value (R1 is scratch for the remainder forms
  too); R1-R3, R12, LR and the flags are clobbered and every caller fact about
  them is dropped; no constant, range or alias is exported;
* the caller's frame is neither read nor written, so stack-passed pointer
  slots and pointer-bearing words are untouched;
* R4-R11 are preserved, so aliases held there survive the call.

Refused: any tracked local stack pointer in R0, R1 or LR at the call (an
operand pointer must never be laundered into an "unknown scalar"),
word-provenance and callee-frame contexts, calls to anything other than the
four exact entries, and runtime addresses reached through literals or data
addends.  A dead pointer left in R2, R3 or R12 is discarded only when the
native walk proves the runtime never reads that register before writing it
AND writes it on every path to every return (divide-by-zero included), so the
pointer is overwritten unread; otherwise it is refused.  For the pinned bytes
only R3 of `__modsi3` qualifies.  Each discard is listed in the report.

Not proved: the numerical quotient or remainder, any bound on it, definedness
of C division by zero, or termination (partial correctness only, as for every
other ordinary-call summary).  A quotient used as an index is an unknown
scalar and must pass the existing buffer index checks on its own.
"""
import hashlib
import json
from pathlib import Path

import bios_fast_fill_source_profile as fast_fill
import named_data_buffer_profile as named

SELECTOR = named.RUNTIME_SUMMARY_SELECTOR
SCHEMA = named.RUNTIME_SUMMARY_SCHEMA
FAST_FILL_SELECTOR = named.RUNTIME_SUMMARY_FAST_FILL_SELECTOR
FAST_FILL_SCHEMA = named.RUNTIME_SUMMARY_FAST_FILL_SCHEMA
SUMMARY_SCHEMA = 'thumb-canonical-division-runtime-leaf-summary-v1'
CONTROL_FLOW = ('complete Thumb owner with typed data literals, ROM-proved bounded buffer callees '
                'and native-proved canonical division runtime leaf summaries')
FAST_FILL_CONTROL_FLOW = (named.MIXED_FAST_FILL_CONTROL_FLOW +
                          '; native-proved canonical division runtime leaf summaries')
CONTRACT = ('exact SHA-pinned canonical __divsi3/__modsi3/__udivsi3/__umodsi3 entries and the shared '
            '__div0 hook; native proof of every reachable path including divide-by-zero: returns to the '
            'entry LR with R4-R11 and SP restored, no memory operand or block transfer, no external write '
            'or incoming stack read; caller summary: R0 unknown scalar, R1-R3/R12/LR/flags clobbered, '
            'caller frame untouched; no tracked local pointer in R0/R1/LR; a pointer in R2/R3/R12 is refused '
            'unless that register is proved written before any read and on every path to every return, '
            'when it is discarded unread; no numeric quotient, '
            'remainder, range, division-by-zero definedness or termination theorem')
ZERO = 0x0814274C
ENTRIES = {'__divsi3': 0x081426B8, '__modsi3': 0x08142950,
           '__udivsi3': 0x08142AB0, '__umodsi3': 0x08142B28}
FAMILY = {address: name for name, address in ENTRIES.items()}
# A source may name a runtime only as the compiler emits it or by its exact
# addressed entry; both resolve to one pinned entry and the report keeps the name.
NAMES = {**ENTRIES, **{f'func_{address:08X}': address for address in ENTRIES.values()}}
COMPILER_NAMES = tuple(ENTRIES)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def covers(address):
    return type(address) is int and address in FAMILY


def scratch_inputs(decoded, start):
    """Prove R2, R3 and R12 are never read before written; return those written on every path.

    The first part means the pinned runtimes compute only from R0/R1.  The
    returned set holds the scratch registers that are definitely overwritten
    at every reached return: only a caller pointer in one of those is gone
    after the call.  Any other scratch register may still hold the caller's
    value (for example on the divide-by-zero path), so a pointer there is refused.
    """
    import match
    scratch = frozenset((match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3, match.ARM_REG_R12))
    # Caller R4-R11 may only be saved by PUSH, never copied into a result
    # register; SP and LR only drive PUSH/POP, the BL and the return.
    saved = frozenset(range(match.ARM_REG_R0 + 4, match.ARM_REG_R0 + 12))
    control = frozenset((match.ARM_REG_SP, match.ARM_REG_LR))
    by_address = {item.address: item for item in decoded}

    def number(register):  # architectural order: PUSH/POP use the lowest register at the lowest address
        return {match.ARM_REG_SP: 13, match.ARM_REG_LR: 14, match.ARM_REG_PC: 15}.get(
            register, register - match.ARM_REG_R0)

    # State: registers holding a runtime-written value, and the provenance of
    # each pushed word (top first): False when it saved a caller R4-R11 or LR.
    # POP restores that provenance, so popping a saved caller R4 still counts
    # as the caller's value, while popping a pushed runtime R0 into R4 does not.
    states, pending, returns = {start: (frozenset(), ())}, [start], {}
    while pending:
        site = pending.pop()
        item = by_address.get(site)
        if item is None:
            raise ValueError('runtime summary scratch walk leaves its pinned body')
        defined, stack = states[site]
        read, written = item.regs_access()
        operands = item.operands
        registers = [operand.reg for operand in operands if operand.type == match.ARM_OP_REG]
        if (set(read) & scratch) - defined:
            raise ValueError('runtime summary component reads a scratch register before writing it')
        returning = item.mnemonic == 'bx' or item.mnemonic == 'pop' and match.ARM_REG_PC in registers or \
            item.mnemonic == 'mov' and registers == [match.ARM_REG_PC, match.ARM_REG_LR]
        if item.mnemonic not in ('push', 'pop', 'bl') and not returning and \
                ((set(read) & saved) - defined or set(read) & control):
            raise ValueError('runtime summary component reads a caller register outside its frame protocol')
        if item.mnemonic == 'push':
            # A word is the caller's when it saves an unwritten caller R4-R11 or LR.
            stack = tuple(not (register in saved | {match.ARM_REG_LR} and register not in defined)
                          for register in sorted(registers, key=number)) + stack
        elif item.mnemonic == 'pop':
            ordered = sorted(registers, key=number)
            if len(ordered) > len(stack):
                raise ValueError('runtime summary scratch walk pops outside its pushed words')
            for register, runtime_value in zip(ordered, stack):
                defined = defined | {register} if runtime_value else defined - {register}
            stack = stack[len(ordered):]
        else:
            defined = defined | (set(written) & (scratch | saved))
        if item.mnemonic == 'bl':
            successors = (site + item.size,)  # the only callee is the separately checked zero hook
        elif item.id == match.ARM_INS_B:
            if len(operands) != 1 or operands[0].type != match.ARM_OP_IMM:
                raise ValueError('runtime summary scratch walk found an unresolved branch')
            successors = (operands[0].imm,) + (() if item.cc in (match.ARM_CC_AL, match.ARM_CC_INVALID) else
                                                (site + item.size,))
        elif returning or item.mnemonic == 'mov' and registers and registers[0] == match.ARM_REG_PC:
            successors = ()
            returns[site] = defined & scratch
        elif match.CS_GRP_JUMP in item.groups or match.CS_GRP_CALL in item.groups or \
                match.CS_GRP_INT in item.groups or item.mnemonic in ('bkpt', 'svc', 'udf', 'blx'):
            raise ValueError('runtime summary scratch walk found an unsupported transfer')
        else:
            successors = (site + item.size,)
        for successor in successors:
            if successor in states and states[successor][1] != stack:
                raise ValueError('runtime summary scratch walk joins different pushed words')
            merged = (defined if successor not in states else states[successor][0] & defined, stack)
            if states.get(successor) != merged:
                states[successor] = merged
                pending.append(successor)
    if not returns:
        raise ValueError('runtime summary scratch walk reached no return')
    return frozenset.intersection(*returns.values())


class RuntimeSummaries:
    """Prove each actually-called runtime family once; record every summarised site."""

    def __init__(self, rom, mapping, index):
        if any(type(value) is not bytes for value in (rom, mapping, index)):
            raise ValueError('runtime summaries require immutable ROM and index snapshots')
        self.rom, self.mapping, self.index = rom, mapping, index
        self.components = {}
        self.overwritten = {}
        self.families = set()
        self.sites = {}
        self.observations = {}

    @staticmethod
    def covers(address):
        return covers(address)

    def prove(self, target):
        import canonical_integer_scalar_inventory as integer
        import match
        if not covers(target):
            raise ValueError('runtime summary requires an exact canonical division entry')
        family = FAMILY[target]
        if family in self.families:
            return
        closures, frames, _ = integer.prove_called_closures(self.rom, self.mapping, self.index, {family})
        end = integer.SPECS[family][0]
        if set(closures) != {target, ZERO} or set(frames) != {target, ZERO}:
            raise ValueError('runtime summary closure differs from the exact entry and zero hook')
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        for start, stop in ((target, end), (ZERO, ZERO + 2)):
            body = self.rom[start - match.ROM_BASE:stop - match.ROM_BASE]
            decoded = list(decoder.disasm(body, start))
            if sum(item.size for item in decoded) != len(body) or any(
                    item.mnemonic.startswith(('ldm', 'stm', 'ldr', 'str')) or
                    any(operand.type == match.ARM_OP_MEM for operand in item.operands)
                    for item in decoded):
                raise ValueError('runtime summary component has a memory operand or undecoded byte')
            proof, frame = closures[start], frames[start]
            if proof['writes'] or proof['stack_reads'] or frame['caller_memory_writes'] or \
                    frame['caller_stack_reads'] or frame['restores'] != 'r4-r11,sp,entry-lr':
                raise ValueError('runtime summary component has caller-visible effects')
            overwritten = scratch_inputs(decoded, start)
            if start == target:
                self.overwritten[target] = overwritten
            record = dict(address=start, end=stop, body_sha256=sha(body), instructions=len(decoded),
                          entry_inputs='r0,r1 only (r2,r3,r12 never read before written)',
                          scratch_overwritten_on_every_return=sorted(
                              register - match.ARM_REG_R0 for register in overwritten),
                          returns=list(proof['returns']), restores=frame['restores'],
                          maximum_additional_stack_bytes=frame['maximum_additional_stack_bytes'])
            if self.components.setdefault(start, record) != record:
                raise ValueError('runtime summary shared zero-hook proofs differ')
        self.families.add(family)

    def observe(self, site, target):
        """A summarised BL in the root or an inspected callee, seen by the CFG walk."""
        self.prove(target)
        if type(site) is not int or self.sites.setdefault(site, target) != target:
            raise ValueError('runtime summary site is ambiguous')

    def call(self, proof, address, arguments, stack, incoming, protected, *,
             site=None, words=None, watched=(), **context):
        """Apply the summary inside BufferCallProof.check_arguments."""
        import match
        self.prove(address)
        if type(site) is not int:
            raise ValueError('runtime summary requires an actual direct call site')
        scratch = {match.ARM_REG_R0 + 2, match.ARM_REG_R0 + 3, match.ARM_REG_R12}
        if set(arguments) - scratch:
            raise ValueError('runtime summary refuses a tracked local pointer in R0, R1 or LR')
        if set(arguments) - self.overwritten[address]:
            raise ValueError('runtime summary refuses a scratch pointer the runtime may return unchanged')
        if words or proof.word_provenance or proof.callee_frames or proof.single_word_stores:
            raise ValueError('runtime summary excludes word-provenance and callee-frame contexts')
        saved = set(range(match.ARM_REG_R0 + 4, match.ARM_REG_R0 + 12))
        if set(watched) - saved:
            raise ValueError('runtime summary preserves only R4-R11 live aliases')
        for offset in incoming.values():
            proof.validate_pointer_value(offset, stack)
        self.observe(site, address)
        record = dict(site=site, target=address, name=FAMILY[address],
                      discarded_scratch_aliases=sorted([register - match.ARM_REG_R0, offset]
                                                       for register, offset in arguments.items()),
                      untouched_incoming_slots=sorted([slot, offset] for slot, offset in incoming.items()),
                      protected_slots=sorted(protected),
                      preserved_alias_registers=sorted(register - match.ARM_REG_R0 for register in watched))
        self.observations[json.dumps(record, sort_keys=True)] = record
        # The native proof covers R4-R11 restoration; nothing is trusted.
        proof.callee_clobbers[address] = frozenset()
        proof.callee_trusted[address] = frozenset()
        return proof.word_result({}, {})

    def manifest(self):
        if not self.sites:
            raise ValueError('runtime summary profile requires an actual summarised runtime call')
        import importlib
        producers = ('runtime_summary_profile', 'match', 'owner_admission_profile', 'named_data_buffer_profile',
                     'bios_fast_fill_source_profile', 'canonical_integer_scalar_inventory',
                     'software_double_profile', 'software_float_profile', 'div_only_ordinary_inventory',
                     'zero_aware_unsigned_quotient_inventory', 'udiv_constant_choices_inventory',
                     'umod_only_ordinary_inventory', 'unsigned_remainder_closure_inventory',
                     'divsi3_profile', 'modsi3_profile', 'umodsi3_profile', 'local_long_branch_profile')
        return dict(schema=SUMMARY_SCHEMA, contract=CONTRACT,
            families=sorted(self.families),
            components=[self.components[key] for key in sorted(self.components)],
            sites=[[site, FAMILY[target]] for site, target in sorted(self.sites.items())],
            observations=[self.observations[key] for key in sorted(self.observations)],
            caller_clobbers=['r0', 'r1', 'r2', 'r3', 'r12', 'lr', 'flags'],
            result='unconstrained scalar in r0; no constant, range or alias exported',
            numeric_equivalence_claim=False, termination_claim=False,
            source_sha256={name + '.py': sha(Path(importlib.import_module(name).__file__).read_bytes())
                           for name in producers})


class RuntimeSummaryBufferProof(named.NamedDataBufferProof):
    """Existing named-data buffer rules plus native-proved runtime leaf summaries."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.runtime_summaries = RuntimeSummaries(rom, mapping, index)

    def manifest(self):
        return self.runtime_summaries.manifest()


class RuntimeSummaryFastFillProof(fast_fill.MixedFastFillSourceProof):
    """The unchanged mixed CpuFastSet root proof plus the same runtime summaries."""

    def __init__(self, rom, mapping, index, objects):
        super().__init__(rom, mapping, index, objects)
        self.runtime_summaries = RuntimeSummaries(rom, mapping, index)

    def manifest(self):
        return self.runtime_summaries.manifest()


SELECTORS = (SELECTOR, FAST_FILL_SELECTOR)
SCHEMAS = {SELECTOR: SCHEMA, FAST_FILL_SELECTOR: FAST_FILL_SCHEMA}
CONTROL_FLOWS = {SELECTOR: CONTROL_FLOW, FAST_FILL_SELECTOR: FAST_FILL_CONTROL_FLOW}
PROOFS = {SELECTOR: RuntimeSummaryBufferProof, FAST_FILL_SELECTOR: RuntimeSummaryFastFillProof}
