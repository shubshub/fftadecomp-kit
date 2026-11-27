"""GBA BIOS SWI wrappers as summarised calls in the plain bounded-buffer walk (#192).

The plain direct-call path walks a callee whenever a tracked pointer into the
owner's frame is live at the call (in a register or as a pointer-bearing frame
word).  A four- or six-byte BIOS wrapper (`svc N; bx lr`) cannot be walked: the
routine is not in the ROM.  This module replaces that walk, for eight exact
indexed wrappers, by a summary whose behaviour is a stated premise, as in every
existing BIOS contract, and whose memory spans are proved from the owner's own
code.  It is constructed by the plain path (`BufferCallProof(...,
bios_wrappers=True)`) and by the restoring owner (`owner_runtime_profile.verify`),
which binds its complete owner CFG first (`bind_owner`) so that each memory call
is discharged where its frame proof makes it; no subclass uses it.

Identity: the call is an actual direct BL site; the target is one of the
entries below; `BufferCallProof.span` gives its complete, unique,
non-overlapping indexed Thumb row, and those bytes equal the pinned wrapper.

Scalar wrappers (ArcTan2, Div, Div remainder, DivArm remainder, Sqrt), at any
walk depth: no tracked local pointer in R0-R3, R12 or LR.  Pointer-bearing
frame words are validated and left as they are.  No alias is returned.

Memory wrappers (CpuSet, CpuFastSet, BgAffineSet), at the owner's own call
only (walk depth 0), with local pointers only in R0 (source) and R1
(destination), or in R3 or R12, which no memory routine takes as an argument
(GBATEK: R0-R2 only; a stale address left by an earlier call, as 0801DD00
leaves one in R3 for 080E0824's CpuSet).  The call is recorded with the walk's
frame at the call, and discharged when the owner's CFG is complete (`finish`,
called by `verify_leaf_instructions` for the owner):

* R2 is known from `bios_cpuset_fill_profile.prove_bits` over the verifier's
  own owner CFG, with its zero-extension rules (the restoring owner's CFG is its
  native inventory graph, where a same-owner BL jump counts as a call: it only
  loses facts);
* CpuSet: count is bits 0-20, the unit is 4 bytes if bit 26 is set and 2
  otherwise, bit 24 selects a fill from one source unit; CpuFastSet moves
  32-bit units in blocks of eight; BgAffineSet reads `count` 20-byte records
  and writes `count` 16-byte records (GBATEK);
* a local fill source (bit 24 proved set) is one unit: 2 bytes when bit 26 is
  known clear (CpuSet), otherwise one aligned word;
* a local destination, or a local source not proved to be a fill source,
  needs the whole control word: no reserved bit, a count of at least 1 (a
  multiple of 8 for CpuFastSet); BgAffineSet needs an exact count in 1..255
  and word-aligned records;
* every unit lies in allocated local words; a source span holds no
  pointer-bearing word; a destination span holds no pointer-bearing or
  return-carrying word; a local source and a local destination are disjoint;
* each register that carried a local pointer into the call is written before
  any read, call, interrupt or return on every path from the call
  (`match.stack_alias_overwritten_before_use`), where a call counts as the write
  only if it is an unconditional direct BL to a mapped callee whose own bytes
  write that register before any read, call, interrupt, return or cycle on every
  path from its entry (`dead_register.prove` with `thumb_step`, the walk of the
  dead stack-address call rule).  The record names each such call, the callee's
  span end, the SHA-256 of its bytes, its killing writes and the states proved,
  and the report states each on a `* buffer BIOS call kill:` line after the
  manifest (none without such a call, so every other report is unchanged);
* a local address in R3 or R12 gives the routine no access under the GBATEK
  premise, since no documented argument carries it, and is proved dead by the
  same kill proof (R3 may also be killed by a call; R12 never is, as the
  callee proof covers R0-R3 only).  Whether the routine leaves it in place is
  not assumed either way: nothing reads the register before it is written.
  The record names each such register and its local offset (`non_argument`),
  the register is in `killed`, and the report states each on a
  `* buffer BIOS non-argument register:` line after the manifest, since the
  contract below names R0 and R1 only; the outputs premise of such a report
  (`OUTPUTS_NON_ARGUMENT`) allows a frame address left in any register that
  carried one in, which trusts strictly less.  None of this appears without
  such a register, so every other report is unchanged.  The rule sits behind
  one policy object (`NON_ARGUMENT_POLICY`): disabled, every local pointer
  outside R0 and R1 refuses as before.

After every summarised call R0-R3, R12 and the flags are unknown scalars and
the frame keeps its facts (no span reaches a word the walk holds a fact
about).  The behaviour of the routines is the GBATEK premise (`PREMISE`); the
registers a routine leaves a frame address in (`OUTPUTS`) and R4-R11
preservation (`TRUSTED`) are trusted, not proved, since GBATEK does not document
them.  Each report that applies a summary states all three verbatim on
`* buffer BIOS premise:` lines, and a loop replay that relies on R4-R11 lists
the wrapper as trusted.  R2's bits rely, as in `BiosFillProof`, on known R4-R11
bits surviving the owner's other calls under the conditional returning ABI.

Not proved: the BIOS routines themselves, any numeric result, termination,
initialization of a source, physical readability, or the extent and nonalias
of an external (non-local) pointer, which gets no claim.
"""
import hashlib
import json

import bios_cpuset_fill_profile as cpuset
import dead_register

SCHEMA = 'gba-bios-swi-wrapper-summaries-v1'
CPUSET = cpuset.ADDRESS
CPUFASTSET = 0x08141868
BGAFFINESET = 0x08141864
# address: (routine, SWI number, exact wrapper bytes), read from the ROM.
SCALAR = {
    0x08141860: ('ArcTan2', 0x0A, bytes.fromhex('0adf7047')),
    0x08141870: ('Div', 0x06, bytes.fromhex('06df7047')),
    0x08141874: ('Div remainder', 0x06, bytes.fromhex('06df081c7047')),
    0x0814187C: ('DivArm remainder', 0x07, bytes.fromhex('07df081c7047')),
    0x08141898: ('Sqrt', 0x08, bytes.fromhex('08df7047')),
}
MEMORY = {
    CPUSET: ('CpuSet', 0x0B, cpuset.WRAPPER),
    CPUFASTSET: ('CpuFastSet', 0x0C, bytes.fromhex('0cdf7047')),
    BGAFFINESET: ('BgAffineSet', 0x0E, bytes.fromhex('0edf7047')),
}
WRAPPERS = {**SCALAR, **MEMORY}
COUNT_MASK = 0x1FFFFF
FILL = 1 << 24
WORDS = 1 << 26
SOURCE_RECORD, DESTINATION_RECORD, MAX_RECORDS = 20, 16, 255
# The premises, each stated verbatim on its own report line.
PREMISE = ('GBATEK (BIOS Functions): each routine returns to its wrapper, preserves SP, and reads and '
           'writes caller memory only through the spans its documented arguments describe (so the '
           'caller frame at or above SP only through those spans)')
OUTPUTS = ('no routine leaves an address of the caller frame in any register except, for a memory '
           'routine, R0 or R1 when that register carried one in; GBATEK documents no output register '
           'of the memory routines, so this is trusted, not proved')
TRUSTED = ('R4-R11 are preserved across each summarised call; nothing of the routine is inspected, so '
           'this is trusted, not proved')
PREMISES = (PREMISE, OUTPUTS, TRUSTED)
# The outputs premise of a manifest with a non-argument register (R3 or R12) that carried a local
# address in: weaker than OUTPUTS, as such a register may keep the address; it is proved dead instead.
OUTPUTS_NON_ARGUMENT = ('no routine leaves an address of the caller frame in any register except, for a memory '
                        'routine, a register that carried one in (R0 or R1, or a non-argument R3 or R12); '
                        'GBATEK documents no output register of the memory routines, so this is trusted, '
                        'not proved')
PREMISES_NON_ARGUMENT = (PREMISE, OUTPUTS_NON_ARGUMENT, TRUSTED)
# The registers no memory routine takes as an argument (GBATEK: R0-R2) that may carry a local
# address into a memory call when the walk proves them dead after it, as numbers 0-12.
NON_ARGUMENT_REGISTERS = (3, 12)


class NonArgumentPolicy:
    """The one policy object of the non-argument rule: ``enabled = False`` restores the refusal of
    every local pointer outside R0 and R1 at a memory wrapper."""
    enabled = True


NON_ARGUMENT_POLICY = NonArgumentPolicy()
CONTRACT = (
    'conditional returning GBA BIOS SWI wrapper summaries: exact indexed wrappers reached by a '
    'direct BL (ArcTan2 0x0A, Div 0x06, Div remainder 0x06, DivArm remainder 0x07, Sqrt 0x08, '
    'CpuSet 0x0B, CpuFastSet 0x0C, BgAffineSet 0x0E) under the premises below; scalar wrappers '
    'take no tracked local pointer in r0-r3, r12 or lr and leave pointer-bearing frame words '
    'untouched; memory wrappers only at the owner\'s own calls, local pointers only in r0 '
    '(source) and r1 (destination), spans from r2 bits proved over the owner CFG, with known bits '
    'in r4-r11 surviving calls under the conditional ordinary returning ABI (CpuSet count '
    'bits 0-20, unit 4 if bit26 else 2, bit24 fill of one source unit, other bits zero; '
    'CpuFastSet 32-bit units, count a multiple of 8; BgAffineSet 1..255 records of 20 source '
    'and 16 destination bytes) inside allocated local words, disjoint, sources off '
    'pointer-bearing words, destinations off pointer-bearing and return-carrying words; each '
    'register that carried a local pointer in is written before any read, call or return; '
    'after the call r0-r3, r12 and the flags are unknown scalars and no alias is returned; '
    'no numeric result, termination, source initialization, physical readability, external '
    'extent or nonalias theorem')


def covers(address):
    return type(address) is int and address in WRAPPERS


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def control_spans(target, source, destination, ones, zeros):
    """The local (offset, bytes, unit) spans the call reads and writes, from R2's known bits."""
    exact = ones | zeros == cpuset.MASK
    if source is None and destination is None:
        return None, None, None, None
    if target == BGAFFINESET:
        if not exact or not 1 <= ones <= MAX_RECORDS:
            raise ValueError('BgAffineSet count is not a proven constant in 1..255')
        return ((None if source is None else (source, SOURCE_RECORD * ones, 4)),
                (None if destination is None else (destination, DESTINATION_RECORD * ones, 4)),
                4, ones)
    fast = target == CPUFASTSET
    if destination is None and ones & FILL:
        # One source unit; an unproved width is a whole aligned word.
        unit = 2 if not fast and zeros & WORDS else 4
        return (source, unit, unit), None, unit, None
    if not exact:
        raise ValueError('BIOS copy source or local destination requires the whole control '
                         'word on every path')
    if ones & ~(COUNT_MASK | FILL | (0 if fast else WORDS)):
        raise ValueError('BIOS control word sets a reserved bit')
    count = ones & COUNT_MASK
    unit = 4 if fast or ones & WORDS else 2
    if count < 1 or fast and count % 8:
        raise ValueError('BIOS control count is zero or not a multiple of eight CpuFastSet words')
    return ((None if source is None else (source, unit if ones & FILL else unit * count, unit)),
            (None if destination is None else (destination, unit * count, unit)), unit, count)


def check_span(span, stack, protected, *, write):
    import match
    offset, size, unit = span
    for start in range(offset, offset + size, unit):
        match.BufferCallProof.access(start, unit, stack)
    if any(offset < word + 4 and word < offset + size for word in protected):
        raise ValueError('BIOS ' + ('destination' if write else 'source') +
                         ' span overlaps a pointer-bearing local word')
    if write and any(stack[slot][0] for slot in range((offset + 4 * len(stack)) // 4,
                                                       (offset + size - 1 + 4 * len(stack)) // 4 + 1)):
        raise ValueError('BIOS destination span overlaps a return-carrying local word')


class BiosWrapperSummaries:
    """Per-proof summaries; every applied summary is an observation bound in the evidence."""

    def __init__(self):
        self.scalar = {}
        self.pending = {}
        self.memory = {}
        # (data, address, instructions, edges) of a complete owner CFG known before the
        # walk (bind_owner), with R2's bit states once a memory call needs them; None
        # leaves every memory call pending until finish.
        self.owner = None
        self.owner_states = None
        # The proof's mapped-span reader, for callees that kill a carried register
        # (set by every call, so that a pending discharge has it), and their entry proofs.
        self.span = None
        self.callee_entries = {}

    def bind_owner(self, data, address, instructions, edges):
        """Discharge each memory call at the owner's own call over this exact CFG.

        For a walk that does not end in verify_leaf_instructions (the restoring owner's
        frame proof), whose CFG is complete before the walk starts.  The checks are
        finish's, on the frame the walk has at the call.
        """
        if self.owner is not None or self.pending or self.memory or type(data) is not bytes or \
                address not in instructions or set(edges) != set(instructions):
            raise ValueError('BIOS wrapper summaries bind one complete owner CFG before any call')
        self.owner = (data, address, instructions, edges)

    @staticmethod
    def covers(address):
        return covers(address)

    def copy(self):
        return dict(self.scalar), dict(self.pending), dict(self.memory)

    def restore(self, state):
        for ledger, saved in zip((self.scalar, self.pending, self.memory), state):
            ledger.clear()
            ledger.update(saved)

    def call(self, proof, address, arguments, stack, incoming, protected, *, site=None,
             constants=None, words=None, **context):
        """Replace the walk of a covered wrapper inside BufferCallProof.check_arguments."""
        try:
            return self._call(proof, address, arguments, stack, incoming, protected, site, words, context)
        except ValueError as error:
            raise ValueError(f'buffer callee 0x{address:08X}: {error}') from error

    def _call(self, proof, address, arguments, stack, incoming, protected, site, words, context):
        import match
        if type(site) is not int:
            raise ValueError('BIOS wrapper summary requires an actual direct call site')
        if words or any(context.values()) or proof.word_provenance or proof.callee_frames or \
                proof.single_word_stores or proof.forwarded_stack_arguments and not proof.default_forwarding:
            raise ValueError('BIOS wrapper summaries exclude word-provenance, callee-frame and '
                             'forwarded-slot contexts')
        # Released forwarded words below SP (forwarded_slot_profile): the BIOS call is trusted under the
        # recorded premise not to read them, and they are handed back unchanged.
        released = {key: arguments[key] for key in match.stale_words(arguments).values()}
        arguments = {key: value for key, value in arguments.items() if key not in released}
        if released:
            if not proof.default_forwarding:
                raise ValueError('released forwarded words reach only the default forwarding proofs')
            proof.forward_trusted_calls.add((0, site, address))
        name, _, wrapper = WRAPPERS[address]
        self.span = proof.span
        data = proof.span(address)
        if data != wrapper:
            raise ValueError(f'BIOS {name} summary requires the exact indexed wrapper bytes')
        if match.ARM_REG_LR in arguments:
            raise ValueError('buffer pointer cannot be passed through the link register')
        for offset in (*arguments.values(), *incoming.values()):
            proof.validate_pointer_value(offset, stack)
        depth = len(proof.active)
        if address in SCALAR:
            if arguments:
                raise ValueError('scalar BIOS wrapper refuses a tracked local pointer in R0-R3, R12 or LR')
            record = dict(site=site, target=address, routine=name, depth=depth,
                          untouched_incoming_slots=sorted([slot, offset] for slot, offset in incoming.items()),
                          pointer_words=sorted(protected))
            self.scalar[canonical(record)] = record
        else:
            if depth:
                raise ValueError("BIOS memory wrapper is summarised only at the owner's own call")
            if not NON_ARGUMENT_POLICY.enabled and set(arguments) - {match.ARM_REG_R0, match.ARM_REG_R0 + 1}:
                raise ValueError('BIOS memory wrapper refuses a local pointer outside R0 and R1')
            others = {register_id(number): number for number in NON_ARGUMENT_REGISTERS}
            if set(arguments) - {match.ARM_REG_R0, match.ARM_REG_R0 + 1} - set(others):
                raise ValueError('BIOS memory wrapper refuses a local pointer outside R0, R1 and the '
                                 'non-argument R3 and R12')
            # (number, offset) of each non-argument register carrying a local address in, proved dead
            # after the call by _discharge.
            non_argument = tuple(sorted((others[register], offset) for register, offset in arguments.items()
                                        if register in others))
            key = (site, address, arguments.get(match.ARM_REG_R0), arguments.get(match.ARM_REG_R0 + 1),
                   tuple(tuple(word) for word in stack), tuple(sorted(protected)), non_argument)
            if self.owner is None:
                self.pending[key] = key
            else:
                code, owner, instructions, edges = self.owner
                if self.owner_states is None:
                    self.owner_states = cpuset.prove_bits(instructions, edges, owner, code,
                                                          zero_extension=True)
                self._discharge(key, code, owner, instructions, self.owner_states)
        # No callee-clobber record: like every uninspected call, R4-R11 survival is
        # trusted under the premise, and a loop replay that relies on it says so.
        proof.dependencies[address] = data
        return proof.word_result(released, {})

    def finish(self, data, address, instructions, edges):
        """Discharge the owner's memory-wrapper calls over its complete verified CFG."""
        pending = sorted((key for key in self.pending if key[0] in instructions), key=repr)
        if not pending:
            return
        states = cpuset.prove_bits(instructions, edges, address, data, zero_extension=True)
        for key in pending:
            try:
                self._discharge(key, data, address, instructions, states)
            except ValueError as error:
                raise ValueError(f'buffer callee 0x{key[1]:08X}: {error}') from error
            del self.pending[key]

    def _discharge(self, key, data, address, instructions, states):
        """Prove one memory call's spans and kills, then record it."""
        import match
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        site, target, source, destination, stack, protected, non_argument = key
        name = MEMORY[target][0]
        instruction = instructions.get(site)
        if instruction is None or instruction.id != match.ARM_INS_BL or instruction.size != 4 or \
                len(instruction.operands) != 1 or instruction.operands[0].imm != target:
            raise ValueError(f'BIOS {name} site is not its direct BL in the owner CFG')
        ones, zeros = states[site].get(match.ARM_REG_R0 + 2, (0, 0))
        spans = control_spans(target, source, destination, ones, zeros)
        if spans[0] is not None:
            check_span(spans[0], stack, protected, write=False)
        if spans[1] is not None:
            check_span(spans[1], stack, protected, write=True)
        if spans[0] is not None and spans[1] is not None and \
                spans[0][0] < spans[1][0] + spans[1][1] and spans[1][0] < spans[0][0] + spans[0][1]:
            raise ValueError('BIOS local source and destination overlap')
        killed = []
        call_kills = []

        def call_kill(call, callee, carried):
            entry = self.callee_entry(callee, carried)
            if entry is not None:
                call_kills.append(dict(entry, site=call, register=carried - match.ARM_REG_R0))
            return entry is not None

        for register, offset in ((0, source), (1, destination), *non_argument):
            if offset is None:
                continue
            if not match.stack_alias_overwritten_before_use(
                    data, address, site + instruction.size, register_id(register), decoder,
                    call_kill=call_kill):
                raise ValueError(f'R{register} carried a local pointer into BIOS {name} and is not '
                                 'written before any read, call or return')
            killed.append(register)
        record = dict(site=site, target=target, routine=name, control=[ones, zeros],
                      source=None if spans[0] is None else list(spans[0][:2]),
                      destination=None if spans[1] is None else list(spans[1][:2]),
                      unit=spans[2], count=spans[3], killed=killed, pointer_words=list(protected))
        if non_argument:
            # Only a record with such a register carries the key, so every other manifest is unchanged.
            record['non_argument'] = [list(pair) for pair in non_argument]
        if call_kills:
            # Only a record that relies on a callee carries the key, so every other manifest is unchanged.
            record['call_kills'] = sorted(call_kills, key=lambda kill: (kill['site'], kill['register']))
        self.memory[canonical(record)] = record

    def callee_entry(self, callee, register):
        """The entry proof that ``callee`` writes ``register`` before any read, call or return, or None."""
        key = (callee, register)
        if key not in self.callee_entries:
            entry = None
            if self.span is not None and register in dead_register.ARGUMENTS:
                try:
                    body = self.span(callee)
                    result = dead_register.prove(
                        callee, {register}, dead_register.thumb_step(callee, body),
                        end='dead register reaches the end of its callee',
                        cycle='dead register callee has a path without its killing write',
                        budget='dead register callee state budget exceeded')
                    entry = dict(callee=callee, end=callee + len(body), body_sha256=dead_register.sha(body),
                                 states=result.states,
                                 kills=sorted([site, written - dead_register.ARM_REG_R0]
                                              for site, written in result.kills))
                except ValueError:
                    entry = None
            self.callee_entries[key] = entry
        return self.callee_entries[key]

    def observed(self):
        return bool(self.scalar or self.pending or self.memory)

    def manifest(self):
        if self.pending:
            raise ValueError('BIOS memory-wrapper summary was not discharged over its owner CFG')
        used = sorted({record['target'] for record in (*self.scalar.values(), *self.memory.values())})
        weaker = any('non_argument' in record for record in self.memory.values())
        manifest = dict(schema=SCHEMA, contract=CONTRACT,
                        premises=list(PREMISES_NON_ARGUMENT if weaker else PREMISES),
                        wrappers=[[target, WRAPPERS[target][0], WRAPPERS[target][1],
                                   WRAPPERS[target][2].hex()] for target in used],
                        scalar_sites=[self.scalar[key] for key in sorted(self.scalar)],
                        memory_sites=[self.memory[key] for key in sorted(self.memory)])
        if self.memory:
            manifest['bit_rules'] = cpuset.ZERO_EXTENSION_RULES
        return manifest

    def digest(self):
        return hashlib.sha256(canonical(self.manifest()).encode()).hexdigest()

    def lines(self):
        """Report lines; none when no summary was applied, so other reports are unchanged."""
        if not self.observed():
            return []
        return manifest_lines(self.manifest())


def manifest_lines(manifest):
    """The report lines of one summaries manifest (BiosWrapperSummaries.manifest)."""
    # The schema and contract are the summary line, each premise is a line of its own,
    # and the rest (wrappers, sites and, with memory sites, the bit rules) is the manifest.
    sites = {key: value for key, value in manifest.items() if key not in ('schema', 'contract', 'premises')}
    return [f'* buffer BIOS summaries: `{SCHEMA}` {CONTRACT}',
            *(f'* buffer BIOS premise: {premise}' for premise in manifest['premises']),
            f'* buffer BIOS manifest: `{canonical(sites)}`',
            *non_argument_lines(manifest),
            *call_kill_lines(manifest)]


def register_id(number):
    """The capstone id of register r<number> (0-12)."""
    import match
    return match.ARM_REG_R12 if number == 12 else match.ARM_REG_R0 + number


def non_argument_lines(manifest):
    """One line per non-argument register that carried a local address into a memory call; none without.

    The contract names R0 and R1 as the only registers that carry local pointers in; where R3 or R12
    carried one, the line states it and why it gives the routine nothing, so no report reads as if the
    contract held as worded.
    """
    lines = []
    for site in manifest.get('memory_sites', ()):
        killers = {kill['register'] for kill in site.get('call_kills', ())}
        for register, offset in site.get('non_argument', ()):
            how = ('written before any read, call, interrupt or return' +
                   (', a call on its call-kill line counting as the write,' if register in killers else ''))
            lines.append(f"* buffer BIOS non-argument register: r{register} carried local {offset} into "
                         f"{site['routine']} at 0x{site['site']:08X}; no memory routine takes r{register} as an "
                         f"argument (GBATEK: R0-R2), so under the GBATEK premise it gives the routine no access, "
                         f"and it is {how} on every path from the call, so nothing the routine leaves in it "
                         f"is observed")
    return lines


def call_kill_lines(manifest):
    """One line per call that killed a carried register; none for a manifest without call_kills.

    The contract above says each carried register is written before any read, call or return. Where a
    call is that write, the line states it and the callee's own proof, so no report reads as if the
    contract held as worded.
    """
    lines = []
    for site in manifest.get('memory_sites', ()):
        for kill in site.get('call_kills', ()):
            writes = ' '.join(f'r{register}@0x{address:08X}' for address, register in kill['kills'])
            lines.append(f"* buffer BIOS call kill: call 0x{kill['site']:08X} to 0x{kill['callee']:08X} "
                         f"kills r{kill['register']} (left by {site['routine']} at 0x{site['site']:08X}): the "
                         f"callee writes {writes} before any read, call, interrupt, return or cycle on every "
                         f"path from its entry ({kill['states']} states)")
    return lines
