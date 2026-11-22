"""Switch pool words that are only a BIOS CpuSet or CpuFastSet control argument.

The u16 scalar switch policies bind every reached literal word that is not the
table pointer, a typed object or a bound function as an exact number, and refuse
a value above 0xFFFF and below 0x10000000 (`switch_wide_scalars` takes the
words from 0x10000000 up): such a word could be an unbound RAM, I/O or ROM
address written as a number. A CpuSet or CpuFastSet control word is such a
value without being an address. GBATEK (BIOS Memory Copy) gives r2 as the
routine's length/mode word: bits 0-20 the count, bit 24 a fixed source and, for
CpuSet, bit 26 32-bit units. 0x04000080 asks CpuSet to copy 0x80 words.

This policy binds such a word as an exact number when the verified switch CFG
shows that its value is nothing but that argument:

* every reached load of the word is a 16-bit `ldr rd, [pc, #imm]`. From each
  load one path (fallthrough, an unconditional `b`, the return of a bound
  direct call) carries the value until every register copy is overwritten. A
  conditional branch, a return or other PC write, an unbound `bl`, a revisited
  instruction or the end of the verified code while a copy is live refuses
  (for the copy a call leaves in r2, see below);
* a copy may be read only by a register copy into r0-r11 (`adds rd, rn, #0` or
  `mov rd, rm`, decoded by `bios_cpuset_fill_profile.transfer`) or as r2 of a
  bound direct call. Any other read refuses: a store or push, arithmetic, a
  comparison, a memory access through it. The flags an `adds` copy sets count
  as a copy until an instruction overwrites them: a conditional branch, `adcs`
  or `sbcs` that reads them, a return, and any call but one of the wrapper
  below while they are live refuse;
* at a bound direct call no copy may be in r0, r1 or r3, and a copy in r2
  requires the target to be the CpuSet (`swi 0x0B; bx lr`) or CpuFastSet
  (`swi 0x0C; bx lr`) wrapper of `bios_wrapper_summary_profile.MEMORY`, with
  the identity those summaries use: the target's complete, unique,
  non-overlapping index row (`BufferCallProof.span`) holds exactly the
  wrapper's bytes. Copies in r4-r11 survive any call (the ordinary returning
  ABI);
* a call is not taken to write r0-r3 or the flags: the copy in r2 of a
  wrapper call stays a copy after it, left in place, and so does the flags'
  taint. A callee may return with r2 unwritten, so a left copy stays a copy
  until an instruction overwrites it, and any read of it refuses, by any
  instruction (a register copy, `bx r2` and `mov pc, r2` included), as does
  its being live at a conditional branch or at a PC write other than a
  return. Two things may receive it unread. One is a single call, the first
  after the wrapper call, and only when that call would not pass it on: the
  translation unit's file-scope prototype of the callee
  (`volatile_semantics.function_signature`) must declare at most two
  argument words, and so must the kit's own count for that callee where it
  has one (`known_arguments`): the larger of the two decides. The kit
  counts r0-r3 for a BIOS SWI wrapper and for a call thunk, so a source
  that declares the CpuFastSet or CpuSet wrapper with two arguments is
  still refused. An unprototyped, variadic, unreadable or missing
  declaration refuses whatever the kit counts, and so does a second call
  while the copy is live. The ROM interface summary
  (`volatile_semantics.RomInterfaces`) is not used: it gives none for a
  callee whose CFG holds a word switch, as the next callee in 080775A8
  (`func_0808A604`) does. The other is the function's own return,
  `pop {..., pc}` or `bx rN`, the forms the switch verifier admits as a
  return: a return reads r0 (r0-r1 for a 64-bit result; agbcc returns a
  larger struct through memory), and a caller treats r2 as clobbered after
  any call. The walk takes every such instruction for that return and
  relies on the switch verifier, whose return provenance refuses one that
  is not (a `bx lr` after a call has written lr, a `bx r3`), in every
  verified switch: `uses()` alone admits those. That the callee reads only
  its declared arguments, and that the function's callers follow that
  convention, are part of the premise;
* each load reaches at least one such call, and the value is a whole control
  word for each routine it reaches, by the rule the BIOS wrapper summaries
  apply to a local copy (`control_spans`): no reserved bit, a count of at
  least 1, a multiple of eight for CpuFastSet.

This is the owner rule's saved scalar-control walk
(`bios_cpuset_fill_profile.saved_scalar_control_words`: the same `transfer`
copies, the same call rule for r0-r3) with these differences: a copy control
word (bit 24 clear) is admitted, validated as a whole word, where that walk
takes fill controls only; an unconditional `b` is followed; copies may sit in
r0-r11, not only r2 and r4-r7; CpuFastSet is a target too, recognised, like
CpuSet, by its indexed bytes rather than its address alone; and the flags and
the copy a call leaves in r2 are tracked as above, where that walk drops r0-r3
at every call.

Each word is recorded as `[offset, value, [[load, call], ...], [[call,
arguments], ...]]` in function offsets under `control_words`, apart from the
u16 and wide words, with `control_word_policy`, and only when one exists: the
wrapper calls each load reaches, and each first call after one that the copy
left in r2 reaches, with the argument words its callee's prototype declares. Replay
recomputes the list from the bytes, the index and the preprocessed source.
The report states the premise once and each word, its calls, its decoded
count and mode and the callees of its left copies on lines of their own.

Not proved: what the BIOS routine does with r2 (and that it does not read the
flags), that other calls leave a copy in r4-r11 alone, that the callee of the
first call after a wrapper call reads only the arguments its prototype
declares, that the function's callers treat r2 as clobbered after calling it,
or which spelling the source used: a data symbol at the same address would
link to the same bytes.
"""

from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B, ARM_INS_BL, ARM_OP_IMM, ARM_OP_MEM,
                                ARM_REG_PC, ARM_REG_R0)

import bios_cpuset_fill_profile as cpuset
import bios_wrapper_summary_profile as summaries
import volatile_semantics as semantics

POLICY = 'bios-copy-control-words-v1'
FIELDS = frozenset(('control_word_policy', 'control_words'))
LOW, HIGH = 0x10000, 0x10000000
# The two copy routines of the BIOS wrapper summaries' table; BgAffineSet takes no control word.
ROUTINES = (summaries.CPUSET, summaries.CPUFASTSET)
ARGUMENTS = frozenset(range(ARM_REG_R0, ARM_REG_R0 + 4))
CONTROL = ARM_REG_R0 + 2
LEFT, SPENT = 'left', 'spent'
COPY_TARGETS = frozenset(range(ARM_REG_R0, ARM_REG_R0 + 12))
# A callee that takes at most this many argument words reads no argument in r2.
ARGUMENT_WORDS = 2
# The argument words the kit counts for a callee it knows to read r0-r3 (known_arguments).
KNOWN_WORDS = len(ARGUMENTS)
SWI, BX, BX_LR = 0xDF00, 0x4700, 0x4770
PREMISE = ('each `control_words` word is an exact number above 0xFFFF and below 0x10000000 that the walk '
           'carries, through register copies on one path from each load, only into r2 of direct calls to the '
           'indexed CpuSet (`swi 0x0B; bx lr`) or CpuFastSet (`swi 0x0C; bx lr`) wrapper, and that is a whole '
           'control word for that routine (no reserved bit, a count of at least 1, a multiple of 8 for '
           'CpuFastSet); GBATEK (BIOS Memory Copy) documents r2 as the routine\'s length/mode word, so the BIOS '
           'reads the value as a count and a mode; a call is not taken to write r2 or the flags, so the walk '
           'keeps the copy a wrapper call leaves in r2, and the flags a copy set, until an instruction '
           'overwrites them, and refuses any read of them and their being live at a conditional branch, a '
           'later call or a PC write, with two allowances for the left r2 unread: the first call after the '
           'wrapper call, when the source\'s prototype of its callee declares at most two argument words and '
           'the callee is no BIOS SWI wrapper or call thunk (the kit counts r0-r3 for those), and '
           'the function\'s own return (`pop {..., pc}` or `bx rN`), since a return reads r0 (r0-r1 for a '
           '64-bit result) and a caller treats r2 as clobbered after a call; trusted, not proved: the routine '
           'reads r2 only so and does not read the flags, other calls neither read nor change a copy in r4-r11 '
           '(the ordinary returning ABI), the callee of that first call reads only the arguments its prototype '
           'declares, and the function\'s callers treat r2 as clobbered after calling it; a data symbol at the '
           'same address would link to the same bytes')
REPORT_PREFIX = '* switch control word'
PREMISE_PREFIX = '* switch control word premise: '
WORD_PREFIX = '* switch control word: '


def check_context(policy):
    if type(policy) is not str or policy != POLICY:
        raise ValueError('switch control words require their canonical policy marker')


def admits(value):
    """True for a word value this policy may bind (the proof below still decides)."""
    return type(value) is int and LOW <= value < HIGH


def decode(target, value):
    """(unit bytes, count) of an exact control word, or ValueError.

    The whole-word rule `control_spans` applies to a local copy source or
    destination; the source and destination offsets passed are placeholders it
    only returns.
    """
    _, _, unit, count = summaries.control_spans(target, 0, 0, value, cpuset.MASK ^ value)
    return unit, count


def wrapper(target, span):
    """True when `target` is the indexed CpuSet or CpuFastSet wrapper; `span` is BufferCallProof.span."""
    if target not in ROUTINES:
        return False
    try:
        return span(target) == summaries.MEMORY[target][2]
    except ValueError:
        return False


def known_arguments(target, span):
    """The argument words the kit itself counts for the callee at `target`, or None when it counts none.

    A BIOS SWI wrapper counts all of r0-r3 (KNOWN_WORDS): the kit's BIOS
    wrapper table (`bios_wrapper_summary_profile.WRAPPERS`, each indexed
    wrapper's routine, SWI number and bytes) is read with the kit's model of
    a BIOS call, which takes r0-r3 (`volatile_semantics.Executor.call`). The
    memory routines read their control word or count in r2
    (`bios_wrapper_summary_profile`), and the BIOS SWI handler stores r2 and
    restores it around every routine, the reason
    `stack_index_frame_words_profile.SWI_ARGUMENTS` counts r2 as read by Div.
    That holds for a table address whatever its bytes, and for any other
    indexed row that begins with `swi` (ObjAffineSet's `swi 0x0F; bx lr` at
    0x08141894, which reads r2 and r3, is not in the table). A row that
    begins with `bx rN`, rN not lr, is a call thunk (agbcc's `_call_via_rN`,
    `match.RUNTIME_HELPERS`): it passes r0-r3 on to a callee the walk does
    not know, so it counts r0-r3 too. `span` is BufferCallProof.span; a
    target it gives no row for gets no count here. The runtime division
    helpers' counts (`volatile_semantics.RUNTIME_ARITY`, two words each) are
    not consulted: the larger of a count and the prototype's can only pass
    when both are at most two, so they would decide nothing.
    """
    if target in summaries.WRAPPERS:
        return KNOWN_WORDS
    try:
        first = int.from_bytes(span(target)[:2], 'little')
    except ValueError:
        return None
    if first & 0xFF00 == SWI or first & 0xFF87 == BX and first != BX_LR:
        return KNOWN_WORDS
    return None


def declarations(text):
    """declared(target): the argument words the file-scope prototype of `func_<target>` declares.

    `text` returns the preprocessed source; it is called once, when a target is
    first asked for. A count comes from `volatile_semantics.function_signature`
    over the file scope of `translation_unit`, the reading the volatile
    checker uses: one word per parameter, None for an unprototyped `()` or a
    variadic list, a refusal for disagreeing declarations or a parameter that
    is not one word. declared() returns None for those, for a name with no
    declaration and when the text cannot be read, so the walk refuses.
    """
    state = {}

    def declared(target):
        if 'scope' not in state:
            try:
                state['scope'] = semantics.file_scope(semantics.translation_unit(text()))
            except (OSError, RuntimeError, ValueError, UnicodeDecodeError):
                state['scope'] = None
        if state['scope'] is None:
            return None
        try:
            _, arguments = semantics.function_signature(state['scope'], f'func_{target:08X}')
        except ValueError:
            return None
        return arguments

    return declared


def undeclared(target):
    """The declared() of a caller without a source: no callee's arguments are known."""
    return None


def uses(data, address, instructions, calls, span, offset, value, declared=undeclared):
    """[[[load, call], ...], [[call, arguments], ...]] in function offsets for the word at `offset`.

    The wrapper calls each load reaches, then each next call that a copy left
    in r2 reaches with the argument words declared() gives its callee; or
    ValueError (see the module).
    """
    if not admits(value):
        raise ValueError('control word value is outside 0x10000-0x0FFFFFFF')
    by_address = {item.address: item for item in instructions}
    literal = address + offset
    loads = sorted(item.address for item in instructions for operand in item.operands
                   if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC and
                   ((item.address + 4) & ~3) + operand.mem.disp == literal)
    if not loads:
        raise ValueError('control word is not loaded')
    result, passed, routines = [], set(), set()
    for load in loads:
        item = by_address[load]
        code = int.from_bytes(item.bytes, 'little')
        if item.size != 2 or code & 0xF800 != 0x4800 or item.mnemonic != 'ldr' or \
                item.operands[0].reg != ARM_REG_R0 + ((code >> 8) & 7):
            raise ValueError('control word load is not a 16-bit PC-relative ldr')
        found, passes = walk(by_address, load, item.operands[0].reg, value, calls, span, declared)
        if not found:
            raise ValueError(f'load at 0x{load:08X} reaches no CpuSet or CpuFastSet call')
        for site in found:
            routines.add(calls[site])
            result.append([load - address, site - address])
        passed.update(passes)
    for target in sorted(routines):
        decode(target, value)
    return [result, [[site - address, arguments] for site, arguments in sorted(passed)]]


def walk(by_address, load, register, value, calls, span, declared):
    """(wrapper call sites, {(next call, arguments)}) the copies of one load reach, or ValueError."""
    exact = cpuset.exact(value)
    copies, flags, sites, passes = {register}, False, [], set()
    # What a call left in r2: LEFT after a wrapper call, until it reaches one callee; SPENT after that,
    # until it is overwritten (see the module).
    left = None
    cursor, visited = load, {load}
    while True:
        item = by_address[cursor]
        following = cursor + item.size
        if cursor != load:
            reads, writes = map(set, item.regs_access())
            conditional = item.cc not in (ARM_CC_AL, ARM_CC_INVALID)
            if flags and (conditional or item.mnemonic in ('adcs', 'sbcs')):
                raise ValueError(f'flags set from the control word are read at 0x{cursor:08X}')
            if left and CONTROL in reads:
                raise ValueError(f'control word a call left in r2 is read at 0x{cursor:08X} by {item.mnemonic} '
                                 f'{item.op_str}')
            call = item.id == ARM_INS_BL or CS_GRP_CALL in item.groups
            if call:
                if cursor not in calls:
                    raise ValueError(f'control word is live at an unbound bl at 0x{cursor:08X}')
                target = calls[cursor]
                if copies & (ARGUMENTS - {CONTROL}):
                    raise ValueError(f'control word is another argument of the call at 0x{cursor:08X}')
                if flags and not wrapper(target, span):
                    raise ValueError(f'flags set from the control word are live at the call at 0x{cursor:08X}')
                if left == SPENT:
                    raise ValueError(f'control word a call left in r2 reaches a second call at 0x{cursor:08X}')
                if left == LEFT:
                    arguments = declared(target)
                    if type(arguments) is not int or not 0 <= arguments <= ARGUMENT_WORDS:
                        declared_words = '' if arguments is None else f' ({arguments} declared)'
                        raise ValueError(f'control word a call left in r2 reaches the call at 0x{cursor:08X}, and '
                                         f'the source does not declare func_{target:08X} with at most '
                                         f'{ARGUMENT_WORDS} argument words{declared_words}')
                    # The larger of the prototype's count and the kit's own decides.
                    known = known_arguments(target, span)
                    counted = arguments if known is None else max(arguments, known)
                    if counted > ARGUMENT_WORDS:
                        raise ValueError(f'control word a call left in r2 reaches the call at 0x{cursor:08X}, and '
                                         f'the kit counts {known} argument words for func_{target:08X}, a BIOS SWI '
                                         f'wrapper or call thunk, whatever the source declares ({arguments} '
                                         'declared)')
                    passes.add((cursor, counted))
                    left = SPENT
                elif CONTROL in copies:
                    if not wrapper(target, span):
                        raise ValueError(f'control word reaches r2 of the call at 0x{cursor:08X}, which is not '
                                         'the indexed CpuSet or CpuFastSet wrapper')
                    sites.append(cursor)
                    left = LEFT
            elif conditional and item.id == ARM_INS_B:
                if copies:
                    raise ValueError(f'control word is live at a conditional branch at 0x{cursor:08X}')
                return sites, passes
            else:
                copied = None
                if copies & reads:
                    code = int.from_bytes(item.bytes, 'little')
                    if item.size == 2 and (code & 0xFF00 == 0x4600 or code & 0xFFC0 == 0x1C00):
                        copied = cpuset.transfer(item, {reg: exact for reg in copies}, b'', 0)
                    if copied is None or copied[0] not in COPY_TARGETS or copied[1] != exact:
                        raise ValueError(f'control word is read at 0x{cursor:08X} by {item.mnemonic} '
                                         f'{item.op_str}, not as a register copy or the CpuSet argument')
                copies -= writes
                if CONTROL in writes:
                    left = None
                if copied is not None:
                    copies.add(copied[0])
                if item.update_flags:
                    flags = copied is not None
                if item.id == ARM_INS_B:
                    if len(item.operands) != 1 or item.operands[0].type != ARM_OP_IMM:
                        raise ValueError(f'unsupported branch at 0x{cursor:08X}')
                    following = item.operands[0].imm
                elif ARM_REG_PC in writes:
                    # A return reads r0 (r0-r1 for a 64-bit result; agbcc returns a larger struct through
                    # memory), and a caller treats r2 as clobbered after any call: the copy a call left in r2
                    # may be live, unread, at the function's own return, which the switch verifier admits as
                    # `pop {..., pc}` or `bx rN` only.
                    returning = item.mnemonic in ('pop', 'bx')
                    if copies - {CONTROL} or flags or CONTROL in copies and not (left and returning):
                        raise ValueError(f'control word is live at a return or PC write at 0x{cursor:08X}')
                    return sites, passes
        if not copies and not flags:
            return sites, passes
        if following not in by_address or following in visited:
            raise ValueError(f'control word is live past the verified straight-line code at 0x{cursor:08X}')
        visited.add(following)
        cursor = following


def records(manifest):
    """The validated control-word records of a manifest that carries the policy."""
    check_context(manifest.get('control_word_policy'))
    words = manifest.get('control_words')
    if not isinstance(words, list) or not words:
        raise ValueError('switch control words require a finite nonempty manifest')
    previous = -1
    for record in words:
        if not isinstance(record, list) or len(record) != 4 or type(record[0]) is not int or \
                record[0] <= previous or not admits(record[1]) or not pairs(record[2], nonempty=True) or \
                not pairs(record[3]):
            raise ValueError('switch control words require unique ordered exact records')
        passed = [site for site, _ in record[3]]
        if passed != sorted(set(passed)) or any(not 0 <= arguments <= ARGUMENT_WORDS
                                                for _, arguments in record[3]):
            raise ValueError('switch control words require unique ordered exact records')
        previous = record[0]
    return words


def pairs(value, nonempty=False):
    """True for a list of two-integer lists, nonempty when asked."""
    return isinstance(value, list) and (bool(value) or not nonempty) and all(
        isinstance(pair, list) and len(pair) == 2 and all(type(part) is int for part in pair) for pair in value)


def report_lines(address, manifest):
    """The premise line and one line per word; none without the policy, so other reports are unchanged."""
    if not isinstance(manifest, dict) or 'control_word_policy' not in manifest:
        return []
    targets = {offset: int(name[5:], 16) for offset, name in manifest['calls']}
    lines = [f'{PREMISE_PREFIX}{PREMISE}']
    for offset, value, used, passed in records(manifest):
        sites = {}
        for _, site in used:
            sites.setdefault(targets[site], set()).add(site)
        calls = []
        for target, at in sorted(sites.items()):
            unit, count = decode(target, value)
            mode = 'fill' if value & summaries.FILL else 'copy'
            calls.append(f'{summaries.MEMORY[target][0]} {mode} of 0x{count:X} {8 * unit}-bit units, r2 of '
                         f'func_{target:08X} at ' + ', '.join(f'0x{address + site:08X}' for site in sorted(at)))
        for site, arguments in passed:
            calls.append(f'r2 left for func_{targets[site]:08X} at 0x{address + site:08X}, declared with '
                         f'{arguments} argument word{"" if arguments == 1 else "s"}')
        loads = ', '.join(f'0x{address + load:08X}' for load in sorted({load for load, _ in used}))
        lines.append(f'{WORD_PREFIX}0x{value:08X} at 0x{address + offset:08X}, loaded at {loads}: '
                     + '; '.join(calls))
    return lines
