"""Canonical _call_via_rN thunk calls inside the complete switch-data family.

Each selector keeps every rule of the complete-object-words switch-data proof
(fixed-gap pool layout, with or without the write-only
outgoing-argument frame; reached u16 scalar words bound when present) and
additionally admits the compiler's indirect-call thunks. The thunk
binding is the one canonical-thunks-v1 already proves: a ROM-checked
``bx rN; mov r8, r8`` pair under the conditional returning indirect ARM ABI.
Function words, local buffers, other runtimes and a second table stay refused.
A thunk call is bound exactly once, in the ``thunks`` list; the ordinary
``calls`` list never names a thunk.
"""

import hashlib
import json

import m4a_track_switch as music

from armv4t import ARMV4T, CONDITIONS, encoding as armv4t_encoding  # noqa: F401 (kit #180 shared checker)

POLICY = 'canonical-call-thunks-v1'
# selector -> (schema, outgoing frame). Only the fixed-gap pool layout is admitted.
SELECTORS = {
    'switch-thunks-v1': ('elf-symbol-thumb-switch-data-thunks-v1', False),
    music.SELECTOR: (music.SCHEMA, False),
    'switch-thunks-frame-v1': ('elf-symbol-thumb-switch-data-thunks-frame-v1', True),
}
SCHEMAS = {selector: value[0] for selector, value in SELECTORS.items()}
BY_SCHEMA = {schema: selector for selector, schema in SCHEMAS.items()}
SUMMARIES = {
    selector: ('one guarded local Thumb table with complete mapped object words, u16 scalar words '
               'where present, and canonical call thunks'
               + (' and a fixed write-only outgoing-argument frame' if frame else ''))
    for selector, (_, frame) in SELECTORS.items()}
SUMMARIES[music.SELECTOR] = music.SUMMARY
FIELDS = frozenset(('thunk_policy', 'thunks', 'dependencies'))


def selected(selector):
    return type(selector) is str and selector in SELECTORS


def framed(selector):
    """Whether a selector admits the write-only outgoing-argument frame."""
    if not selected(selector):
        raise ValueError('switch thunks require an explicit versioned selector')
    return SELECTORS[selector][1]


def selector_for_manifest(manifest):
    """The selector a thunk manifest's markers name, or None when it has no thunk policy."""
    if type(manifest) is not dict or 'thunk_policy' not in manifest:
        return None
    if manifest['thunk_policy'] != POLICY or 'pool_policy' in manifest:
        raise ValueError('switch thunks require their canonical policy marker and fixed pool layout')
    if 'engine_tracks' in manifest:
        if 'stack_policy' in manifest or 'scalar_policy' in manifest:
            raise ValueError('m4a engine tracks exclude scalar pools and outgoing frames')
        return music.SELECTOR
    return 'switch-thunks-frame-v1' if 'stack_policy' in manifest else 'switch-thunks-v1'


def selector_for_report(report):
    """The selector a saved report's verification line names; callers must replay it."""
    lines = [line for line in report.splitlines() if line.lstrip().startswith('* verification')]
    for selector, schema in SCHEMAS.items():
        if lines == [f'* verification: `{schema}`']:
            return selector
    if any(schema in line for line in report.splitlines() for schema in SCHEMAS.values()):
        raise ValueError('mixed or malformed switch-thunk selection')
    return None


def exact(left, right):
    """Compare manifest facts as canonical JSON, so 4.0 or true cannot stand for 4 or 1."""
    return json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)


def check_link(selector, function_relocations, targets):
    """Binding gate: every runtime-helper call is a canonical alias and at least one exists."""
    from match import RUNTIME_HELPERS
    import function_thunk_profile as function_thunk
    framed(selector)
    thunks = {name for name, target in targets.items() if target in RUNTIME_HELPERS.values()}
    if function_relocations or not thunks or any(
            name not in function_thunk.ALIASES or function_thunk.ALIASES[name] != targets[name]
            for name in thunks):
        raise ValueError('switch thunks require canonical _call_via aliases without function words')
    return thunks


def thunk_sites(selector, calls):
    """Call sites that go through canonical thunks (at least one is required)."""
    import function_thunk_profile as function_thunk
    from match import RUNTIME_HELPERS
    framed(selector)
    sites = {site for site, target in calls.items() if target in RUNTIME_HELPERS.values()}
    if not sites or any(calls[site] not in function_thunk.ALIASES.values() for site in sites):
        raise ValueError('switch thunk calls differ from the selector')
    return sites


ROM_LOW, ROM_HIGH = 0x08000000, 0x0E000000
# Binary operations whose exact result over constants is modelled; any other operation
# with a constant-derived source makes its result a possible code address.
BINARY = frozenset(('add', 'adds', 'sub', 'subs', 'lsls', 'lsrs', 'orrs', 'ands', 'eors', 'bics'))
OTHER = frozenset(('asrs', 'rors', 'muls', 'adcs', 'sbcs', 'mvns', 'negs', 'rsbs'))
CONSTANT_BUDGET = 16
MIXED = (-1, -1)  # constant-derived, value unknown (a constant combined with a loaded value)


def constant_value(operand, constants):
    """(low, high) of an operand known to be built from immediates, else None."""
    from capstone.arm import ARM_OP_IMM, ARM_OP_REG
    if operand.type == ARM_OP_IMM:
        return operand.imm & 0xFFFFFFFF, operand.imm & 0xFFFFFFFF
    if operand.type == ARM_OP_REG:
        return constants.get(operand.reg)
    return None


def combine(mnemonic, left, right):
    """Interval of ``left op right``, or None when it is not representable."""
    (a, b), (c, d) = left, right
    if mnemonic in ('add', 'adds'):
        low, high = a + c, b + d
    elif mnemonic in ('sub', 'subs'):
        low, high = a - d, b - c
    elif a == b and c == d and mnemonic in ('lsls', 'lsrs') and 0 <= c < 32:
        low = high = (a << c if mnemonic == 'lsls' else a >> c) & 0xFFFFFFFF
    elif a == b and c == d and mnemonic in ('orrs', 'ands', 'eors', 'bics'):
        low = high = {'orrs': a | c, 'ands': a & c, 'eors': a ^ c, 'bics': a & ~c}[mnemonic] & 0xFFFFFFFF
    else:
        return None
    return (low, high) if 0 <= low <= high <= 0xFFFFFFFF else None


def verify_thunk_targets(instructions, edges, address, calls, pointer, data=None, *, engine_rom=None, objects=None):
    """Refuse a thunk call whose target register may hold a local code address.

    Local provenance enters through every load of the switch table pointer
    literal at ``pointer``, any other read of PC or SP, the entry return
    address and the return address each BL leaves in LR. It follows every register
    operation and every load whose address uses a tainted register, so table
    entries and the dispatch registers that stay live into the cases are
    tainted too. No store may use a tainted register, and pops are tainted
    because stack words are not tracked, so provenance cannot be laundered
    through memory. Results returned by callees are untainted under the
    ordinary call ABI premise; values loaded through untainted addresses and
    values built from immediates are not tracked.

    Values built from immediates are tracked as intervals (movs/mov of an
    immediate, then add, sub, shifts and logical operations over constants).
    An interval that reaches the ROM range, or any other operation on a
    constant, makes the register tainted; a loop that keeps changing a constant
    taints it after a fixed number of revisits. A thunk register that holds any
    constant-derived value is refused, so a callback must be loaded from memory.

    Premises: callee results are untainted under the ordinary call ABI; a code
    address passed to a callee as an argument (r0-r3 or stack) and kept in
    memory is not followed; nothing ties the callback register to a particular
    callback object, so any mapped object may be loaded.

    The walk decodes every reached instruction itself, so it admits only the
    16-bit ARMv4T mnemonics in ``ARMV4T`` (hi-register and bx forms checked by
    encoding) plus the bound BL pairs, and refuses ``svc``, ``bkpt`` and
    ``udf`` (kit #180): the model must agree with the ARM7TDMI on every byte.
    """
    import function_thunk_profile as function_thunk
    from capstone import CS_GRP_INT
    from capstone.arm import (ARM_INS_BL, ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_LR, ARM_REG_PC,
                              ARM_REG_R0, ARM_REG_R12, ARM_REG_SP)
    from match import CALLER_CLOBBERED
    registers = {*range(ARM_REG_R0, ARM_REG_R12 + 1), ARM_REG_LR}
    thunks = {site: ARM_REG_R0 + (target - function_thunk.START) // 4
              for site, target in calls.items() if target in function_thunk.ALIASES.values()}
    engine_call = None
    if engine_rom is not None:
        engine_call = music.verified_callback(instructions, edges, address, calls, data, engine_rom, objects)
    states, revisits = {}, {}
    pending = [(address, frozenset((ARM_REG_LR,)), (), False)]
    while pending:
        site, incoming, known, dirty_in = pending.pop()
        old_tainted, old_known, old_stored = states.get(site, (frozenset(), {}, False))
        merged = dict(old_known)
        for register, low, high in known:
            old = merged.get(register)
            if old is None:
                merged[register] = (low, high)
            elif MIXED in (old, (low, high)):
                merged[register] = MIXED
            else:
                merged[register] = (min(low, old[0]), max(high, old[1]))
        if site in states and incoming <= old_tainted and merged == old_known and (not dirty_in or old_stored):
            continue
        tainted, stored = old_tainted | incoming, old_stored or dirty_in
        revisits[site] = revisits.get(site, 0) + 1
        if revisits[site] > CONSTANT_BUDGET:
            # Widen only what this visit changed: an unchanged entry is already the
            # join of every path seen here. MIXED tops the constant lattice but does
            # not cover an exact interval for taint (the interval's ROM check would be
            # lost), so an exact incoming value absorbed into MIXED is also a change.
            # The kept map only shrinks from here on.
            exact_in = {register for register, low, high in known if (low, high) != MIXED}
            changing = frozenset(register for register, value in merged.items()
                                 if old_known.get(register) != value or
                                 value == MIXED and register in exact_in)
            tainted |= changing
            merged = {register: value for register, value in merged.items() if register not in changing}
        states[site] = (tainted, merged, stored)
        constants = dict(merged)
        item = instructions[site]
        if item.size != 2 and not (item.id == ARM_INS_BL and item.size == 4 and site in calls) or \
                CS_GRP_INT in item.groups or item.size == 2 and not armv4t_encoding(item):
            raise ValueError('switch thunks admit only 16-bit ARMv4T encodings and bound BL pairs')
        read, written = item.regs_access()
        read, written = set(read), set(written) & registers
        mems = [operand.mem for operand in item.operands if operand.type == ARM_OP_MEM]
        literals = [((item.address + 4) & ~3) + mem.disp for mem in mems if mem.base == ARM_REG_PC]
        if item.id == ARM_INS_BL:
            target = thunks.get(site)
            if target in tainted:
                raise ValueError('thunk target register can hold a local code address')
            if target in constants and site != engine_call:
                raise ValueError('thunk target register holds a constant-derived value')
            clobbered = (set(CALLER_CLOBBERED) if site in calls else set()) | {ARM_REG_LR}
            tainted = (tainted - clobbered) | {ARM_REG_LR}
            constants = {register: value for register, value in constants.items() if register not in clobbered}
        elif item.mnemonic == 'pop':
            tainted = tainted | written
            constants = {register: value for register, value in constants.items() if register not in written}
        elif item.mnemonic.startswith(('str', 'stm')):
            if tainted & read:
                raise ValueError('a local code address cannot be stored')
            # Once a constant-derived value is stored on a path, memory may hold a code
            # address built from immediates: every later load on the path is constant-derived,
            # whatever register or address it uses, and a call cannot clear that.
            skip = {mem.base for mem in mems} | {mem.index for mem in mems}
            if item.mnemonic.startswith('stm'):
                skip = {item.operands[0].reg}
            # Stores through SP are the verified write-only outgoing frame; the function never
            # reads them back, so only a callee could copy them (a stated premise).
            if any(register in constants for register in read - skip) and \
                    not (mems and all(mem.base == ARM_REG_SP for mem in mems)):
                stored = True
        elif item.mnemonic != 'push':
            source = literals == [pointer] if literals else \
                item.mnemonic == 'adr' or bool(read & (tainted | {ARM_REG_PC, ARM_REG_SP}))
            tainted = tainted | written if source else tainted - written
            operands = list(item.operands)
            modelled = item.mnemonic in BINARY or item.mnemonic in OTHER or item.mnemonic in ('mov', 'movs')
            for register in written:
                constants.pop(register, None)
            loaded = item.mnemonic.startswith('ld') and not source
            if loaded and literals:
                # A reached literal word is a known constant: its bound value, whatever it names.
                word = literals[0] - address
                if data is None or not 0 <= word <= len(data) - 4:
                    raise ValueError('thunk literal word is outside the function')
                value = int.from_bytes(data[word:word + 4], 'little')
                if written:
                    constants[operands[0].reg] = (value, value)
            elif loaded and stored:
                for register in written:
                    constants[register] = MIXED
            elif not source and modelled and operands and operands[0].type == ARM_OP_REG:
                destination = operands[0].reg
                sources = operands[1:]
                # x + 0, x - 0 and x << 0 are exactly x (agbcc's register copy is adds rd, rs, #0):
                # a move, so the source's state carries over unchanged.
                identity = item.mnemonic in ('add', 'adds', 'sub', 'subs', 'lsls') and len(operands) <= 3 and \
                    bool(sources) and sources[-1].type == ARM_OP_IMM and sources[-1].imm == 0
                if identity:
                    sources = [operands[len(operands) - 2]]
                elif len(sources) == 1 and (item.mnemonic in BINARY or item.mnemonic in ('asrs', 'rors', 'muls',
                                                                                         'adcs', 'sbcs')):
                    sources = [operands[0], *sources]
                values = [constant_value(operand, merged) for operand in sources]
                result, escapes, mixed = None, False, False
                if item.mnemonic in ('mov', 'movs') or identity:
                    result = values[0] if values else None
                    mixed = result == MIXED
                    result = None if mixed else result
                elif any(value is not None for value in values):
                    if item.mnemonic in BINARY and (None in values or MIXED in values):
                        mixed = True  # a constant combined with another value stays constant-derived
                    elif item.mnemonic in BINARY:
                        result = combine(item.mnemonic, *values)
                        escapes = result is None
                    else:
                        escapes = True
                if escapes or result is not None and result[1] >= ROM_LOW and result[0] < ROM_HIGH:
                    tainted = tainted | {destination}
                elif mixed and destination in registers:
                    constants[destination] = MIXED
                elif result is not None and destination in registers:
                    constants[destination] = result
        pending.extend((target, frozenset(tainted), tuple((r, *v) for r, v in constants.items()), stored)
                       for target in edges[site])


def fingerprint(address, data, manifest):
    from match_evidence import switch_manifest
    selector = selector_for_manifest(manifest)
    framed(selector)
    proof = hashlib.sha256()
    for payload in (SCHEMAS[selector].encode('ascii'), address.to_bytes(4, 'little'),
                    data, switch_manifest(manifest).encode('ascii')):
        proof.update(len(payload).to_bytes(8, 'little'))
        proof.update(payload)
    return proof.hexdigest()
