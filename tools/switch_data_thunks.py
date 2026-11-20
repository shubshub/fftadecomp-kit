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
# A register in the constant map may be constant-derived. Its value is the interval of the
# exact values it holds on the paths where it was built only from immediates and literal
# words; MIXED holds none (on every such path a constant met a loaded value).
MIXED = (-1, -1)


def join(old, new):
    """The constant state of a register that reaches a join with ``old`` and ``new``.

    A MIXED path adds no exact value, so it cannot hide the other paths' interval from
    the ROM check (kit #367); the register stays constant-derived by staying in the map.
    An interval is the hull of the exact paths only: even a one-value interval does not
    mean the register holds that value on every path (it may be MIXED or loaded on others).
    """
    if old == MIXED:
        return new
    if new == MIXED:
        return old
    return min(old[0], new[0]), max(old[1], new[1])


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
    if mnemonic in ('add', 'adds', 'sub', 'subs') and (high < 0 or low > 0xFFFFFFFF):
        low, high = low % 0x100000000, high % 0x100000000  # wrapped whole: the same values mod 2**32
    return (low, high) if 0 <= low <= high <= 0xFFFFFFFF else None


def byte_range(value, index):
    """The range of byte ``index`` over every value in the interval ``value``."""
    low, high = value
    shift = 8 * index
    if low >> (shift + 8) != high >> (shift + 8):
        return 0, 0xFF
    return (low >> shift) & 0xFF, (high >> shift) & 0xFF


def hull(left, right):
    """The interval covering both (None is empty)."""
    if left is None or right is None:
        return right if left is None else left
    return min(left[0], right[0]), max(left[1], right[1])


def join_memory(old, new):
    """Join two paths' constant memory: every exact byte either path may have left, anywhere."""
    (old_bytes, old_wild, old_count, old_stores, old_through), \
        (new_bytes, new_wild, new_count, new_stores, new_through) = old, new
    merged = dict(old_bytes)
    for location, value in new_bytes:
        merged[location] = hull(merged.get(location), value)
    return (tuple(sorted(merged.items())), hull(old_wild, new_wild), max(old_count, new_count),
            old_stores | new_stores, old_through | new_through)


# no constant byte stored on the path: (exact bytes, wild byte range, wild byte count, store sites,
# constant stores through registers that hold no exact address: (base, index, offset, width))
CLEAN = ((), None, 0, frozenset(), frozenset())


def canonical(address):
    """The byte a GBA address names: masked to 32 bits, mirrors folded; None where that is not fixed.

    EWRAM, IWRAM, palette RAM, VRAM, OAM, the I/O mirror at 0x04000800 and the ROM wait-state
    windows mirror by the ARM7TDMI memory map. SRAM's mirroring depends on the cartridge and the
    unused regions on the bus, so an address there is not a fixed byte; nor is the cartridge's
    GPIO port (0x080000C4-0x080000C9) or the 0x0D window, where an EEPROM may answer. On this
    cartridge (FLASH512 save, 16 MiB ROM) that window is a plain ROM mirror, as kit #406 folds it,
    so treating its bytes as unfixed is conservative.
    """
    address &= 0xFFFFFFFF
    region = address >> 24
    if region == 0x02:
        return 0x02000000 + address % 0x40000
    if region == 0x03:
        return 0x03000000 + address % 0x8000
    if region == 0x04:
        return 0x04000800 + (address & 3) if address & 0xFFFC == 0x0800 else address
    if region in (0x05, 0x07):
        return (region << 24) + address % 0x400
    if region == 0x06:
        offset = address % 0x20000
        return 0x06000000 + (offset - 0x8000 if offset >= 0x18000 else offset)
    if 0x08 <= region <= 0x0C and not 0xC4 <= address % 0x2000000 < 0xCA:
        return 0x08000000 + address % 0x2000000
    return None


def rom(key):
    """Whether a canonical byte is cartridge ROM, which ignores writes: no store leaves a byte there."""
    return key is not None and 0x08000000 <= key < 0x0A000000


ANY, ZERO, SIGN = 'any', 'zero', 'sign'
SAME = 'same'  # one SRAM byte, the same in every lane it fills (SRAM has an 8-bit bus)


def sram(address):
    return address is not None and (address & 0xFFFFFFFF) >> 24 in (0x0E, 0x0F)


def may_overlap(left, right):
    """Whether two accesses through one unknown register can touch a common byte.

    Each is (offset, width); the ARM7TDMI forcibly aligns a halfword or word access, so the bytes
    depend on the register's alignment, and every alignment is tried. An offset of None (after a
    writeback) may touch any byte.
    """
    if left[0] is None or right[0] is None:
        return True
    def span(residue, offset, width):
        start = ((residue + offset) & -width) - residue
        return start, start + width
    return any(span(r, *left)[0] < span(r, *right)[1] and span(r, *right)[0] < span(r, *left)[1]
               for r in range(4))


def load_layouts(mnemonic, at, slot=0):
    """The ARM7TDMI byte layouts a load can produce: each is four result bytes, low first, and each
    byte is a memory address (``ANY`` when the address is not exact), ``ZERO`` or ``SIGN`` (a copy
    of the sign of the highest memory byte). With an unknown address every alignment is possible.

    LDR rotates a misaligned word right by 8 x (address & 3); LDRH [odd] is the halfword at
    address - 1 rotated right by 8; LDRSH [odd] is LDRSB; LDM is forcibly word aligned (GBATEK,
    ARM CPU Memory Alignments). SRAM's 8-bit bus repeats the one byte at the address in every
    lane a halfword or word read fills (``SAME``, or an ('sram', address) byte), and the CPU's
    misaligned rules apply on top: LDRH [odd] of byte b is b, 0, 0, b, and LDRSH [odd] is LDRSB.
    """
    if at is None:
        return {'ldrb': [[ANY, ZERO, ZERO, ZERO]], 'ldrsb': [[ANY, SIGN, SIGN, SIGN]],
                'ldrh': [[ANY, ANY, ZERO, ZERO], [ANY, ZERO, ZERO, ANY], [SAME, SAME, ZERO, ZERO],
                         [SAME, ZERO, ZERO, SAME]],
                'ldrsh': [[ANY, ANY, SIGN, SIGN], [ANY, SIGN, SIGN, SIGN], [SAME, SAME, SIGN, SIGN],
                          [SAME, SIGN, SIGN, SIGN]]
                }.get(mnemonic, [[ANY] * 4, [SAME] * 4])
    if sram(at):
        byte = ('sram', (at & ~3) + 4 * slot if mnemonic.startswith('ldm') else at)
        odd = at & 1
        return [{'ldrb': [byte, ZERO, ZERO, ZERO], 'ldrsb': [byte, SIGN, SIGN, SIGN],
                 'ldrh': [byte, ZERO, ZERO, byte] if odd else [byte, byte, ZERO, ZERO],
                 'ldrsh': [byte, SIGN, SIGN, SIGN] if odd else [byte, byte, SIGN, SIGN]}.get(mnemonic, [byte] * 4)]
    if mnemonic.startswith('ldm'):
        word = (at & ~3) + 4 * slot
        return [[word, word + 1, word + 2, word + 3]]
    if mnemonic == 'ldrb':
        return [[at, ZERO, ZERO, ZERO]]
    if mnemonic == 'ldrsb' or mnemonic == 'ldrsh' and at & 1:
        return [[at, SIGN, SIGN, SIGN]]
    if mnemonic == 'ldrh':
        return [[at, at + 1, ZERO, ZERO]] if at & 1 == 0 else [[at, ZERO, ZERO, at - 1]]
    if mnemonic == 'ldrsh':
        return [[at, at + 1, SIGN, SIGN]]
    word, turn = at & ~3, at & 3
    return [[word + (index + turn) % 4 for index in range(4)]]


PREMISE = 'thunk store premise'


class StorePremises:
    """The thunk store premises of one verification (kit #393).

    ``expected`` is the manifest's record, or None to derive one; the walk sets ``derived``.
    """

    def __init__(self, expected=None):
        self.expected, self.derived = expected, None


def premise_records(manifest):
    """The ``store_premises`` records of a thunk manifest, checked, as ((load, (stores...)), ...)."""
    if 'store_premises' not in manifest:
        return ()
    records, previous = manifest['store_premises'], -1
    if type(records) is not list or not records:
        raise ValueError('invalid thunk store premises')
    result = []
    for record in records:
        if type(record) is not list or len(record) != 2 or type(record[0]) is not int or \
                type(record[1]) is not list or not record[1] or record[0] <= previous or record[0] % 2 or \
                any(type(store) is not int or store % 2 for store in record[1]) or \
                record[1] != sorted(set(record[1])):
            raise ValueError('invalid thunk store premises')
        previous = record[0]
        result.append((record[0], tuple(record[1])))
    return tuple(result)


def premise_manifest(records):
    return [[load, list(stores)] for load, stores in records]


def premise_lines(address, manifest):
    """The report lines stating each load-bearing thunk store premise of a manifest."""
    return [f'* {PREMISE}: the load at 0x{address + load:08X} through a non-exact address reads back no '
            f'byte this function stored as a constant (stores at '
            f'{", ".join(f"0x{address + store:08X}" for store in stores)})'
            for load, stores in premise_records(manifest)]


def verify_thunk_targets(instructions, edges, address, calls, pointer, data=None, *, engine_rom=None, objects=None,
                         premises=None):
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
    taints it after a fixed number of revisits. A constant combined with a
    loaded value is constant-derived with no exact value (MIXED). At a join the
    interval covers the exact values of every path that has one, and a MIXED or
    non-constant path adds none, so it cannot hide them from the ROM check. A
    thunk register that holds any constant-derived value is refused, so a
    callback must be loaded from memory.

    Memory keeps the exact bytes of constant stores (kit #393). An address is
    exact when its base (and index) hold one value on every path; it is taken
    mod 2**32 and its mirrors are folded (``canonical``). A store there, forcibly
    aligned as the ARM7TDMI does, replaces those bytes; a store anywhere else may
    land on any byte, so its bytes and their count are kept apart. A load takes
    the exact values its bytes can hold in every layout the ARM7TDMI can produce
    (``load_layouts``: rotated misaligned LDR and LDRH, LDRSH [odd] as LDRSB,
    SRAM's 8-bit bus repeating one byte in every lane, and every alignment where
    the address is not exact), and the ROM check applies to them; a byte no
    constant store can have written makes it MIXED. An 8-bit store to palette
    RAM or BG VRAM fills both halves of its halfword, and one to OAM or OBJ VRAM
    is ignored (where the display mode decides, either). The cartridge ROM
    ignores writes, so no store leaves a byte there (``rom``); its GPIO port and
    the 0x0D window are no fixed byte. LDM and STM write their base back, with
    the ROM check on the new base. Once a
    constant-derived value is stored on a path, every later load on the path is
    constant-derived, whatever register or address it uses, and a call clears
    neither.

    The walk is sound by itself. Where it refuses, a load through a non-exact
    address may be assumed to read back none of the bytes this function stored
    as constants: the thunk store premise. A load at an exact address, or one
    that may overlap a constant store through the same unchanged register (or
    a copy of it), is never covered; a call or a pop forgets those stores, and
    a writeback makes them overlap anything through that register. That match
    follows registers and their copies, not values computed from them: after
    adds r6, r5, #28, a load through r6 is not tied to a store through r5.
    The smallest such set of loads that admits the function (each one needed,
    in address order) is ``premises.derived``, and it must
    equal ``premises.expected`` unless that is None (derive only). Without
    ``premises`` no premise is admitted. When no premise helps, the sound
    walk's refusal is reported.

    Premises: callee results are untainted under the ordinary call ABI; a code
    address passed to a callee as an argument (r0-r3 or stack) and kept in
    memory is not followed, nor is a constant a callee or a DMA transfer copies
    to another address; nothing ties the callback register to a particular
    callback object, so any mapped object may be loaded. A constant combined
    with a loaded value (MIXED), including a word only partly assembled from
    stored constant bytes, is not checked against the ROM range: a loaded value
    is assumed not to complete a local code address. Stores through SP are the
    verified write-only outgoing frame and are not followed into memory.

    The walk decodes every reached instruction itself, so it admits only the
    16-bit ARMv4T mnemonics in ``ARMV4T`` (hi-register and bx forms checked by
    encoding) plus the bound BL pairs, and refuses ``svc``, ``bkpt`` and
    ``udf`` (kit #180): the model must agree with the ARM7TDMI on every byte.
    """
    engine_call = None if engine_rom is None else \
        music.verified_callback(instructions, edges, address, calls, data, engine_rom, objects)

    def walk(relaxed):
        return walk_thunk_targets(instructions, edges, address, calls, pointer, data, engine_call, relaxed)

    try:
        walk(frozenset())
        derived = ()
    except ValueError as refusal:
        try:
            needed = sorted(walk(None))  # every non-exact load relaxed
        except ValueError:
            raise refusal from None  # no premise admits it: the sound walk's reason stands
        for site in list(needed):
            try:
                walk(frozenset(needed) - {site})
            except ValueError:
                continue
            needed.remove(site)
        stores = walk(frozenset(needed))
        derived = tuple((site - address, tuple(sorted(store - address for store in stores[site])))
                        for site in needed)
    expected = () if premises is None else premises.expected
    if premises is not None:
        premises.derived = derived
    if expected is not None and expected != derived:
        if derived and not expected:
            raise ValueError('a thunk store premise is required: '
                             f'{premise_lines(address, {"store_premises": premise_manifest(derived)})[0]}')
        raise ValueError('thunk store premises differ from the verified walk')
    return derived


def walk_thunk_targets(instructions, edges, address, calls, pointer, data, engine_call, relaxed):
    """One walk of ``verify_thunk_targets``: {relaxed load: the constant stores it may read}.

    ``relaxed`` is the set of non-exact loads the premise covers, or None for all of them.
    """
    import function_thunk_profile as function_thunk
    from capstone import CS_GRP_INT
    from capstone.arm import (ARM_INS_BL, ARM_OP_IMM, ARM_OP_MEM, ARM_OP_REG, ARM_REG_LR, ARM_REG_PC,
                              ARM_REG_R0, ARM_REG_R12, ARM_REG_SP)
    from match import CALLER_CLOBBERED
    registers = {*range(ARM_REG_R0, ARM_REG_R12 + 1), ARM_REG_LR}
    thunks = {site: ARM_REG_R0 + (target - function_thunk.START) // 4
              for site, target in calls.items() if target in function_thunk.ALIASES.values()}
    states, revisits, premised = {}, {}, {}
    pending = [(address, frozenset((ARM_REG_LR,)), (), False, frozenset(), CLEAN)]
    while pending:
        site, incoming, known, dirty_in, definite_in, memory_in = pending.pop()
        old_tainted, old_known, old_stored, old_definite, old_memory = \
            states.get(site, (frozenset(), {}, False, None, CLEAN))
        merged = dict(old_known)
        for register, low, high in known:
            old = merged.get(register)
            merged[register] = (low, high) if old is None else join(old, (low, high))
        # ``definite`` registers hold an exact value on every path (a must-set: it only shrinks).
        definite = definite_in if old_definite is None else old_definite & definite_in
        memory = join_memory(old_memory, memory_in)
        if site in states and incoming <= old_tainted and merged == old_known and (not dirty_in or old_stored) \
                and definite == old_definite and memory == old_memory:
            continue
        tainted, stored = old_tainted | incoming, old_stored or dirty_in
        revisits[site] = revisits.get(site, 0) + 1
        if revisits[site] > CONSTANT_BUDGET:
            # Widen only what this visit changed: an unchanged entry is already the
            # join of every path seen here (an exact value arriving at a MIXED entry
            # changes it, see join). The kept map only shrinks from here on.
            changing = frozenset(register for register, value in merged.items()
                                 if old_known.get(register) != value)
            tainted |= changing
            merged = {register: value for register, value in merged.items() if register not in changing}
            definite -= changing
        states[site] = (tainted, merged, stored, definite, memory)
        constants, exact = dict(merged), set(definite)
        stored_bytes, wild, count, stores, through = dict(memory[0]), *memory[1:]

        def location(base, index=0, offset=0):
            """The address an access names when it is one exact value on every path (mod 2**32), else None.

            Read from the state before the instruction, whose own writes may replace the base."""
            parts = [base, index] if index else [base]
            if any(part not in definite or merged[part][0] != merged[part][1] for part in parts):
                return None
            return (sum(merged[part][0] for part in parts) + offset) & 0xFFFFFFFF

        def term(base, index, offset):
            """(register, index, signed offset) of an access, an exact register folded into the offset."""
            for moving, fixed in ((base, index), (index, base)):
                if fixed and fixed in definite and merged[fixed][0] == merged[fixed][1]:
                    return moving, 0, (offset + merged[fixed][0] + 0x80000000) % 0x100000000 - 0x80000000
            return base, index, offset

        def written_back(base, step):
            """LDM/STM writeback: the base advances by ``step``, with the ROM check on the result."""
            nonlocal tainted, through
            moved = any(entry[0] == base for entry in through)
            through = frozenset(entry for entry in through if base not in entry[:2]) | \
                ({(base, 0, None, None)} if moved else set())  # it may now touch any byte
            value = merged.get(base)
            constants.pop(base, None)
            exact.discard(base)
            if base in tainted or value is None:
                return
            result = MIXED if value == MIXED else combine('adds', value, (step, step))
            if result is None or result != MIXED and result[1] >= ROM_LOW and result[0] < ROM_HIGH:
                tainted = tainted | {base}
                return
            constants[base] = result
            if result != MIXED and base in definite:
                exact.add(base)
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
            exact -= clobbered
            through = frozenset(entry for entry in through if not clobbered & set(entry[:2]))
        elif item.mnemonic == 'pop':
            tainted = tainted | written
            constants = {register: value for register, value in constants.items() if register not in written}
            exact -= written
            through = frozenset(entry for entry in through if not written & set(entry[:2]))
        elif item.mnemonic.startswith(('str', 'stm')):
            if tainted & read:
                raise ValueError('a local code address cannot be stored')
            # Once a constant-derived value is stored on a path, memory may hold a code
            # address built from immediates: every later load on the path is constant-derived,
            # whatever register or address it uses, and a call cannot clear that.
            skip = {mem.base for mem in mems} | {mem.index for mem in mems}
            if item.mnemonic.startswith('stm'):  # the base is stored too when it is listed
                skip = {item.operands[0].reg} - {operand.reg for operand in item.operands[1:]}
            # Stores through SP are the verified write-only outgoing frame; the function never
            # reads them back, so only a callee could copy them (a stated premise).
            if any(register in constants for register in read - skip) and \
                    not (mems and all(mem.base == ARM_REG_SP for mem in mems)):
                stored = True
            # The exact bytes a store may leave (kit #393). At an address that is one exact value on
            # every path (forcibly aligned, as the ARM7TDMI does) they replace the bytes there; anywhere
            # else, or where the address is not a fixed byte, they may land on any byte.
            if not (mems and all(mem.base == ARM_REG_SP for mem in mems)):
                if item.mnemonic.startswith('stm'):
                    base, at = item.operands[0].reg, location(item.operands[0].reg)
                    accesses = [(None if at is None else (at & ~3) + 4 * slot, 4, operand.reg,
                                 term(base, 0, 4 * slot))
                                for slot, operand in enumerate(item.operands[1:])]
                else:
                    width = {'strb': 1, 'strh': 2}.get(item.mnemonic, 4)
                    at = location(mems[0].base, mems[0].index, mems[0].disp)
                    accesses = [(None if at is None else at & -width, width, item.operands[0].reg,
                                 term(mems[0].base, mems[0].index, mems[0].disp))]
                for at, width, register, (base, index, offset) in accesses:
                    value = constants.get(register, MIXED)
                    parts = None if value == MIXED else [byte_range(value, index) for index in range(width)]
                    keys = None if at is None else [canonical(at + index) for index in range(width)]
                    weak = False
                    if keys and rom(keys[0]):
                        continue  # the cartridge ROM ignores the write
                    if width == 1 and keys and keys[0] is not None and keys[0] >> 24 in (5, 6, 7):
                        # 8-bit video stores (GBATEK, GBA Unpredictable Things): palette RAM and BG VRAM
                        # write the byte to both halves of the halfword; OAM and OBJ VRAM ignore it; the
                        # BG/OBJ boundary in VRAM depends on the display mode, so between the two the
                        # halfword either takes the byte or keeps its bytes.
                        video = keys[0] - 0x06000000
                        if keys[0] >> 24 == 7 or keys[0] >> 24 == 6 and video >= 0x14000:
                            continue  # it leaves no byte, so it is no store a premise names
                        keys, weak = [keys[0] & ~1, (keys[0] & ~1) + 1], keys[0] >> 24 == 6 and video >= 0x10000
                        parts = parts and parts * 2
                    if parts:
                        stores = stores | {site}
                        if at is None:
                            through = through | {(base, index, offset, width)}
                    if keys is None or None in keys:
                        for part in parts or ():  # a byte store may fill two video lanes
                            wild, count = hull(wild, part), min(4, count + (2 if width == 1 else 1))
                        continue
                    for key, part in zip(keys, parts or [None] * len(keys)):
                        if weak:
                            if part is not None:
                                stored_bytes[key] = hull(stored_bytes.get(key), part)
                        elif part is None:
                            stored_bytes.pop(key, None)
                        else:
                            stored_bytes[key] = part
                if item.mnemonic.startswith('stm') and item.writeback:
                    written_back(item.operands[0].reg, 4 * (len(item.operands) - 1))
        elif item.mnemonic != 'push':
            source = literals == [pointer] if literals else \
                item.mnemonic == 'adr' or bool(read & (tainted | {ARM_REG_PC, ARM_REG_SP}))
            tainted = tainted | written if source else tainted - written
            operands = list(item.operands)
            modelled = item.mnemonic in BINARY or item.mnemonic in OTHER or item.mnemonic in ('mov', 'movs')
            for register in written:
                constants.pop(register, None)
            exact -= written
            writeback = item.mnemonic.startswith('ldm') and item.writeback
            moved = written - ({operands[0].reg} if writeback else set())  # written_back shifts the base
            through = frozenset(entry for entry in through if not moved & {entry[0], entry[1]})
            loaded = item.mnemonic.startswith('ld') and not source
            if loaded and literals:
                # A reached literal word is a known constant: its bound value, whatever it names.
                word = literals[0] - address
                if data is None or not 0 <= word <= len(data) - 4:
                    raise ValueError('thunk literal word is outside the function')
                value = int.from_bytes(data[word:word + 4], 'little')
                if written:
                    constants[operands[0].reg] = (value, value)
                    exact.add(operands[0].reg)
            elif loaded and stored:
                # A load after a constant store is constant-derived. Its exact values are those the
                # constant stores on its path can have left in every byte it reads: each byte must
                # come from the stores at its exact address or from the stores anywhere else (``wild``,
                # ``count`` bytes of them); a load through a non-exact address may read any of them.
                if item.mnemonic.startswith('ldm'):
                    at = location(operands[0].reg)
                    accesses = [(at, slot, operand.reg, (*term(operands[0].reg, 0, 4 * slot), 4))
                                for slot, operand in enumerate(operands[1:])]
                else:
                    width = {'ldrb': 1, 'ldrsb': 1, 'ldrh': 2, 'ldrsh': 2}.get(item.mnemonic, 4)
                    accesses = [(location(mems[0].base, mems[0].index, mems[0].disp), 0, operands[0].reg,
                                 (*term(mems[0].base, mems[0].index, mems[0].disp), width))]
                anywhere = wild
                for value in stored_bytes.values():
                    anywhere = hull(anywhere, value)
                for at, slot, register, (base, index, offset, width) in accesses:
                    value = None
                    for layout in load_layouts(item.mnemonic, at, slot):
                        reads = [byte for byte in layout if byte not in (ZERO, SIGN)]
                        part_of = {byte: anywhere if byte == ANY else wild if byte == SAME or type(byte) is tuple
                                   else None if rom(canonical(byte))  # ROM: no store leaves a byte there
                                   else hull(stored_bytes.get(canonical(byte)), wild)
                                   if canonical(byte) is not None else wild for byte in reads}
                        # wild bytes it needs: one per distinct byte no exact-address store covers
                        needed = max(0, reads.count(ANY) - len(stored_bytes)) + sum(
                            1 for byte in set(reads) - {ANY}
                            if type(byte) is not int or canonical(byte) not in stored_bytes)
                        if None in part_of.values() or needed > count:
                            continue  # some byte it reads holds no stored constant
                        sign = part_of[reads[-1]]  # the highest memory byte
                        ranges = [(0, 0) if byte == ZERO else
                                  (0 if sign[0] < 0x80 else 0xFF, 0xFF if sign[1] >= 0x80 else 0)
                                  if byte == SIGN else part_of[byte] for byte in layout]
                        value = hull(value, (sum(low << 8 * i for i, (low, _) in enumerate(ranges)),
                                             sum(high << 8 * i for i, (_, high) in enumerate(ranges))))
                    if value is None:
                        constants[register] = MIXED
                        continue
                    # The premise covers a load through a non-exact address only, and never one that
                    # reads back through the same unchanged register as a constant store before it.
                    aliased = any(b == base and i == index and may_overlap((o, w), (offset, width))
                                  for b, i, o, w in through)
                    if at is None and not aliased and (relaxed is None or site in relaxed):
                        premised[site] = premised.get(site, frozenset()) | stores
                        constants[register] = MIXED
                        continue
                    if value[1] >= ROM_LOW and value[0] < ROM_HIGH:
                        tainted = tainted | {register}
                    else:
                        constants[register] = value
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
                    if sources and sources[0].type == ARM_OP_REG:  # a copy aliases what its source does
                        through = through | {(destination, *entry[1:]) for entry in through
                                             if entry[0] == sources[0].reg}
                    result = values[0] if values else None
                    mixed = result == MIXED
                    result = None if mixed else result
                elif any(value is not None for value in values):
                    if item.mnemonic in BINARY and (None in values or MIXED in values):
                        mixed = True  # a constant combined with another value stays constant-derived
                    elif item.mnemonic in BINARY:
                        # The paths where every operand is exact. On an operand's MIXED paths the result
                        # is MIXED, which its map entry (or its taint) already covers.
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
                    if all(operand.type == ARM_OP_IMM or operand.reg in definite for operand in sources):
                        exact.add(destination)  # every source held its exact value on every path
            if writeback:
                written_back(operands[0].reg, 4 * (len(operands) - 1))
        memory = tuple(sorted(stored_bytes.items())), wild, count, stores, through
        pending.extend((target, frozenset(tainted), tuple((r, *v) for r, v in constants.items()), stored,
                        frozenset(exact & set(constants)), memory)
                       for target in edges[site])
    return premised


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
