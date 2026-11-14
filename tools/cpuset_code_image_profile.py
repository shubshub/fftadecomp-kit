"""Name an indexed code entry as the proven source of a BIOS CpuSet copy.

A game may copy ARM (or Thumb) routines from ROM to RAM and run them there, so the
ROM rows stay in the index as bounded entries while the owner's literal word holds the
entry start. This module is the CFG-level half of the opt-in code-image selectors: a
typed object literal whose value is exactly an indexed entry start is admitted only if
every load of that word reaches r0 of an actual CpuSet wrapper call and the copy
length, source and RAM destination are exact constants on every path. It records the
exact set of indexed rows the copied span covers. It proves no BIOS effect, no
physical readability, no persistence of the installed bytes and no property of the
installed code; the literal is never callable, storable or otherwise observable. The span is bounded
(MAX_BYTES, MAX_ROWS, alignment-sized gaps, a small trailing overrun) and may not cover
its owner or the CpuSet wrapper.
"""
import hashlib
import json

from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_MEM, ARM_OP_REG, ARM_REG_CPSR,
                                ARM_REG_PC, ARM_REG_R0)

import bios_cpuset_fill_profile as bios
import iwram_installation_prerequisite as constants

SCHEMA = 'rom-cpuset-code-image-source-v1'
ROM_BASE = 0x08000000
MAX_BYTES = 0x200      # real images are 0xB0 and 0x140 bytes
MAX_ROWS = 3           # the largest real case, 0x08002768; a reviewed bump to go higher
MAX_GAP = 3            # alignment padding only
MAX_OVERRUN = 0x80
# IWRAM above 0x03007E00 holds the BIOS-reserved IRQ vector and stacks.
RAM = ((0x02000000, 0x02040000), (0x03000000, 0x03007E00))
CONTRACT = ('An indexed entry start named by a typed object literal is consumed only as r0 of '
            'an actual CpuSet wrapper call whose r0, r1 and r2 are exact constants on every '
            'reaching path (copy mode, no reserved bits, bounded positive count, RAM '
            'destination). The indexed rows intersecting the copied span are recorded, and a '
            'final partially covered row is an explicit overrun. Static source-span identity '
            'only: no BIOS effect or return, readability, persistence, destination safety, '
            'installed-code behaviour or numeric theorem; the literal is not a callable, '
            'a stored address or an object bound.')


def rows_at(entries, value):
    return [row for row in entries if int(row['rom'], 16) <= value < int(row['end'], 16)]


def alias_words(literals, entries):
    """Typed literals whose value lies in indexed code (only entry starts reach here)."""
    result = {}
    for offset, (name, value) in literals.items():
        rows = rows_at(entries, value)
        if rows:
            if len(rows) != 1 or int(rows[0]['rom'], 16) != value or value % 2:
                raise ValueError('code-image literal must be exactly one indexed entry start')
            result[offset] = (name, value)
    return result


def r2_step(item):
    """A 16-bit r2 -> r2 shift or add/sub immediate: the only reads of a derived length."""
    raw = int.from_bytes(item.bytes, 'little')
    if item.size != 2:
        return False
    if raw & 0xF800 in (0x0000, 0x0800):
        return item.mnemonic == ('lsls' if raw & 0x0800 == 0 else 'lsrs') and \
            raw & 7 == 2 and (raw >> 3) & 7 == 2
    return raw & 0xF000 == 0x3000 and (raw >> 8) & 7 == 2 and \
        item.mnemonic == ('subs' if raw & 0x0800 else 'adds')


def is_length_subs(item):
    """Exactly `subs r2, rN, r0` (r0 is the subtrahend, r2 the destination)."""
    raw = int.from_bytes(item.bytes, 'little')
    return item.size == 2 and raw & 0xFE00 == 0x1A00 and item.mnemonic == 'subs' and \
        raw & 7 == 2 and (raw >> 6) & 7 == 0 and (raw >> 3) & 7 != 0


FLAG_READERS = ('adcs', 'adc', 'sbcs', 'sbc', 'rors', 'ror')
FLAG_RESETS = ('cmp', 'cmn', 'adds', 'subs', 'negs')


def reads_flags(item, reads):
    return item.mnemonic in FLAG_READERS or ARM_REG_CPSR in reads or \
        item.cc not in (ARM_CC_AL, ARM_CC_INVALID)


def resets_flags(item):
    """A flag-setting op that recomputes every flag (movs and shifts leave carry alone)."""
    return item.mnemonic in FLAG_RESETS


def after_call(call, instructions, edges, calls, flags):
    """No path may read r0 (BIOS may leave source plus length there) or, when the flags
    still hold the length subtraction, read them, before the register or flags are reset.
    Reaching an exit with r0 still live is refused: the caller would receive it."""
    pending, seen = [(call, True, flags)], set()
    while pending:
        site, live, tainted = pending.pop()
        if (site, live, tainted) in seen:
            continue
        seen.add((site, live, tainted))
        if live and not edges[site]:
            raise ValueError('code-image r0 is still live at a function exit')
        for successor in edges[site]:
            item = instructions[successor]
            reads, writes = item.regs_access()
            if live and ARM_REG_R0 in reads:
                raise ValueError('code-image r0 is read after the CpuSet call')
            if tainted and (reads_flags(item, reads) or successor in calls):
                raise ValueError('code-image length flags are read after the CpuSet call')
            if live and successor in calls:
                raise ValueError('code-image r0 reaches a later call')
            pending.append((successor, live and ARM_REG_R0 not in writes,
                            tainted and not resets_flags(item)))


def source_uses(word, instructions, edges, calls, address, reverse):
    """Each load of the word is a plain r0 load reaching a CpuSet call and nothing else."""
    uses = []
    two = ARM_REG_R0 + 2
    if not word['load_sites'] or word['switch_word']:
        raise ValueError('code-image literal requires actual plain loads')
    for load in word['load_sites']:
        item = instructions[load]
        op, code = item.operands, int.from_bytes(item.bytes, 'little')
        if item.size != 2 or code & 0xFF00 != 0x4800 or item.mnemonic != 'ldr' or len(op) != 2 or \
                op[0].type != ARM_OP_REG or op[0].reg != ARM_REG_R0 or \
                op[1].type != ARM_OP_MEM or op[1].mem.base != ARM_REG_PC or \
                op[1].mem.index or item.writeback or \
                ((load + 4) & ~3) + op[1].mem.disp != word['address']:
            raise ValueError('code-image literal must be loaded only into r0')
        cursor, visited, derived, flags = load, {load}, False, False
        while True:
            if len(edges[cursor]) != 1:
                raise ValueError('code-image literal must reach its call on one linear path')
            successor = edges[cursor][0]
            if successor in visited or successor != cursor + instructions[cursor].size or \
                    len(reverse[successor]) != 1:
                raise ValueError('code-image literal must reach its call on one linear path '
                                 'without joins')
            visited.add(successor)
            if successor in calls:
                if calls[successor] != bios.ADDRESS:
                    raise ValueError('code-image literal reaches a call other than CpuSet')
                after_call(successor, instructions, edges, calls, flags)
                uses.append(successor)
                break
            following = instructions[successor]
            reads, writes = following.regs_access()
            if ARM_REG_R0 in writes:
                raise ValueError('code-image literal register is overwritten before its call')
            if flags and reads_flags(following, reads):
                raise ValueError('code-image length flags are read before the CpuSet call')
            if is_length_subs(following):
                derived = flags = True
            elif ARM_REG_R0 in reads:
                raise ValueError('code-image literal register is read other than by '
                                 'subs r2, rN, r0')
            elif derived and two in reads and not r2_step(following):
                raise ValueError('code-image length in r2 is read other than by an r2 step')
            elif derived and two in writes and two not in reads:
                derived = False
            if flags and not is_length_subs(following) and not (derived and two in reads) \
                    and resets_flags(following):
                flags = False
            cursor = successor
    return uses


def verify(literals, partition, instructions, edges, calls, address, data, rom, mapping):
    entries = json.loads(mapping)
    aliases = alias_words(literals, entries)
    if not aliases:
        raise ValueError('code-image selector requires an actual indexed entry literal')
    words = {row['address'] - address: row for row in partition['words']}
    states = constants.constant_states(instructions, edges, address, data)
    reverse = {site: set() for site in instructions}
    for site, targets in edges.items():
        for target in targets:
            reverse[target].add(site)
    copies = {}
    for offset, (name, value) in sorted(aliases.items()):
        for site in source_uses(words[offset], instructions, edges, calls, address, reverse):
            arguments = states[site]
            if any(ARM_REG_R0 + n not in arguments for n in range(3)):
                raise ValueError('code-image copy arguments are not exact on every reaching path')
            source, destination, control = (arguments[ARM_REG_R0 + n] for n in range(3))
            if source != value:
                raise ValueError('code-image call source differs from its literal')
            copies[site] = plan(site - address, name, value, destination, control, entries, rom,
                                 (address, address + len(data)))
    return [copies[site] for site in sorted(copies)]


def plan(site, name, value, destination, control, entries, rom, owner):
    if control & ~(0x04000000 | 0x1FFFFF):
        raise ValueError('code-image control is not a plain CpuSet copy (fill or reserved bits)')
    count, width = control & 0x1FFFFF, 4 if control & 0x04000000 else 2
    size = count * width
    low, high = value, value + size
    if not 1 <= size <= MAX_BYTES or value % width or destination % width or \
            not ROM_BASE <= low < high <= ROM_BASE + len(rom):
        raise ValueError('code-image copy span is empty, oversized, unaligned or outside ROM')
    if not any(a <= destination < destination + size <= b for a, b in RAM):
        raise ValueError('code-image copy destination is not wholly inside EWRAM or IWRAM')
    rows, gaps, overrun, cursor = [], [], None, low
    for row in sorted(entries, key=lambda row: int(row['rom'], 16)):
        start, end = int(row['rom'], 16), int(row['end'], 16)
        if end <= low or start >= high:
            continue
        if start < low or overrun is not None:
            raise ValueError('code-image span covers indexed code before its entry start')
        if start < owner[1] and end > owner[0] or start < bios.ADDRESS + 4 and end > bios.ADDRESS:
            raise ValueError('code-image span covers its owner or the CpuSet wrapper')
        if start > cursor:
            gaps.append([cursor, start])
        record = [start, end, row['mode'], min(end, high) - start]
        if end > high:
            overrun = record
        rows.append(record)
        cursor = min(end, high)
    if cursor < high:
        gaps.append([cursor, high])
    if len(rows) > MAX_ROWS or any(hi - lo > MAX_GAP for lo, hi in gaps) or \
            overrun is not None and overrun[3] > MAX_OVERRUN:
        raise ValueError('code-image span exceeds the row, gap or overrun bounds')
    if rows[0][0] != value:
        raise ValueError('code-image copy does not begin at an indexed entry')
    return dict(site=site, literal=name, source=value, destination=destination, control=control,
                width=width, units=count, bytes=size, rows=rows, unindexed_gaps=gaps,
                overrun=overrun, source_sha256=hashlib.sha256(
                    rom[low - ROM_BASE:high - ROM_BASE]).hexdigest())


def manifest(copies):
    return dict(schema=SCHEMA, contract=CONTRACT, copies=copies)
