"""ARMv4T Thumb encoding checks shared by the walks that decode Thumb with Capstone (kit #180).

Capstone's ``CS_MODE_THUMB`` also decodes Thumb-2 and ARMv5/v6 encodings, which the
ARM7TDMI does not execute (``0xF04F`` is the first half of a BL there, ``bkpt``,
``udf``, ``cps``, ``rev``, ``sxt``/``uxt``, ``cbz``, ``it`` and the hint
instructions do not exist, and a hi-register form of two low registers is
UNPREDICTABLE).  A proof's model must agree with the hardware on every byte it
admits, so a walk calls ``encoding`` on each reached 16-bit instruction and
``bl_pair`` on each reached 4-byte one.  The callers are the base leaf walk
(``match.verify_leaf_instructions``), the owner-graph decode
(``owner_graph_profile.graph``), the generic dead-alias walk, the dead-argument
scan and the switch-thunk taint pass; a walk that decodes Thumb on its own and is
not fed by one of these is not covered.

An item must come from a detail decode that starts at that instruction (one
address at a time).  Within one multi-instruction decode Capstone carries
Thumb-2 ``it`` state forward: after an ``it`` halfword it renames ``b`` to
``b<cond>``, changes conditions and drops the ``s`` of ``adds``/``subs``/``movs``,
none of which the ARM7TDMI does.  The checks below read the condition and the
flag-setting class from the encoding bits and refuse an item whose decode
disagrees with them, so such an item is refused rather than modelled wrongly.
"""
from capstone.arm import ARM_CC_AL, ARM_CC_EQ

# The only 16-bit mnemonics ARMv4T Thumb defines, plus the bound BL pair.
ARMV4T = frozenset((
    'adcs', 'add', 'adds', 'adr', 'ands', 'asrs', 'b', 'bics', 'bl', 'bx', 'cmn', 'cmp', 'eors',
    'ldm', 'ldmia', 'ldr', 'ldrb', 'ldrh', 'ldrsb', 'ldrsh', 'lsls', 'lsrs', 'mov', 'movs', 'muls',
    'mvns', 'negs', 'orrs', 'pop', 'push', 'rors', 'rsbs', 'sbcs', 'stm', 'stmia', 'str', 'strb',
    'strh', 'sub', 'subs', 'tst'))
CONDITIONS = ('eq', 'ne', 'cs', 'hs', 'cc', 'lo', 'mi', 'pl', 'vs', 'vc', 'hi', 'ls', 'ge', 'lt', 'gt', 'le')
# Condition names by the 4-bit field of a conditional branch (0xD000 | field << 8 | offset).
BRANCH_CONDITIONS = (('eq',), ('ne',), ('cs', 'hs'), ('cc', 'lo'), ('mi',), ('pl',), ('vs',), ('vc',),
                     ('hi',), ('ls',), ('ge',), ('lt',), ('gt',), ('le',))


def encoding(item):
    """Whether one 16-bit instruction is an ARMv4T Thumb encoding (not ARMv5/v6).

    ``item`` is a detail decode that starts at this instruction (see the module docstring).
    """
    if item.size != 2:
        return False
    mnemonic = item.mnemonic
    half = int.from_bytes(bytes(item.bytes), 'little')
    if half >> 12 == 0xD:  # conditional branch; fields 0xE and 0xF are undefined and swi
        field = half >> 8 & 0xF
        return field < 0xE and item.cc == ARM_CC_EQ + field and \
            mnemonic[:1] == 'b' and mnemonic[1:] in BRANCH_CONDITIONS[field]
    if item.cc != ARM_CC_AL:
        return False  # no other ARMv4T Thumb encoding is conditional
    if mnemonic == 'nop':
        return half == 0x46C0
    if mnemonic not in ARMV4T:
        return False
    if half < 0x4400 and mnemonic not in ('cmp', 'cmn', 'tst') and not mnemonic.endswith('s'):
        return False  # shift, add/subtract, immediate and ALU forms always set the flags
    if mnemonic in ('stm', 'stmia') and half >> 11 == 0x18 and half >> 8 & 7 != 0 and \
            half & (1 << (half >> 8 & 7)) and half & ((1 << (half >> 8 & 7)) - 1):
        return False  # writeback base in the list but not the lowest register: UNPREDICTABLE
    if half >> 8 == 0x47:  # bx: blx (bit 7) and nonzero low bits are not ARMv4T
        return mnemonic == 'bx' and half & 0x87 == 0
    if half >> 10 == 0x11:  # hi-register add, cmp, mov: at least one register must be high
        return (half >> 6) & 3 != 0
    return True


def bl_pair(item):
    """Whether a 4-byte decode is exactly the ARMv4T BL prefix and suffix halves."""
    if item.size != 4 or item.mnemonic != 'bl':
        return False
    raw = bytes(item.bytes)
    return int.from_bytes(raw[:2], 'little') & 0xF800 == 0xF000 and \
        int.from_bytes(raw[2:], 'little') & 0xF800 == 0xF800


def instruction(item):
    """Whether a reached Thumb instruction is a 16-bit ARMv4T encoding or a BL pair."""
    return encoding(item) if item.size == 2 else bl_pair(item)
