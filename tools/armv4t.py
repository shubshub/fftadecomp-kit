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

The standard is "defined for ARMv4T by the ARM Architecture Reference Manual" (ARM
DDI 0100I, chapter A7).  An operand combination that chapter leaves UNPREDICTABLE is
refused whatever the ARM7TDMI does with it: an ``stmia`` whose base is listed but
not lowest, ``muls`` with one register as both operands, and a hi-register ``cmp``
whose first operand is ``pc``.  The last follows the 2005 wording on purpose: DDI 0100E
(2000) A7.1.23 allows R15 as Rn and the ARM7TDMI data sheet (DDI 0029E 5.5.5) defines it.  ``tests/test_armv4t_table.py`` compares ``encoding``
with a bit-level table of the encodings on every halfword.

An item must come from a detail decode that starts at that instruction (one
address at a time), or from a multi-instruction decode in which every preceding
item of the same call was checked and accepted (``owner_graph_profile.graph``
and ``dead_argument_buffer_profile.killing_instruction`` decode a whole range
this way and stop at the first refused item).  Within one multi-instruction
decode Capstone carries Thumb-2 ``it`` state forward: after an ``it`` halfword
it renames ``b`` to ``b<cond>``, changes conditions and drops the ``s`` of
``adds``/``subs``/``movs``, none of which the ARM7TDMI does.  ``it`` is itself
refused, so a decode whose earlier items all passed carries no such state.  The
checks below also read the condition and the flag-setting class from the
encoding bits and refuse an item whose decode disagrees with them, so an item
that follows an unchecked ``it`` is refused rather than modelled wrongly.
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
    """Whether one 16-bit instruction is an ARMv4T Thumb encoding other than SWI (not ARMv5/v6).

    SWI (``0xDFxx``) is an ARMv4T encoding but is refused here, because every caller refuses
    interrupts.  ``item`` is a detail decode that starts at this instruction, or an item of a
    multi-instruction decode whose preceding items all passed (see the module docstring).
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
    if half >> 6 == 0x10D and half >> 3 & 7 == half & 7:
        return False  # muls with Rd == Rm: UNPREDICTABLE before ARMv6 (ARM DDI 0100I A7.1.45)
    if half & 0xFF87 == 0x4587:
        return False  # hi-register cmp with Rn == pc: UNPREDICTABLE in DDI 0100I A7.1.23 only (2005 wording, on purpose)
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
