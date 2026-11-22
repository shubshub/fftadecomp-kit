"""``armv4t`` agrees with a bit-level ARMv4T Thumb table on every halfword and on the BL pairs.

``tools/armv4t.py`` decides from Capstone's decode (an allow-list of mnemonics plus bit checks),
so its verdict can move with the Capstone version.  The table below is written from the encoding
tables alone and never asks Capstone anything; the tests decode every halfword with the installed
Capstone and compare the checker's verdict with the table's.

Sources:

* DS: ARM7TDMI Data Sheet, ARM DDI 0029E, chapter 5 "THUMB Instruction Set", Figure 5-1 (formats
  1 to 19) and the per-format sections 5.1 to 5.19; chapter 4 for the ARM instruction each Thumb
  instruction is equivalent to.
* ARM: ARM Architecture Reference Manual, ARM DDI 0100I, chapter A7 "Thumb Instructions", for the
  operand combinations ARMv4T leaves UNPREDICTABLE.

An encoding is in the table as ARMv4T only when a data sheet format assigns it and neither
document restricts the encoding itself.  (``bx pc`` is admitted: both documents make it
UNPREDICTABLE from a halfword that is not word-aligned, which a table of halfwords cannot state.)  SWI is a format of its own class here: it is an ARMv4T encoding that
``armv4t.encoding`` refuses on purpose, because its callers refuse interrupts.

The halfword sweeps are exhaustive.  The pair sweep is not all 4,194,304 prefix and suffix pairs:
it takes every possible second halfword (all 65,536) after one prefix, every prefix and every suffix value in rows and
columns of six, and every other 32-bit first halfword before five second halves.
"""
from collections import Counter
from pathlib import Path
import struct
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / 'tools'))
import capstone
from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
import armv4t

BASE = 0x08000000
V4T, SWI, BL_PREFIX, BL_SUFFIX, NONE = 'armv4t', 'swi', 'bl prefix', 'bl suffix', 'none'

# (mask, value, class): the first row a halfword matches decides it; no row means NONE.
RESTRICTIONS = (
    # DS 5.5.1: "The action of H1= 0, H2 = 0 for Op = 00 (ADD), Op =01 (CMP) and Op = 10 (MOV) is
    # undefined, and should not be used."  ARM A7.1.6, A7.1.23, A7.1.44: UNPREDICTABLE.
    (0xFFC0, 0x4400, NONE), (0xFFC0, 0x4500, NONE), (0xFFC0, 0x4600, NONE),
    # ARM DDI 0100I A7.1.23 CMP (3): "If H1 == 1 and Rn == 0b1111, apparently encoding R15, the
    # results of the instruction are UNPREDICTABLE."  Only the 2005 edition says so: DDI 0100E
    # (2000) A7.1.23 lets Rn be any of R0 to R15, and DDI 0029E 5.5.5 defines R15 as an operand.
    # The table follows the stricter wording on purpose.
    (0xFF87, 0x4587, NONE),
    # DS 5.5.3: "The action of H1 = 1 for this instruction [BX] is undefined, and should not be
    # used."  ARM A7.1.19: bits[2:0] of BX are SBZ.
    (0xFF87, 0x4700, V4T), (0xFF00, 0x4700, NONE),
    # ARM A7.1.45 MUL: "Prior to ARMv6, specifying the same register for <Rd> and <Rm> had
    # UNPREDICTABLE results."  DS Table 5-5 gives MUL Rd, Rs as MULS Rd, Rs, Rd, and DS 4.7.1:
    # "The destination register Rd must not be the same as the operand register Rm."
    *((0xFFFF, 0x4340 | reg << 3 | reg, NONE) for reg in range(8)),
    # ARM A7.1.49 POP, A7.1.50 PUSH: "If bits[8:0] are all zero, the result is UNPREDICTABLE."
    # DS 4.11.1: "the register list should not be empty."
    (0xF7FF, 0xB400, NONE),
    # ARM A7.1.27 LDMIA, A7.1.57 STMIA: "If bits[7:0] are all zero, the result is UNPREDICTABLE."
    (0xF0FF, 0xC000, NONE),
    # ARM A7.1.57 STMIA: with <Rn> in <registers> and not the lowest-numbered register there,
    # "the stored value of <Rn> is UNPREDICTABLE."  One row per base and lower listed register.
    # (LDMIA with the base in the list is defined, ARM A7.1.27: "the final value of <Rn> is the
    # loaded value"; DS 4.11.6: "A LDM will always overwrite the updated base".)
    *((0xF800 | 7 << 8 | 1 << base | 1 << lower, 0xC000 | base << 8 | 1 << base | 1 << lower, NONE)
      for base in range(8) for lower in range(base)),
    # DS 5.16.1: "Cond = 1110 is undefined, and should not be used."  ARM A7.1.13: UNDEFINED.
    (0xFF00, 0xDE00, NONE),
)
FORMATS = (
    (0xF800, 0x1800, V4T),        # DS 5.2  format 2: 00011 I Op, add/subtract
    (0xE000, 0x0000, V4T),        # DS 5.1  format 1: 000 Op, Op = 00 01 10 (11 is format 2)
    (0xE000, 0x2000, V4T),        # DS 5.3  format 3: 001 Op, move/compare/add/subtract immediate
    (0xFC00, 0x4000, V4T),        # DS 5.4  format 4: 010000 Op, ALU operations
    (0xFC00, 0x4400, V4T),        # DS 5.5  format 5: 010001 Op H1 H2, ADD CMP MOV (BX is above)
    (0xF800, 0x4800, V4T),        # DS 5.6  format 6: 01001, PC-relative load
    (0xF200, 0x5000, V4T),        # DS 5.7  format 7: 0101 L B 0, load/store with register offset
    (0xF200, 0x5200, V4T),        # DS 5.8  format 8: 0101 H S 1, sign-extended byte/halfword
    (0xE000, 0x6000, V4T),        # DS 5.9  format 9: 011 B L, load/store with immediate offset
    (0xF000, 0x8000, V4T),        # DS 5.10 format 10: 1000 L, load/store halfword
    (0xF000, 0x9000, V4T),        # DS 5.11 format 11: 1001 L, SP-relative load/store
    (0xF000, 0xA000, V4T),        # DS 5.12 format 12: 1010 SP, load address
    (0xFF00, 0xB000, V4T),        # DS 5.13 format 13: 10110000 S, add offset to stack pointer
    (0xF600, 0xB400, V4T),        # DS 5.14 format 14: 1011 L 10 R, push/pop registers
    (0xF000, 0xC000, V4T),        # DS 5.15 format 15: 1100 L, multiple load/store
    (0xFF00, 0xDF00, SWI),        # DS 5.17 format 17: 11011111, software interrupt
    (0xF000, 0xD000, V4T),        # DS 5.16 format 16: 1101 Cond, conditional branch
    (0xF800, 0xE000, V4T),        # DS 5.18 format 18: 11100, unconditional branch
    (0xF800, 0xF000, BL_PREFIX),  # DS 5.19 format 19: 1111 H, H = 0, first half of BL
    (0xF800, 0xF800, BL_SUFFIX),  # DS 5.19 format 19: 1111 H, H = 1, second half of BL
)
# What no row assigns: 1011 with bits 11:8 other than 0000 and x10x, and 11101.

# Encodings the table refuses and ``armv4t.encoding`` admits today; the checker has no rule for
# either group.  The sweep below requires the disagreement to be exactly this set: a checker that
# starts refusing a group fails the test until that group is deleted here, and no other
# disagreement can appear.
#
# * ``muls rN, rN``: restricted by both documents as quoted above.  ARM A4.1.40 (the equivalent
#   ARM instruction) adds that "it is believed all relevant ARMv4 and ARMv5 implementations do not
#   require this restriction either"; A7.1.45 still gives the Thumb form as UNPREDICTABLE before
#   ARMv6, and agbcc copies an operand instead of emitting it (``x * x`` compiles to
#   ``mov r1, r0`` then ``mul r1, r1, r0``).
# * ``cmp pc, rM``: UNPREDICTABLE in DDI 0100I A7.1.23 only; DDI 0100E A7.1.23 allows R15 as Rn
#   and DDI 0029E 5.5.5 defines it.  The table follows the 2005 wording on purpose.
ADMITTED_AGAINST_THE_TABLE = frozenset((
    *(0x4340 | reg << 3 | reg for reg in range(8)),
    *(0x4587 | rm << 3 for rm in range(16)),
))
FIELDS = (0x000, 0x001, 0x2AA, 0x400, 0x555, 0x7FF)  # 11-bit offset fields sampled in the pair test


def classify(half):
    for mask, value, kind in RESTRICTIONS + FORMATS:
        if half & mask == value:
            return kind
    return NONE


def halves(*values):
    return b''.join(struct.pack('<H', value) for value in values)


def named(values):
    return [f'0x{value:04X}' for value in sorted(values)]


class TableCensus(unittest.TestCase):
    """The table against counts worked out by hand from the field widths."""

    def test_every_halfword_has_one_class(self):
        stm_base_not_lowest = sum((2 ** base - 1) * 2 ** (7 - base) for base in range(8))
        self.assertEqual(stm_base_not_lowest, 769)
        by_format = {
            'format 1': 3 * 2048, 'format 2': 2048, 'format 3': 4 * 2048, 'format 4': 1024 - 8,
            'format 5': 192 + (192 - 16) + 192 + 16, 'format 6': 2048, 'format 7': 2048,
            'format 8': 2048, 'format 9': 4 * 2048, 'format 10': 4096, 'format 11': 4096,
            'format 12': 4096, 'format 13': 256, 'format 14': 4 * 256 - 2,
            'format 15': 4096 - 16 - stm_base_not_lowest, 'format 16': 14 * 256,
            'format 18': 2048}
        restricted = 3 * 64 + 16 + (256 - 16) + 8 + 2 + 16 + stm_base_not_lowest + 256
        unassigned = (16 - 1 - 4) * 256 + 2048  # 1011 outside formats 13 and 14, and 11101
        census = Counter(classify(half) for half in range(0x10000))
        self.assertEqual(census, {V4T: sum(by_format.values()), SWI: 256, BL_PREFIX: 2048,
                                  BL_SUFFIX: 2048, NONE: restricted + unassigned})
        self.assertEqual((census[V4T], census[NONE]), (54821, 6363))

    def test_rows_that_decide(self):
        for half, kind in ((0x46C0, V4T), (0x4770, V4T), (0x4778, V4T), (0x4771, NONE),
                           (0x4780, NONE), (0x4408, NONE), (0x4448, V4T), (0x4587, NONE),
                           (0x4586, V4T), (0x4340, NONE), (0x4348, V4T), (0xB400, NONE),
                           (0xB500, V4T), (0xBC00, NONE), (0xBD00, V4T), (0xC000, NONE),
                           (0xC800, NONE), (0xC003, V4T), (0xC102, V4T), (0xC103, NONE),
                           (0xC783, NONE), (0xC780, V4T), (0xC903, V4T), (0xDD00, V4T),
                           (0xDE00, NONE), (0xDF00, SWI), (0xB100, NONE), (0xB600, NONE),
                           (0xBA00, NONE), (0xBE00, NONE), (0xBF00, NONE), (0xE7FF, V4T),
                           (0xE800, NONE), (0xEFFF, NONE), (0xF000, BL_PREFIX),
                           (0xF7FF, BL_PREFIX), (0xF800, BL_SUFFIX), (0x1FFF, V4T)):
            with self.subTest(f'0x{half:04X}'):
                self.assertEqual(classify(half), kind)


class CheckerAgainstTheTable(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        cls.engine.detail = True
        cls.version = f'capstone {capstone.__version__}'

    def first(self, *values):
        return next(self.engine.disasm(halves(*values), BASE, 1), None)

    def admitted(self, item, size):
        return item is not None and item.size == size and armv4t.instruction(item)

    def test_every_halfword_alone(self):
        table = {half for half in range(0x10000) if classify(half) == V4T}
        checker = {half for half in range(0x10000) if self.admitted(self.first(half), 2)}
        self.assertEqual(named(table - checker), [], self.version)
        self.assertEqual(named(checker - table), named(ADMITTED_AGAINST_THE_TABLE), self.version)

    def test_every_16_bit_halfword_before_a_bl_suffix(self):
        # A 16-bit instruction is decided by its own halfword, whatever follows it.
        wrong = [half for half in range(0xE800)
                 if self.admitted(self.first(half, 0xF800), 2) !=
                 (classify(half) == V4T or half in ADMITTED_AGAINST_THE_TABLE)]
        self.assertEqual(named(wrong), [], self.version)

    def test_bl_pairs(self):
        # Admitted exactly when the first half is a format 19 prefix and the second a suffix, and
        # never as a 16-bit instruction.
        pairs = {(0xF000, second) for second in range(0x10000)}
        pairs |= {(first, second) for first in range(0xE800, 0x10000)
                  for second in (0x0000, 0xD000, 0xE800, 0xF000, 0xF800)}
        pairs |= {(0xF000 | high, 0xF800 | low) for high in range(0x800) for low in FIELDS}
        pairs |= {(0xF000 | high, 0xF800 | low) for high in FIELDS for low in range(0x800)}
        pairs |= {(0xF000 | high, top << 11 | low) for high in FIELDS for top in range(32)
                  for low in FIELDS}
        wrong = []
        for first, second in sorted(pairs):
            item = self.first(first, second)
            expected = classify(first) == BL_PREFIX and classify(second) == BL_SUFFIX
            if self.admitted(item, 4) != expected or self.admitted(item, 2) or \
                    item is not None and armv4t.encoding(item):
                wrong.append(f'{first:04X} {second:04X}')
        self.assertEqual(wrong[:20], [], (self.version, len(wrong)))


if __name__ == '__main__':
    unittest.main()
