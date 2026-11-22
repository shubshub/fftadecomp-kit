"""RomInterfaces' callee budget is spent per called name, not per checked function.

A function with many calls used to exhaust the shared MAX_CALLEES budget, after
which every later callee fell back to the strict interface (reads r0-r3).  The
budget now restarts for each name the executor asks about; one name whose
callee tree is wider than the budget still fails closed.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_semantics as semantics
import synthetic_thumb_rom

try:
    import capstone  # noqa: F401
except ImportError:
    capstone = None

LEAF = [0x2000, 0x4770]                  # movs r0, #0; bx lr: reads none, writes r0
READER = [0x3001, 0x4770]                # adds r0, #1; bx lr: reads r0, writes r0
READS_R1 = [0x1C08, 0x4770]              # adds r0, r1, #0; bx lr: reads r1, writes r0
LEAVES = 0x08001000                       # leaf i at LEAVES + 4 * i
UNREAD_R0 = frozenset({"r1", "r2", "r3"})


def wide(count):
    """push {lr}; bl leaf_0 .. leaf_{count-1}; pop {r0}; bx r0"""
    return [0xB500] + [("bl", LEAVES + 4 * i) for i in range(count)] + [0xBC01, 0x4700]


def rom_with(functions):
    return synthetic_thumb_rom.image(functions, 0x2000)


def leaves():
    return [(LEAVES + 4 * i, LEAF) for i in range(semantics.MAX_CALLEES + 8)]


def interfaces(width):
    """a wide function at 0x08000200 calling `width` distinct leaves, and two
    small functions after it (0x08000800 reads r0, 0x08000810 reads none)"""
    return semantics.RomInterfaces(*rom_with(
        [(0x08000200, wide(width)), (0x08000800, READER), (0x08000810, LEAF)] + leaves()))


@unittest.skipUnless(capstone, "capstone required")
class CalleeBudgetTests(unittest.TestCase):

    def test_a_later_name_is_analysed_after_an_earlier_one_spent_the_budget(self):
        rom = interfaces(semantics.MAX_CALLEES + 4)
        # wider than the budget: the leaves past it count as reading r0-r3, and
        # only r0, which the earlier leaves overwrite, is known not to be read
        self.assertEqual(rom("func_08000200"), (UNREAD_R0, frozenset({"r0"})))
        self.assertEqual(rom.budget, 0)
        # a shared budget would leave nothing for these; each name has its own
        self.assertEqual(rom("func_08000800"), (frozenset({"r0"}), frozenset({"r0"})))
        self.assertEqual(rom.budget, semantics.MAX_CALLEES - 1)
        self.assertEqual(rom("func_08000810"), (frozenset(), frozenset({"r0"})))
        self.assertEqual(rom.budget, semantics.MAX_CALLEES - 1)
        # the answer stays fixed per name
        self.assertEqual(rom("func_08000200"), (UNREAD_R0, frozenset({"r0"})))
        self.assertEqual(rom.budget, semantics.MAX_CALLEES - 1)

    def test_the_budget_still_bounds_one_name(self):
        # the wide function plus MAX_CALLEES - 1 leaves fit exactly
        fits = interfaces(semantics.MAX_CALLEES - 1)
        self.assertEqual(fits("func_08000200"), (frozenset(), frozenset({"r0"})))
        self.assertEqual(fits.budget, 0)
        # one more leaf is unknown, so the name reads what it may pass on
        over = interfaces(semantics.MAX_CALLEES)
        self.assertEqual(over("func_08000200"), (UNREAD_R0, frozenset({"r0"})))

    def test_exact_summaries_are_shared_across_names(self):
        rom = interfaces(4)
        self.assertEqual(rom("func_08000200"), (frozenset(), frozenset({"r0"})))
        self.assertEqual(rom.budget, semantics.MAX_CALLEES - 5)
        # the leaf at LEAVES was cached exactly by the first name: no budget spent
        self.assertEqual(rom(f"func_{LEAVES:08X}"), (frozenset(), frozenset({"r0"})))
        self.assertEqual(rom.budget, semantics.MAX_CALLEES)

    def test_a_later_name_whose_tree_was_cut_is_analysed_afresh(self):
        # T calls W, which is wider than the budget, so under T the summary of
        # W is cut.  Asked for later as its own name, W gets a fresh budget and
        # is not served the cut summary left from T.
        rom = semantics.RomInterfaces(*rom_with(
            [(0x08000200, wide(semantics.MAX_CALLEES + 4)),
             (0x08000900, [0xB500, ("bl", 0x08000200), 0xBC01, 0x4700])] + leaves()))
        self.assertEqual(rom("func_08000900"), (UNREAD_R0, frozenset({"r0"})))
        self.assertEqual(rom("func_08000200"), (frozenset(), frozenset({"r0"})))

    def test_a_later_name_that_reads_r1_still_reads_r1(self):
        rom = semantics.RomInterfaces(*rom_with(
            [(0x08000200, wide(semantics.MAX_CALLEES + 4)), (0x08000800, READS_R1)] + leaves()))
        rom("func_08000200")
        self.assertEqual(rom.budget, 0)
        self.assertEqual(rom("func_08000800"), (frozenset({"r1"}), frozenset({"r0"})))

    def test_a_reader_past_the_budget_fails_closed(self):
        # the callee past the budget reads r1; it is not analysed, so the name
        # counts as reading r1
        last = LEAVES + 4 * (semantics.MAX_CALLEES + 8)
        words = [0xB500] + [("bl", LEAVES + 4 * i) for i in range(semantics.MAX_CALLEES)] + \
                [("bl", last), 0xBC01, 0x4700]
        rom = semantics.RomInterfaces(*rom_with([(0x08000200, words), (last, READS_R1)] + leaves()))
        self.assertEqual(rom("func_08000200"), (UNREAD_R0, frozenset({"r0"})))


if __name__ == "__main__":
    unittest.main()
