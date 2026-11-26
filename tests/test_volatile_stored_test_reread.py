"""kit#375, rule R4: the re-read of a stored member for its own test.

`sym.m--; if (sym.m == 0)` reads the volatile member again after the store;
without the qualifier agbcc tests the stored value (08057578 0x08057A3C:
`strb r0, [r2]; ldrb r0, [r2]; adds r2, r0, #0; cmp r2, #0; beq`).  Under the
forwarded re-reads' premise the re-read is an optional counterpart, but only
when it directly follows the store and feeds exactly one comparison whose flags
reach a branch.
"""
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import volatile_semantics as semantics
import test_volatile_semantics as fixtures

SYMBOL = fixtures.SYMBOL
MEMBER = semantics.add(("sym", SYMBOL), 0x3C)
OTHER = semantics.add(("sym", SYMBOL), 0x3D)


def pinned_width(address):
    return 1 if address in (MEMBER, OTHER) else None


def step(text, kind="alu", reads=(), writes=(), **fields):
    return (text, kind, reads, writes, fields)


STORE = step("strb\tr0, [r1]", "store", ("r0", "r1"), (), address=MEMBER, width=1, value_register="r0")
LOAD = step("ldrb\tr0, [r1]", "load", ("r1",), ("r0",), address=MEMBER, width=1, forwarded=True)
COMPARE = step("cmp\tr0, #0", reads=("r0",), flags_written=True)
BRANCH = step("bne\t.L9", "branch")
OVERWRITE = step("mov\tr0, #5", writes=("r0",), constant=True, immediate=True, flags_written=True)


def records(*steps):
    return [semantics.Record(index, text, kind, reads, writes, **fields)
            for index, (text, kind, reads, writes, fields) in enumerate(steps)]


def classified(*steps, position=None):
    built = records(*steps)
    if position is None:
        position = next(index for index, record in enumerate(built) if record.text == LOAD[0] or
                        record.kind == "load" and record.forwarded)
    return semantics.stored_value_test_reread(built, position, pinned_width)


class RuleTests(unittest.TestCase):
    def test_the_re_read_for_the_test_is_admitted(self):
        self.assertTrue(classified(STORE, LOAD, COMPARE, BRANCH, OVERWRITE))
        # through an unchanged copy, and with an unrelated literal load in between
        copy = step("add\tr2, r0, #0", reads=("r0",), writes=("r2",), copy=True, flags_written=True)
        literal = step("ldr\tr3, .L5", "literal", (), ("r3",))
        self.assertTrue(classified(STORE, literal, LOAD, copy, step("cmp\tr2, #0", reads=("r2",),
                                                                     flags_written=True), BRANCH, OVERWRITE,
                                   step("mov\tr2, #1", writes=("r2",), flags_written=True)))
        # the far form `beq .LCB; b .L`
        self.assertTrue(classified(STORE, LOAD, COMPARE, BRANCH, step("b\t.L7", "branch", unconditional=True),
                                   OVERWRITE))

    def test_stores_of_the_tested_value_after_the_branch_are_admitted(self):
        # agbcc reuses the register the branch proved zero for later stores of zero
        store = step("strb\tr0, [r3]", "store", ("r0", "r3"), (), address=("arg", "r3"), width=1,
                     value_register="r0")
        self.assertTrue(classified(STORE, LOAD, COMPARE, BRANCH, store, store, OVERWRITE))
        # but not as an address, in arithmetic, as a call argument, or returned
        for use in (step("strb\tr3, [r0]", "store", ("r0", "r3"), (), address=("arg", "r0"), width=1,
                         value_register="r3"),
                    step("strb\tr0, [r0, #1]", "store", ("r0",), (), address=("arg", "r0"), width=1,
                         value_register="r0"),
                    step("add\tr3, r0, #1", reads=("r0",), writes=("r3",), flags_written=True),
                    step("bl\tfunc_0802A2C0", "call", ("r0", "r1", "r2", "r3"), ("r0", "r1", "r2", "r3", "lr")),
                    step("bx\tlr", "return", ("r0",)),
                    step(".L2", "loop")):
            with self.subTest(use=use[0]):
                self.assertFalse(classified(STORE, LOAD, COMPARE, BRANCH, use, OVERWRITE))
        # a copy's own flags may not reach another branch
        copy = step("add\tr2, r0, #0", reads=("r0",), writes=("r2",), copy=True, flags_written=True)
        self.assertFalse(classified(STORE, LOAD, COMPARE, BRANCH, copy, step("beq\t.L8", "branch"), OVERWRITE))

    def test_the_load_must_be_the_forwarded_unsigned_member_read(self):
        for changes in ({"forwarded": False}, {"signed": True}, {"width": 2}, {"address": OTHER}):
            with self.subTest(changes=changes):
                text, kind, reads, writes, fields = LOAD
                load = (text, kind, reads, writes, {**fields, **changes})
                self.assertFalse(classified(STORE, load, COMPARE, BRANCH, OVERWRITE, position=1))

    def test_the_store_must_come_directly_before(self):
        between = (step("ldr\tr3, [r4]", "load", ("r4",), ("r3",), address=("arg", "r4"), width=4),
                   step("bl\tfunc_0802A2C0", "call", ("r0",), ("r0", "r1", "r2", "r3", "lr")),
                   step("beq\t.L5", "branch"),
                   step("add\tr1, r1, #0", reads=("r1",), writes=("r1",), copy=True))
        for record in between:
            with self.subTest(between=record[0]):
                self.assertFalse(classified(STORE, record, LOAD, COMPARE, BRANCH, OVERWRITE, position=2))
        self.assertFalse(classified(LOAD, COMPARE, BRANCH, OVERWRITE, position=0))
        wider = step("strh\tr0, [r1]", "store", ("r0", "r1"), (), address=MEMBER, width=2, value_register="r0")
        self.assertFalse(classified(wider, LOAD, COMPARE, BRANCH, OVERWRITE))

    def test_exactly_one_comparison_reaches_the_branch(self):
        stored = step("strb\tr0, [r3]", "store", ("r0", "r3"), (), address=("arg", "r3"), width=1,
                      value_register="r0")
        for shape in ((COMPARE, step("cmp\tr0, #1", reads=("r0",), flags_written=True), BRANCH),
                      (COMPARE, step("mov\tr3, #1", writes=("r3",), constant=True, flags_written=True), BRANCH),
                      (COMPARE, step("add\tr3, r0, #0", reads=("r0",), writes=("r3",), copy=True), BRANCH),
                      (stored, COMPARE, BRANCH),
                      (step("add\tr3, r0, #1", reads=("r0",), writes=("r3",), flags_written=True), BRANCH),
                      (BRANCH,),
                      (step("b\t.L9", "branch", unconditional=True),),
                      (OVERWRITE, COMPARE, BRANCH),
                      (COMPARE,)):
            with self.subTest(shape=[record[0] for record in shape]):
                self.assertFalse(classified(STORE, LOAD, *shape, OVERWRITE))


def body(*test, after=("mov\tr0, #5",), narrow=False):
    """`sym.unknown_3C--; if (sym.unknown_3C == 0) ...`: real (re-read) or stripped (narrowed) compile"""
    tail = (("lsl\tr0, r0, #24", "lsr\tr0, r0, #24") if narrow else ("ldrb\tr0, [r1]",))
    rmw = () if narrow else ("ldrb\tr2, [r1]",)
    return fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "ldrb\tr0, [r1]", "sub\tr0, r0, #1", *rmw,
                             "strb\tr0, [r1]", *tail, *test, "bne\t.L9", *after, ".L9:", "bx\tlr")


class CompareTests(unittest.TestCase):
    def test_the_decrement_test_passes_and_prints_the_premise(self):
        results = fixtures.compare(body("cmp\tr0, #0"), body("cmp\tr0, #0", narrow=True))
        line = semantics.record(SYMBOL, results)
        self.assertIn("stored-value test re-reads (kit#375) at [7]", line)
        self.assertIn("(the chained, same-member constant update, ordinary-store and stored-value test lists) "
                      "under premise: " + semantics.FORWARDED_REREADS.premise, line)

    def test_without_the_premise_or_with_a_second_reader_it_refuses(self):
        with self.assertRaisesRegex(semantics.SemanticError, "the qualifier added a read"):
            fixtures.compare(body("cmp\tr0, #0", "cmp\tr0, #1"), body("cmp\tr0, #0", "cmp\tr0, #1", narrow=True))
        enabled = semantics.FORWARDED_REREADS.enabled
        semantics.FORWARDED_REREADS.enabled = False
        try:
            with self.assertRaisesRegex(semantics.SemanticError, "the qualifier added a read"):
                fixtures.compare(body("cmp\tr0, #0"), body("cmp\tr0, #0", narrow=True))
        finally:
            semantics.FORWARDED_REREADS.enabled = enabled

    def test_a_record_without_the_rule_keeps_its_text(self):
        plain = fixtures.compare(fixtures.assembly("bx\tlr"), fixtures.assembly("bx\tlr"))
        self.assertNotIn("stored-value test", semantics.record(SYMBOL, plain))


if __name__ == "__main__":
    unittest.main()
