"""tested-update-reread-v1: `if (sym.x < N) sym.x++;` re-reads the member for its update."""

import copy
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import plausible
import volatile_semantics as semantics
import volatile_tested_update as tested_update
import test_volatile_semantics as fixtures

ADDED = "the qualifier added a read"


def bodies(*, before_test=(), test=("cmp\tr0, #15", "bhi\t.Lelse"), between=(),
           reread="ldrb\tr0, [r2]", before_update=(), update="add\tr0, r0, #1", after_update=(),
           insertion="ldrb\tr1, [r2]", store="strb\tr0, [r2]", suffix=(),
           stripped_test=None, stripped_update=None, stripped_store="strb\tr0, [r1]",
           stripped_before_update=(), stripped_after_update=(), stripped_suffix=None,
           stripped_reread=(), stripped_reread_else=()):
    """0x0812BA08's case 0x102 on the fixture object: `if (x < 16) x++; else if (y != 0) y--;`

    with x = unknown_3C and y = unknown_3D; the two updates share the store
    tail, as agbcc cross-jumps them.  The real re-reads are instructions 7
    and 15 (1-based), the shared read-modify-write load 17."""
    real = fixtures.assembly(
        "ldr\tr5, .L3", "add\tr2, r5, #0", "add\tr2, r2, #60", "ldrb\tr0, [r2]", *before_test,
        *test, *between, reread, *before_update, update, *after_update, "b\t.Lstore",
        ".Lelse:", "add\tr2, r5, #0", "add\tr2, r2, #61", "ldrb\tr0, [r2]", "cmp\tr0, #0",
        "beq\t.Ldone", "ldrb\tr0, [r2]", "sub\tr0, r0, #1", ".Lstore:",
        *((insertion,) if insertion else ()), store, ".Ldone:", *suffix, "bx\tlr")
    stripped = fixtures.assembly(
        "ldr\tr5, .L3", "add\tr1, r5, #0", "add\tr1, r1, #60", "ldrb\tr0, [r1]", *before_test,
        *(test if stripped_test is None else stripped_test), *between, *stripped_reread,
        *stripped_before_update,
        update if stripped_update is None else stripped_update, *stripped_after_update,
        stripped_store, "b\t.Ldone",
        ".Lelse:", "add\tr1, r5, #0", "add\tr1, r1, #61", "ldrb\tr0, [r1]", "cmp\tr0, #0",
        "beq\t.Ldone", *stripped_reread_else, "sub\tr0, r0, #1", "strb\tr0, [r1]", ".Ldone:",
        *(suffix if stripped_suffix is None else stripped_suffix), "bx\tlr")
    return real, stripped


def admitted(real, stripped):
    """[(records, position, pinned_width)] for every load the rule admitted"""
    calls, original = [], tested_update.tested_update_reread

    def spy(records, position, pinned_width):
        verdict = original(records, position, pinned_width)
        if verdict:
            calls.append((records, position, pinned_width))
        return verdict

    with mock.patch.object(tested_update, "tested_update_reread", side_effect=spy):
        fixtures.compare(real, stripped)
    return sorted(calls, key=lambda call: call[0][call[1]].index)


def single(insertion="ldrb\tr1, [r2]", store="strb\tr0, [r2]", stripped_store="strb\tr0, [r1]"):
    """`if (x < 16) x++;` alone, with the store replaceable"""
    real = fixtures.assembly("ldr\tr2, .L3", "add\tr2, r2, #60", "ldrb\tr0, [r2]", "cmp\tr0, #15",
                             "bhi\t.Ldone", "ldrb\tr0, [r2]", "add\tr0, r0, #1",
                             *((insertion,) if insertion else ()), store, ".Ldone:", "bx\tlr")
    stripped = fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "ldrb\tr0, [r1]", "cmp\tr0, #15",
                                 "bhi\t.Ldone", "add\tr0, r0, #1", stripped_store, ".Ldone:", "bx\tlr")
    return real, stripped


class TestedUpdateComparisonTests(unittest.TestCase):
    def refused(self, reason=ADDED, **kwargs):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(*bodies(**kwargs))
        self.assertIn(reason, str(caught.exception))

    def test_the_target_shape_is_admitted_and_recorded_with_its_premise(self):
        (report,) = fixtures.compare(*bodies())
        self.assertEqual(report[:4], ("func_08028C34", 3, [16], []))
        self.assertIsInstance(report[-1], tested_update.Rereads)
        self.assertEqual(report[-1], [6, 14])
        record = semantics.record(fixtures.SYMBOL, [report])
        self.assertIn("read-modify-write loads at [17], chained re-reads at [], tested-update "
                      f"re-reads at [7, 15] (tested-update-reread-v1, premise: "
                      f"{tested_update.POLICY.premise})", record)
        self.assertEqual(record.count(tested_update.POLICY.premise), 1)

    def test_records_without_the_rule_keep_their_text(self):
        real = fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "ldrb\tr0, [r1]", "mov\tr0, #1",
                                 "strb\tr0, [r1]", "bx\tlr")
        stripped = fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr0, #1",
                                     "strb\tr0, [r1]", "bx\tlr")
        (report,) = fixtures.compare(real, stripped)
        self.assertEqual(report, ("func_08028C34", 1, [2], [], [], []))
        self.assertNotIn("tested-update", semantics.record(fixtures.SYMBOL, [report]))
        # the tag is found after any optional part, and a plain list is not it
        tagged = report + ([], [], [], [], tested_update.Rereads([4]))
        self.assertIn("tested-update re-reads at [5]", semantics.record(fixtures.SYMBOL, [tagged]))
        plain = report + ([], [], [], [], [4])
        self.assertNotIn("tested-update", semantics.record(fixtures.SYMBOL, [plain]))
        # nor is the tag read as one of the positional parts
        early = semantics.record(fixtures.SYMBOL, [report + (tested_update.Rereads([4]),)])
        self.assertIn("tested-update re-reads at [5]", early)
        self.assertNotIn("same-member constant update", early)

    def test_a_re_read_the_stripped_compile_keeps_stays_a_counterpart(self):
        # main's verdict and record: both compiles load the member again
        (report,) = fixtures.compare(*bodies(stripped_reread=("ldrb\tr0, [r1]",),
                                             stripped_reread_else=("ldrb\tr0, [r1]",)))
        self.assertEqual(report, ("func_08028C34", 3, [16], [], [], []))
        self.assertNotIn("tested-update", semantics.record(fixtures.SYMBOL, [report]))

    def test_only_the_re_reads_the_stripped_compile_lacks_are_listed(self):
        (report,) = fixtures.compare(*bodies(stripped_reread=("ldrb\tr0, [r1]",)))
        self.assertEqual(report[-1], [14])
        (report,) = fixtures.compare(*bodies(stripped_reread_else=("ldrb\tr0, [r1]",)))
        self.assertEqual(report[-1], [6])

    def test_policy_switch_restores_the_refusal(self):
        self.addCleanup(setattr, tested_update.POLICY, "enabled", True)
        tested_update.POLICY.enabled = False
        self.refused()
        tested_update.POLICY.enabled = True
        self.assertTrue(fixtures.compare(*bodies()))

    def test_no_candidates_under_a_callers_own_trace_pairing(self):
        # the overwritten-store composition pairs traces itself and prints no premise (review finding 4)
        real, stripped = bodies()
        size, pinned = semantics.pinned_members(fixtures.DECLARATION)
        functions = [semantics.parse_assembly(text)[0]["func_08028C34"] for text in (real, stripped)]
        signatures = {"func_08028C34": (False, 0)}
        with self.assertRaises(semantics.SemanticError) as caught:
            semantics.compare_function("func_08028C34", *functions, signatures, fixtures.SYMBOL, size, pinned,
                                       _ordered_trace_check=lambda path, other, dead: (path.trace, other.trace))
        self.assertIn(ADDED, str(caught.exception))
        self.assertEqual(semantics.compare_function("func_08028C34", *functions, signatures, fixtures.SYMBOL,
                                                    size, pinned)[-1], [6, 14])

    def test_ordinary_loads_are_not_paired(self):
        # a load outside the object, in both compiles, is no counterpart on either side
        report, = fixtures.compare(*bodies(suffix=("ldr\tr4, [r6]", "str\tr4, [r7]")))
        self.assertEqual(report[-1], [6, 14])

    def test_a_test_through_a_copy_counts(self):
        report, = fixtures.compare(*bodies(test=("mov\tr3, r0", "cmp\tr3, #15", "bhi\t.Lelse")))
        self.assertEqual(report[-1], [7, 15])

    def test_untested_re_read_is_refused(self):
        # `t = x; if (n < 16) x++; ...; y = t`: the first read is used, not tested
        kwargs = dict(test=("mov\tr3, r0", "cmp\tr4, #15", "bhi\t.Lelse"), suffix=("strb\tr3, [r6]",))
        self.refused(**kwargs)
        # the same with the copy tested is admitted
        self.assertTrue(fixtures.compare(*bodies(**dict(kwargs, test=(
            "mov\tr3, r0", "cmp\tr3, #15", "bhi\t.Lelse")))))

    def test_a_test_by_a_derived_value_is_not_a_test(self):
        # flags of `x << 1`, not of x or a copy of it; the value itself is spilled
        self.refused(test=("lsl\tr3, r0, #1", "mov\tr4, r0", "cmp\tr3, #15", "bhi\t.Lelse"),
                     suffix=("strb\tr4, [r6]",))
        # the flags a shift or an AND of the value sets itself (review finding 3)
        for test in (("lsl\tr3, r0, #24", "bmi\t.Lelse"), ("mov\tr3, #8", "and\tr3, r0", "beq\t.Lelse")):
            with self.subTest(test=test):
                self.refused(test=test)

    def test_a_comparison_or_a_flag_setting_copy_is_a_test(self):
        for test in (("tst\tr0, r4", "beq\t.Lelse"), ("cmn\tr0, r4", "beq\t.Lelse"),
                     ("mov\tr3, r0", "beq\t.Lelse"), ("add\tr3, r0, #0", "bmi\t.Lelse")):
            with self.subTest(test=test):
                report, = fixtures.compare(*bodies(test=test))
                self.assertEqual(report[-1], [6 + len(test) - 2, 14 + len(test) - 2])

    def test_flags_of_the_value_overwritten_before_the_branch_are_no_test(self):
        self.refused(test=("mov\tr3, r0", "cmp\tr0, #15", "cmp\tr4, #15", "bhi\t.Lelse"),
                     suffix=("strb\tr3, [r6]",))
        # nor is a register that no longer holds the value
        self.refused(test=("mov\tr3, r0", "mov\tr0, r4", "cmp\tr0, #15", "bhi\t.Lelse"),
                     suffix=("strb\tr3, [r6]",), stripped_update="add\tr0, r3, #1")

    def test_memory_access_between_test_and_re_read_is_refused(self):
        for access in ("ldr\tr4, [r6]", "push\t{r4}", "str\tr4, [r6]"):
            with self.subTest(access=access), self.assertRaises(semantics.SemanticError):
                fixtures.compare(*bodies(between=(access,)))
        self.refused(between=("ldr\tr4, [r6]",))

    def test_re_read_of_another_member_is_refused(self):
        # `if (x < 16) x = y + 1;` the stripped compile still loads y
        with self.assertRaises(semantics.SemanticError):
            fixtures.compare(*bodies(reread="ldrb\tr0, [r2, #1]"))

    def test_non_constant_update_is_refused(self):
        self.refused(update="add\tr0, r0, r4")
        self.refused(update="lsl\tr0, r0, #1")
        self.refused(update="orr\tr0, r4")

    def test_second_update_is_refused(self):
        self.refused(after_update=("add\tr0, r0, #1",), stripped_after_update=("add\tr0, r0, #1",))

    def test_other_consumer_of_the_re_read_is_refused(self):
        self.refused(before_update=("mov\tr4, r0",), stripped_before_update=("mov\tr4, r0",),
                     suffix=("str\tr4, [r6]",), stripped_suffix=("str\tr4, [r6]",))
        # of the update's result
        self.refused(after_update=("mov\tr4, r0",), stripped_after_update=("mov\tr4, r0",),
                     suffix=("str\tr4, [r6]",), stripped_suffix=("str\tr4, [r6]",))

    def test_single_update_is_admitted(self):
        (report,) = fixtures.compare(*single())
        self.assertEqual(report[-1], [5])

    def test_store_to_another_member_is_refused(self):
        # `if (x < 16) y = x + 1;`
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(*single(insertion="ldrb\tr1, [r2, #1]", store="strb\tr0, [r2, #1]",
                                     stripped_store="strb\tr0, [r1, #1]"))
        self.assertIn(ADDED, str(caught.exception))

    def test_store_to_ordinary_memory_is_refused(self):
        # `if (x < 16) z = x + 1;`
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(*single(insertion=None, store="strb\tr0, [r6]",
                                     stripped_store="strb\tr0, [r6]"))
        self.assertIn(ADDED, str(caught.exception))

    def test_live_value_after_the_store_is_refused(self):
        self.refused(suffix=("strb\tr0, [r6]",))
        # overwritten first, it is no use
        self.assertTrue(fixtures.compare(*bodies(suffix=("mov\tr0, #0", "strb\tr0, [r6]"))))

    def test_live_update_flags_after_the_store_are_refused(self):
        self.refused(suffix=("beq\t.Lend", "mov\tr3, #1", ".Lend:"))
        # killed by an independent flag writer first, they are no use
        self.assertTrue(fixtures.compare(*bodies(suffix=("cmp\tr4, #0", "beq\t.Lend", "mov\tr3, #1",
                                                         ".Lend:"))))


class TestedUpdateClassifierTests(unittest.TestCase):
    """each obligation alone, on the executor's records of the target shape"""

    def setUp(self):
        self.calls = admitted(*bodies())
        self.assertEqual([records[position].index for records, position, _ in self.calls], [6, 14])
        records, self.position, self.width = self.calls[0]
        self.records = copy.deepcopy(records)
        self.at = {record.index: n for n, record in enumerate(self.records)}

    def record(self, index):
        return self.records[self.at[index]]

    def check(self, records=None, width=None):
        return tested_update.tested_update_reread(records or self.records, self.position,
                                                  width or self.width)

    def test_admitted(self):
        self.assertTrue(self.check())
        # the else-branch decrement, through the shared tail
        records, position, width = self.calls[1]
        self.assertTrue(tested_update.tested_update_reread(records, position, width))

    def test_obligation_1_the_re_read(self):
        for field, value in (("signed", True), ("forwarded", True), ("kind", "store"),
                             ("writes", {"r0", "r7"})):
            with self.subTest(field=field):
                self.setUp()
                setattr(self.record(6), field, value)
                self.assertFalse(self.check())
        self.setUp()
        self.assertFalse(self.check(width=lambda address: 2))
        self.assertFalse(self.check(width=lambda address: None))

    def test_obligation_2_the_tested_read(self):
        for field, value in (("kind", "store"), ("kind", "call"), ("kind", "summary"),
                             ("signed", True), ("width", 2), ("value", ("load", 1, "x", "entry"))):
            with self.subTest(field=field, value=value):
                self.setUp()
                setattr(self.record(3), field, value)
                self.assertFalse(self.check())
        self.setUp()
        self.record(3).address = semantics.add(self.record(3).address, 1)
        self.assertFalse(self.check())
        # nothing but register operations, literal loads and branches between
        for kind in ("load", "store", "call", "push", "pop", "summary", "return"):
            with self.subTest(between=kind):
                self.setUp()
                self.record(4).kind = kind
                self.assertFalse(self.check())
        self.setUp()
        self.record(4).kind = "literal"
        self.assertTrue(self.check())
        self.setUp()
        self.assertFalse(tested_update.tested_update_reread(self.records[:1] + self.records[6:7], 1,
                                                           self.width))

    def test_obligation_2_the_tested_read_lies_before_the_re_read(self):
        # the first memory access of the path is the re-read: no earlier read,
        # even with an identical load later on the path
        tail = self.records[self.at[4]:]
        self.assertFalse(tested_update.tested_update_reread(
            tail + [copy.deepcopy(self.record(3))], self.position - self.at[4], self.width))

    def test_obligation_3_the_test(self):
        self.setUp()
        self.record(5).unconditional = True
        self.assertFalse(self.check())
        self.setUp()
        self.record(4).flags_written = False
        self.assertFalse(self.check())
        self.setUp()
        self.record(4).reads = {"r4"}
        self.assertFalse(self.check())
        # a flag-setting copy reading another register too is no copy of the value alone
        self.setUp()
        self.record(4).copy, self.record(4).reads, self.record(4).writes = True, {"r0", "r4"}, {"r3"}
        self.assertFalse(self.check())
        self.setUp()
        self.record(4).copy, self.record(4).reads, self.record(4).writes = True, {"r0"}, {"r3"}
        self.assertTrue(self.check())
        # only an unchanged copy of the value carries the test
        for reads, admitted in (({"r0"}, True), ({"r0", "r4"}, False)):
            with self.subTest(reads=reads):
                self.setUp()
                carrier = semantics.Record(95, "mov r3, r0", "alu", reads, {"r3"}, copy=True)
                self.record(4).reads = {"r3"}
                records = self.records[:self.at[4]] + [carrier] + self.records[self.at[4]:]
                self.assertEqual(tested_update.tested_update_reread(
                    records, self.position + 1, self.width), admitted)

    def test_obligation_4_the_update(self):
        update = self.record(7)
        for field, value in (("alu_operation", "orr"), ("alu_operation", "mul"), ("copy", True),
                             ("alu_sources", (("r0", None), ("r4", 1))),
                             ("alu_sources", (("r0", None), (None, ("arg", 4)))),
                             ("alu_sources", (("r0", None), (None, 0))),
                             ("alu_sources", (("r0", None), (None, 256))),
                             ("alu_sources", (("r4", None), (None, 1))),
                             ("alu_sources", (("r0", None),)),
                             ("reads", {"r0", "r4"})):
            with self.subTest(field=field, value=value):
                self.setUp()
                setattr(self.record(7), field, value)
                self.assertFalse(self.check())
        self.setUp()
        self.record(7).alu_sources = (("r0", None), (None, 255))
        self.assertTrue(self.check())
        self.assertTrue(tested_update.update_step(update, {"r0"}, 1))
        self.assertFalse(tested_update.update_step(update, {"r1"}, 1))
        self.assertTrue(tested_update.update_step(update, {"r0"}, 2))
        wide = copy.deepcopy(update)
        wide.alu_sources = (("r0", None), (None, 256))
        self.assertFalse(tested_update.update_step(wide, {"r0"}, 1))
        self.assertTrue(tested_update.update_step(wide, {"r0"}, 2))
        wide.alu_sources = (("r0", None), (None, 0x10000))
        self.assertFalse(tested_update.update_step(wide, {"r0"}, 2))
        copied = copy.deepcopy(update)
        copied.copy = True
        self.assertFalse(tested_update.update_step(copied, {"r0"}, 1))
        # a plain copy instead of the update leaves nothing updated
        self.setUp()
        self.record(7).copy = True
        self.record(7).alu_sources = (("r0", None), (None, 0))
        self.assertFalse(self.check())

    def test_obligation_5_the_store(self):
        store = self.at[17]
        for field, value in (("width", 2), ("value_register", "r1"), ("reads", {"r0", "r1", "r2"}),
                             ("address", semantics.add(self.records[store].address, 1))):
            with self.subTest(field=field):
                self.setUp()
                setattr(self.records[store], field, value)
                self.assertFalse(self.check())
        # the read-modify-write load: exactly one, of the member, dead, its store's
        for field, value in (("kind", "alu"), ("signed", True), ("width", 2), ("writes", {"r0"}),
                             ("reads", {"r0", "r2"}), ("address", semantics.add(self.record(16).address, 1))):
            with self.subTest(insertion=field):
                self.setUp()
                setattr(self.record(16), field, value)
                self.assertFalse(self.check())
        # its value read later, or an operation its store's window refuses
        self.setUp()
        later = semantics.Record(96, "mov r3, r1", "alu", {"r1"}, {"r3"}, copy=True)
        self.assertFalse(self.check(self.records[:-1] + [later] + self.records[-1:]))
        self.setUp()
        address = semantics.Record(96, "add r2, r2, r4", "alu", {"r2", "r4"}, {"r2"})
        self.assertFalse(self.check(self.records[:self.at[17]] + [address] + self.records[self.at[17]:]))
        self.setUp()
        twice = self.records[:self.at[16]] + [copy.deepcopy(self.record(16))] + self.records[self.at[16]:]
        self.assertFalse(self.check(twice))
        # an extra record between the update and the store
        for kind, unconditional in (("call", False), ("branch", False), ("push", False),
                                    ("return", False), ("summary", False)):
            with self.subTest(between=kind):
                self.setUp()
                self.record(8).kind, self.record(8).unconditional = kind, unconditional
                self.assertFalse(self.check())
        # a register operation that overwrites the update's result before the store
        self.setUp()
        self.record(8).kind, self.record(8).writes = "alu", {"r0"}
        self.assertFalse(self.check())
        # a conditional branch whose flags the update no longer sets
        self.setUp()
        killer = semantics.Record(97, "cmp r4, #0", "alu", {"r4"}, set(), flags_written=True)
        self.record(8).unconditional = False
        self.assertFalse(self.check(self.records[:self.at[8]] + [killer] + self.records[self.at[8]:]))
        # a literal load is no use
        self.setUp()
        self.record(8).kind, self.record(8).writes = "literal", {"r3"}
        self.assertTrue(self.check())
        # with the result copied to r4, which the store writes: r0 may not be
        # overwritten, by the insertion load or otherwise, nor address the store
        for change in ("insertion", "overwrite", "address", "orr"):
            with self.subTest(copy=change):
                self.setUp()
                extra = semantics.Record(99, "mov r4, r0", "alu", {"r0"}, {"r4"}, copy=True)
                if change == "orr":
                    extra = semantics.Record(99, "orr r4, r0", "alu", {"r0", "r4"}, {"r4"}, copy=True)
                store = self.records[self.at[17]]
                store.value_register, store.reads = "r4", {"r4", "r2"}
                inserted = [extra]
                if change == "insertion":
                    self.record(16).writes = {"r0"}
                elif change == "overwrite":
                    inserted.append(semantics.Record(98, "mov r0, #0", "alu", set(), {"r0"}))
                elif change == "address":
                    store.reads = {"r4", "r0"}
                records = self.records[:self.at[8]] + inserted + self.records[self.at[8]:]
                self.assertFalse(self.check(records))
        # a copy overwritten by another before the store: the first feeds nothing
        self.setUp()
        first = semantics.Record(99, "mov r4, r0", "alu", {"r0"}, {"r4"}, copy=True)
        second = semantics.Record(100, "mov r4, r0", "alu", {"r0"}, {"r4"}, copy=True)
        store = self.records[self.at[17]]
        store.value_register, store.reads = "r4", {"r4", "r2"}
        self.assertFalse(self.check(self.records[:self.at[8]] + [first, second] + self.records[self.at[8]:]))
        self.assertTrue(self.check(self.records[:self.at[8]] + [second] + self.records[self.at[8]:]))
        # a copy that does not feed the store
        self.setUp()
        extra = semantics.Record(99, "mov r4, r0", "alu", {"r0"}, {"r4"}, copy=True)
        records = self.records[:self.at[8]] + [extra] + self.records[self.at[8]:]
        self.assertFalse(self.check(records))
        # a copy that does feed it
        self.setUp()
        extra = semantics.Record(99, "mov r4, r0", "alu", {"r0"}, {"r4"}, copy=True)
        self.records[self.at[17]].value_register = "r4"
        self.records[self.at[17]].reads = {"r4", "r2"}
        records = self.records[:self.at[8]] + [extra] + self.records[self.at[8]:]
        self.assertTrue(self.check(records))

    def test_obligation_6_after_the_store(self):
        self.setUp()
        end = semantics.Record(98, "str r0, [r6]", "store", {"r0", "r6"}, set())
        self.assertFalse(self.check(self.records[:-1] + [end] + self.records[-1:]))
        self.setUp()
        branch = semantics.Record(98, "beq .Lx", "branch", set(), set())
        self.assertFalse(self.check(self.records[:-1] + [branch] + self.records[-1:]))
        self.setUp()
        killer = semantics.Record(97, "cmp r4, #0", "alu", {"r4"}, set(), flags_written=True)
        self.assertTrue(self.check(self.records[:-1] + [killer, branch] + self.records[-1:]))
        self.setUp()
        self.assertFalse(self.check(self.records[:self.at[17]]))
        self.assertFalse(self.check(self.records[:self.at[16]]))

    def test_the_update_is_judged_at_the_member_width(self):
        # a halfword member: +0x100 changes it, as it would not change a byte
        for index in (3, 6, 16, 17):
            self.record(index).width = 2
        self.record(7).alu_sources = (("r0", None), (None, 0x100))
        self.assertTrue(self.check(width=lambda address: 2))
        self.record(7).alu_sources = (("r0", None), (None, 0x10000))
        self.assertFalse(self.check(width=lambda address: 2))


class AlignmentTests(unittest.TestCase):
    """explained: candidates are skipped only where the stripped compile has no load for them"""

    @staticmethod
    def entries(*loads):
        """counterpart entries for (address, value) pairs, as compare_function builds them"""
        return [(1, False, where, semantics.Record(n, where, "load", address=where, width=1, value=value))
                for n, (where, value) in enumerate(loads)]

    @staticmethod
    def stripped(*loads):
        return [semantics.Record(90 + n, where, "load", address=where, width=1, value=value)
                for n, (where, value) in enumerate(loads)]

    @staticmethod
    def pair(counterparts, loads, candidates):
        """explained, given the stripped compile's records, as compare_function calls it"""
        return tested_update.explained(counterparts, [(r.width, r.signed, r.address) for r in loads],
                                       [getattr(r, "value", None) for r in loads], candidates)

    def explained(self, counterparts, theirs, candidates):
        return self.pair(counterparts, self.stripped(*theirs), candidates)

    def test_alignment(self):
        x, y, z = ("x", 1), ("y", 2), ("z", 3)
        a, b, c, d = self.entries(x, x, y, x)
        ids = lambda *entries: {id(entry[3]) for entry in entries}
        for counterparts, theirs, candidates, expected in (
                ([a, b, c], [x, y], ids(b), ids(b)),
                ([a, b, c], [x, y], ids(a), ids(a)),
                ([a, b, c], [x, y], ids(a, b), ids(b)),      # the later one when either will do
                ([a, b], [x], ids(a), ids(a)),
                ([a, b, c], [x, y], set(), None),
                ([a, b, c], [x, y], ids(c), None),
                ([a, b, c], [y], ids(a, b), ids(a, b)),
                ([a, b, c, d], [x, y, x], ids(b), ids(b)),
                ([a, b, c, d], [x, x, y], ids(d), ids(d)),
                ([a, b, c, d], [x, y], ids(b, d), ids(b, d)),
                ([a, b, c, d], [x, y], ids(b), None),
                ([a, c], [x, y], ids(a), set()),
                ([b, c], [x, y, z], ids(b), None),
                ([], [], set(), set())):
            with self.subTest(counterparts=[e[2] for e in counterparts], theirs=theirs):
                self.assertEqual(self.explained(counterparts, theirs, candidates), expected)

    def test_a_pair_needs_the_same_value(self):
        # review finding 1: a second test read (value 1) may not stand in for the stripped
        # compile's later load of the member (value 7, after a store)
        x, later = ("x", 1), ("x", 7)
        test, second, update = self.entries(x, x, x)
        ids = lambda *entries: {id(entry[3]) for entry in entries}
        self.assertIsNone(self.explained([test, second, update], [x, later], ids(update)))
        self.assertEqual(self.explained([test, second, update], [x, x], ids(update)), ids(update))
        # signedness and width count too
        signed = [(1, True, "x", semantics.Record(5, "x", "load", address="x", width=1, value=1))]
        self.assertIsNone(self.explained(signed, [x], set()))
        self.assertEqual(self.pair(signed, [semantics.Record(
            9, "x", "load", address="x", width=1, value=1, signed=True)], set()), set())
        self.assertIsNone(self.pair([test], [semantics.Record(9, "x", "load", address="x", width=2, value=1)],
                                    set()))
        self.assertEqual(self.pair([test], [semantics.Record(9, "x", "load", address="x", width=1, value=1)],
                                   set()), set())

    def test_entries_without_a_value_pair_as_before(self):
        # loop induction's cut: an entry whose record is no load and has no value, on both sides
        cut = (None, None, "loop cut")
        x = ("x", 1)
        test, update = self.entries(x, x)
        real_cut = cut + (semantics.Record(40, "cut", "loop"),)
        self.assertFalse(hasattr(real_cut[3], "value"))
        ids = lambda *entries: {id(entry[3]) for entry in entries}
        stripped = self.stripped(x)
        self.assertEqual(tested_update.explained(
            [test, real_cut, update], [(1, False, "x"), cut], [stripped[0].value, None], ids(update)), ids(update))
        self.assertIsNone(tested_update.explained(
            [test, real_cut, update], [(1, False, "x")], [stripped[0].value], ids(update)))


HEADER = fixtures.HEADER


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which("cpp") and shutil.which("arm-none-eabi-as") and
                     shutil.which("arm-none-eabi-objcopy"), "fixed compiler required")
class CompiledTestedUpdateTests(unittest.TestCase):
    """through agbcc: the target statement passes; planted and neighbouring shapes do not"""

    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        cls.root = Path(cls.directory.name)
        entry = plausible.volatile_allow_entries()[0]
        for name in ("config", "src", "include"):
            (cls.root / name).mkdir()
        (cls.root / "config" / "data_symbols.json").write_text(
            json.dumps({entry["symbol"]: entry["address"]}))
        declaration = entry["declaration"].replace("; ", ";\n    ")
        (cls.root / entry["header"]).write_text(HEADER.format(declaration=declaration))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def check(self, body, parameters="void"):
        (self.root / "src" / "08028C34.c").write_text(
            '#include "control_flags.h"\nextern void func_0802A2C0(u8, u8, u8, u8);\n'
            f"void func_08028C34({parameters})\n{{\n" + body + "\n}\n")
        with mock.patch.dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")):
            return match.allowlisted_volatile_semantics(self.root, 0x08028C34)

    def test_tested_updates_pass(self):
        s = fixtures.SYMBOL
        for body in (f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo++; "
                     f"else if ({s}.bldalpha_hi != 0) {s}.bldalpha_hi--;",
                     f"if ({s}.bldy_lo < 16) {s}.bldy_lo += 2;",
                     f"if ({s}.bg0hofs != 0) {s}.bg0hofs -= 4;"):
            with self.subTest(body=body):
                (record,) = self.check(body)
                self.assertIn("tested-update re-reads at [", record)
                self.assertIn(tested_update.POLICY.premise, record)

    def test_neighbouring_shapes_are_refused(self):
        s = fixtures.SYMBOL
        for body, reason in (
                # the re-read is dead: a planted read before a constant store
                (f"if ({s}.bldalpha_lo < 16) {{ (void){s}.bldalpha_lo; {s}.bldalpha_lo = 3; }}",
                 "dead load"),
                # the re-read feeds another member
                (f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_hi = {s}.bldalpha_lo + 1;", ADDED),
                # not a constant update
                (f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo = {s}.bldalpha_lo << 1;", ADDED),
                # twice tested, then updated: the second test re-reads too
                (f"if ({s}.bldalpha_lo < 16 && {s}.bldalpha_lo != 3) {s}.bldalpha_lo++;", ADDED),
                # the same with both arms updating and a join copy (review finding 1): the stripped
                # compile's join load, after the update, may not pair with the second test's read
                (f"if ({s}.bldalpha_lo < 16) {{ if ({s}.bldalpha_lo != 3) {s}.bldalpha_lo++; "
                 f"else {s}.bldalpha_lo--; }} {s}.bldalpha_hi = {s}.bldalpha_lo;", ADDED),
                # g(x - x): the PR's model has no test and no update
                (f"func_0802A2C0({s}.bldalpha_lo - {s}.bldalpha_lo, 0, 0, 0);", ADDED)):
            with self.subTest(body=body):
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.check(body)
                self.assertIn(reason, str(caught.exception))

    def test_second_test_against_an_argument_with_a_join_copy_is_refused(self):
        s = fixtures.SYMBOL
        with self.assertRaises(semantics.SemanticError) as caught:
            self.check(f"if ({s}.bldalpha_lo < 16) {{ if ({s}.bldalpha_lo != a) {s}.bldalpha_lo++; "
                       f"else {s}.bldalpha_lo--; }} {s}.bldalpha_hi = {s}.bldalpha_lo;", "u8 a")
        self.assertIn(ADDED, str(caught.exception))

    def test_policy_switch_restores_the_refusal(self):
        s = fixtures.SYMBOL
        self.addCleanup(setattr, tested_update.POLICY, "enabled", True)
        tested_update.POLICY.enabled = False
        with self.assertRaises(semantics.SemanticError) as caught:
            self.check(f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo++;")
        self.assertIn(ADDED, str(caught.exception))


if __name__ == "__main__":
    unittest.main()
