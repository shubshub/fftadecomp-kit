"""The forwarded re-read premise in the allowlisted volatile semantics record.

A chained, same-member constant update or ordinary-store re-read is admitted
because the stripped compile reuses the value it has just stored.  That is the
same read only if nothing writes the member between the forwarding store and
its re-read, which the check does not prove for an interrupt or a DMA.  The
record prints that premise for each function that lists such a re-read, and
for no other, and a saved report is refused when the clause is missing.
"""
import itertools
import os
import shutil
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import match_evidence
import report_fixtures
import plausible
import unsigned_divmod_profile
import volatile_semantics as semantics
import volatile_tested_update as tested_update
import test_volatile_semantics as fixtures
import test_volatile_forwarded_pairing as pairing
import test_volatile_forwarded_update as forwarded_update
import test_volatile_plain_chain as plain_chain
import test_volatile_records_all_profiles as profiles

PREMISE = ("the member is ordinary memory and nothing writes it between the forwarding store and "
           "its re-read (no interrupt, DMA or other asynchronous write), so the re-read returns the "
           "stored value, which the stripped compile reuses")
CLAUSE = (", forwarded re-reads (the chained, same-member constant update and ordinary-store lists) "
          "under premise: " + PREMISE)
HEAD = "* allowlisted volatile semantics: `g` stripped of volatile compiles to the same behaviour; "
ADDED = "the qualifier added a read"
COMPILER = (Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which("cpp") and
            shutil.which("arm-none-eabi-as") and shutil.which("arm-none-eabi-objcopy"))


def result(chained=(), updates=(), ordinary=(), unloaded=(), relied=(), conditional=(), indirect=(),
           premises=(), tested=(), name="f"):
    """one function's result with every part compare_function can return"""
    parts = (name, 2, [1], list(chained), list(unloaded), list(relied), list(updates), list(ordinary),
             list(conditional), list(indirect), list(premises))
    return parts + ((tested_update.Rereads(tested),) if tested else ())


def forwarded_lists(report):
    """the chained, same-member constant update and ordinary-store lists of one compare_function result"""
    parts = [part for part in report[2:] if not isinstance(part, tested_update.Rereads)] + [[]] * 6
    return parts[1], parts[4], parts[5]


class ForwardedPremiseRecordTests(unittest.TestCase):
    def test_the_premise_is_the_documented_sentence(self):
        self.assertEqual(semantics.FORWARDED_REREADS.premise, PREMISE)
        self.assertIs(semantics.FORWARDED_REREADS.enabled, True)

    def test_the_premise_is_printed_exactly_when_a_forwarded_list_is_non_empty(self):
        others = (dict(), dict(unloaded=[4]), dict(relied=["func_1 reads {r0} writes {r0}"]),
                  dict(conditional=["func_2: c"], indirect=["r3: void (*)(void)"]),
                  dict(premises=semantics.FRAME_READ_PREMISES), dict(tested=[8]),
                  dict(unloaded=[4], relied=["x"], conditional=["y"], indirect=["z"],
                       premises=["p"], tested=[8]))
        for chained, updates, ordinary in itertools.product(([], [5]), ([], [6]), ([], [7])):
            for other in others:
                with self.subTest(chained=chained, updates=updates, ordinary=ordinary, other=other):
                    record = semantics.record("g", [result(chained, updates, ordinary, **other)])
                    listed = bool(chained or updates or ordinary)
                    self.assertEqual(record.count(CLAUSE), int(listed))
                    self.assertEqual(record.count(PREMISE), int(listed))
                    self.assertEqual(record.count("forwarded re-reads"), int(listed))

    def test_records_without_a_forwarded_list_keep_their_text(self):
        self.assertEqual(semantics.record("g", [("f", 1, [2, 6], [])]),
                         HEAD + "`f` agrees on 1 path; read-modify-write loads at [3, 7], chained re-reads at []")
        self.assertEqual(
            semantics.record("g", [result(unloaded=[4], relied=["x"], conditional=["y"], indirect=["z"],
                                          premises=["p"])], perturbed=True),
            HEAD.replace("behaviour; ", "behaviour, and a compile with the pinned bytes moved follows every "
                                        "pinned access; ") +
            "`f` agrees on 2 paths; read-modify-write loads at [2], chained re-reads at [], unloaded all-ones "
            "stores at [5], callee interfaces from ROM: x, conditional callee interfaces: y, indirect calls "
            "typed by declaration: z, frame reads under premises: p")
        self.assertEqual(
            semantics.record("g", [result(tested=[8])]),
            HEAD + "`f` agrees on 2 paths; read-modify-write loads at [2], chained re-reads at [], tested-update "
                   f"re-reads at [9] (tested-update-reread-v1, premise: {tested_update.POLICY.premise})")

    def test_the_clause_follows_the_lists_it_covers(self):
        self.assertEqual(semantics.record("g", [("f", 1, [2, 7], [5])]),
                         HEAD + "`f` agrees on 1 path; read-modify-write loads at [3, 8], chained re-reads at [6]" +
                         CLAUSE)
        self.assertEqual(
            semantics.record("g", [result([5], [6], [7], unloaded=[4], relied=["x"], tested=[8])]),
            HEAD + "`f` agrees on 2 paths; read-modify-write loads at [2], chained re-reads at [6], unloaded "
                   "all-ones stores at [5], same-member constant update re-reads at [7], ordinary-store chained "
                   "re-reads at [8]" + CLAUSE +
                   f", tested-update re-reads at [9] (tested-update-reread-v1, premise: "
                   f"{tested_update.POLICY.premise}), callee interfaces from ROM: x")

    def test_each_function_prints_it_for_its_own_lists(self):
        plain, chained = result(name="plain"), result(ordinary=[3], name="chained")
        record = semantics.record("g", [plain, chained])
        first, second = record[len(HEAD):].split("; `")
        self.assertTrue(first.startswith("`plain` agrees"))
        self.assertNotIn("premise", first)
        self.assertTrue(second.startswith("chained` agrees"))
        self.assertTrue(second.endswith("ordinary-store chained re-reads at [4]" + CLAUSE))
        both = semantics.record("g", [result(updates=[3], name="update"), chained])
        self.assertEqual(both.count(CLAUSE), 2)


class ForwardedPremiseComparisonTests(unittest.TestCase):
    """the three rules through compare_function: each prints the premise, and the switch refuses each"""

    @staticmethod
    def chained():
        # `sym.unknown_3C = (sym.unknown_3D = 0);`
        real = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #0", "add\tr2, r2, #61", "ldrb\tr0, [r2]",
                                 "mov\tr1, #0", "strb\tr1, [r2]", "ldrb\tr0, [r2]", "sub\tr2, r2, #1",
                                 "ldrb\tr1, [r2]", "strb\tr0, [r2]", "bx\tlr")
        stripped = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #61", "mov\tr1, #0", "strb\tr1, [r2]",
                                     "sub\tr2, r2, #1", "strb\tr1, [r2]", "bx\tlr")
        return real, stripped

    @staticmethod
    def plain():
        # `sym.unknown_3C = 1;`: no forwarded re-read
        real = fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "ldrb\tr0, [r1]", "mov\tr0, #1",
                                 "strb\tr0, [r1]", "bx\tlr")
        stripped = fixtures.assembly("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr0, #1", "strb\tr0, [r1]",
                                     "bx\tlr")
        return real, stripped

    def shapes(self):
        return (("chained re-reads at [7]", self.chained(), 0),
                ("same-member constant update re-reads at [", forwarded_update.ForwardedUpdateTests().bodies(), 1),
                ("ordinary-store chained re-reads at [", plain_chain.PlainChainTests().bodies(), 2))

    def test_each_forwarded_rule_is_recorded_with_the_premise(self):
        for listed, (real, stripped), part in self.shapes():
            with self.subTest(listed=listed):
                (report,) = fixtures.compare(real, stripped)
                self.assertEqual([bool(listing) for listing in forwarded_lists(report)],
                                 [index == part for index in range(3)])
                record = semantics.record(fixtures.SYMBOL, [report])
                self.assertIn(listed, record)
                self.assertEqual(record.count(CLAUSE), 1)

    def test_a_function_without_a_forwarded_re_read_prints_no_premise(self):
        (report,) = fixtures.compare(*self.plain())
        self.assertEqual(report, ("func_08028C34", 1, [2], [], [], []))
        self.assertEqual(semantics.record(fixtures.SYMBOL, [report]),
                         f"* allowlisted volatile semantics: `{fixtures.SYMBOL}` stripped of volatile compiles "
                         "to the same behaviour; `func_08028C34` agrees on 1 path; read-modify-write loads at "
                         "[3], chained re-reads at []")

    def test_policy_switch_refuses_exactly_the_listed_re_reads(self):
        self.addCleanup(setattr, semantics.FORWARDED_REREADS, "enabled", True)
        semantics.FORWARDED_REREADS.enabled = False
        for listed, (real, stripped), _ in self.shapes():
            with self.subTest(listed=listed):
                with self.assertRaises(semantics.SemanticError) as caught:
                    fixtures.compare(real, stripped)
                self.assertIn(ADDED, str(caught.exception))
        (report,) = fixtures.compare(*self.plain())
        self.assertEqual(report, ("func_08028C34", 1, [2], [], [], []))
        semantics.FORWARDED_REREADS.enabled = True
        for listed, (real, stripped), _ in self.shapes():
            with self.subTest(listed=listed, enabled=True):
                self.assertTrue(fixtures.compare(real, stripped))


class ForwardedPremiseReplayTests(unittest.TestCase):
    """match_evidence.report_matches recomputes the record, so the clause cannot be dropped or added"""
    USES = "* allowlisted volatile: `g_control_flags_03000940` at `0x03000940` declared in x"
    CHAINED = semantics.record(fixtures.SYMBOL, [("func_08028C34", 1, [3, 8], [6])])
    PLAIN = semantics.record(fixtures.SYMBOL, [("func_08028C34", 1, [3, 8], [])])

    def matches(self, saved, fresh):
        report = "\n".join(("* verification: x", "* source plausibility: plausible", self.USES, saved,
                            "* hand-asm allow list: not listed", "", "**MATCH - byte identical** - 4/4 bytes", ""))
        with mock.patch.object(plausible, "allowlisted_volatile_uses", return_value=[self.USES]), \
                mock.patch.object(match, "allowlisted_volatile_semantics", return_value=[fresh]), \
                mock.patch.object(unsigned_divmod_profile, "selected", return_value=True), \
                mock.patch.object(unsigned_divmod_profile, "report_matches", return_value=True), \
                report_fixtures.premise_line_checked_elsewhere():
            return match_evidence.report_matches(report, "/nonexistent", 0x08028C34)

    def test_a_record_with_the_clause_removed_is_refused(self):
        self.assertTrue(self.CHAINED.endswith("chained re-reads at [7]" + CLAUSE))
        self.assertTrue(self.matches(self.CHAINED, self.CHAINED))
        self.assertFalse(self.matches(self.CHAINED.replace(CLAUSE, ""), self.CHAINED))
        self.assertFalse(self.matches(self.CHAINED.replace(PREMISE, PREMISE.split(" (no ")[0]), self.CHAINED))

    def test_a_record_with_the_clause_added_is_refused(self):
        self.assertNotIn("premise", self.PLAIN)
        self.assertTrue(self.matches(self.PLAIN, self.PLAIN))
        self.assertFalse(self.matches(self.PLAIN + CLAUSE, self.PLAIN))


@unittest.skipUnless(COMPILER, "fixed compiler required")
class CompiledForwardedPremiseTests(unittest.TestCase):
    """through agbcc: the premise follows the listed re-reads, not the forwarded loads the pairing explains"""
    setUpClass = classmethod(pairing.CompiledForwardedPairingTests.setUpClass.__func__)
    tearDownClass = classmethod(pairing.CompiledForwardedPairingTests.tearDownClass.__func__)
    check = pairing.CompiledForwardedPairingTests.check

    def sources(self):
        s = fixtures.SYMBOL
        # (body, parameters, the lists the record prints, whether a forwarded re-read is listed)
        return ((f"{s}.bldcnt_lo = ({s}.bldcnt_hi = 0);", "void",
                 "read-modify-write loads at [4, 9], chained re-reads at [7]", True),
                (f"{s}.bldcnt_hi = 0;\n*q = {s}.bldcnt_hi;", "u8 *q",
                 "chained re-reads at [], ordinary-store chained re-reads at [6]", True),
                (f"{s}.bldcnt_lo = 63;\nif (c <= 1) {s}.bldcnt_lo |= 128; else {s}.bldcnt_lo |= 192;",
                 "signed char c", "chained re-reads at [], same-member constant update re-reads at [13, 16]", True),
                # the join read is forwarded on one path and pairs with the stripped compile's reload
                (f"if (c) {s}.bldalpha_lo = 5;\n{s}.bldalpha_hi = {s}.bldalpha_lo;", "u8 c",
                 "chained re-reads at []", False),
                (f"{s}.bldcnt_lo = 1;\n{s}.bldcnt_hi = 2;", "void", "chained re-reads at []", False))

    def test_the_premise_follows_the_listed_re_reads(self):
        for body, parameters, lists, listed in self.sources():
            with self.subTest(body=body):
                (record,) = self.check(body, parameters)
                self.assertIn(lists, record)
                self.assertEqual(record.count(CLAUSE), int(listed))
                self.assertEqual(record.count("premise"), int(listed))

    def test_policy_switch_refuses_the_listed_re_reads_and_keeps_the_other_records(self):
        enabled = {body: self.check(body, parameters) for body, parameters, _, _ in self.sources()}
        self.addCleanup(setattr, semantics.FORWARDED_REREADS, "enabled", True)
        semantics.FORWARDED_REREADS.enabled = False
        for body, parameters, _, listed in self.sources():
            with self.subTest(body=body):
                if listed:
                    with self.assertRaises(semantics.SemanticError) as caught:
                        self.check(body, parameters)
                    self.assertIn(ADDED, str(caught.exception))
                else:
                    self.assertEqual(self.check(body, parameters), enabled[body])


@unittest.skipUnless(COMPILER, "fixed compiler required")
class CompiledForwardedPremiseReplayTests(unittest.TestCase):
    """a written report of a chained assignment replays, and not with the clause removed"""
    DATA = profiles.OwnerRuntimeRecordTests.DATA
    tree = profiles.OwnerRuntimeRecordTests.tree
    profile = profiles.OwnerRuntimeRecordTests.profile
    run_owner = profiles.OwnerRuntimeRecordTests.run_owner

    def test_written_report_is_refused_with_the_clause_removed(self):
        first, second = profiles.PINNED
        root = self.tree(f"{profiles.SYMBOL}.{first} = ({profiles.SYMBOL}.{second} = 0);")
        build, render = self.profile()
        with build, render:
            status, output = self.run_owner(root)
            self.assertEqual(status, 0, output)
            report = (root / f"docs/match/{profiles.A:08X}.md").read_text()
            (line,) = [line for line in report.split("\n") if line.startswith("* allowlisted volatile semantics")]
            self.assertEqual(line.count(CLAUSE), 1)
            self.assertTrue(match_evidence.report_matches(report, root, profiles.A))
            self.assertFalse(match_evidence.report_matches(report.replace(CLAUSE, ""), root, profiles.A))
            self.assertFalse(match_evidence.report_matches(report.replace(PREMISE, PREMISE.replace("DMA", "dma")),
                                                           root, profiles.A))


if __name__ == "__main__":
    unittest.main()
