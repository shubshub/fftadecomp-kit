"""kit#378: counterparts pair on value and event segment, and forwarded re-reads are optional counterparts."""

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
import test_volatile_semantics as fixtures
import test_volatile_forwarded_update as forwarded_update
import overwritten_control_store_composition as composition
import volatile_tested_update as tested_update

ADDED = "the qualifier added a read"
VALUE = "the stripped compile's load there reads a different value; the qualifier added a read"
ACROSS = "the stripped compile's load there lies across a store or call from it; the qualifier added a read"


def listings(update="lsl\tr0, r0, #1", join=True):
    """issue #378's source 1 (`update` = the shift) or 2 (`add r0, r0, #1`) on the fixture object:
    `if (x < 16) x = f(x); y = x;` with x = unknown_3C and y = unknown_3D"""
    copy_real = ("ldrb\tr0, [r2]", "add\tr1, r3, #0", "add\tr1, r1, #61", "ldrb\tr2, [r1]",
                 "strb\tr0, [r1]") if join else ()
    copy_stripped = ("ldrb\tr1, [r1]", "add\tr0, r2, #0", "add\tr0, r0, #61", "strb\tr1, [r0]") if join else ()
    real = fixtures.assembly("push\t{lr}", "ldr\tr3, .L3", "add\tr2, r3, #0", "add\tr2, r2, #60",
                             "ldrb\tr0, [r2]", "cmp\tr0, #15", "bhi\t.Ljoin", "ldrb\tr0, [r2]", update,
                             "ldrb\tr1, [r2]", "strb\tr0, [r2]", ".Ljoin:", *copy_real, "pop\t{r0}", "bx\tr0")
    stripped = fixtures.assembly("push\t{lr}", "ldr\tr2, .L3", "add\tr1, r2, #0", "add\tr1, r1, #60",
                                 "ldrb\tr0, [r1]", "cmp\tr0, #15", "bhi\t.Ljoin", update, "strb\tr0, [r1]",
                                 ".Ljoin:", *copy_stripped, "pop\t{r0}", "bx\tr0")
    return real, stripped


class ForwardedPairingTests(unittest.TestCase):
    def refused(self, real, stripped, reason):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)
        self.assertIn(reason, str(caught.exception))
        return str(caught.exception)

    def test_issue_source_1_is_refused_and_2_needs_the_tested_update(self):
        message = self.refused(*listings("lsl\tr0, r0, #1"), VALUE)
        self.assertIn("(instruction 8)", message)
        # source 2's re-read is a tested update (volatile_tested_update), admitted with that rule's
        # premise; its forwarded join read pairs with the stripped reload and is not listed
        (report,) = fixtures.compare(*listings("add\tr0, r0, #1"))
        self.assertIn("chained re-reads at [], tested-update re-reads at [8] (tested-update-reread-v1, premise:",
                      semantics.record(fixtures.SYMBOL, [report]))
        self.addCleanup(setattr, tested_update.POLICY, "enabled", tested_update.POLICY.enabled)
        tested_update.POLICY.enabled = False
        message = self.refused(*listings("add\tr0, r0, #1"), VALUE)
        self.assertIn("(instruction 8)", message)

    def test_without_the_join_copy_the_refusal_is_unchanged(self):
        message = self.refused(*listings(join=False), ADDED)
        self.assertIn("(instruction 8) loads g_control_flags_03000940+0x3c, which the stripped compile "
                      "does not load there", message)

    def test_a_chained_re_read_the_stripped_compile_forwards_is_still_listed(self):
        # `sym.unknown_3C = (sym.unknown_3D = 0);` (test_volatile_semantics' chained case)
        real = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #0", "add\tr2, r2, #61", "ldrb\tr0, [r2]",
                                 "mov\tr1, #0", "strb\tr1, [r2]", "ldrb\tr0, [r2]", "sub\tr2, r2, #1",
                                 "ldrb\tr1, [r2]", "strb\tr0, [r2]", "bx\tlr")
        stripped = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #61", "mov\tr1, #0", "strb\tr1, [r2]",
                                     "sub\tr2, r2, #1", "strb\tr1, [r2]", "bx\tlr")
        self.assertEqual(fixtures.compare(real, stripped)[0][1:4], (1, [3, 8], [6]))

    def test_an_added_read_after_an_optional_counterpart_is_named(self):
        # `sym.unknown_3E = (sym.unknown_3F = 0); if (sym.unknown_3C < 16) sym.unknown_3C <<= 1;`
        # the chained re-read stays unpaired, and the refusal names the update re-read (15),
        # not the counterpart at the same place in the list before the optional one is removed
        declaration = ("extern struct { u16 display; u8 unknown_02[0x3A]; volatile u8 unknown_3C : 8; "
                       "volatile u8 unknown_3D : 8; volatile u8 unknown_3E : 8; volatile u8 unknown_3F : 8; } "
                       + fixtures.SYMBOL + ";")
        real = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #0", "add\tr2, r2, #63", "ldrb\tr0, [r2]",
                                 "mov\tr1, #0", "strb\tr1, [r2]", "ldrb\tr0, [r2]", "sub\tr2, r2, #1",
                                 "ldrb\tr1, [r2]", "strb\tr0, [r2]", "sub\tr2, r2, #2", "ldrb\tr0, [r2]",
                                 "cmp\tr0, #15", "bhi\t.Ldone", "ldrb\tr0, [r2]", "lsl\tr0, r0, #1",
                                 "ldrb\tr1, [r2]", "strb\tr0, [r2]", ".Ldone:", "bx\tlr")
        stripped = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #63", "mov\tr1, #0", "strb\tr1, [r2]",
                                     "sub\tr2, r2, #1", "strb\tr1, [r2]", "sub\tr2, r2, #2", "ldrb\tr0, [r2]",
                                     "cmp\tr0, #15", "bhi\t.Ldone", "lsl\tr0, r0, #1", "strb\tr0, [r2]",
                                     ".Ldone:", "bx\tlr")
        with self.assertRaises(semantics.SemanticError) as caught:
            semantics._compare_compiles(real, stripped, fixtures.PREPROCESSED, fixtures.SYMBOL, declaration)
        self.assertIn("`ldrb\tr0, [r2]` (instruction 15) loads g_control_flags_03000940+0x3c, which the "
                      "stripped compile does not load there; the qualifier added a read", str(caught.exception))

    def test_a_constant_update_checks_ordinary_provenance_on_its_first_path(self):
        # the classification no longer lists the update before the pairing, so the ordinary-load
        # check must not wait for the list: an extra ordinary read is refused on path 1
        real, stripped = forwarded_update.ForwardedUpdateTests().bodies()
        stripped = stripped.replace("\tldrsb\tr0, [r6, r0]\n", "\tldrsb\tr0, [r6, r0]\n\tldrb\tr3, [r6]\n", 1)
        self.refused(real, stripped, "same-member constant update crosses different ordinary load provenance "
                                     "(path 1)")

    def test_a_forwarded_re_read_the_stripped_compile_reloads_pairs_with_the_reload(self):
        # `if (n) x = 5; y = x;`: on the store path the join read is forwarded in both compiles'
        # memory, but only the real compile reads it as a re-read; the stripped compile reloads
        real = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #60", "cmp\tr0, #0", "beq\t.Ljoin",
                                 "ldrb\tr1, [r2]", "mov\tr1, #5", "strb\tr1, [r2]", ".Ljoin:",
                                 "ldrb\tr0, [r2]", "add\tr2, r2, #1", "ldrb\tr1, [r2]", "strb\tr0, [r2]",
                                 "bx\tlr")
        stripped = fixtures.assembly("ldr\tr3, .L3", "add\tr2, r3, #60", "cmp\tr0, #0", "beq\t.Ljoin",
                                     "mov\tr1, #5", "strb\tr1, [r2]", ".Ljoin:", "ldrb\tr0, [r2]",
                                     "add\tr2, r2, #1", "strb\tr0, [r2]", "bx\tlr")
        (report,) = fixtures.compare(real, stripped, "void func_08028C34(int);\n")
        self.assertEqual(report[1:4], (2, [4, 9], []))
        # main refused it: main skipped every forwarded re-read and paired by address and width
        # alone, so the reload was left unpaired
        self.addCleanup(setattr, semantics, "paired_counterparts", semantics.paired_counterparts)
        semantics.paired_counterparts = lambda mine, theirs, optional: \
            {i for i, skip in enumerate(optional) if skip} if \
            [key[:3] for key, skip in zip(mine, optional) if not skip] == [key[:3] for key in theirs] else None
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped, "void func_08028C34(int);\n")
        self.assertIn("the stripped compile loads g_control_flags_03000940+0x3c where the real one does not",
                      str(caught.exception))


class PairedCounterpartsTests(unittest.TestCase):
    def test_pairing(self):
        x, x2, y, x_later = ("x", 1, 0), ("x", 2, 0), ("y", 3, 0), ("x", 1, 1)
        a, b, c, d = 0, 1, 2, 3
        for mine, theirs, optional, expected in (
                ([x, y], [x, y], (), set()),                  # all required, all paired
                ([x, y], [x2, y], (), None),                  # same address, another value
                ([x, y], [x_later, y], (), None),             # same value, across an event
                ([x, x2, y], [x, y], (b,), {b}),              # the optional one unpaired
                ([x, x2, y], [x, x2, y], (b,), set()),        # ... or paired where needed
                ([x, x2, y], [x, y], (a,), None),             # a required one is never skipped
                ([x, x2, y], [x2, y], (a,), {a}),
                ([x, x2, y], [x, x2, y], (a, b), set()),
                ([x, x2, y], [x, y], (a, b), {b}),            # skipped where both are possible
                ([x, x2], [x], (a, b), {b}),
                ([x, x2], [x2], (a, b), {a}),
                ([x], [x, x2], (a,), None),                   # a stripped load is never left unpaired
                ([x, x], [x], (a, b), {a}),                   # of two that could pair, the later pairs
                ([x, x_later], [x_later], (a,), {a}),
                ([x, x_later], [x], (b,), {b}),
                ([x, x_later], [x], (a,), None),
                ([], [], (), set())):
            with self.subTest(mine=mine, theirs=theirs, optional=optional):
                flags = [i in optional for i in range(len(mine))]
                self.assertEqual(semantics.paired_counterparts(mine, theirs, flags), expected)

    def test_keys_compare_every_field(self):
        key = (1, False, "x", 1, 0)
        for other in ((1, True, "x", 1, 0), (2, False, "x", 1, 0), (1, False, "y", 1, 0),
                      (1, False, "x", 2, 0), (1, False, "x", 1, 1)):
            with self.subTest(other=other):
                self.assertIsNone(semantics.paired_counterparts([key], [other], [False]))
        self.assertEqual(semantics.paired_counterparts([key], [key], [False]), set())
        cut = semantics.LOOP_CUT + (None, None)
        self.assertEqual(semantics.paired_counterparts([cut, key], [cut, key], [False, False]), set())
        self.assertIsNone(semantics.paired_counterparts([cut, key], [key, cut], [False, False]))

    def test_canonical_versions(self):
        events = {0: 0, 2: 1, 3: 2}
        load = ("load", 1, ("lin", 0, ((("sym", "s"), 1),)), ("store", 2))
        self.assertEqual(semantics.canonical_versions(load, events), ("load", 1, load[2], ("store", 1)))
        self.assertEqual(semantics.canonical_versions(("ret", 3), events), ("ret", 2))
        self.assertEqual(semantics.canonical_versions(("load", 1, ("load", 4, ("arg", 0), ("call", 3)), "entry"),
                                                      events),
                         ("load", 1, ("load", 4, ("arg", 0), ("call", 2)), "entry"))
        self.assertEqual(semantics.canonical_versions(("trunc", ("ret", 2), 8), events), ("trunc", ("ret", 1), 8))
        for value in (("load", 1, ("sym", "s"), ("store", 1)), ("ret", 1), ("ret", ("raw-call", 0)),
                      ("load", 1, ("sym", "s"), "barrier")):
            with self.subTest(value=value):
                with self.assertRaises(semantics.SemanticError):
                    semantics.canonical_versions(value, events)


class CompositionPairingTests(unittest.TestCase):
    """under the overwritten-store composition, loads pair by the surviving events"""
    HEAD = ("ldr\tr2, .L3", "ldrb\tr1, [r2, #60]", "mov\tr1, #0", "strb\tr1, [r2, #60]",
            "ldrb\tr1, [r2, #60]", "mov\tr1, #19", "strb\tr1, [r2, #60]")

    def run_composition(self, real, stripped):
        permuted = real.replace("#60", "#61")
        functions = [semantics.parse_assembly(text)[0]["func_08028C34"] for text in (real, stripped, permuted)]
        size, pinned = semantics.pinned_members(fixtures.DECLARATION)
        _, mapping, _ = semantics.perturbed_declaration(fixtures.DECLARATION)
        return composition.compare_function("func_08028C34", *functions, {"func_08028C34": (True, 1)},
                                            fixtures.SYMBOL, size, pinned, mapping, selector=composition.SELECTOR,
                                            premise=composition.PREMISE)["result"]

    def test_a_load_after_a_removed_store_pairs_by_surviving_events(self):
        # the real compile's overwritten store shifts its raw event numbers: the returned load of
        # +0x2 reads the version of the store through r3, event 2 in the real compile, 1 in the stripped
        real = fixtures.assembly("add\tr3, r0, #0", *self.HEAD, "mov\tr1, #0", "strb\tr1, [r3]",
                                 "ldrb\tr0, [r2, #2]", "bx\tlr")
        stripped = fixtures.assembly("add\tr3, r0, #0", "ldr\tr2, .L3", "mov\tr1, #19", "strb\tr1, [r2, #60]",
                                     "mov\tr1, #0", "strb\tr1, [r3]", "ldrb\tr0, [r2, #2]", "bx\tlr")
        self.assertEqual(self.run_composition(real, stripped), (1, [2, 5], [], [], []))
        # the stripped compile keeps an overwritten store too, so both compiles' events are renumbered
        stripped = fixtures.assembly("add\tr3, r0, #0", "ldr\tr2, .L3", "mov\tr1, #0", "strb\tr1, [r2, #60]",
                                     "mov\tr1, #19", "strb\tr1, [r2, #60]", "mov\tr1, #0", "strb\tr1, [r3]",
                                     "ldrb\tr0, [r2, #2]", "bx\tlr")
        self.assertEqual(self.run_composition(real, stripped), (1, [2, 5], [], [], []))
        self.assertEqual(self.run_composition(fixtures.assembly(*self.HEAD, "ldrb\tr0, [r2, #2]", "bx\tlr"),
                                              fixtures.assembly("ldr\tr2, .L3", "mov\tr1, #19",
                                                                "strb\tr1, [r2, #60]", "ldrb\tr0, [r2, #2]",
                                                                "bx\tlr")),
                         (1, [1, 4], [], [], []))

    def test_a_trace_pairing_without_its_event_map_refuses(self):
        real, stripped = listings(join=False)
        message = None
        try:
            semantics.compare_function("func_08028C34", *self.functions(real, stripped), fixtures.SYMBOL,
                                       *semantics.pinned_members(fixtures.DECLARATION),
                                       _ordered_trace_check=lambda path, other, dead:
                                       (path.trace[1:], other.trace[1:]))
        except semantics.SemanticError as error:
            message = str(error)
        self.assertIn("a caller's trace pairing changed the traces without mapping their events", message)

    @staticmethod
    def functions(real, stripped):
        return (semantics.parse_assembly(real)[0]["func_08028C34"],
                semantics.parse_assembly(stripped)[0]["func_08028C34"], {"func_08028C34": (False, 0)})


HEADER = fixtures.HEADER


@unittest.skipUnless(Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and
                     shutil.which("cpp") and shutil.which("arm-none-eabi-as") and
                     shutil.which("arm-none-eabi-objcopy"), "fixed compiler required")
class CompiledForwardedPairingTests(unittest.TestCase):
    """the issue's three sources through agbcc, and the shapes next to them"""

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

    def test_the_issue_sources_are_refused(self):
        s = fixtures.SYMBOL
        for body, parameters, instruction in (
                (f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo = {s}.bldalpha_lo << 1;\n"
                 f"{s}.bldalpha_hi = {s}.bldalpha_lo;", "void", 8),
                (f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo = {s}.bldalpha_lo << 1;\n*q = {s}.bldalpha_lo;",
                 "u8 *q", 9)):
            with self.subTest(body=body):
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.check(body, parameters)
                self.assertIn(f"(instruction {instruction})", str(caught.exception))
                self.assertIn(VALUE, str(caught.exception))
        (record,) = self.check(f"if ({s}.bldalpha_lo < 16) {s}.bldalpha_lo++;\n{s}.bldalpha_hi = {s}.bldalpha_lo;")
        self.assertIn("chained re-reads at [], tested-update re-reads at [8] "
                      "(tested-update-reread-v1, premise:", record)

    def test_an_equal_valued_read_across_a_store_is_refused(self):
        s = fixtures.SYMBOL
        x, y, z, w, v = (f"{s}.{member}" for member in ("bldalpha_lo", "bldalpha_hi", "bldcnt_lo", "bldy_lo",
                                                         "bldcnt_hi"))
        for body, parameters, instruction in (
                # the update re-read writes back the value it read, so it equals the stripped join reload
                (f"if ({x} < 16) {{ u8 t = {x}; *p = 0; {x} = t; }}\n{y} = {x};", "u8 *p", 9),
                # a tail-merged store: the second read of x hides behind the stripped compile's one read
                (f"if (c) {x} = 5; else {x} = 6;\n{y} = {x};\n{z} = {x};", "u8 c", 25),
                # ... and with a forwarded join read that pairs with the stripped reload after it
                (f"if (c) {x} = 5; else {x} = 6;\n{y} = {x};\n{z} = {x};\nif (d) {w} = 7;\n{v} = {w};",
                 "u8 c, u8 d", 28),
                # the review's other shapes of the same two cases
                (f"if ({x} < 16) {{ u8 t = {x}; *p = 0; {x} = t; }}\n*q = {x};", "u8 *p, u8 *q", 10),
                (f"if (c) {x} = 5; else {x} = 6;\n{y} = {x};\n*q = {x};", "u8 c, u8 *q", 25),
                (f"if (c) {x} = 5; else {x} = 6;\n{y} = {x};\n{z} = {x} + 1;", "u8 c", 25),
                (f"if (c) {s}.bg0cnt = 5; else {s}.bg0cnt = 6;\n{s}.bg1cnt = {s}.bg0cnt;\n"
                 f"{s}.bg2cnt = {s}.bg0cnt;", "u8 c", 17),
                (f"if (c) {s}.bg0cnt = 5; else {s}.bg0cnt = 6;\n{s}.bg1cnt = {s}.bg0cnt;\n*q = {s}.bg0cnt;",
                 "u8 c, u16 *q", 18),
                # inside a loop that relational induction proves
                (f"int i;\nfor (i = 0; i < n; i++) {{\n if (p[i]) {x} = 5; else {x} = 6;\n"
                 f" {y} = {x};\n {z} = {x};\n}}", "u8 *p, int n", 29)):
            with self.subTest(body=body):
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.check(body, parameters)
                self.assertIn(f"(instruction {instruction})", str(caught.exception))
                self.assertIn(ACROSS, str(caught.exception))
        (record,) = self.check(f"if (d) {w} = 7;\n{v} = {w};", "u8 d")
        self.assertIn("read-modify-write loads at [8, 15], chained re-reads at []", record)

    def test_neighbouring_shapes(self):
        s = fixtures.SYMBOL
        # a constant store on one path, then a copy at the join: the join read pairs with the
        # stripped reload (main refused this), and is not listed as a chained re-read
        (record,) = self.check(f"if (c) {s}.bldalpha_lo = 5;\n{s}.bldalpha_hi = {s}.bldalpha_lo;", "u8 c")
        self.assertIn("chained re-reads at []", record)
        # chained assignment, and a constant store copied to ordinary memory at a join: as on main
        (record,) = self.check(f"{s}.bldcnt_lo = ({s}.bldcnt_hi = 0);")
        self.assertIn("read-modify-write loads at [4, 9], chained re-reads at [7]", record)
        (record,) = self.check(f"if (c) {s}.bldalpha_lo = 5;\n*q = {s}.bldalpha_lo;", "u8 c, u8 *q")
        self.assertIn("read-modify-write loads at [9], chained re-reads at []", record)
        self.assertNotIn("ordinary-store", record)


if __name__ == "__main__":
    unittest.main()
