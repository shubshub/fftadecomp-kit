"""kit#582: a byte or halfword reload of the low bytes of a word spill.

agbcc keeps a narrow local zero-extended in a word register, so reload spills
the whole word and reads only its low bytes back for a byte or halfword use
(0x080200C8: `lsls r0, #16; lsrs r0, #16; str r0, [sp]` ... `mov r1, sp;
ldrh r0, [r1]; strh r0, [r1, #0x22]`).  Executor.load reads those bytes from
the word store its scan reaches (narrow_spill_reload), and spill_reload admits
the same reload inside a read-modify-write window (0x080D3208: `ldrh r0,
[r4, #14]; mov r1, sp; ldrh r1, [r1, #8]; strh r1, [r4, #14]`).  Every other
partial overlap of stack accesses is still refused.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import escaped_local_extents as extents
import volatile_semantics as semantics
import test_data_buffer_calls as calls
import test_volatile_escaped_extents as escaped
import test_volatile_rules_issuance as issuance
import test_volatile_semantics as fixtures

SYMBOL = fixtures.SYMBOL
PARTIAL = "partially overlapping stack access"
DIFFER = "differ in observable behaviour"
WINDOW = "not directly followed by a store"
LINE = "word spills reloaded by their low bytes (kit#582): "


def framed(*body):
    return fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", *body, "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")


# 080200C8's u16 parameter: spilled zero-extended as a word, its low half reloaded for a
# halfword store (to `display`, an ordinary member)
SPILL16 = ("lsl\tr0, r0, #16", "lsr\tr0, r0, #16", "str\tr0, [sp]")


def reload(*load, spill=SPILL16, store="strh\tr0, [r2]"):
    return framed(*spill, "ldr\tr2, .L3", *load, store)


RELOAD16 = reload("mov\tr1, sp", "ldrh\tr0, [r1]")
KEPT16 = framed("lsl\tr0, r0, #16", "lsr\tr0, r0, #16", "ldr\tr2, .L3", "strh\tr0, [r2]")


def records(body):
    function = semantics.parse_assembly(body)[0]["func_08028C34"]
    return semantics.explore("func_08028C34", function, {}, "real", (SYMBOL, 0x3E, {0x3C: 1, 0x3D: 1}))[0].records


class NarrowReloadTests(unittest.TestCase):
    def refused(self, real, stripped=KEPT16, reason=PARTIAL):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)
        self.assertIn(reason, str(caught.exception))

    def test_a_halfword_reload_reads_the_low_half(self):
        results = fixtures.compare(RELOAD16, KEPT16)
        self.assertIn(LINE + "real compile at [8], stripped compile at []", semantics.record(SYMBOL, results))
        load = next(r for r in records(RELOAD16) if r.kind == "load" and r.width == 2)
        self.assertEqual(load.value, ("trunc", 16, ("arg", 0)))
        self.assertTrue(load.forwarded and load.narrowed_reload)

    def test_the_record_lists_each_compile(self):
        results = fixtures.compare(RELOAD16, RELOAD16)
        self.assertIn(LINE + "real compile at [8], stripped compile at [8]", semantics.record(SYMBOL, results))
        # a later reload of another kind is not listed
        later = reload("mov\tr1, sp", "ldrh\tr0, [r1]", "ldr\tr3, [sp]")
        self.assertIn(LINE + "real compile at [8], stripped compile at []",
                      semantics.record(SYMBOL, fixtures.compare(later, KEPT16)))
        # only where the rule is used: a function without such a reload keeps its record's text
        self.assertNotIn("kit#582", semantics.record(SYMBOL, fixtures.compare(KEPT16, KEPT16)))
        self.assertFalse(any(hasattr(r, "narrowed_reload") for r in records(KEPT16)))

    def test_a_byte_reload_reads_the_low_byte(self):
        # a member byte spilled as a word and reloaded for a byte store
        real = framed("ldr\tr2, .L3", "ldrb\tr0, [r2, #2]", "str\tr0, [sp]", "mov\tr1, sp", "ldrb\tr0, [r1]",
                      "strb\tr0, [r2, #3]")
        stripped = framed("ldr\tr2, .L3", "ldrb\tr0, [r2, #2]", "strb\tr0, [r2, #3]")
        results = fixtures.compare(real, stripped)
        self.assertIn(LINE + "real compile at [7], stripped compile at []", semantics.record(SYMBOL, results))
        load = [r for r in records(real) if r.kind == "load"][-1]
        self.assertEqual(load.value, ("load", 1, ("lin", 2, ((("sym", SYMBOL), 1),)), "entry"))

    def test_the_reload_is_the_low_bytes_not_the_word(self):
        # a full word spilled, its low half reloaded and stored as a word: the real compile stores
        # the truncation, not the argument the other compile stores
        real = framed("str\tr0, [sp]", "ldr\tr2, .L3", "mov\tr1, sp", "ldrh\tr0, [r1]", "str\tr0, [r2]")
        self.refused(real, framed("ldr\tr2, .L3", "str\tr0, [r2]"), DIFFER)

    def test_any_other_offset_is_refused(self):
        self.refused(reload("mov\tr1, sp", "ldrh\tr0, [r1, #2]"))
        self.refused(reload("mov\tr1, sp", "ldrb\tr0, [r1, #1]", store="strb\tr0, [r2]"))
        self.refused(reload("mov\tr1, sp", "ldrb\tr0, [r1, #3]", store="strb\tr0, [r2]"))

    def test_a_straddle_is_refused(self):
        # across two word stores, and a word read of a word written as two halfwords, high half first
        self.refused(reload("mov\tr1, sp", "ldrh\tr0, [r1, #3]", spill=("str\tr0, [sp]", "str\tr1, [sp, #4]")))
        self.refused(reload("ldr\tr0, [sp]", spill=("mov\tr3, sp", "strh\tr1, [r3, #2]", "strh\tr0, [r3]"),
                            store="str\tr0, [r2]"))

    def test_a_signed_reload_is_refused(self):
        self.refused(reload("mov\tr1, sp", "ldrsh\tr0, [r1]"))
        self.refused(reload("mov\tr1, sp", "ldrsb\tr0, [r1]", store="strb\tr0, [r2]"))

    def test_a_narrower_store_is_refused(self):
        halfword = ("mov\tr3, sp", "strh\tr0, [r3]")
        self.refused(reload("mov\tr1, sp", "ldrb\tr0, [r1]", spill=halfword, store="strb\tr0, [r2]"))
        self.refused(reload("ldr\tr0, [sp]", spill=halfword, store="str\tr0, [r2]"))

    def test_a_pushed_slot_is_refused(self):
        # the low half of the saved r4, at sp+8 below `add sp, #-8`
        real = fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "ldr\tr2, .L3", "mov\tr1, sp",
                                 "ldrh\tr0, [r1, #8]", "strh\tr0, [r2]", "add\tsp, sp, #8", "pop\t{r4}", "pop\t{r0}",
                                 "bx\tr0")
        self.refused(real)

    def test_an_intervening_partial_write_is_refused(self):
        self.refused(reload("ldrh\tr0, [r1]", spill=SPILL16 + ("mov\tr3, #5", "mov\tr1, sp", "strb\tr3, [r1, #1]")))

    def test_a_narrow_store_over_a_spill_still_refuses(self):
        # the store-time self-assignment probe of a loaded value reads the slot, and is no reload
        self.refused(framed("ldr\tr2, .L3", "ldrh\tr0, [r2]", "str\tr1, [sp]", "mov\tr3, sp", "strh\tr0, [r3]",
                            "strh\tr0, [r2]"))

    def test_a_reload_after_a_call_that_received_the_frame(self):
        # the callee may have written the slot: the reload reads a value of its own, not the spill
        def body(*use):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", *SPILL16, "mov\tr4, r0", "mov\tr0, sp",
                                     "bl\tfunc_0802A2C0", "ldr\tr2, .L3", *use, "add\tsp, sp, #8", "pop\t{r4}",
                                     "pop\t{r0}", "bx\tr0")
        self.refused(body("mov\tr1, sp", "ldrh\tr0, [r1]", "strh\tr0, [r2]"), body("strh\tr4, [r2]"), DIFFER)

    def test_a_reloaded_value_builds_no_object_offset(self):
        real = framed("mov\tr0, #2", "str\tr0, [sp]", "ldr\tr2, .L3", "mov\tr1, sp", "ldrh\tr3, [r1]",
                      "ldrb\tr0, [r2, r3]", "strb\tr0, [r2, #3]")
        self.refused(real, framed("ldr\tr2, .L3", "ldrb\tr0, [r2, #2]", "strb\tr0, [r2, #3]"),
                     "read back from memory")

    def test_a_halfword_of_a_traced_word_store_stays_refused(self):
        # escaped-local extents: the word at sp+8 overlaps the escaped s (sp+10), so its store is
        # traced, while its low half stays internal; only an untraced spill is read this way
        def body(load):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-12", "mov\tr0, sp", "bl\tfunc_0802A2C0",
                                     "add\tr0, sp, #10", "bl\tfunc_0802A2C0", "mov\tr1, #7", "str\tr1, [sp, #8]",
                                     "mov\tr2, sp", load, "bl\tfunc_0802A2C0", "add\tsp, sp, #12", "pop\t{r4}",
                                     "pop\t{r0}", "bx\tr0")
        locals_ = [extents.Local("x", 0, 4, ()), extents.Local("s", 10, 2, ())]
        with self.assertRaises(semantics.SemanticError) as caught:
            escaped.check(body("ldrh\tr0, [r2, #8]"), body("ldrh\tr0, [r2, #8]"), real_locals=locals_)
        self.assertIn(PARTIAL, str(caught.exception))
        # the word itself reads back, so the frame model is not what refuses
        escaped.check(body("ldr\tr0, [r2, #8]"), body("ldr\tr0, [r2, #8]"), real_locals=locals_)

    def test_a_halfword_at_a_variable_offset_is_refused(self):
        # after the escape, an internal spill at sp+8 and a halfword at sp + 4*r5 + 8: the constant
        # parts agree, but the load may read any frame byte outside the push area
        def body(load):
            return escaped.frame("mov\tr1, #7", "str\tr1, [sp, #8]", "lsl\tr3, r5, #2", "mov\tr2, sp",
                                 "add\tr2, r2, r3", load, "bl\tfunc_0802A2C0")
        with self.assertRaises(semantics.SemanticError) as caught:
            escaped.check(body("ldrh\tr0, [r2, #8]"), body("ldrh\tr0, [r2, #8]"))
        self.assertIn(PARTIAL, str(caught.exception))

    def test_a_halfword_reload_of_a_callee_argument_word_is_refused(self):
        # the fifth argument word after the call is the callee's (kit#590): its low half is not the spill's
        def outgoing(*use):
            return fixtures.assembly("push\t{r4, lr}", "add\tsp, sp, #-8", "mov\tr4, r0", "str\tr0, [sp]",
                                     "mov\tr0, #1", "mov\tr1, #2", "mov\tr2, #3", "mov\tr3, #4",
                                     "bl\tfunc_0802A2C4", "ldr\tr2, .L3", *use, "add\tsp, sp, #8", "pop\t{r4}",
                                     "pop\t{r0}", "bx\tr0")
        five = fixtures.PREPROCESSED + "extern void func_0802A2C4(int, int, int, int, int);\n"
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(outgoing("mov\tr1, sp", "ldrh\tr0, [r1]", "strh\tr0, [r2]"), outgoing("strh\tr4, [r2]"),
                             five)
        self.assertIn(DIFFER, str(caught.exception))

    def test_a_halfword_reload_of_a_released_word_is_refused(self):
        # sp rose above the spill and came down again (kit#591): the word holds no defined value
        self.refused(reload("mov\tr1, sp", "ldrh\tr0, [r1]", spill=SPILL16 + ("add\tsp, sp, #8", "add\tsp, sp, #-8")),
                     reason="reads a frame word released by an sp increase")

    def test_the_policy_switch(self):
        with mock.patch.object(semantics.NARROW_SPILL_RELOADS, "enabled", False):
            self.refused(RELOAD16)


# 0813F22C's window (kit#165) with a byte reload: `sym.unknown_3C = arg0`, the value spilled
# to sp+4 as a word and reloaded through a copy of sp, as Thumb has no sp-based ldrb
BYTE_RELOAD = ("mov\tr3, sp", "ldrb\tr3, [r3, #4]")


def window(*between, spill=("str\tr3, [sp, #4]",), store="strb\tr3, [r1]"):
    return framed("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr3, r0", *spill, "ldrb\tr2, [r1]", *between, store)


STRIPPED = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "strb\tr0, [r1]")


class WindowReloadTests(unittest.TestCase):
    def refused(self, real, stripped=STRIPPED, reason=WINDOW):
        with self.assertRaises(semantics.SemanticError) as caught:
            fixtures.compare(real, stripped)
        self.assertIn(reason, str(caught.exception))

    def test_a_byte_reload_in_the_window(self):
        # the spilled value is the whole argument word: the reload is its low byte
        results = fixtures.compare(window(*BYTE_RELOAD), STRIPPED)
        self.assertEqual(results[0][2], [6])
        record = semantics.record(SYMBOL, results)
        self.assertIn("read-modify-write windows holding a spill reload (kit#165) at [7]", record)
        self.assertIn(LINE + "real compile at [9], stripped compile at []", record)

    def test_a_halfword_reload_in_the_window(self):
        real = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "ldr\tr1, .L3", "mov\tr3, r0",
                                 "str\tr3, [sp, #4]", "ldrh\tr2, [r1, #2]", "mov\tr3, sp", "ldrh\tr3, [r3, #4]",
                                 "strh\tr3, [r1, #2]", "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")
        stripped = fixtures.assembly("push\t{lr}", "add\tsp, sp, #-8", "ldr\tr1, .L3", "strh\tr0, [r1, #2]",
                                     "add\tsp, sp, #8", "pop\t{r0}", "bx\tr0")
        report, = semantics._compare_compiles(real, stripped, fixtures.PREPROCESSED, SYMBOL, fixtures.DECLARATION16)
        self.assertEqual(report[2], [5])

    def test_a_store_to_another_byte_of_the_word_is_refused(self):
        # sp+6 is outside the reloaded byte, so the executor reads the spill; the window still wants
        # the whole word untouched since the spill
        self.refused(window(*BYTE_RELOAD, spill=("str\tr3, [sp, #4]", "mov\tr2, sp", "strb\tr0, [r2, #6]")))

    def test_a_register_offset_is_refused(self):
        self.refused(window("mov\tr3, sp", "mov\tr2, #4", "ldrb\tr3, [r3, r2]"))

    def test_a_byte_spill_is_refused(self):
        # a same-width reload of a byte store: the window, like kit#165's, takes word spills only
        self.refused(window(*BYTE_RELOAD, spill=("mov\tr2, sp", "strb\tr3, [r2, #4]")))

    def test_a_reload_into_the_address_is_refused(self):
        real = framed("ldr\tr1, .L3", "add\tr1, r1, #60", "mov\tr2, #0", "str\tr2, [sp, #4]", "ldrb\tr3, [r1]",
                      "mov\tr2, sp", "ldrb\tr2, [r2, #4]", "strb\tr0, [r1, r2]")
        self.refused(real, reason="read back from memory")

    def test_spill_reload_names_the_store(self):
        path = records(window(*BYTE_RELOAD))
        position = next(i for i, r in enumerate(path) if getattr(r, "narrowed_reload", False))
        store = semantics.spill_reload(path, position)
        self.assertEqual((store.kind, store.width, store.index), ("store", 4, 5))


# 08000200 sources for match.py: each holds eight members across a call, so agbcc spills two or
# three of them as words and reloads their low bytes
SAVE16 = """typedef struct { u16 v[8]; } Saved;

extern Saved data_02000000;
extern void func_08000400(void);

void func_08000200(void)
{
""" + "".join(f"    u16 {name} = {SYMBOL}.{name};\n" for name in (
    "bg0hofs", "bg0vofs", "bg1hofs", "bg1vofs", "bg2hofs", "bg2vofs", "bg3hofs", "bg3vofs")) + """
    func_08000400();
""" + "".join(f"    data_02000000.v[{n}] = {name};\n" for n, name in enumerate((
    "bg0hofs", "bg0vofs", "bg1hofs", "bg1vofs", "bg2hofs", "bg2vofs", "bg3hofs", "bg3vofs"))) + "}\n"


def restore(kind, names):
    return ("extern void func_08000400(void);\n\nvoid func_08000200(void)\n{\n" +
            "".join(f"    {kind} {name} = {SYMBOL}.{name};\n" for name in names) + "\n    func_08000400();\n" +
            "".join(f"    {SYMBOL}.{name} = {name};\n" for name in names) + "}\n")


RESTORE16 = restore("u16", ("bg0hofs", "bg0vofs", "bg1hofs", "bg1vofs", "bg2hofs", "bg2vofs", "bg3hofs", "bg3vofs"))
RESTORE8 = restore("u8", ("bldcnt_lo", "bldcnt_hi", "bldalpha_lo", "bldalpha_hi", "bldy_lo", "winin_lo",
                          "winin_hi", "winout_lo"))


@unittest.skipUnless(calls.tools_present(), "fixed compiler and ARM tools required")
class IssuanceTests(unittest.TestCase):
    """issued by match.py as a subprocess (its `__main__` copy), then replayed by --check-report"""

    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="volatile_narrow_reload_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replayed(self, root):
        environment = dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
        result = subprocess.run([sys.executable, str(ROOT / "tools/match.py"), "--root", str(root), "0x08000200",
                                 "--check-report"], capture_output=True, text=True, env=environment, timeout=900)
        return result.returncode, result.stdout + result.stderr

    def issue_and_replay(self, name, source, objects=issuance.OBJECTS):
        root = issuance.tree(self.base / name, source, objects=objects)
        report = issuance.issued(self, root)
        lists = dict(re.findall(r"(real|stripped|layout-perturbed) compile at (\[[0-9, ]*\])",
                                report.split(LINE, 1)[1].split("\n", 1)[0]))
        # the real and permuted compiles differ only in member offsets, so they reload at the same places
        self.assertEqual(sorted(lists), ["layout-perturbed", "real", "stripped"])
        self.assertNotEqual(lists["real"], "[]")
        self.assertEqual(lists["layout-perturbed"], lists["real"])
        code, output = self.replayed(root)
        self.assertEqual(code, 0, output[-3000:])
        self.assertIn("report  identical to the saved", output)
        # the line is derived again on replay: a saved report with another reload list differs
        saved = Path(root) / "docs/match/08000200.md"
        saved.write_text(re.sub(r"layout-perturbed compile at \[[0-9, ]*\]", "layout-perturbed compile at [1]",
                                report, count=1))
        code, output = self.replayed(root)
        self.assertEqual(code, 1, output[-3000:])
        self.assertIn("report  DIFFERS from the saved", output)
        return report

    def test_halfword_reloads_for_ordinary_stores(self):
        # 080200C8's shape: the reloads feed stores to another object, outside any window
        report = self.issue_and_replay("ordinary", SAVE16, dict(issuance.OBJECTS, data_02000000="0x02000000"))
        self.assertNotIn("spill reload (kit#165)", report)

    def test_halfword_reloads_in_read_modify_write_windows(self):
        # 080D3208's scroll members: `ldrh rA, [rB, #k]; mov rC, sp; ldrh rC, [rC, #j]; strh rC, [rB, #k]`
        report = self.issue_and_replay("halfwords", RESTORE16)
        self.assertIn("read-modify-write windows holding a spill reload (kit#165) at [", report)

    def test_byte_reloads_in_read_modify_write_windows(self):
        # 080D3208's blend members, through `mov rC, sp; ldrb rC, [rC, #j]`
        report = self.issue_and_replay("bytes", RESTORE8)
        self.assertIn("read-modify-write windows holding a spill reload (kit#165) at [", report)


if __name__ == "__main__":
    unittest.main()
