"""bios-fill-temporary-v1: a frame reference at an unplaceable offset, on no path to or from a fill.

0811E1F8 fills from the SDK's CpuFill16 temporary in one switch arm, and reads
`heights[context->mode]` (a local array at a variable index) in another.  The rule
refused the whole function for that read ("a frame reference of the function has
no constant offset").  Such a reference is now admitted when no path from any
fill's block reaches it and no path from it reaches any fill's block, loops
included: it then runs only on executions that run no fill, so it can neither
change the temporary between its store and the BIOS call nor read it afterwards.

The graph must hold every edge the code has.  A jump table's cases print as
`(label_ref:SI N)`, so labels are matched by code at any mode, and a jump the
dump does not bound (a computed goto, a tablejump with no table, a label value,
a call that may return twice) refuses rather than drop its edges.
"""
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import bios_fill_temporary as fill
import volatile_rom_proof as proof
import test_bios_fill_temporary as base

ENTRY, function, fill_insns = base.ENTRY, base.function, base.fill_insns
UNKNOWN = (30, "insn (set (mem:SI (plus:SI (reg:SI 18 virtual-stack-vars) (reg/v:SI 22)) 0) "
               "(const_int 0)) -1 (nil) (nil)")
READ = (30, "insn (set (reg:SI 70) (mem:SI (plus:SI (reg:SI 18 virtual-stack-vars) (reg/v:SI 22)) 0)) "
            "-1 (nil) (nil)")


def branch(uid, label):
    return (uid, f"jump_insn (set (pc) (if_then_else (eq (cc0) (const_int 0)) (label_ref {label}) (pc))) "
                 "-1 (nil) (nil)")


def jump(uid, label):
    return (uid, f"jump_insn (set (pc) (label_ref {label})) -1 (nil) (nil)")


def label(uid):
    return (uid, f'code_label {uid + 1} ""')


def arms(reference=UNKNOWN, loop=False):
    """`if (c) { fill } else { reference }`, then the end, optionally jumping back to the head"""
    head = [label(40)] if loop else []
    tail = [jump(70, 40), (71, "barrier")] if loop else []
    return [ENTRY] + head + [branch(3, 50)] + fill_insns(10) + [jump(20, 60), (21, "barrier"), label(50),
                                                               reference, label(60)] + tail



def table(loop=False, kind="addr_vec"):
    """`switch` through a jump table: case A fills, case B holds the reference; optionally a loop round both"""
    head = [label(40)] if loop else []
    tail = [jump(70, 40), (71, "barrier")] if loop else []
    cases = "(label_ref:SI 9) (label_ref:SI 50)"
    vector = (f"addr_vec:SI[ {cases} ]" if kind == "addr_vec" else
              f"addr_diff_vec:SI (label_ref:SI 6) [ {cases} ] (const_int 0) (const_int 0) 0")
    return [ENTRY] + head + [
        (3, "insn (set (reg:SI 49) (plus:SI (reg:SI 48) (label_ref 6))) -1 (nil) (nil)"),
        (4, "jump_insn (parallel[ (set (pc) (reg:SI 50)) (use (label_ref 6)) ] ) -1 (nil) (nil)"),
        (5, "barrier"), label(6), (7, f"jump_insn ({vector}) -1 (nil) (nil)"), (8, "barrier"),
        label(9)] + fill_insns(10) + [jump(20, 60), (21, "barrier"), label(50), UNKNOWN, label(60)] + tail


def with_jump(insns, uid, text):
    """insns with the jump_insn of UID uid's pattern replaced"""
    return [(u, f"jump_insn {text} -1 (nil) (nil)" if u == uid else rest) for u, rest in insns]


class RtlTests(unittest.TestCase):
    def test_a_reference_in_another_arm_is_admitted_and_recorded(self):
        for reference in (UNKNOWN, READ):
            with self.subTest(reference=reference[1][:30]):
                (found,) = fill.fills(function(arms(reference)))
                self.assertEqual((found["slot"], found["apart"]), ((18, -2), [30]))

    def test_a_reference_on_a_path_to_or_from_a_fill_is_refused(self):
        reason = "UID 30 is a frame reference with no constant offset on a path to or from the fill at insn UID 16"
        inside = fill_insns(10)
        for at in (3, 5, 6):
            with self.subTest(inside=at), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function([ENTRY] + inside[:at] + [UNKNOWN] + inside[at:]))
        for label_, insns in (("before the fill", [ENTRY, UNKNOWN] + fill_insns(10)),
                              ("after the fill", [ENTRY] + fill_insns(10) + [UNKNOWN]),
                              ("a loop round both arms", arms(loop=True)),
                              ("a loop round both arms, read", arms(READ, loop=True))):
            with self.subTest(label=label_), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function(insns))

    def test_a_volatile_store_at_an_unplaceable_offset_is_refused(self):
        volatile = (30, "insn (set (mem/v:SI (plus:SI (reg:SI 18 virtual-stack-vars) (reg/v:SI 22)) 0) "
                        "(const_int 0)) -1 (nil) (nil)")
        with self.assertRaisesRegex(proof.ProofError, "volatile frame store at an offset the proof cannot place"):
            fill.fills(function(arms(volatile)))

    def test_without_a_fill_the_reference_still_refuses(self):
        with self.assertRaisesRegex(proof.ProofError, "a frame reference of the function has no constant offset"):
            fill.fills(function([ENTRY, UNKNOWN]))

    def test_the_graph(self):
        fn = function(arms(loop=True))
        graph = fill.successors(fn)
        index = {insn.uid: insn.index for insn in fn.insns}
        self.assertEqual(graph[index[3]], {index[10], index[50]})
        self.assertEqual(graph[index[20]], {index[21], index[60]})
        self.assertEqual(graph[index[21]], set())
        self.assertEqual(graph[index[70]], {index[71], index[40]})
        self.assertIn(index[30], fill.reached(graph, index[10]))
        straight = function(arms())
        where = {insn.uid: insn.index for insn in straight.insns}
        self.assertNotIn(where[30], fill.reached(fill.successors(straight), where[10]))
        self.assertNotIn(where[10], fill.reached(fill.successors(straight), where[30]))
        with self.assertRaisesRegex(proof.ProofError, "refers to a label the dump does not hold"):
            fill.successors(function([ENTRY, jump(3, 99), (4, "barrier")]))


    def test_jump_table_cases_are_edges_at_any_mode(self):
        for kind in ("addr_vec", "addr_diff_vec"):
            with self.subTest(kind=kind):
                fn = function(table(kind=kind))
                graph = fill.successors(fn)
                index = {insn.uid: insn.index for insn in fn.insns}
                self.assertEqual(graph[index[4]], {index[5], index[6]})
                self.assertTrue({index[9], index[50]} <= graph[index[7]])
                (found,) = fill.fills(fn)
                self.assertEqual(found["apart"], [30])
                reason = "UID 30 is a frame reference with no constant offset on a path to or from the fill"
                with self.assertRaisesRegex(proof.ProofError, reason):
                    fill.fills(function(table(loop=True, kind=kind)))

    def test_jumps_the_dump_does_not_bound_refuse(self):
        reason = "the proof cannot bound where it goes"
        for what, insns in (
                ("a computed goto", with_jump(arms(), 20, "(set (pc) (reg:SI 50))")),
                ("a jump through memory", with_jump(arms(), 20, "(set (pc) (mem:SI (reg:SI 50) 0))")),
                ("a tablejump with no table", with_jump(arms(), 20, "(parallel[ (set (pc) (reg:SI 50)) "
                                                                    "(use (label_ref 50)) ] )")),
                ("a tablejump at the end", with_jump(arms(), 20, "(parallel[ (set (pc) (reg:SI 50)) "
                                                                 "(use (label_ref 60)) ] )")),
                ("a tablejump with a clobber", with_jump(table(), 4, "(parallel[ (set (pc) (reg:SI 50)) "
                                                                     "(use (label_ref 6)) (clobber (reg:SI 51)) ] )")),
                ("a conditional arm that is not a label", with_jump(
                    arms(), 3, "(set (pc) (if_then_else (eq (cc0) (const_int 0)) (reg:SI 50) (pc)))")),
                ("a table holding a register", with_jump(table(), 7, "(addr_vec:SI[ (label_ref:SI 9) (reg:SI 50) ] )")),
                ("an empty table", with_jump(table(), 7, "(addr_vec:SI[ ] )")),
                ("two sets of the pc", with_jump(arms(), 20, "(parallel[ (set (pc) (label_ref 60)) "
                                                             "(set (pc) (label_ref 50)) ] )"))):
            with self.subTest(what), self.assertRaisesRegex(proof.ProofError, reason):
                fill.fills(function(insns))
        with self.assertRaisesRegex(proof.ProofError, "a label reference the proof cannot read"):
            fill.fills(function(with_jump(arms(), 20, "(set (pc) (label_ref:SI L60))")))
        # a return leaves; its arm or form adds no edge
        fill.fills(function(with_jump(arms(), 3, "(set (pc) (if_then_else (eq (cc0) (const_int 0)) "
                                                 "(label_ref 50) (return)))")))

    def test_hidden_jump_sources_refuse(self):
        value = (25, "insn (set (reg:SI 49) (label_ref 50)) -1 (nil) (nil)")
        insns = arms()
        where = [u for u, _ in insns].index(21) + 1
        with self.assertRaisesRegex(proof.ProofError, "takes the address of label UID 50, which heads no jump table"):
            fill.fills(function(insns[:where] + [value] + insns[where:]))
        setjmp = (8, 'call_insn (set (reg:SI 0 r0) (call (mem:SI (symbol_ref:SI ("_setjmp")) 0) (const_int 0))) '
                     "-1 (nil) (nil) (nil)")
        with self.assertRaisesRegex(proof.ProofError, "calls a function that may return twice"):
            fill.fills(function(arms()[:2] + [setjmp] + arms()[2:]))
        self.assertTrue(all(fill.returns_twice(name) for name in ("setjmp", "__sigsetjmp", "__xqsetjmp", "vfork")))
        self.assertFalse(fill.returns_twice("longjmp"))

SHAPE = """void func_08000400(u16 *dest, int phase, int index, u16 value)
{
    u32 heights[4];

    switch (phase) {
    case 0:
        {
            volatile u16 fill = dest[8];
            func_0814186C((const void *)&fill, dest + 0x10, 0x010000A0);
        }
        break;
    case 1:
        heights[0] = 3;
        heights[3] = 5;
        dest[0] = heights[index];
        break;
    case 2:
        dest[1] = 7;
        break;
    case 3:
        dest[2] = 9;
        break;
    case 4:
        dest[3] = 11;
        break;
    }
}
"""
INSIDE = """void func_08000400(u16 *dest, int index, u16 value)
{
    u32 heights[4];

    heights[0] = 3;
    heights[3] = 5;
    {
        volatile u16 fill = dest[8];
        func_0814186C((const void *)&fill, dest + heights[index], 0x010000A0);
    }
}
"""
LOOP = """void func_08000400(u16 *dest, int n, int index, u16 value)
{
    u32 heights[4];
    int i;

    heights[0] = 3;
    heights[3] = 5;
    for (i = 0; i < n; i++) {
        if (i & 1) {
            volatile u16 fill = dest[8];
            func_0814186C((const void *)&fill, dest + 0x10, 0x010000A0);
        } else {
            dest[i] = heights[index];
        }
    }
}
"""


LOOPED_TABLE = """void func_08000400(u16 *dest, int phase, int index, u16 value)
{
    u32 heights[4];

    do {
        switch (phase) {
        case 0:
            {
                volatile u16 fill = dest[8];
                func_0814186C((const void *)&fill, dest + 0x10, 0x010000A0);
            }
            break;
        case 1:
            dest[1] = 7;
            break;
        case 2:
            dest[2] = 9;
            break;
        case 3:
            dest[3] = 11;
            break;
        case 4:
            heights[0] = 3;
            heights[3] = 5;
            dest[0] = heights[index];
            break;
        case 5:
            dest[4] = 13;
            break;
        }
    } while (--phase < 6);
}
"""
COMPUTED = """void func_08000400(u16 *dest, int phase, int index, u16 value)
{
    u32 heights[4];
    void *arm = phase ? &&second : &&first;

    goto *arm;
first:
    {
        volatile u16 fill = dest[8];
        func_0814186C((const void *)&fill, dest + 0x10, 0x010000A0);
    }
    return;
second:
    heights[0] = 3;
    heights[3] = 5;
    dest[0] = heights[index];
}
"""

@unittest.skipUnless(base.COMPILER and base.capstone, "fixed compiler and capstone required")
class CompiledTests(unittest.TestCase):
    run_fill = base.CompiledTests.run_fill

    def test_the_shapes_are_fills(self):
        # each source is the SDK block, so only the reference decides (an extra statement in the block
        # would leave the source rule nothing to consider)
        for source in (SHAPE, INSIDE, LOOP, LOOPED_TABLE, COMPUTED):
            self.assertEqual([g["kind"] for g in fill.fill_groups(base.TYPES + base.CPUSET + source)], ["block"])

    def test_the_0811e1f8_shape_is_admitted(self):
        (offset, (state, text)), = self.run_fill(SHAPE)
        self.assertEqual(state, "admitted", text)
        self.assertIn("frame references at offsets the proof cannot place, on no path to or from a fill: "
                      "expand insn UIDs [", text)

    def test_the_reference_inside_the_window_or_a_loop_round_both_refuses(self):
        for source in (INSIDE, LOOP):
            with self.subTest(source=source.splitlines()[0]):
                with self.assertRaisesRegex(proof.ProofError, "frame reference with no constant offset on a path "
                                                              "to or from the fill"):
                    self.run_fill(source)

    def rtl(self, body):
        source = base.TYPES + base.CPUSET + body
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "src").mkdir()
            (root / "include").mkdir()
            (root / "src" / "08000400.c").write_text(source)
            with tempfile.TemporaryDirectory(dir=root) as work:
                unit = proof.Unit(root, "src/08000400.c", source, [], work)
                return unit.compile("probe", unit.real, "func_08000400")["dumps"]["rtl"]["func_08000400"]

    def test_a_jump_table_switch_has_its_case_edges(self):
        # SHAPE's switch compiles to a jump table whose cases print `(label_ref:SI N)`; its fill and its
        # reference stay apart with those edges in the graph
        fn = self.rtl(SHAPE)
        tables = [insn for insn in fn.insns if insn.code == "jump_insn" and proof.code(insn.pattern) == "addr_vec"]
        self.assertEqual(len(tables), 1)
        self.assertTrue(proof.rtl_mode(tables[0].pattern[1][1]) == "SI")
        graph = fill.successors(fn)
        labels = {insn.uid: insn.index for insn in fn.insns if insn.code == "code_label"}
        self.assertEqual({labels[uid] for uid in fill.label_refs(tables[0].pattern)} - graph[tables[0].index], set())
        self.assertGreaterEqual(len(graph[tables[0].index]), 5)

    def test_a_loop_round_a_jump_table_or_a_computed_goto_refuses(self):
        with self.assertRaisesRegex(proof.ProofError, "frame reference with no constant offset on a path to or "
                                                      "from the fill"):
            self.run_fill(LOOPED_TABLE)
        with self.assertRaisesRegex(proof.ProofError, "the proof cannot bound"):
            self.run_fill(COMPUTED)


ARMS = """void func_08000200(u16 *dest, int phase, int index)
{
    u32 heights[4];

    if (phase == 0) {
        {
            volatile u16 fill = dest[8];
            func_0814186C((const void *)&fill, dest + 0x10, 0x010000A0);
        }
    } else if (phase == 1) {
        heights[0] = 3;
        heights[3] = 5;
        dest[0] = heights[index & 3];
    }
}
"""


@unittest.skipUnless(base.COMPILER and base.capstone, "fixed compiler and capstone required")
class IssuanceTests(unittest.TestCase):
    """the rule through match.py as a subprocess (`__main__`), on a tree whose ROM holds CpuSet"""

    def test_the_0811e1f8_shape_is_issued(self):
        import os
        import subprocess
        import test_data_buffer_calls as calls
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="bios_fill_reachability_", dir=scratch) as directory:
            # two arms, so no jump table (whose local words the fixture's linker does not place)
            source = base.TYPES + base.CPUSET + ARMS
            root = calls.build(Path(directory) / "tree", source, [("func_08000400", "bx lr")], objects={},
                               large=True)
            import json
            environment = dict(os.environ, FFTA_ROM=str(root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
            command = [sys.executable, str(Path(fill.__file__).with_name("match.py")), "--root", str(root),
                       "0x08000200"]
            # the indexed read needs its reviewed stack-index row, as 0811E1F8's does: the tree's entry repeats
            # the rows match.py asks for
            first = subprocess.run(command, capture_output=True, text=True, env=environment, timeout=900)
            asked = first.stdout + first.stderr
            self.assertIn("need a reviewed entry in config/stack_index_premises.json", asked)
            entry = json.loads(asked[asked.index("add:\n") + 5:].strip())
            entry["0x08000200"]["review"] = "a test: phase 1 indexes a four-word local with a masked index"
            (root / "config/stack_index_premises.json").write_text(json.dumps(entry, indent=2) + "\n")
            result = subprocess.run(command, capture_output=True, text=True, env=environment, timeout=900)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output[-3000:])
            self.assertIn("MATCH - byte identical", output)
            report = (root / "docs/match/08000200.md").read_text()
            self.assertIn("frame references at offsets the proof cannot place, on no path to or from a fill", report)


if __name__ == "__main__":
    unittest.main()
