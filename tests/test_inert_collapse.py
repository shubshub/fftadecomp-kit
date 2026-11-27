"""The collapse compile: a justified inert-control-flow test is admitted only if the ROM keeps a trace of it.

A justification that cites a ROM address clears `if (c) X; else X;` in plausible.py, but a comment cannot show
what the test left in the ROM.  match.py compiles the source again with the test collapsed to `X;`
(inert_collapse, inert_trace_records): the same bytes refuse, and so does a difference in register allocation
alone; a load, a compare or test, or a frame the collapsed form lacks counts.  Every report of the source prints
the trace, and replay recompiles and compares it.
"""
import io
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import match
import match_evidence
import inert_collapse
import addressed_signed_runtime_profile as addressed
import test_addressed_signed_runtime_profile as addressed_fixtures

A = 0x08010000
SCRATCH = Path(__file__).resolve().parents[1] / "build/tests"
COMPILER = (Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and shutil.which("cpp") and
            shutil.which("arm-none-eabi-as") and shutil.which("arm-none-eabi-objcopy"))
TYPES = "typedef unsigned char u8;\ntypedef unsigned short u16;\ntypedef unsigned int u32;\n"
CITE = "/* plausible: the ROM keeps the test at 0x0814862C */"
# the shape of 0814862C: a dead load of the test's operand and the frame (16 bytes against 4 collapsed)
MEMORY_LEAF = TYPES + f"""typedef struct {{ u16 id; u8 unknown_02[0x1a]; u8 flag; }} S;
void func_{A:08X}(S *p, u32 v) {{
    u8 b = (u8)v;
    {CITE}
    if (p->id)
        p->flag = b;
    else
        p->flag = b;
}}
"""
MEMORY_LEAF_BYTES = bytes.fromhex("00b5021c0906090e1088117701bc0047")
SHAPES = {
    # a register condition in a leaf: only the frame stays
    "frame": TYPES + f"void func_{A:08X}(int c, int *x) {{\n    {CITE}\n    if (c) *x = 1; else *x = 1;\n}}\n",
    "load and frame": MEMORY_LEAF,
    # a memory condition after a call: the dead load stays, the frame was there anyway
    "load": TYPES + f"""typedef struct {{ u16 id; u8 unknown_02[0x1a]; u8 flag; }} S;
extern void g(void);
void func_{A:08X}(S *p, u32 v) {{
    u8 b = (u8)v;
    g();
    {CITE}
    if (p->id) p->flag = b; else p->flag = b;
}}
""",
    # a register condition after a call: the condition is kept in a callee-saved register, nothing else
    "registers after a call": TYPES + f"""extern void g(void);
void func_{A:08X}(int c, int *x) {{
    g();
    {CITE}
    if (c) *x = 1; else *x = 1;
}}
""",
    # a leaf with a frame of its own: only the register allocation differs
    "registers in a framed leaf": TYPES + f"""void func_{A:08X}(int c, int *x, int *y, int *z, int w) {{
    int t = *y + *z;
    *z = w;
    *y = t;
    {CITE}
    if (c) *x = t; else *x = t;
    x[1] = c + t + w;
}}
""",
    # a condition that is live after the arms: the same bytes as the collapsed source
    "nothing": TYPES + f"""extern void g(void);
extern void h(int);
void func_{A:08X}(int c, int *x) {{
    g();
    {CITE}
    if (c) *x = 1; else *x = 1;
    h(c);
}}
""",
}


# rv-plaus's review fixtures (z1-z7): label renumbering, stack offsets and compound assignments
REVIEW = {
    'z1_framed_pool': '/* allocation-only identical arms (rv a8) in a leaf that also stores to a global through a pool word */\nextern int g_total;\nvoid func_08010000(int c, int *x, int *y, int *z, int w)\n{\n    int t = *y + *z;\n    *z = w;\n    *y = t;\n    {CITE}\n    if (c) *x = t; else *x = t;\n    x[1] = c + t + w;\n    g_total = t;\n}\n'.replace("{CITE}", CITE),
    'z2_nonleaf_pool': '/* allocation-only identical arms (rv a2) followed by a global store through a pool word */\nextern void g(void);\nextern int g_total;\nvoid func_08010000(int c, int *x)\n{\n    g();\n    {CITE}\n    if (c) *x = 1; else *x = 1;\n    g_total = 5;\n}\n'.replace("{CITE}", CITE),
    'z3_shift_assign': '/* a condition that writes with <<=: not inert, and its collapse drops the write */\ntypedef struct { int id; int flag; } S;\nvoid func_08010000(S *p, int v)\n{\n    {CITE}\n    if (p->id <<= 1) p->flag = v; else p->flag = v;\n}\n'.replace("{CITE}", CITE),
    'z4_shiftr_assign': '/* the same with >>= on a register condition */\nvoid func_08010000(int c, int *x)\n{\n    {CITE}\n    if (c >>= 2) *x = 1; else *x = 1;\n    x[1] = c;\n}\n'.replace("{CITE}", CITE),
    'z5_spill': '/* register pressure: the condition is live across a call with every callee-saved register busy */\nextern int g(int, int, int, int);\nvoid func_08010000(int c, int *a, int *b, int *d, int e)\n{\n    int p = *a, q = *b, r = *d, s = e;\n    int u = g(p, q, r, s);\n    {CITE}\n    if (c) *a = u; else *a = u;\n    *b = p + q + r + s + u;\n}\n'.replace("{CITE}", CITE),
    'z6_loop_after': '/* allocation-only identical arms followed by a loop (branch labels after the test) */\nextern void g(void);\nvoid func_08010000(int c, int *x, int n)\n{\n    int i;\n    g();\n    {CITE}\n    if (c) *x = 1; else *x = 1;\n    for (i = 0; i < n; i++)\n        x[i + 1] = i;\n}\n'.replace("{CITE}", CITE),
    'z7_table_pool': '/* a memory-condition dead load (counts) together with a pool load after it */\ntypedef unsigned short u16;\nextern int g_total;\ntypedef struct { u16 id; u16 flag; } S;\nvoid func_08010000(S *p, int v)\n{\n    {CITE}\n    if (p->id) p->flag = v; else p->flag = v;\n    g_total = v;\n}\n'.replace("{CITE}", CITE),
    'z8_cse_join': "/* identical arms on a local: does the join stop CSE of a load across it (an extra load that is not the test's)? */\nint func_08010000(int c, int *p, int t)\n{\n    int a = p[0];\n    {CITE}\n    if (c) t = 1; else t = 1;\n    return a + p[0] + t;\n}\n".replace("{CITE}", CITE),
    'z9_pressure': '/* the condition live across a call with nine other values live: an extra spill reload of another value? */\nextern int g(int);\nint func_08010000(int c, int *p)\n{\n    int a = p[0], b = p[1], d = p[2], e = p[3], f = p[4], h = p[5], i = p[6], j = p[7], k = p[8];\n    g(0);\n    {CITE}\n    if (c) p[9] = 1; else p[9] = 1;\n    return a + b + d + e + f + h + i + j + k;\n}\n'.replace("{CITE}", CITE),
    'z10_pressure_after': '/* the same with the values used before and after the test */\nextern int g(int);\nint func_08010000(int c, int *p)\n{\n    int a = p[0], b = p[1], d = p[2], e = p[3], f = p[4], h = p[5], i = p[6], j = p[7];\n    g(a + b);\n    {CITE}\n    if (c) p[9] = d; else p[9] = d;\n    g(e + f);\n    return a + b + d + e + f + h + i + j + c;\n}\n'.replace("{CITE}", CITE),
    'z11_const_remat': '/* register pressure on values loaded from const memory: may reload rematerialise a value from its home (a non-sp load)? */\nextern const int k[10];\nextern int g(int);\nint func_08010000(int c, int *p)\n{\n    int a = k[0], b = k[1], d = k[2], e = k[3], f = k[4], h = k[5], i = k[6], j = k[7], m = k[8];\n    g(0);\n    {CITE}\n    if (c) p[9] = 1; else p[9] = 1;\n    return a + b + d + e + f + h + i + j + m;\n}\n'.replace("{CITE}", CITE),
    'z12_const_remat2': '/* the same with every value used on both sides of a second call */\nextern const int k[10];\nextern int g(int);\nint func_08010000(int c, int *p)\n{\n    int a = k[0], b = k[1], d = k[2], e = k[3], f = k[4], h = k[5], i = k[6], j = k[7];\n    g(a + b + d + e);\n    {CITE}\n    if (c) p[9] = f; else p[9] = f;\n    g(h + i + j);\n    return a + b + d + e + f + h + i + j;\n}\n'.replace("{CITE}", CITE),
}


def tree(root, source):
    for name in ("src", "include", "config", "symbols", "docs/match", "build"):
        (root / name).mkdir(parents=True, exist_ok=True)
    (root / "config/data_symbols.json").write_text("{}\n")
    (root / f"src/{A:08X}.c").write_text(source)


def scratch(test, prefix):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    directory = tempfile.TemporaryDirectory(prefix=prefix, dir=SCRATCH)
    test.addCleanup(directory.cleanup)
    return Path(directory.name)


def line_of(text, needle):
    return text[:text.index(needle)].count("\n") + 1


def run_main(argv):
    output = io.StringIO()
    with patch.object(sys, "argv", ["match.py", *argv]), redirect_stdout(output):
        try:
            status = match.main()
        except SystemExit as stop:
            return stop.code, output.getvalue()
    return status, output.getvalue()


def without(report, prefix):
    return "\n".join(line for line in report.split("\n") if not line.startswith(prefix))


# agbcc's listings of the shapes above (rv-plaus's fixtures a1-a4 and a8), as written and collapsed
LISTINGS = {
    "frame": ("f:\n\tpush\t{lr}\n\tmov\tr0, #1\n\tstr\tr0, [r1]\n\tpop\t{r0}\n\tbx\tr0\n.Lfe1:\n",
              "f:\n\tmov\tr0, #1\n\tstr\tr0, [r1]\n\tbx\tlr\n.Lfe1:\n"),
    "registers after a call": (
        "f:\n\tpush\t{r4, r5, lr}\n\tadd\tr4, r0, #0\n\tadd\tr5, r1, #0\n\tbl\tg\n\tmov\tr0, #1\n"
        "\tstr\tr0, [r5]\n\tpop\t{r4, r5}\n\tpop\t{r0}\n\tbx\tr0\n",
        "f:\n\tpush\t{r4, lr}\n\tadd\tr4, r1, #0\n\tbl\tg\n\tmov\tr0, #1\n\tstr\tr0, [r4]\n\tpop\t{r4}\n"
        "\tpop\t{r0}\n\tbx\tr0\n"),
    "load and frame": (
        "f:\n\tpush\t{lr}\n\tadd\tr2, r0, #0\n\tlsl\tr1, r1, #24\n\tlsr\tr1, r1, #24\n\tldrh\tr0, [r2]\n"
        "\tstrb\tr1, [r2, #28]\n\tpop\t{r0}\n\tbx\tr0\n",
        "f:\n\tstrb\tr1, [r0, #28]\n\tbx\tlr\n"),
    "load": (
        "f:\n\tpush\t{r4, r5, lr}\n\tadd\tr4, r0, #0\n\tlsl\tr1, r1, #24\n\tlsr\tr5, r1, #24\n\tbl\tg\n"
        "\tldrh\tr0, [r4]\n\tstrb\tr5, [r4, #28]\n\tpop\t{r4, r5}\n\tpop\t{r0}\n\tbx\tr0\n",
        "f:\n\tpush\t{r4, r5, lr}\n\tadd\tr5, r0, #0\n\tlsl\tr4, r1, #24\n\tlsr\tr4, r4, #24\n\tbl\tg\n"
        "\tstrb\tr4, [r5, #28]\n\tpop\t{r4, r5}\n\tpop\t{r0}\n\tbx\tr0\n"),
    "registers in a framed leaf": (
        "f:\n\tpush\t{r4, r5, r6, lr}\n\tadd\tr5, r0, #0\n\tadd\tr4, r1, #0\n\tldr\tr6, [sp, #16]\n"
        "\tldr\tr1, [r2]\n\tldr\tr0, [r3]\n\tadd\tr0, r1, r0\n\tstr\tr6, [r3]\n\tstr\tr0, [r2]\n\tstr\tr0, [r4]\n"
        "\tadd\tr0, r5, r0\n\tadd\tr0, r0, r6\n\tstr\tr0, [r4, #4]\n\tpop\t{r4, r5, r6}\n\tpop\t{r0}\n\tbx\tr0\n",
        "f:\n\tpush\t{r4, r5, r6, lr}\n\tldr\tr6, [sp, #16]\n\tldr\tr4, [r2]\n\tldr\tr5, [r3]\n"
        "\tadd\tr4, r4, r5\n\tstr\tr6, [r3]\n\tstr\tr4, [r2]\n\tstr\tr4, [r1]\n\tadd\tr0, r0, r4\n"
        "\tadd\tr0, r0, r6\n\tstr\tr0, [r1, #4]\n\tpop\t{r4, r5, r6}\n\tpop\t{r0}\n\tbx\tr0\n"),
}


class CollapseTests(unittest.TestCase):
    PREPROCESSED = ('# 1 "src/08010000.c"\nint a;\n# 5 "src/08010000.c"\nvoid f(int c, int *x) {\n'
                    "    if (c)\n        *x = 1;\n    else\n        *x = 1;\n    if (c) *x = 2; else *x = 2;\n}\n")

    def test_lines_come_from_the_markers(self):
        lines = inert_collapse.source_lines(self.PREPROCESSED)
        self.assertEqual(lines[:5], [None, ("src/08010000.c", 1), None, ("src/08010000.c", 5),
                                     ("src/08010000.c", 6)])

    def test_the_named_test_collapses_to_its_arm_and_keeps_the_line_count(self):
        collapsed = inert_collapse.collapse(self.PREPROCESSED, "src/08010000.c", 6)
        self.assertEqual(collapsed.count("\n"), self.PREPROCESSED.count("\n"))
        self.assertIn("    *x = 1;\n\n\n\n    if (c) *x = 2; else *x = 2;", collapsed)
        self.assertNotIn("*x = 1;\n    else", collapsed)
        second = inert_collapse.collapse(self.PREPROCESSED, "src/08010000.c", 10)
        self.assertIn("    *x = 2;\n}", second)
        self.assertIn("if (c)\n        *x = 1;", second)

    def test_a_test_that_is_not_there_or_writes_in_its_condition_refuses(self):
        writes = [(self.PREPROCESSED.replace("if (c)\n", f"if ({condition})\n"), 6)
                  for condition in ("c = 1", "c++", "--c", "c <<= 1", "c >>= 2", "c += 1", "c -= 1", "c *= 2",
                                    "c /= 2", "c %= 2", "c &= 1", "c |= 1", "c ^= 1")]
        for preprocessed, line in [(self.PREPROCESSED, 7), (self.PREPROCESSED.replace("08010000", "08010004"), 6)] + writes:
            with self.subTest(preprocessed=preprocessed, line=line), self.assertRaises(inert_collapse.TraceError):
                inert_collapse.collapse(preprocessed, "src/08010000.c", line)
        # two tests on one line cannot be told apart
        twice = self.PREPROCESSED.replace("    if (c) *x = 2; else *x = 2;", "    if (c) *x = 2; else *x = 2; "
                                          "if (c) *x = 3; else *x = 3;")
        with self.assertRaises(inert_collapse.TraceError):
            inert_collapse.collapse(twice, "src/08010000.c", 10)
        for condition in ("c == 1", "c <= 1", "c >= 1", "c != 1", "c << 1", "c >> 1", "c < 1", "c > 1"):
            with self.subTest(condition=condition):
                inert_collapse.collapse(self.PREPROCESSED.replace("if (c)\n", f"if ({condition})\n"),
                                        "src/08010000.c", 6)

    def test_the_trace_counts_a_load_a_test_or_a_frame_and_not_registers(self):
        expected = {"frame": ["frame"], "registers after a call": [], "load and frame": ["load", "frame"],
                    "load": ["load"], "registers in a framed leaf": []}
        for name, (original, collapsed) in LISTINGS.items():
            with self.subTest(name=name):
                self.assertEqual(inert_collapse.trace(original, collapsed)[0], expected[name])
        kinds, extra, missing = inert_collapse.trace(*LISTINGS["load and frame"])
        self.assertEqual(extra, ["push {lr}", "lsl r1, r1, #24", "lsr r1, r1, #24", "ldrh r0, [r2]", "pop {r0}",
                                 "bx r0"])
        self.assertEqual(missing, ["bx lr"])
        tested = ("f:\n\tpush\t{lr}\n\tldrh\tr0, [r2]\n\tcmp\tr0, #0\n\tbeq\t.L4\n\tpop\t{r0}\n\tbx\tr0\n",
                  "f:\n\tpush\t{lr}\n\tpop\t{r0}\n\tbx\tr0\n")
        self.assertEqual(inert_collapse.trace(*tested), (["load", "test"], ["ldrh r0, [r2]", "cmp r0, #0", "beq .L"], []))

    def test_operands_never_count(self):
        # a literal pool renumbered by the arms (z1, z2), a stack argument moved by a wider push (z5) and branch
        # labels renumbered (z6) are the same mnemonics: registers only
        for original, collapsed in (
                ("f:\n\tpush\t{r4, r5, lr}\n\tldr\tr1, [r2]\n\tldr\tr0, .L5\n\tstr\tr1, [r0]\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tpush\t{r4, lr}\n\tldr\tr4, [r2]\n\tldr\tr0, .L3\n\tstr\tr4, [r0]\n\tpop\t{r0}\n\tbx\tr0\n"),
                ("f:\n\tpush\t{r4, r5, r6, r7, lr}\n\tldr\tr4, [sp, #32]\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tpush\t{r4, r5, r6, lr}\n\tldr\tr7, [sp, #28]\n\tpop\t{r0}\n\tbx\tr0\n"),
                # the same field reached from another base CSE formed: a different offset, the same load
                ("f:\n\tldr\tr0, [r1, #8]\n\tbx\tlr\n",
                 "f:\n\tadd\tr2, r1, #4\n\tldr\tr0, [r2, #4]\n\tbx\tlr\n"),
                # a spill reload the collapsed form does not need: sp-based loads never count
                ("f:\n\tadd\tsp, sp, #-16\n\tstr\tr0, [sp, #12]\n\tldr\tr1, [sp, #12]\n\tldrh\tr2, [sp, #4]\n"
                 "\tldrsb\tr3, [sp]\n\tadd\tsp, sp, #16\n\tbx\tlr\n",
                 "f:\n\tadd\tsp, sp, #-12\n\tadd\tsp, sp, #12\n\tbx\tlr\n"),
                ("f:\n\tpush\t{lr}\n\tbge\t.L6\n\tblt\t.L8\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tpush\t{lr}\n\tbge\t.L4\n\tblt\t.L6\n\tpop\t{r0}\n\tbx\tr0\n"),
                # a frame that saves callee-saved registers too: the pressure of keeping the condition live
                ("f:\n\tpush\t{r4, lr}\n\tmov\tr4, r0\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tbx\tlr\n"),
                # a lone push of lr against a collapsed frame of its own: both have a frame
                ("f:\n\tpush\t{lr}\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tpush\t{r4, lr}\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n"),
                # a far branch is a bl to a local label, not a call
                ("f:\n\tpush\t{r4, lr}\n\tbl\t.L12\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tb\t.L9\n\tbx\tlr\n"),
                # a second push saves high registers for the allocation, not a frame for the test
                ("f:\n\tpush\t{r4, lr}\n\tmov\tr7, r8\n\tpush\t{r7}\n\tpop\t{r7}\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n",
                 "f:\n\tpush\t{r4, lr}\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n")):
            with self.subTest(original=original):
                self.assertEqual(inert_collapse.trace(original, collapsed)[0], [])
        # a literal-pool load is no load the test made; a dead ldrh is, and the record drops label numbers
        kinds, extra, missing = inert_collapse.trace(
            "f:\n\tpush\t{lr}\n\tldrh\tr0, [r2]\n\tldr\tr0, .L5\n\tpop\t{r0}\n\tbx\tr0\n",
            "f:\n\tldr\tr0, .L3\n\tbx\tlr\n")
        self.assertEqual(kinds, ["load", "frame"])
        self.assertEqual(extra, ["push {lr}", "ldrh r0, [r2]", "pop {r0}", "bx r0"])
        self.assertEqual(inert_collapse.trace("f:\n\tldr\tr0, .L5\n\tldr\tr1, .L5+4\n\tbx\tlr\n",
                                              "f:\n\tbx\tlr\n")[0], [])
        # a frame for a call only the original makes (a call in the condition) counts, callee-saved or not
        self.assertEqual(inert_collapse.trace(
            "f:\n\tpush\t{r4, lr}\n\tbl\tg\n\tpop\t{r4}\n\tpop\t{r0}\n\tbx\tr0\n", "f:\n\tbx\tlr\n")[0], ["frame"])
        self.assertEqual(inert_collapse.trace(
            "f:\n\tpush\t{lr}\n\tpop\t{r0}\n\tbx\tr0\n", "f:\n\tbx\tlr\n")[0], ["frame"])
        # what matters is a push of lr: a collapsed push of other registers alone is no frame of lr
        self.assertEqual(inert_collapse.trace(
            "f:\n\tpush\t{lr}\n\tpop\t{r0}\n\tbx\tr0\n", "f:\n\tpush\t{r4}\n\tpop\t{r4}\n\tbx\tlr\n")[0],
            ["frame"])

    def test_normalising_drops_moves_registers_and_list_widths(self):
        for instruction, form in (("mov r0, r1", None), ("mov r8, r9", None), ("add r2, r0, #0", None),
                                  ("mov r0, #1", "mov r, #1"), ("add r0, r1, #1", "add r, r, #1"),
                                  ("push {r4, r5, lr}", "push {lr}"), ("pop {r4, r5}", "pop {}"),
                                  ("pop {r4, pc}", "pop {pc}"), ("ldr r6, [sp, #16]", "ldr r, [sp, #16]"),
                                  ("bx lr", "bx lr"), ("bx r0", "bx r"), ("ldr r0, .L5", "ldr r, .L"),
                                  ("bge .L12", "bge .L")):
            with self.subTest(instruction=instruction):
                self.assertEqual(inert_collapse.normalised(instruction), form)
        self.assertEqual(inert_collapse.instructions(".gcc2_compiled.:\n\t.globl\tf\nf:\n\tbx\tlr @ x\n.L2:\n"
                                                     "\t.word\t0x1\n"), ["bx lr"])


@unittest.skipUnless(COMPILER, "fixed compiler required")
class CompiledTraceTests(unittest.TestCase):
    def records(self, source):
        root = scratch(self, "inert_trace_")
        tree(root, source)
        return match.inert_trace_records(root, A)

    def test_a_load_or_a_frame_counts(self):
        for name, kinds in (("frame", "frame"), ("load and frame", "load and frame"), ("load", "load")):
            with self.subTest(name=name):
                (record,) = self.records(SHAPES[name])
                line = line_of(SHAPES[name], "if (")
                self.assertTrue(record.startswith(f"{inert_collapse.RECORD}`src/{A:08X}.c` line {line} keeps "
                                                  f"{kinds}: "), record)
        (record,) = self.records(MEMORY_LEAF)
        self.assertIn("16 bytes against 4 with the arms collapsed", record)
        self.assertIn("ldrh r0, [r2]", record)

    def test_the_review_fixtures(self):
        for name, reason in (("z1_framed_pool", "changes only register allocation"),
                             ("z2_nonleaf_pool", "changes only register allocation"),
                             ("z3_shift_assign", "condition with a side effect"),
                             ("z4_shiftr_assign", "condition with a side effect"),
                             ("z5_spill", "changes only register allocation"),
                             ("z6_loop_after", "changes only register allocation"),
                             ("z8_cse_join", "leaves nothing in the ROM"),
                             # a spill and its reload of another value: register pressure, not the test
                             ("z9_pressure", "changes only register allocation"),
                             ("z10_pressure_after", "changes only register allocation"),
                             ("z11_const_remat", "changes only register allocation"),
                             ("z12_const_remat2", "changes only register allocation")):
            with self.subTest(name=name), self.assertRaisesRegex(inert_collapse.TraceError, reason):
                self.records(REVIEW[name])
        (record,) = self.records(REVIEW["z7_table_pool"])
        self.assertIn(" keeps load and frame: ", record)
        self.assertNotRegex(record, r"\.L\d")

    def test_registers_alone_or_nothing_refuses(self):
        for name, reason in (("registers after a call", "changes only register allocation"),
                             ("registers in a framed leaf", "changes only register allocation"),
                             ("nothing", "leaves nothing in the ROM")):
            with self.subTest(name=name), self.assertRaisesRegex(inert_collapse.TraceError, reason):
                self.records(SHAPES[name])

    def test_a_justified_test_in_a_header_counts_only_where_it_is_included(self):
        header = ("static void flag(int c, int *x) {\n    /* plausible: the ROM keeps the test at 0x08001234 */\n"
                  "    if (c) *x = 1; else *x = 1;\n}\n")
        root = scratch(self, "inert_header_")
        tree(root, SHAPES["load"])
        (root / "include/flag.h").write_text(header)
        # not included: nothing of it is in this unit
        (record,) = match.inert_trace_records(root, A)
        self.assertIn(f"`src/{A:08X}.c` line", record)
        # included and used: its test is collapsed in this unit too
        (root / f"src/{A:08X}.c").write_text('#include "flag.h"\n' + SHAPES["load"].replace(
            "    g();\n", "    g();\n    flag(v, (int *)p);\n"))
        records = match.inert_trace_records(root, A)
        self.assertEqual([record.split("` line")[0] for record in records],
                         [f"{inert_collapse.RECORD}`include/flag.h", f"{inert_collapse.RECORD}`src/{A:08X}.c"])

    def test_an_unjustified_or_uncited_test_needs_no_compile(self):
        for source in (MEMORY_LEAF.replace(CITE, "/* the ROM keeps the test */"),
                       MEMORY_LEAF.replace(CITE, "/* plausible: the ROM keeps the test */")):
            with self.subTest(source=source), patch.object(match, "compile_object",
                                                           side_effect=AssertionError("no compile")):
                self.assertEqual(self.records(source), [])


@unittest.skipUnless(COMPILER, "fixed compiler required")
class GenericWriterTests(unittest.TestCase):
    """the generic writer prints the record, --check-report holds it, and replay recompiles it"""

    def tree(self, source, data):
        root = scratch(self, "inert_generic_")
        tree(root, source)
        mapping, index = addressed_fixtures.indexes(
            [{"rom": f"0x{A:08X}", "end": f"0x{A + len(data):08X}", "mode": "thumb", "instrs": len(data) // 2}])
        (root / "config/functions.json").write_bytes(mapping)
        (root / "symbols/functions.txt").write_bytes(index)
        rom = bytearray(A - match.ROM_BASE + 0x100)
        rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
        (root / "baserom.bin").write_bytes(bytes(rom))
        environment = patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin"))
        environment.start()
        self.addCleanup(environment.stop)
        return root

    def test_a_traced_match_prints_its_record_and_replay_recompiles_it(self):
        root = self.tree(MEMORY_LEAF, MEMORY_LEAF_BYTES)
        status, output = run_main(["--root", str(root), f"{A:08X}"])
        self.assertIn("verdict MATCH - byte identical", output)
        (record,) = match.inert_trace_records(root, A)
        printed = output.splitlines()
        self.assertLess(printed.index(record.removeprefix("* ")), printed.index("verdict MATCH - byte identical"))
        report = (root / f"docs/match/{A:08X}.md").read_text()
        lines = report.split("\n")
        self.assertEqual(lines[lines.index("* source plausibility: plausible") + 1], record)
        status, output = run_main(["--root", str(root), "--check-report", f"{A:08X}"])
        self.assertIn("report  identical to the saved", output)
        self.assertTrue(match_evidence.report_matches(report, root, A))
        self.assertFalse(match_evidence.report_matches(without(report, inert_collapse.RECORD), root, A))
        self.assertFalse(match_evidence.report_matches(
            report.replace(record, record.replace("ldrh r0, [r2]", "ldrh r0, [r3]")), root, A))
        with patch.object(match, "inert_trace_records", side_effect=inert_collapse.TraceError("planted")):
            self.assertFalse(match_evidence.report_matches(report, root, A))

    def test_an_implausible_source_prints_no_record(self):
        root = self.tree(MEMORY_LEAF.replace("    u8 b = (u8)v;\n", "    u8 b = (u8)v; /* a hack */\n"),
                         MEMORY_LEAF_BYTES)
        status, output = run_main(["--root", str(root), f"{A:08X}"])
        self.assertIn("source  IMPLAUSIBLE", output)
        self.assertIn("hack-vocabulary", output)
        self.assertNotIn("inert test trace", output)
        report = root / f"docs/match/{A:08X}.md"
        self.assertFalse(report.exists() and inert_collapse.RECORD in report.read_text())

    def test_a_test_that_changes_only_registers_is_implausible(self):
        # a leaf, so the generic path needs no callee index (the no-trace shape calls out, CompiledTraceTests)
        root = self.tree(SHAPES["registers in a framed leaf"], bytes(32))
        status, output = run_main(["--root", str(root), f"{A:08X}"])
        self.assertIn("source  IMPLAUSIBLE", output)
        self.assertIn("changes only register allocation", output)
        report = root / f"docs/match/{A:08X}.md"
        self.assertFalse(report.exists() and inert_collapse.RECORD in report.read_text())


RECORD = f"{inert_collapse.RECORD}`src/{A:08X}.c` line 9 keeps load and frame: 16 bytes against 4 ..."


class RecordPlacementTests(unittest.TestCase):
    REPORT = "# 0x08010000\n\n* verification: `x`\n* source plausibility: plausible\n* rest: y\n\n**MATCH**\n"
    VOLATILE = ["* allowlisted volatile: `s`", "* allowlisted volatile semantics: `s`"]
    RECORDS = [f"{inert_collapse.RECORD}`src/a.c` line 3 keeps load: a", f"{inert_collapse.RECORD}`src/a.c` line 9 keeps frame: b"]

    def test_records_follow_the_plausible_source_line_and_the_volatile_records(self):
        carried = match_evidence.carry_trace_records(self.REPORT, self.RECORDS)
        self.assertEqual(carried.split("\n")[3:7], ["* source plausibility: plausible", *self.RECORDS, "* rest: y"])
        self.assertEqual(match_evidence.carry_trace_records(self.REPORT, []), self.REPORT)
        self.assertEqual(match_evidence.strip_trace_records(carried, self.RECORDS), self.REPORT)
        both = match_evidence.carry_trace_records(
            match_evidence.carry_volatile_records(self.REPORT, self.VOLATILE), self.RECORDS)
        self.assertEqual(both.split("\n")[3:9],
                         ["* source plausibility: plausible", *self.VOLATILE, *self.RECORDS, "* rest: y"])
        self.assertEqual(match_evidence.strip_trace_records(
            match_evidence.strip_volatile_records(both, self.VOLATILE), self.RECORDS), self.REPORT)

    def test_a_report_that_cannot_carry_them_is_refused(self):
        for report in (self.REPORT.replace("* source plausibility: plausible\n", ""),
                       self.REPORT.replace("plausible\n", "IMPLAUSIBLE\n"),
                       self.REPORT + "* source plausibility: plausible\n",
                       match_evidence.carry_trace_records(self.REPORT, self.RECORDS)):
            with self.subTest(report=report), self.assertRaises(ValueError):
                match_evidence.carry_trace_records(report, self.RECORDS)

    def test_stripping_requires_exactly_the_recomputed_records(self):
        carried = match_evidence.carry_trace_records(self.REPORT, self.RECORDS)
        for report, records in ((carried, self.RECORDS[:1]), (self.REPORT, self.RECORDS), (carried, []),
                                (carried.replace("frame: b", "frame: c"), self.RECORDS),
                                (carried.replace(self.RECORDS[1], "  " + self.RECORDS[1]), self.RECORDS),
                                (self.REPORT + "\n".join(self.RECORDS) + "\n", self.RECORDS),
                                (carried.replace(self.RECORDS[1], "* other: z\n" + self.RECORDS[1]), self.RECORDS),
                                (carried.replace(self.RECORDS[1], self.RECORDS[1] + "\n" + self.RECORDS[1]),
                                 self.RECORDS),
                                (carried + "* source plausibility: plausible\n", self.RECORDS)):
            with self.subTest(report=report, records=records), self.assertRaises(ValueError):
                match_evidence.strip_trace_records(report, records)


class SelectorRecordTests(unittest.TestCase):
    """--addressed-signed-runtime-profile writes its own report: the record is carried into it (compiles mocked)"""
    setUp = addressed_fixtures.AddressedSignedRuntimeTests.setUp
    fixture = addressed_fixtures.AddressedSignedRuntimeTests.fixture
    synthetic_result = addressed_fixtures.AddressedSignedRuntimeTests.synthetic_result

    def tree(self):
        root = scratch(self, "inert_selector_")
        tree(root, f"void func_{A:08X}(void)\n{{\n}}\n")
        f = self.fixture()
        (root / "config/functions.json").write_bytes(f["mapping"])
        (root / "symbols/functions.txt").write_bytes(f["index"])
        (root / "baserom.bin").write_bytes(f["rom"])
        environment = patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin"))
        environment.start()
        self.addCleanup(environment.stop)
        return root, f

    def argv(self, root, *extra):
        return ["--root", str(root), "--addressed-signed-runtime-profile", addressed.SELECTOR, *extra, f"{A:08X}"]

    def test_the_report_carries_the_record_and_replay_checks_it(self):
        root, f = self.tree()
        result = self.synthetic_result(root, f)
        with patch.object(addressed, "build", return_value=result), \
                patch.object(match, "inert_trace_records", return_value=[RECORD]):
            status, output = run_main(self.argv(root))
            self.assertEqual(status, 0, output)
            report = (root / f"docs/match/{A:08X}.md").read_text()
            self.assertEqual(report, match_evidence.carry_trace_records(addressed.render(result), [RECORD]))
            printed = output.splitlines()
            self.assertLess(printed.index(RECORD.removeprefix("* ")), printed.index("verdict MATCH - byte identical"))
            self.assertTrue(match_evidence.report_matches(report, root, A))
            self.assertFalse(match_evidence.report_matches(addressed.render(result), root, A))
            self.assertFalse(match_evidence.report_matches(report.replace("line 9", "line 8"), root, A))
        with patch.object(addressed, "build", return_value=result), \
                patch.object(match, "inert_trace_records", return_value=[]):
            self.assertFalse(match_evidence.report_matches(report, root, A))
            self.assertTrue(match_evidence.report_matches(addressed.render(result), root, A))

    def test_a_refused_trace_is_implausible_before_the_selector(self):
        root, _ = self.tree()
        with patch.object(addressed, "build", side_effect=AssertionError("selector must not run")), \
                patch.object(match, "inert_trace_records", side_effect=inert_collapse.TraceError("planted")):
            status, output = run_main(self.argv(root))
        self.assertIn("source    IMPLAUSIBLE", status)
        self.assertIn("inert test trace: planted", status)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())

    def test_a_writer_that_cannot_carry_records_is_refused(self):
        root, f = self.tree()
        result = self.synthetic_result(root, f)
        plain = addressed.render(result).replace("* source plausibility: plausible\n", "")
        with patch.object(addressed, "build", return_value=result), \
                patch.object(addressed, "render", return_value=plain), \
                patch.object(match, "inert_trace_records", return_value=[RECORD]):
            status, output = run_main(self.argv(root, "--emit", "build/symbol.bin"))
        self.assertIn("inert test trace records not carried", status)
        self.assertNotIn("verdict MATCH", output)
        self.assertFalse((root / f"docs/match/{A:08X}.md").exists())
        self.assertFalse((root / "build/symbol.bin").exists())

    def test_a_labelled_report_is_refused(self):
        root, _ = self.tree()
        with patch.object(addressed, "build", side_effect=AssertionError("selector must not run")), \
                patch.object(match, "inert_trace_records", return_value=[RECORD]):
            status, output = run_main(self.argv(root, "--label", "draft"))
        self.assertIn("inert test trace records need the unlabelled report", status)

    def test_a_refused_selector_keeps_its_diagnostics(self):
        root, _ = self.tree()

        def selector(*args):
            print("selector refused: planted")
            return 19
        with patch.object(addressed, "issue", side_effect=selector), \
                patch.object(match, "inert_trace_records", return_value=[RECORD]):
            status, output = run_main(self.argv(root))
        self.assertEqual(output, "selector refused: planted\n")
        self.assertIn("inert test trace records not carried: the selector did not verify the source", status)

    def test_a_source_without_records_passes_through(self):
        root, _ = self.tree()

        def selector(*args):
            print("selector output")
            return 19
        with patch.object(addressed, "issue", side_effect=selector):
            status, output = run_main(self.argv(root))
        self.assertEqual((status, output), (19, "selector output\n"))


if __name__ == "__main__":
    unittest.main()
