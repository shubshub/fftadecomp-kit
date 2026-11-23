"""Plain-schema replay admits exactly the fields match.py writes, with walk-derived labels (kit #247).

The unit tests check `plain_report_fields.check` on field lists. The end-to-end tests compile natural C
with the fixed agbcc, run match.py, and then replay the saved report with foreign, duplicate and
relabelled fields.
"""
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import plain_report_fields as fields

ADDRESS = 0x08000200
HEX = "0" * 64


def report_lines(schema, *, unit=False, self_calls=False, loop_replays=0, data_flow=evidence.CALL_SUMMARY):
    """The `* ` lines match.py writes for a plain schema, in its order."""
    framed = schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.FRAMED_DATA_SCHEMA,
                        evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA)
    buffer = schema in (evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA)
    data = schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA)
    linked = schema in (evidence.LINKED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA) or buffer
    lines = ["* source: `src/08000200.c`", f"* verification: `{schema}`", f"* source SHA-256: `{HEX}`"]
    if framed:
        lines.append(f"* stack frame: {evidence.STACK_SUMMARY}")
    if buffer:
        lines += [f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}", f"* buffer proof SHA-256: `{HEX}`"]
        lines += ["* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400"] * loop_replays
    if linked or data:
        lines += [f"* mapping SHA-256: `{HEX}`",
                  f"* control flow: {data_flow if data else evidence.CALL_SUMMARY}"]
        if self_calls:
            lines += [f"* self calls: {evidence.SELF_CALL_SUMMARY}", "* self call sites: `[4]`"]
    if data:
        lines.append(f"* data symbols SHA-256: `{HEX}`")
    if unit:
        lines += ["* library unit: `row`", "* unit toolchain: `tool`", f"* unit compiler SHA-256: `{HEX}`"]
    lines += [f"* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`",
              "* verified extent: complete ELF function symbol, including literal pools",
              "* relocations: none", "* ROM bytes: `0047` (2 bytes)", "* compiled : `0047`",
              "* source plausibility: plausible", "* hand-asm allow list: not listed"]
    return ["# match report - 0x08000200", ""] + lines + ["", "**MATCH - byte identical** - 2/2 bytes"]


PLAIN = (evidence.SCHEMA, evidence.FRAMED_SCHEMA, evidence.LINKED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA,
         evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA, evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA)
# Field lines other profiles write, as #247 measured them on saved reports.
FOREIGN = (f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}", f"* buffer proof SHA-256: `{HEX}`",
           "* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400",
           "* buffer switch callee: `guarded-switch-callee-v1` 0x08000400",
           "* buffer BIOS summaries: `x`", "* buffer BIOS premise: x", "* buffer BIOS manifest: `{}`",
           f"* stack frame: {evidence.STACK_SUMMARY}", f"* mapping SHA-256: `{HEX}`",
           f"* control flow: {evidence.CALL_SUMMARY}", f"* data symbols SHA-256: `{HEX}`",
           f"* ROM SHA-256: `{HEX}`", f"* function index SHA-256: `{HEX}`", "* scope: `x`",
           "* admission scope: `x`", "* named data binding: `x`", "* stack index premise: `x`",
           "* switches: x", "* function addresses: x", "* empty body: x", "* owner runtime: x",
           f"* self calls: {evidence.SELF_CALL_SUMMARY}", "* allowlisted volatile access: x",
           "  * buffer calls: indented", "*\tbuffer calls: tab",
           # Other bullet forms render as field bullets too; the writer emits only `* name: ` lines.
           f"- data symbols SHA-256: `{HEX}`", "+ buffer calls: x", f"\u00a0* data symbols SHA-256: `{HEX}`",
           f"*\u00a0data symbols SHA-256: `{HEX}`", f"\t- mapping SHA-256: `{HEX}`")


def insert_after(lines, prefix, added):
    """`added` placed after the line starting with `prefix`: the writer's slot for it."""
    at = next(index for index, line in enumerate(lines) if line.startswith(prefix))
    return lines[:at + 1] + list(added) + lines[at + 1:]


def insert_before(lines, prefix, added):
    """`added` placed before the line starting with `prefix`."""
    at = next(index for index, line in enumerate(lines) if line.startswith(prefix))
    return lines[:at] + list(added) + lines[at:]


class FieldListTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="plain_report_fields_")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "src/08000200.c").write_text("/* fixture */\n")

    def check(self, lines, schema, address=ADDRESS):
        fields.check(lines, schema, address, self.root)

    def test_the_writer_lists_pass(self):
        for schema in PLAIN:
            with self.subTest(schema=schema):
                self.check(report_lines(schema), schema)
                self.check(report_lines(schema, unit=True), schema)
        for schema in (evidence.LINKED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.DATA_SCHEMA,
                       evidence.FRAMED_DATA_SCHEMA):
            with self.subTest(schema=schema, self_calls=True):
                self.check(report_lines(schema, self_calls=True), schema)
        self.check(report_lines(evidence.DATA_SCHEMA, data_flow="closed leaf CFG"), evidence.DATA_SCHEMA)
        for schema in (evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA):
            self.check(report_lines(schema, loop_replays=3), schema)

    def test_any_field_the_schema_does_not_write_refuses(self):
        # Optional fields the writer emits for a schema: self calls on the four direct-call
        # schemas; on the two buffer schemas, the buffer proof lines, which the proof compares
        # exactly (SavedReportTests replays those).
        optional = {evidence.LINKED_SCHEMA: ("* self calls",), evidence.FRAMED_LINKED_SCHEMA: ("* self calls",),
                    evidence.DATA_SCHEMA: ("* self calls",), evidence.FRAMED_DATA_SCHEMA: ("* self calls",),
                    evidence.BUFFER_SCHEMA: ("* buffer ",), evidence.STACK_BUFFER_SCHEMA: ("* buffer ",)}
        for schema in PLAIN:
            own = set(line.split(":")[0] for line in report_lines(schema) if line.startswith("* "))
            for line in FOREIGN:
                if line.split(":")[0] in own or line.startswith(optional.get(schema, ())):
                    continue
                with self.subTest(schema=schema, line=line), self.assertRaisesRegex(
                        ValueError, "not written for this schema"):
                    lines = report_lines(schema)
                    self.check(lines[:4] + [line] + lines[4:], schema)

    def test_self_calls_only_on_the_direct_call_schemas_and_in_pairs(self):
        for schema in (evidence.SCHEMA, evidence.FRAMED_SCHEMA, evidence.BUFFER_SCHEMA):
            with self.subTest(schema=schema), self.assertRaisesRegex(ValueError, "not written"):
                self.check(report_lines(schema) + [f"* self calls: {evidence.SELF_CALL_SUMMARY}"], schema)
        lines = [line for line in report_lines(evidence.LINKED_SCHEMA, self_calls=True)
                 if not line.startswith("* self call sites")]
        with self.assertRaisesRegex(ValueError, "self-call lines are incomplete"):
            self.check(lines, evidence.LINKED_SCHEMA)

    def test_every_field_once(self):
        for schema in PLAIN:
            lines = report_lines(schema, self_calls=schema in (evidence.LINKED_SCHEMA, evidence.DATA_SCHEMA),
                                 unit=True)
            for line in lines:
                if not line.startswith("* "):
                    continue
                with self.subTest(schema=schema, line=line), self.assertRaisesRegex(ValueError, "duplicated"):
                    self.check(lines + [line], schema)

    def test_buffer_proof_lines_only_on_the_buffer_schemas(self):
        proof = ["* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000400",
                 "* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000500",
                 "* buffer BIOS summaries: `x`", "* buffer BIOS premise: a", "* buffer BIOS premise: b",
                 "* buffer BIOS manifest: `{}`"]
        for schema in (evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA):
            self.check(insert_after(report_lines(schema), "* buffer proof SHA-256", proof), schema)
        for schema in PLAIN[:6]:
            for line in proof:
                with self.subTest(schema=schema, line=line), self.assertRaisesRegex(ValueError, "not written"):
                    self.check(report_lines(schema) + [line], schema)
        # The two bound buffer fields stay single.
        for line in report_lines(evidence.STACK_BUFFER_SCHEMA):
            if line.startswith(("* buffer calls", "* buffer proof SHA-256")):
                with self.subTest(line=line), self.assertRaisesRegex(ValueError, "duplicated"):
                    self.check(report_lines(evidence.STACK_BUFFER_SCHEMA) + [line], evidence.STACK_BUFFER_SCHEMA)

    def test_callee_saved_premise_lines_only_on_the_call_schemas(self):
        # Kit #350: match.py writes them after the buffer proof lines, before the mapping line.
        premises = ["* callee-saved premise: call at 0x08000204 in 0x08000200 through _call_via_r3 to an "
                    "unknown address, with R5 depending on owner stack addresses; unproved premise: x",
                    "* callee-saved premise: indexed stack load at 0x08000206 in 0x08000200, excluding the "
                    "saved or released frame word at sp+8; unproved premise: y",
                    "* callee-saved fact: 0x02000000 may still hold the frame address stored at 0x08000208 in "
                    "0x08000200 when 0x08000200 returns at 0x0800020C, releasing that frame; z"]
        for schema in PLAIN[2:]:
            with self.subTest(schema=schema):
                self.check(insert_before(report_lines(schema), "* mapping SHA-256", premises), schema)
                with self.assertRaisesRegex(ValueError, "order"):
                    self.check(insert_after(report_lines(schema), "* mapping SHA-256", premises), schema)
        for schema in PLAIN[:2]:
            with self.subTest(schema=schema), self.assertRaisesRegex(ValueError, "not written"):
                self.check(report_lines(schema) + premises[:1], schema)

    def test_fields_keep_the_writer_order(self):
        def swap(lines, first, second):
            a = next(index for index, line in enumerate(lines) if line.startswith(first))
            b = next(index for index, line in enumerate(lines) if line.startswith(second))
            lines = list(lines)
            lines[a], lines[b] = lines[b], lines[a]
            return lines

        def below_verdict(lines, prefix):
            # the fields from `prefix` on, in their order, moved below the verdict line
            at = next(index for index, line in enumerate(lines) if line.startswith(prefix))
            verdict = next(index for index, line in enumerate(lines) if line.startswith("**"))
            return lines[:at] + lines[verdict:] + lines[at:verdict]

        cases = []
        for schema in PLAIN:
            lines = report_lines(schema, unit=True)
            cases += [(schema, swap(lines, "* compiler", "* verified extent")),
                      (schema, swap(lines, "* source: ", "* verification")),
                      (schema, swap(lines, "* source plausibility", "* hand-asm")),
                      (schema, swap(lines, "* library unit", "* compiler"))]
        for schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_DATA_SCHEMA, evidence.STACK_BUFFER_SCHEMA):
            cases.append((schema, swap(report_lines(schema), "* source SHA-256", "* stack frame")))
        for schema in (evidence.LINKED_SCHEMA, evidence.DATA_SCHEMA):
            lines = report_lines(schema, self_calls=True)
            cases += [(schema, swap(lines, "* self calls", "* self call sites")),
                      (schema, swap(lines, "* mapping", "* control flow"))]
        cases.append((evidence.DATA_SCHEMA, swap(report_lines(evidence.DATA_SCHEMA), "* control flow",
                                                 "* data symbols")))
        for schema in (evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA):
            lines = report_lines(schema, loop_replays=2)
            cases += [(schema, swap(lines, "* buffer calls", "* buffer proof")),
                      (schema, swap(lines, "* buffer proof", "* buffer loop replay")),
                      (schema, swap(lines, "* buffer loop replay", "* mapping"))]
        for schema, lines in cases:
            with self.subTest(schema=schema, lines=[line[:12] for line in lines if line.startswith("* ")]), \
                    self.assertRaisesRegex(ValueError, "not in the writer's order"):
                self.check(lines, schema)
        # The last fields, or all of them, moved below the verdict in the writer's order.
        for prefix in ("* hand-asm", "* compiler", "* source: "):
            for schema in PLAIN:
                with self.subTest(schema=schema, prefix=prefix), \
                        self.assertRaisesRegex(ValueError, "follows the verdict"):
                    self.check(below_verdict(report_lines(schema), prefix), schema)

    def test_every_written_field_is_required(self):
        for schema in PLAIN:
            lines = report_lines(schema)
            for index, line in enumerate(lines):
                if not line.startswith("* "):
                    continue
                with self.subTest(schema=schema, line=line), self.assertRaisesRegex(ValueError, "missing"):
                    self.check(lines[:index] + lines[index + 1:], schema)

    def test_compiler_line_is_required(self):
        # library_units admits a report without `* compiler:`; match.py always writes one.
        lines = [line for line in report_lines(evidence.LINKED_SCHEMA) if not line.startswith("* compiler")]
        with self.assertRaisesRegex(ValueError, "missing: \\* compiler:"):
            self.check(lines, evidence.LINKED_SCHEMA)

    def source_admitted(self, value):
        lines = [f"* source: {value}" if line.startswith("* source: ") else line
                 for line in report_lines(evidence.SCHEMA)]
        try:
            self.check(lines, evidence.SCHEMA)
        except ValueError as error:
            self.assertRegex(str(error), "source line")
            return False
        return True

    def test_source_names_the_file_match_py_compiles(self):
        # match.py names src/<ADDR>.c, else the first <ADDR>.c under src/ in sorted order.
        refused = ("`src/20101/08000200.c`", "`src/08000202.c`", "`src/0800020a.c`", "`src/../src/08000200.c`",
                   "`src/./08000200.c`", "`/src/08000200.c`", "src/08000200.c", "`include/08000200.c`",
                   "`src/08000200.c` extra", "`src/08000200.C`")
        self.assertTrue(self.source_admitted("`src/08000200.c`"))
        for value in refused:
            with self.subTest(value=value):
                self.assertFalse(self.source_admitted(value))

    def test_a_module_folder_is_bound(self):
        (self.root / "src/20101").mkdir()
        (self.root / "src/08000200.c").rename(self.root / "src/20101/08000200.c")
        self.assertTrue(self.source_admitted("`src/20101/08000200.c`"))
        for value in ("`src/08000200.c`", "`src/30101/08000200.c`", "`src/20101/08000202.c`"):
            with self.subTest(value=value):
                self.assertFalse(self.source_admitted(value))

    def test_the_top_level_source_is_the_one_named(self):
        (self.root / "src/0000").mkdir()
        (self.root / "src/0000/08000200.c").write_text("/* second copy, sorted first */\n")
        self.assertTrue(self.source_admitted("`src/08000200.c`"))
        self.assertFalse(self.source_admitted("`src/0000/08000200.c`"))
        (self.root / "src/08000200.c").unlink()
        self.assertTrue(self.source_admitted("`src/0000/08000200.c`"))

    def test_no_source_refuses(self):
        (self.root / "src/08000200.c").unlink()
        self.assertFalse(self.source_admitted("`src/08000200.c`"))

    def test_hand_asm_line_has_the_writer_form(self):
        lines = report_lines(evidence.SCHEMA)
        for value, admitted in (("not listed", True), ("listed (maintainer reason)", True),
                                ("unlisted", False), ("not listed, plus", False), ("", False)):
            changed = [f"* hand-asm allow list: {value}" if line.startswith("* hand-asm") else line
                       for line in lines]
            with self.subTest(value=value):
                if admitted:
                    self.check(changed, evidence.SCHEMA)
                else:
                    with self.assertRaisesRegex(ValueError, "hand-asm"):
                        self.check(changed, evidence.SCHEMA)

    def test_other_schemas_are_not_plain(self):
        self.assertIsNone(fields.layout("elf-symbol-thumb-switches-v1"))
        with self.assertRaisesRegex(ValueError, "not a plain report schema"):
            self.check(report_lines(evidence.SCHEMA), "elf-symbol-thumb-switches-v1")


def decode(data):
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return list(decoder.disasm(data, ADDRESS))


class LabelTests(unittest.TestCase):
    """check_labels on decoded bodies: frame use, calls and data literals as match.py derives them."""
    LEAF = bytes.fromhex("7047")                       # bx lr
    FRAME = bytes.fromhex("81b001b07047")              # sub sp, #4; add sp, #4; bx lr
    LOAD = bytes.fromhex("00487047")                   # ldr r0, [pc, #0]; bx lr: at a word offset, loads the next word

    @staticmethod
    def word(value):
        return value.to_bytes(4, "little")

    @staticmethod
    def bl(site, target):
        from synthetic_entry_owner import bl
        return bl(site, target)

    def labels(self, schema, data, calls, thumb=True):
        fields.check_labels(schema, decode(data), ADDRESS, data, thumb, calls)

    def test_frame_label_follows_stack_use(self):
        self.labels(evidence.SCHEMA, self.LEAF, False)
        self.labels(evidence.FRAMED_SCHEMA, self.FRAME, False)
        for schema, data in ((evidence.FRAMED_SCHEMA, self.LEAF), (evidence.SCHEMA, self.FRAME),
                             (evidence.DATA_SCHEMA, self.FRAME), (evidence.FRAMED_DATA_SCHEMA, self.LEAF)):
            with self.subTest(schema=schema, data=data.hex()), self.assertRaisesRegex(ValueError, "frame label"):
                self.labels(schema, data, False)

    def test_arm_code_is_never_framed(self):
        # match.py: framed_profile = thumb and uses_stack_frame(...)
        self.labels(evidence.SCHEMA, self.FRAME, False, thumb=False)
        with self.assertRaisesRegex(ValueError, "frame label"):
            self.labels(evidence.FRAMED_SCHEMA, self.FRAME, False, thumb=False)

    def test_call_label_follows_reached_calls(self):
        external = self.bl(ADDRESS, ADDRESS + 0x200) + self.LEAF
        own_entry = self.bl(ADDRESS, ADDRESS) + self.LEAF
        inside = self.bl(ADDRESS, ADDRESS + 4) + self.LEAF
        for data in (external, own_entry):
            with self.subTest(data=data.hex()):
                self.labels(evidence.LINKED_SCHEMA, data, True)
                loaded = data[:4] + self.LOAD + self.word(0x02000000)
                self.labels(evidence.DATA_SCHEMA, loaded, True)
                for schema, body in ((evidence.SCHEMA, data), (evidence.DATA_SCHEMA, loaded)):
                    with self.assertRaisesRegex(ValueError, "call label"):
                        self.labels(schema, body, False)
        for data in (self.LEAF, inside):
            with self.subTest(data=data.hex()):
                self.labels(evidence.SCHEMA, data, False)
                with self.assertRaisesRegex(ValueError, "call label"):
                    self.labels(evidence.LINKED_SCHEMA, data, True)

    def test_a_data_label_needs_a_loaded_literal_outside_the_function(self):
        # match.py binds data only through an aligned in-function word whose linked value lies
        # outside the function, and Thumb code reads such a pool word only with `ldr rd, [pc, #imm]`.
        outside = self.LOAD + self.word(0x02000000)
        framed = self.FRAME[:4] + self.LOAD + self.word(0x02000000)
        self.labels(evidence.DATA_SCHEMA, outside, False)
        self.labels(evidence.FRAMED_DATA_SCHEMA, framed, False)
        # At a halfword site the PC rounds down: nop; ldr r0, [pc, #4]; bx lr; movs r0, r0 reaches offset 8.
        self.labels(evidence.DATA_SCHEMA, bytes.fromhex("c046014870470000") + self.word(0x02000000), False)
        refused = {
            "no literal": self.LEAF,
            "a calls body": self.bl(ADDRESS, ADDRESS + 0x200) + self.LEAF,
            "a word nothing loads": bytes.fromhex("70470000") + self.word(0x02000000),
            "a register load": bytes.fromhex("08687047") + self.word(0x02000000),   # ldr r0, [r1]; bx lr
            "a load past the end": bytes.fromhex("01487047") + self.word(0x02000000),
            "a literal at the function's entry": self.LOAD + self.word(ADDRESS),
            "a literal inside the function": self.LOAD + self.word(ADDRESS + 2),
            "a literal at the function's end": self.LOAD + self.word(ADDRESS + len(outside) - 1),
        }
        for name, data in refused.items():
            calls = name == "a calls body"
            with self.subTest(body=name), self.assertRaisesRegex(ValueError, "data label"):
                self.labels(evidence.DATA_SCHEMA, data, calls)
        with self.assertRaisesRegex(ValueError, "data label"):
            self.labels(evidence.FRAMED_DATA_SCHEMA, self.FRAME, False)
        # The first address past the function is outside it.
        self.labels(evidence.DATA_SCHEMA, self.LOAD + self.word(ADDRESS + len(outside)), False)
        # The known limit: a literal outside the function may be a raw constant, and is admitted.
        self.labels(evidence.DATA_SCHEMA, self.LOAD + self.word(0x04000000), False)
        # Only the data schemas need one.
        self.labels(evidence.SCHEMA, self.LEAF, False)
        self.labels(evidence.SCHEMA, outside, False)


SOURCES = {
    # One external call, no frame: calls-v1.
    "calls": """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    func_08000400(value, 0);
}
""",
    # A fifth argument on the stack: frame-calls-v1.
    "frame-calls": """typedef unsigned short u16;
extern void func_08000400(u16 a, u16 b, u16 c, u16 d, u16 e);
void func_08000200(u16 value)
{
    func_08000400(value, value, value, value, value);
}
""",
    # A leaf with no relocation: cfg-leaf-v2.
    "leaf": """typedef unsigned short u16;
u16 func_08000200(u16 value)
{
    return value + 1;
}
""",
    # A leaf that loads a raw constant from its literal pool: cfg-leaf-v2.
    "leaf-literal": """typedef unsigned int u32;
u32 func_08000200(u32 value)
{
    return value ^ 0x12345678;
}
""",
}
DATA_SOURCES = {
    # A leaf store through a named data symbol: data-v1 with the closed leaf summary.
    "data-leaf": """typedef unsigned short u16;
extern u16 data_02000000[];
void func_08000200(u16 value)
{
    data_02000000[1] = value;
}
""",
    # A named data symbol passed as the fifth argument: frame-data-v1.
    "frame-data": """typedef unsigned short u16;
extern u16 data_02000000[];
extern void func_08000400(u16 a, u16 b, u16 c, u16 d, u16 *e);
void func_08000200(u16 value)
{
    func_08000400(value, value, value, value, data_02000000);
}
""",
}


def leaf_link(runner, workspace, args, original, address, *rest, **options):
    """The unlinked function bytes: a leaf has no relocation for link_calls to bind."""
    symbol, offset = match.function_record(original, f"func_{address:08X}", address, True)
    return original["text"][offset:offset + symbol["size"]], None, None


@unittest.skipUnless(os.path.exists(os.path.expandvars(match.DEFAULT_CC)), "fixed compiler required")
class SavedReportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import test_data_buffer_calls as data_calls
        if not data_calls.tools_present():
            raise unittest.SkipTest("fixed compiler and ARM tools required")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="plain_report_fields_", dir=scratch)
        base = Path(cls.temporary.name)
        cls.roots, cls.reports = {}, {}
        for name, source in list(SOURCES.items()) + list(DATA_SOURCES.items()) + [
                ("data", data_calls.DATA_ONLY), ("buffer", data_calls.BUFFER_ONLY)]:
            if name.startswith("leaf"):
                with patch.object(match, "link_calls", leaf_link):
                    root = data_calls.build(base / name, source, [("func_08000400", data_calls.STORES)])
            else:
                root = data_calls.build(base / name, source, [("func_08000400", data_calls.STORES)])
            code, output, report = data_calls.run(root)
            assert code == 0, output
            cls.roots[name], cls.reports[name] = root, report

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, text):
        with patch.dict(os.environ, FFTA_ROM=str(self.roots[name] / "baserom.bin")):
            return evidence.report_matches(text, self.roots[name], ADDRESS)

    @staticmethod
    def schema(text):
        return re.search(r"^\* verification: `([^`]+)`", text, re.M)[1]

    @staticmethod
    def edit(text, add=(), drop=(), schema=None, after=None):
        """`add` goes after the line starting with `after` (the writer's slot), else after the last field."""
        rows = [row for row in text.splitlines() if not row.startswith(tuple(drop))]
        if schema:
            rows = [f"* verification: `{schema}`" if row.startswith("* verification:") else row for row in rows]
        at = max(index for index, row in enumerate(rows) if row.startswith(after or "* "))
        return "\n".join(rows[:at + 1] + list(add) + rows[at + 1:]) + "\n"

    def test_the_fixtures_have_the_expected_schemas_and_replay(self):
        expected = {"calls": evidence.LINKED_SCHEMA, "frame-calls": evidence.FRAMED_LINKED_SCHEMA,

                    "leaf": evidence.SCHEMA, "leaf-literal": evidence.SCHEMA,
                    "data": evidence.DATA_SCHEMA, "data-leaf": evidence.DATA_SCHEMA,
                    "frame-data": evidence.FRAMED_DATA_SCHEMA, "buffer": evidence.STACK_BUFFER_SCHEMA}
        for name, schema in expected.items():
            with self.subTest(name=name):
                self.assertEqual(self.schema(self.reports[name]), schema)
                self.assertTrue(self.replays(name, self.reports[name]))

    def test_foreign_fields_refuse(self):
        for name, report in self.reports.items():
            own = {row.split(":")[0] for row in report.splitlines() if row.startswith("* ")}
            for line in FOREIGN:
                if line.split(":")[0] in own:
                    continue
                with self.subTest(name=name, line=line):
                    self.assertFalse(self.replays(name, self.edit(report, add=[line])))

    def test_contradictory_duplicates_refuse(self):
        for name, report in self.reports.items():
            for line in report.splitlines():
                if not line.startswith("* ") or line.startswith("* verification"):
                    continue
                body = line.rstrip("`")
                changed = body[:-1] + ("0" if body[-1] != "0" else "1") + line[len(body):]
                with self.subTest(name=name, line=line[:40]):
                    self.assertFalse(self.replays(name, self.edit(report, add=[changed])))

    def test_a_compiler_less_report_now_refuses(self):
        # library_units.report_admitted admits a report without `* compiler:`;
        # match.py always writes one, and replay of the plain schemas now requires it.
        import library_units
        for name in ("calls", "leaf", "data", "buffer"):
            text = self.edit(self.reports[name], drop=["* compiler:"])
            with self.subTest(name=name):
                self.assertTrue(library_units.report_admitted(text, self.roots[name], ADDRESS))
                self.assertFalse(self.replays(name, text))

    def test_a_module_move_replays_once_regenerated(self):
        root, report = self.roots["calls"], self.reports["calls"]
        old = evidence.source_fingerprint(root, ADDRESS)
        (root / "src/20101").mkdir()
        (root / "src/08000200.c").rename(root / "src/20101/08000200.c")
        try:
            new = evidence.source_fingerprint(root, ADDRESS)
            self.assertNotEqual(new, old)
            moved = report.replace(old, new)
            regenerated = moved.replace("`src/08000200.c`", "`src/20101/08000200.c`")
            # The fingerprint binds the path, so the saved report needs regeneration, as before #247.
            self.assertFalse(self.replays("calls", report))
            # Regenerated, it replays.
            self.assertTrue(self.replays("calls", regenerated))
            # The source line must name the new folder, and the file's own name.
            self.assertFalse(self.replays("calls", moved))
            self.assertFalse(self.replays("calls", regenerated.replace("20101/08000200.c", "20101/08000202.c")))
            self.assertFalse(self.replays("calls", regenerated.replace("`src/20101/", "`src/30101/")))
        finally:
            (root / "src/20101/08000200.c").rename(root / "src/08000200.c")
            (root / "src/20101").rmdir()
        self.assertTrue(self.replays("calls", report))

    def test_the_data_fixtures_have_the_expected_control_flow(self):
        self.assertIn("* control flow: closed leaf CFG", self.reports["data-leaf"].splitlines())
        for name in ("data", "frame-data"):
            self.assertIn(f"* control flow: {evidence.CALL_SUMMARY}", self.reports[name].splitlines())

    def test_labels_follow_the_walk(self):
        # Each relabel below replayed before #247: the label was not compared with the walk.
        frame = f"* stack frame: {evidence.STACK_SUMMARY}"
        flow = f"* control flow: {evidence.CALL_SUMMARY}"
        leaf_mapping = f"* mapping SHA-256: `{evidence.mapping_fingerprint(evidence.mapping_snapshot(self.roots['leaf']))}`"
        # Added lines go to the writer's slot, so only the label is wrong.
        head = "* source SHA-256"
        cases = (
            ("calls", self.edit(self.reports["calls"], add=[frame], schema=evidence.FRAMED_LINKED_SCHEMA,
                                after=head)),
            ("frame-calls", self.edit(self.reports["frame-calls"], drop=["* stack frame"],
                                      schema=evidence.LINKED_SCHEMA)),
            ("leaf", self.edit(self.reports["leaf"], add=[frame], schema=evidence.FRAMED_SCHEMA, after=head)),
            ("leaf", self.edit(self.reports["leaf"], add=[leaf_mapping, flow], schema=evidence.LINKED_SCHEMA,
                               after=head)),
            ("data-leaf", self.reports["data-leaf"].replace("* control flow: closed leaf CFG", flow)),
            ("data", self.edit(self.reports["data"], add=[frame], schema=evidence.FRAMED_DATA_SCHEMA, after=head)),
            ("frame-data", self.edit(self.reports["frame-data"], drop=["* stack frame"],
                                     schema=evidence.DATA_SCHEMA)),
        )
        for name, text in cases:
            with self.subTest(name=name, schema=self.schema(text)):
                self.assertFalse(self.replays(name, text))

    def upgrade(self, name, schema):
        """A non-data report relabelled to a data schema, with current mapping, flow and data-symbol lines."""
        root = self.roots[name]
        mapping = f"* mapping SHA-256: `{evidence.mapping_fingerprint(evidence.mapping_snapshot(root))}`"
        objects = f"* data symbols SHA-256: `{evidence.mapping_fingerprint(evidence.data_snapshot(root))}`"
        text = self.reports[name]
        if "* control flow: " in text:
            return self.edit(text, add=[objects], schema=schema, after="* control flow: ")
        return self.edit(text, add=[mapping, "* control flow: closed leaf CFG", objects], schema=schema,
                         after="* source SHA-256")

    def test_a_data_upgrade_needs_a_loaded_literal(self):
        # Each upgrade replayed before: the data label was not compared with the bytes. These bodies
        # load no literal word outside the function, so no data relocation can exist.
        for name, schema in (("calls", evidence.DATA_SCHEMA), ("frame-calls", evidence.FRAMED_DATA_SCHEMA),
                             ("leaf", evidence.DATA_SCHEMA)):
            with self.subTest(name=name, schema=schema):
                self.assertFalse(self.replays(name, self.upgrade(name, schema)))
        # The known limit: a body that loads a raw constant cannot be told from a data literal.
        self.assertTrue(self.replays("leaf-literal", self.upgrade("leaf-literal", evidence.DATA_SCHEMA)))
        # So does the downgrade: a data report with calls relabelled without its data-symbol line.
        self.assertIn(f"* control flow: {evidence.CALL_SUMMARY}", self.reports["data"].splitlines())
        self.assertTrue(self.replays("data", self.edit(self.reports["data"], drop=["* data symbols"],
                                                       schema=evidence.LINKED_SCHEMA)))

    def test_a_reached_call_still_needs_the_call_summary(self):
        # Refused before #247 too: the leaf walk has no call resolver.
        text = self.reports["data"].replace(f"* control flow: {evidence.CALL_SUMMARY}",
                                            "* control flow: closed leaf CFG")
        self.assertFalse(self.replays("data", text))



@unittest.skipUnless(os.path.exists(os.path.expandvars(match.DEFAULT_CC)), "fixed compiler required")
class SourcePathAgreementTests(unittest.TestCase):
    """match.py compiles and names the source `match_evidence.report_source` resolves.

    match.py calls report_source (src/<ADDR>.c, else the first sorted <ADDR>.c under src/) and prints
    the result as `source    <path>` before compiling, so each layout is compared with what match.py
    itself chose (`source    <path>`; the plausibility line is `source  plausible`), and with the
    `* source:` line when it writes a report. The expected path of each layout is written out here,
    so the comparison does not depend on the function under test.
    """
    LAYOUTS = (("top level", ("src/08000200.c",), "src/08000200.c"),
               ("module folder", ("src/20101/08000200.c",), "src/20101/08000200.c"),
               ("top level and a folder that sorts first", ("src/08000200.c", "src/0000/08000200.c"),
                "src/08000200.c"),
               ("two folders", ("src/20101/08000200.c", "src/0000/08000200.c"), "src/0000/08000200.c"),
               ("missing", (), None))

    def test_match_py_and_replay_name_the_same_source(self):
        import test_data_buffer_calls as data_calls
        if not data_calls.tools_present():
            self.skipTest("fixed compiler and ARM tools required")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="plain_report_source_", dir=scratch) as directory:
            root = data_calls.build(Path(directory), SOURCES["calls"], [("func_08000400", data_calls.STORES)])
            source = (root / "src/08000200.c").read_text()
            for name, paths, expected in self.LAYOUTS:
                with self.subTest(layout=name):
                    for path in (root / "src").rglob("08000200.c"):
                        path.unlink()
                    for path in paths:
                        (root / path).parent.mkdir(parents=True, exist_ok=True)
                        (root / path).write_text(source)
                    code, output, report = data_calls.run(root)
                    chosen = re.findall(r"^source {4}(\S+)$", output, re.MULTILINE)
                    if expected is None:
                        self.assertNotEqual(code, 0)
                        self.assertIn("no source for 0x08000200 under src/", output)
                        self.assertEqual(chosen, [])
                        continue
                    self.assertEqual(chosen, [expected], output)
                    if report is not None:
                        self.assertIn(f"* source: `{expected}`", report.splitlines())
            with self.assertRaisesRegex(ValueError, "no source for 0x08000200 under src/"):
                evidence.report_source(root, ADDRESS)


class OneSourceResolutionTests(unittest.TestCase):
    """`check` has no source resolution of its own: it names what `match_evidence.report_source` names.

    These run without the compiler. The layouts and their expected paths are the ones
    SourcePathAgreementTests holds match.py to.
    """
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="plain_report_source_")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()

    def admitted(self, path):
        lines = [f"* source: `{path}`" if line.startswith("* source: ") else line
                 for line in report_lines(evidence.SCHEMA)]
        try:
            fields.check(lines, evidence.SCHEMA, ADDRESS, self.root)
        except ValueError as error:
            self.assertEqual(str(error), "plain report source line does not name the source match.py compiles")
            return False
        return True

    def test_check_names_what_report_source_resolves(self):
        # The file on disk is src/08000200.c; check follows the resolver, not the tree.
        (self.root / "src/08000200.c").write_text("/* fixture */\n")
        self.assertTrue(self.admitted("src/08000200.c"))
        with patch.object(evidence, "report_source", return_value="src/chosen/08000200.c") as resolver:
            self.assertTrue(self.admitted("src/chosen/08000200.c"))
            self.assertFalse(self.admitted("src/08000200.c"))
            self.assertEqual([call.args for call in resolver.call_args_list], [(self.root, ADDRESS)] * 2)
        with patch.object(evidence, "report_source", side_effect=ValueError("no source")):
            self.assertFalse(self.admitted("src/08000200.c"))
            self.assertFalse(self.admitted("None"))

    def test_each_layout_names_one_fixed_path(self):
        every = sorted({path for _, paths, _ in SourcePathAgreementTests.LAYOUTS for path in paths})
        for name, paths, expected in SourcePathAgreementTests.LAYOUTS:
            with self.subTest(layout=name):
                for path in (self.root / "src").rglob("08000200.c"):
                    path.unlink()
                for path in paths:
                    (self.root / path).parent.mkdir(parents=True, exist_ok=True)
                    (self.root / path).write_text("/* fixture */\n")
                if expected is None:
                    with self.assertRaisesRegex(ValueError, "no source for 0x08000200 under src/"):
                        evidence.report_source(self.root, ADDRESS)
                else:
                    self.assertEqual(evidence.report_source(self.root, ADDRESS), expected)
                self.assertEqual([path for path in every if self.admitted(path)],
                                 [] if expected is None else [expected])



# Kit #350 on the plain framed schemas: the owner keeps the addresses of two locals in R4 and R5
# across a call (an inlined helper's output pointers, as 080D8CD4 does), so the callee is walked;
# it calls through _call_via_r3 to an unknown address, a premised site.
PREMISE_TYPES = ("typedef unsigned short u16;\ntypedef short s16;\ntypedef signed char s8;\n"
                 "typedef unsigned char u8;\nextern u16 data_02000000[];\n")
PREMISE_HELPER = """extern u8 *func_08000400(void *object);
extern u8 func_08000500(u8 x, u8 y);
static inline void get_coordinates(void *object, s16 *x, s16 *y)
{
    u8 *position = func_08000400(object);

    *x = (s8)position[10];
    *y = (s8)position[11];
}
"""
PREMISE_SOURCES = {
    "frame-calls": PREMISE_TYPES + PREMISE_HELPER + """u8 func_08000200(void *object)
{
    s16 x, y;

    get_coordinates(object, &x, &y);
    return func_08000500(x, y);
}
""",
    "frame-data": PREMISE_TYPES + PREMISE_HELPER + """u8 func_08000200(void *object)
{
    s16 x, y;

    get_coordinates(object, &x, &y);
    data_02000000[0] = x;
    return func_08000500(x, y);
}
""",
}
PREMISE_CALLEES = [
    ("func_08000400", ".equ via_r3, 0x%08X\npush {lr}\nldr r3, =0x02000000\nldr r3, [r3]\nbl via_r3\n"
                      "pop {r1}\nbx r1\n.ltorg" % match.RUNTIME_HELPERS["_call_via_r3"]),
    ("func_08000500", "movs r0, #0\nbx lr"),
]


@unittest.skipUnless(os.path.exists(os.path.expandvars(match.DEFAULT_CC)), "fixed compiler required")
class PlainFramedPremiseReplayTests(unittest.TestCase):
    """A plain framed report with callee-saved premise lines replays: the closed re-render states
    them in match.py's slot, from the walk the replay repeats."""

    @classmethod
    def setUpClass(cls):
        import test_data_buffer_calls as data_calls
        if not data_calls.tools_present():
            raise unittest.SkipTest("fixed compiler and ARM tools required")
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="plain_framed_premises_", dir=scratch)
        cls.roots, cls.reports = {}, {}
        for name, source in PREMISE_SOURCES.items():
            root = data_calls.build(Path(cls.temporary.name) / name, source, PREMISE_CALLEES, large=True)
            code, output, report = data_calls.run(root)
            assert code == 0, output
            cls.roots[name], cls.reports[name] = root, report

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, name, text):
        with patch.dict(os.environ, FFTA_ROM=str(self.roots[name] / "baserom.bin")):
            return evidence.report_matches(text, self.roots[name], ADDRESS)

    def test_a_plain_framed_report_with_a_premise_line_replays(self):
        schemas = {"frame-calls": evidence.FRAMED_LINKED_SCHEMA, "frame-data": evidence.FRAMED_DATA_SCHEMA}
        for name, schema in schemas.items():
            with self.subTest(name=name):
                report = self.reports[name]
                self.assertIn(f"* verification: `{schema}`", report)
                premises = [line for line in report.splitlines() if line.startswith("* callee-saved premise:")]
                self.assertEqual(len(premises), 1)
                self.assertIn("call at 0x08000406 in 0x08000400 through _call_via_r3 to an unknown address, "
                              "with R4,R5 depending on owner stack addresses", premises[0])
                self.assertTrue(self.replays(name, report))
                # The line is held to the walk: dropped, edited or moved, the report does not replay.
                self.assertFalse(self.replays(name, report.replace(premises[0] + "\n", "")))
                self.assertFalse(self.replays(name, report.replace("R4,R5 depending", "R4 depending")))
                rows = report.splitlines()
                at = rows.index(premises[0])
                moved = rows[:at] + rows[at + 1:]
                moved.insert(moved.index("* source plausibility: plausible"), premises[0])
                self.assertFalse(self.replays(name, "\n".join(moved) + "\n"))

if __name__ == "__main__":
    unittest.main()
