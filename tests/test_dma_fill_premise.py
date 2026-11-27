"""Immediate DMA fills whose destination or count is not exact, under a reviewed premise.

The walk tests assemble Thumb bodies with the ARM tools (no ROM); the native tests compile natural C
with the fixed agbcc and `-mthumb-interwork -O2`, run `match.py` on a synthetic tree and replay the
report.
"""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import test_dma_fill as base
import dma_fill_profile as dma
import dma_fill_premise as premise

match = base.match
evidence = base.evidence
BASE = base.BASE
REVIEW = "Every caller passes a VRAM screen block and a size below 0x800 bytes (callers listed)."

# push {r4, r5, lr}; sub sp, #8: entry_SP-0x14 is SP.  The destination (R1) is spilled to sp+4
# (entry_SP-0x10) and reloaded inside the window; the count is half the u16 at R2+6.
TEMPLATE = """push {{r4, r5, lr}}
sub sp, #8
str r1, [sp, #4]
{before}
mov r0, sp
movs r5, #0
strh r5, [r0]
{count}
ldr r4, =0x040000D4
str r0, [r4]
{destination}
str r3, [r4, #4]
{control}
str r2, [r4, #8]
ldr r0, [r4, #8]
{after}
add sp, #8
pop {{r4, r5}}
pop {{r1}}
bx r1
.ltorg"""
DEFAULTS = dict(before="", count="ldrh r2, [r2, #6]", destination="ldr r3, [sp, #4]",
                control="lsrs r2, r2, #1\nmovs r1, #0x81\nlsls r1, r1, #24\norrs r2, r1", after="")


def source(**changes):
    return TEMPLATE.format(**dict(DEFAULTS, **changes))


def entry(rows, review=REVIEW, address=BASE):
    return json.dumps({f"0x{address:08X}": {"review": review, "rows": rows}}).encode()


class DmaFillPremiseWalkTests(unittest.TestCase):
    setUp = base.DmaFillWalkTests.setUp
    body = base.DmaFillWalkTests.body

    def walk(self, text, premises=None):
        data = self.body(text)
        policy = dma.Fills(base.BOOT_ROM, premises)
        match.verify_leaf_instructions(data, BASE, True, base.calls(data), incoming_narrow_reads=True,
                                       dma_fills=policy)
        return policy

    def rows(self, text):
        """The rows the refusal prints, read back from its JSON."""
        with self.assertRaises(ValueError) as raised:
            self.walk(text)
        message = str(raised.exception)
        self.assertIn("need a reviewed entry in config/dma_fill_premises.json that repeats them exactly "
                      "(none found)", message)
        return json.loads(message.split("add:\n", 1)[1])[f"0x{BASE:08X}"]["rows"]

    def refused(self, text, message, premises=None):
        with self.assertRaisesRegex(ValueError, message):
            self.walk(text, premises)

    def test_without_an_entry_the_fill_refuses_with_the_rows_to_review(self):
        with self.assertRaises(ValueError) as raised:
            self.walk(source())
        message = str(raised.exception)
        # the #239 cause stays first, so its existing refusal is still the message's prefix
        self.assertTrue(message.startswith("DMA fill control is not an exact immediate fixed-source enable; "
                                           "DMA fill destination premise: the rows of 0x08000000"), message)
        self.assertIn('"review": "<why every execution of each fill keeps its destination span off the stack>"',
                      message)
        (row,) = self.rows(source())
        self.assertEqual(set(row), set(premise.ROW_KEYS))
        self.assertEqual((row["channel"], row["unit"]), (3, 2))
        # the destination is the value the window's load reads, named by that load's site: no claim that the
        # spilled word still holds entry_R1 (a frame word's content never crosses into a derivation)
        self.assertRegex(row["destination"], r"^u32\[entry_SP-0x10\]@0x080000[0-9A-F]{2}$")
        self.assertRegex(row["control"], r"^\(\(u16\[\(entry_R2 \+ 6\)\]@0x080000[0-9A-F]{2} >> 1\) \| 0x81000000\)$")

    def test_a_reviewed_entry_admits_records_and_states_the_premise(self):
        rows = self.rows(source())
        fills = self.walk(source(), entry(rows))
        (record,) = fills.records
        self.assertEqual((record["region"], record["bytes"], record["destination"], record["control"]),
                         ("premise", None, rows[0]["destination"], rows[0]["control"]))
        self.assertEqual(record["review_sha256"], hashlib.sha256(REVIEW.encode()).hexdigest())
        lines = fills.report_lines()
        self.assertEqual(lines[:1 + len(base.PREMISE_LINES)], [dma.SUMMARY_FIELD + dma.SUMMARY] + base.PREMISE_LINES)
        (stated,) = [line for line in lines if line.startswith(premise.FIELD)]
        self.assertEqual(lines.index(stated), 1 + len(base.PREMISE_LINES))
        self.assertEqual(stated, f"{premise.FIELD}site {rows[0]['site']} DMA3 unit 2 destination "
                                 f"{rows[0]['destination']} control {rows[0]['control']}: {premise.CLAIM}; "
                                 f"unproved runtime premise, accepted by config/dma_fill_premises.json")
        self.assertTrue(lines[-1].startswith(dma.MANIFEST_FIELD))

    def test_the_entry_must_repeat_every_row_exactly(self):
        rows = self.rows(source())
        for key, value in (("site", "0x08000002"), ("channel", 0), ("unit", 4), ("destination", "entry_R1"),
                           ("control", "0x81000001")):
            with self.subTest(key=key):
                changed = [dict(rows[0], **{key: value})]
                self.refused(source(), r"repeats them exactly \(the entry differs\)", entry(changed))
        self.refused(source(), r"\(the entry differs\)", entry(rows + rows))
        self.refused(source(), r"\(none found\)", entry(rows, address=BASE + 0x100))

    def test_a_review_must_be_written(self):
        rows = self.rows(source())
        for review in ("", "   ", "<why every execution of each fill keeps its destination span off the stack>",
                       "scratch: copied", "Todo later"):
            with self.subTest(review=review):
                self.refused(source(), "needs a written review and its rows", entry(rows, review))
        for broken in (b"[]", b'{"0x8000000": {"review": "x", "rows": [{}]}}',
                       b'{"0x08000000": {"review": "x", "rows": [{"site": "0x0"}]}}',
                       b'{"0x08000000": {"review": "x", "rows": [], "extra": 1}}'):
            with self.subTest(broken=broken):
                with self.assertRaises(ValueError):
                    self.walk(source(), broken)

    def test_an_entry_for_exact_fills_refuses(self):
        rows = self.rows(source())
        with self.assertRaisesRegex(ValueError, "lists premises 0x08000000 does not need"):
            self.walk(base.source(), entry(rows))
        # and without fills a file is never read
        fills = self.walk("push {r4, lr}\nmovs r0, #0\npop {r4}\npop {r1}\nbx r1", b"not json")
        self.assertEqual(fills.records, [])

    def test_bits_16_to_31_of_the_control_must_be_known_and_a_fixed_source_enable(self):
        self.refused(source(count="ldr r2, [r2, #4]", control=""), r"bits 16-31 are not known on every path\)$")
        for high, name in ((0x83000000, "repeat"), (0x80000000, "incrementing source"), (0x89000000, "Game Pak DRQ"),
                           (0x91000000, "VBlank start"), (0x01000000, "no enable"),
                           (0x81200000, "decrementing destination"), (0x81010000, "unused bit 16")):
            with self.subTest(name=name):
                control = f"lsrs r2, r2, #1\nldr r1, =0x{high:08X}\norrs r2, r1"
                self.refused(source(control=control), "control is not an exact immediate fixed-source enable$")
        # a count field that may reach bits 16-19 leaves them unknown
        self.refused(source(count="ldr r2, [r2, #4]\nlsls r2, r2, #12\nlsrs r2, r2, #12"),
                     r"bits 16-31 are not known on every path\)$")
        # the unit comes from bit 26
        control = "lsrs r2, r2, #1\nmovs r1, #0x85\nlsls r1, r1, #24\norrs r2, r1"
        (row,) = self.rows(source(control=control))
        self.assertEqual(row["unit"], 4)

    def test_values_need_one_derivation_on_every_path(self):
        joined = "cmp r1, #0\nbeq 1f\nldr r3, [sp, #4]\nb 2f\n1:\nadds r3, r5, #0\n2:"
        # the join is before the window: the destination store follows a join of two derivations
        self.refused(source(before=joined, destination=""), "destination is not an exact unit-aligned address "
                     r"\(it has no defined derivation, so no premise can be stated\)")
        self.refused(source(count="ldrh r2, [r2, r1]"), r"count has no defined derivation")

    def test_a_frame_address_destination_stays_an_escape(self):
        self.refused(source(destination="add r3, sp, #4"), base.ESCAPE)
        # formed before the source store, the core refuses the destination store itself
        self.refused(source(before="add r3, sp, #4", destination=""), base.ESCAPE)

    def test_an_exact_destination_must_start_in_a_region_and_be_aligned(self):
        # only the count is unknown: an exact start on the stack or misaligned is refused, never premised
        (row,) = self.rows(source(destination="ldr r3, =0x06000000"))
        self.assertEqual(row["destination"], "0x06000000")
        self.refused(source(destination="ldr r3, =0x03007000"), base.REGION)
        self.refused(source(destination="ldr r3, =0x06000001"), base.DESTINATION)

    def test_calls_keep_only_r4_to_r11(self):
        # entry_R1 copied to R6 survives the call (the ABI premise); in R1 or R3 it does not
        before = "adds r6, r1, #0\nbl callee"
        (row,) = self.rows(source(before=before, destination="adds r3, r6, #0", count="movs r2, #0x40"))
        self.assertEqual(row["destination"], "entry_R1")
        self.assertEqual(row["control"], "0x81000020")
        self.refused(source(before="adds r3, r1, #0\nbl callee", destination=""), "no defined derivation")

    def test_exact_values_keep_the_239_path(self):
        # an exact control with a premised destination states the constant in the row
        (row,) = self.rows(source(count="", control="ldr r2, =0x81000100"))
        self.assertEqual(row["control"], "0x81000100")
        # and the exact fills of kit #239 record exactly as before, with no premise line
        self.assertEqual(self.walk(base.source()).records, [base.VRAM_RECORD])
        self.assertEqual([line for line in self.walk(base.source()).report_lines() if line.startswith(premise.FIELD)],
                         [])

    def test_the_window_admits_sp_relative_loads_only(self):
        self.refused(source(destination="ldr r3, [r5]"), base.ESCAPE)
        self.refused(source(destination="ldr r3, [sp, #4]\nstr r3, [sp]"), base.ESCAPE)

    def test_a_literal_stack_allocation_keeps_the_frame_load_offsets(self):
        # The frame allocated by the literal pair `ldr r5, =-8; add sp, r5` (which the walk admits) instead of
        # `sub sp, #8`: the destination is still spilled to sp+4, entry_SP-0x10, and the row must name that word.
        literal = TEMPLATE.replace("sub sp, #8", "ldr r5, =0xFFFFFFF8\nadd sp, r5").format(**DEFAULTS)
        (row,) = self.rows(literal)
        self.assertRegex(row["destination"], r"^u32\[entry_SP-0x10\]@0x080000[0-9A-F]{2}$")
        (plain,) = self.rows(source())
        self.assertEqual(row["destination"].split("@")[0], plain["destination"].split("@")[0])

    def test_every_sp_write_is_tracked_exactly_or_refuses(self):
        decoder = base.match.Cs(base.match.CS_ARCH_ARM, base.match.CS_MODE_THUMB)
        decoder.detail = True
        r5 = premise._reg(5)

        def step(code, value):
            (instruction,) = decoder.disasm(code.to_bytes(2, "little"), BASE)
            return premise.step(instruction, (12, {} if value is None else {r5: premise._const(value)}), b"", BASE)
        self.assertEqual(step(0x44AD, 0xFFFFFFF8)[0], 20)          # add sp, r5 with r5 = -8: eight bytes lower
        self.assertEqual(step(0x44AD, 8)[0], 4)
        for code, value, message in ((0x44AD, None, "need an exact constant"),
                                     (0x44AD, 6, "bounded aligned"), (0x44AD, 0x2000, "bounded aligned"),
                                     (0x46AD, 0xFFFFFFF8, "do not model this SP write")):    # mov sp, r5
            with self.subTest(code=hex(code), value=value), self.assertRaisesRegex(ValueError, message):
                step(code, value)


NATIVE = base.HEADER + base.FILL + """
typedef struct { u16 unknown_00[3]; u16 size; } Config;

void func_08000200(void *destination, const Config *config)
{
    fill16(destination, 0x81000000 | (config->size / 2));
    func_08000400();
}
"""


@unittest.skipUnless(base.tools_present(), "fixed compiler and ARM tools required")
class DmaFillPremiseNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", base.ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="dma_fill_premise_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def replays(self, root, report):
        with patch.dict(os.environ, FFTA_ROM=str(Path(root) / "baserom.bin")):
            return evidence.report_matches(report, root, base.A)

    def test_natural_fill_matches_under_its_reviewed_entry_and_replays(self):
        # the leaf clears R0-R3 before it returns, so no stack address comes back to the caller's return
        root = base.build(self.base / "premised", NATIVE, leaf=bytes.fromhex("00200021002200237047"))
        code, output, report = base.run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("DMA fill destination premise: the rows of 0x08000200 need a reviewed entry", output)
        generated, _ = json.JSONDecoder().raw_decode(output.split("add:\n", 1)[1])
        rows = generated["0x08000200"]["rows"]
        (root / premise.PREMISES_PATH).write_bytes(entry(rows, address=base.A))
        code, output, report = base.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        lines = report.splitlines()
        (stated,) = [line for line in lines if line.startswith(premise.FIELD)]
        self.assertIn(f"destination {rows[0]['destination']} control {rows[0]['control']}", stated)
        self.assertTrue(self.replays(root, report))
        code, output = base.check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)
        # replay re-reads the file: an edited review, a removed entry, a changed row or a dropped line refuse
        (root / premise.PREMISES_PATH).write_bytes(entry(rows, REVIEW + " Rechecked.", base.A))
        self.assertFalse(self.replays(root, report))
        (root / premise.PREMISES_PATH).unlink()
        self.assertFalse(self.replays(root, report))
        (root / premise.PREMISES_PATH).write_bytes(entry([dict(rows[0], unit=4)], address=base.A))
        self.assertFalse(self.replays(root, report))
        (root / premise.PREMISES_PATH).write_bytes(entry(rows, address=base.A))
        self.assertTrue(self.replays(root, report))
        self.assertFalse(self.replays(root, report.replace(stated + "\n", "")))
        self.assertFalse(self.replays(root, report.replace(stated, stated.replace("DMA3", "DMA2"))))

    def test_a_premised_fill_beside_an_exact_fill_records_both_and_replays(self):
        # kit #239's natural layout (fill, call, fill), its first fill premised
        text = base.HEADER + base.FILL + """
typedef struct { u16 unknown_00[3]; u16 size; } Config;

void func_08000200(void *destination, const Config *config)
{
    fill16(destination, 0x81000000 | (config->size / 2));
    func_08000400();
    fill16(data_03003860 + 0x100, 0x81000100);
}
"""
        root = base.build(self.base / "mixed", text)
        code, output, report = base.run(root)
        self.assertNotEqual(code, 0, output)
        generated, _ = json.JSONDecoder().raw_decode(output.split("add:\n", 1)[1])
        rows = generated["0x08000200"]["rows"]
        (root / premise.PREMISES_PATH).write_bytes(entry(rows, address=base.A))
        code, output, report = base.run(root)
        self.assertEqual(code, 0, output)
        self.assertIn("verdict MATCH - byte identical", output)
        lines = report.splitlines()
        (stated,) = [line for line in lines if line.startswith(premise.FIELD)]
        self.assertIn(f"destination {rows[0]['destination']} ", stated)
        # the exact fill keeps its #239 record beside the premised one
        (sites,) = [line for line in lines if line.startswith(dma.MANIFEST_FIELD)]
        self.assertEqual([r["region"] for r in json.loads(sites[len(dma.MANIFEST_FIELD) + 1:-1])["sites"]],
                         ["premise", "iwram"])
        self.assertTrue(self.replays(root, report))
        code, output = base.check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)
        self.assertFalse(self.replays(root, report.replace(stated + "\n", "")))
        (root / premise.PREMISES_PATH).write_bytes(entry(rows, REVIEW + " Rechecked.", base.A))
        self.assertFalse(self.replays(root, report))


if __name__ == "__main__":
    unittest.main()
