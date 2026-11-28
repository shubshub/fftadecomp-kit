"""The standing frame premise line (tools/standing_premise.py, `untracked-pointer-frame-v1`).

Every MATCH report whose verified function holds a frame word states the walk's standing premise
for untracked pointers, directly after its verification line; a frameless function's report does
not.  match.py carries the line onto the report its own writer renders and onto the report a
selector writes; report_matches and the re-issuing replays require it and remove it before any
schema replay runs; issued_report_pins, which runs only after --check-report bound the whole text,
reads the report without it.

* HoldsFrameTests: the reachability test on synthetic Thumb and ARM bytes, including every
  conservative case.
* CarryStripTests: round trips and every refusal on synthetic reports over a fixture ROM.
* ReaderTests: the readers that parse saved reports (saved_selectors, issued_report_pins,
  library_units.binding, the palette evidence reader, push.check_reports), the flash re-issue
  replay, and the ROM the check reads.
* EndToEndTests (agbcc): subprocess match.py on a framed and a frameless function, replay,
  --check-report, issued_report_pins and status.py --verify.
* SelectorTests (agbcc): a report an owner selector writes gains the line through
  issue_with_volatile_records, and replays only with it.
"""

import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
KIT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(KIT / "tools"))
import match
import match_evidence as evidence
import standing_premise as standing

BASE = 0x08000000
CALLEE = 0x08000400
ROM_SIZE = 0x1000
MATCH_PY = str(KIT / "tools" / "match.py")
AGBCC = Path(os.path.expandvars(match.DEFAULT_CC)).is_file()


def thumb(*halfwords):
    return b"".join(struct.pack("<H", half) for half in halfwords)


def arm(*words):
    return b"".join(struct.pack("<I", word) for word in words)


def bl(site, target):
    offset = (target - (site + 4)) >> 1
    return (0xF000 | (offset >> 11) & 0x7FF, 0xF800 | offset & 0x7FF)


PUSH_LR, POP_R0, BX_R0, BX_LR = 0xB500, 0xBC01, 0x4700, 0x4770
FRAMED = thumb(PUSH_LR, POP_R0, BX_R0)
FRAMELESS = thumb(0x3001, BX_LR)                     # adds r0, #1; bx lr


def scratch_root(test, prefix):
    scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", KIT / "build"))
    scratch.mkdir(parents=True, exist_ok=True)
    directory = tempfile.TemporaryDirectory(prefix=prefix, dir=scratch)
    test.addCleanup(directory.cleanup)
    return Path(directory.name)


class HoldsFrameTests(unittest.TestCase):
    def frame(self, *halfwords):
        return standing.holds_frame(thumb(*halfwords), BASE, True)

    def test_frameless_leaf(self):
        self.assertFalse(self.frame(0x3001, BX_LR))

    def test_every_sp_write_is_a_frame(self):
        self.assertTrue(self.frame(PUSH_LR, POP_R0, BX_R0))             # push
        self.assertTrue(self.frame(0xB082, 0xB002, BX_LR))              # sub sp, #8; add sp, #8
        self.assertTrue(self.frame(0x449D, BX_LR))                      # add sp, r3 (literal frame)
        self.assertTrue(self.frame(0x4685, BX_LR))                      # mov sp, r0

    def test_frame_reached_only_through_a_conditional_branch(self):
        # cmp r0, #0; beq +6; bx lr; push {lr}; pop {r0}; bx r0
        self.assertTrue(self.frame(0x2800, 0xD000, BX_LR, PUSH_LR, POP_R0, BX_R0))
        # cmp r0, #0; beq (to bx lr); push {lr}; pop {r0}; bx r0; bx lr: the fallthrough holds it
        self.assertTrue(self.frame(0x2800, 0xD002, PUSH_LR, POP_R0, BX_R0, BX_LR))

    def test_frame_reached_only_through_a_branch(self):
        # b +6; bx lr (unreached); pad; push {lr}; pop {r0}; bx r0
        self.assertTrue(self.frame(0xE001, BX_LR, 0x0000, PUSH_LR, POP_R0, BX_R0))

    def test_frame_reached_only_through_a_local_long_branch(self):
        # bl +8 (inside the span); bx lr; pad; push {lr}; pop {r0}; bx r0
        self.assertTrue(self.frame(*bl(BASE, BASE + 8), BX_LR, 0x0000, PUSH_LR, POP_R0, BX_R0))
        # 200 bl 206; 204 bx lr; 206 push {lr}; 208 pop {r0}; 20a bx r0: only the target edge reaches it
        self.assertTrue(self.frame(*bl(BASE, BASE + 6), BX_LR, PUSH_LR, POP_R0, BX_R0))

    def test_a_far_jump_is_followed_on_both_edges(self):
        # bl +0xA (an agbcc far jump inside the span, to bx lr); push {lr}; pop {r0}; bx r0; bx lr.
        # A far jump reaches only its target, so this function never builds the frame on its
        # fall-through; the test follows that edge too, and the answer errs towards stating the line.
        self.assertTrue(self.frame(*bl(BASE, BASE + 0xA), PUSH_LR, POP_R0, BX_R0, BX_LR))
        self.assertFalse(self.frame(*bl(BASE, BASE + 0x6), BX_LR, BX_LR))

    def test_frame_after_an_outside_call(self):
        self.assertTrue(self.frame(*bl(BASE, CALLEE), PUSH_LR, POP_R0, BX_R0))
        self.assertFalse(self.frame(*bl(BASE, CALLEE), BX_LR))

    def test_paths_that_leave_the_function(self):
        self.assertFalse(self.frame(0xE0FE))                            # b out of the span
        self.assertFalse(self.frame(0x4718))                            # bx r3
        self.assertFalse(self.frame(0xDF06, BX_LR))                     # swi 6; bx lr
        self.assertTrue(self.frame(0xDF06, PUSH_LR, POP_R0, BX_R0))     # swi returns to the next one

    def test_conservative_cases(self):
        for name, halfwords in (
                # a frameless return follows, so only the PC write itself makes these conservative
                # (capstone puts neither in its jump group)
                ("computed mov pc", (0x4687, BX_LR)),
                ("computed add pc", (0x4487, BX_LR)),
                ("bx pc", (0x4778, 0x0000, BX_LR)),
                ("undecodable halfword", (0xE800, BX_LR)),
                ("Thumb-2 only encoding", (0xB100, BX_LR)),            # cbz
                ("undefined encoding", (0xDE00, BX_LR)),               # udf
                ("runs off the span", (0x3001,)),
                ("truncated BL at the end", (0x2800, 0xD000, BX_LR, 0xF000)),
                ("branch past the end of a fallthrough", (0x2800, 0xD1FF))):
            with self.subTest(name):
                self.assertTrue(self.frame(*halfwords))
        self.assertTrue(standing.holds_frame(b"", BASE, True))
        self.assertTrue(standing.holds_frame(FRAMELESS, BASE + 1, True))

    def test_arm_mode(self):
        self.assertFalse(standing.holds_frame(arm(0xE2800001, 0xE12FFF1E), BASE, False))
        self.assertTrue(standing.holds_frame(arm(0xE92D4010, 0xE8BD4010, 0xE12FFF1E), BASE, False))
        self.assertTrue(standing.holds_frame(arm(0xE24DD008, 0xE12FFF1E), BASE, False))
        self.assertTrue(standing.holds_frame(arm(0xE1A0F000, 0xE12FFF1E), BASE, False))   # mov pc, r0; bx lr
        self.assertTrue(standing.holds_frame(FRAMELESS, BASE + 2, False))     # misaligned

    def test_the_strict_walk_drops_only_the_end_of_the_bytes(self):
        for name, data, normal, strict in (
                ("no bytes", b"", True, False),
                ("runs off the end", thumb(0x3001), True, False),
                ("an instruction cut short at the end", thumb(0x3001, 0xF000), True, False),
                ("a frame", FRAMED, True, True),
                ("a frameless leaf", FRAMELESS, False, False),
                ("an undecodable halfword inside the bytes", thumb(0xE800, BX_LR), True, True),
                ("a computed PC write", thumb(0x4687, BX_LR), True, True)):
            with self.subTest(name):
                self.assertEqual(standing.holds_frame(data, BASE, True), normal)
                self.assertEqual(standing.holds_frame(data, BASE, True, strict=True), strict)
        self.assertTrue(standing.holds_frame(FRAMELESS, BASE + 1, True, strict=True))     # misaligned

    def test_require_relies_only_where_the_line_is_printed(self):
        # 0xE3A0B500, 0xE12FFF1E: mov fp, #0; bx lr in ARM (no frame); its first halfword is a Thumb push.
        either = arm(0xE3A0B500, 0xE12FFF1E)
        self.assertTrue(standing.holds_frame(either, BASE, True))
        self.assertFalse(standing.holds_frame(either, BASE, False))
        framed_at, leaf_at, arm_at, unmapped_at = BASE, BASE + 0x100, BASE + 0x200, BASE + 0x300
        tail_at, next_at, off_at, unindexed_at = BASE + 0x500, BASE + 0x504, BASE + 0x600, BASE + 0x700
        cut_at, twice_at = BASE + 0x800, BASE + 0x900
        cut = thumb(0x3001, 0xF000)                # adds r0, #1; the first half of a BL, cut by its end
        tail = thumb(0xE000)                       # b +4: to the next function, outside its own span
        off_end = thumb(0x3001, *bl(off_at + 2, CALLEE))    # adds r0, #1; bl out: falls off its end
        fixture = FixtureRoot(self, {framed_at: FRAMED, leaf_at: FRAMELESS, arm_at: either, unmapped_at: either,
                                     tail_at: tail, next_at: FRAMED, off_at: off_end, unindexed_at: FRAMED,
                                     cut_at: cut, twice_at: FRAMED},
                              modes={arm_at: "arm"})
        root = fixture.path
        rows = json.loads((root / "config/functions.json").read_text())
        fixture.write_mapping([row for row in rows if int(row["rom"], 16) != unmapped_at])
        spans = {int(row["rom"], 16): int(row["end"], 16) - int(row["rom"], 16) for row in rows}
        del spans[unindexed_at]
        fixture.write_index(spans)
        index = root / "symbols/functions.txt"             # a second row for twice_at: no single span
        index.write_text(index.read_text() + f"{twice_at:08X} {twice_at + 8:08X} 8 1 return\n")
        overlong = (root / "baserom.bin").read_bytes()[tail_at - BASE:next_at - BASE + len(FRAMED)]
        self.assertTrue(standing.holds_frame(overlong, tail_at, True, strict=True))   # reaches next's push
        accepted = [("framed", FRAMED, framed_at),
                    ("no unique mode: the line is printed whatever the bytes", either, unmapped_at),
                    ("no unique mode, a prefix", either[:2], unmapped_at)]
        refused = [("frameless", FRAMELESS, leaf_at),
                   ("a prefix of a frameless function, which runs off its own end", FRAMELESS[:2], leaf_at),
                   ("a prefix of a framed function", FRAMED[:2], framed_at),
                   ("bytes past the function, reached by its branch out", overlong, tail_at),
                   ("the whole of that frameless function", tail, tail_at),
                   ("mapped ARM, framed only as Thumb", either, arm_at),
                   ("framed only by running off its end (printed, but not proved)", off_end, off_at),
                   ("framed only by an instruction cut short at its end", cut, cut_at),
                   ("mapped but not indexed", FRAMED, unindexed_at),
                   ("indexed twice", FRAMED, twice_at),
                   ("not the ROM's bytes", FRAMED, leaf_at),
                   ("below the ROM", FRAMED, BASE - 4)]
        for name, data, address in accepted:
            with self.subTest(name):
                standing.require(data, root, address)
        for name, data, address in refused:
            with self.subTest(name), self.assertRaises(ValueError):
                standing.require(data, root, address)
        # it relies on the premise only where the function's report prints the line
        for name, data, address in accepted:
            with self.subTest(printed=name):
                self.assertIn(standing.LINE, standing.carry(report_text(data, address), root, address))


def report_text(body, address=BASE, schema="elf-symbol-thumb-calls-v1"):
    """A minimal MATCH report: the fields the premise check reads, in match.py's writer order."""
    return (f"# match report - 0x{address:08X}\n\n* source: `src/{address:08X}.c`\n"
            f"* verification: `{schema}`\n* source SHA-256: `{'0' * 64}`\n"
            f"* compiler: `agbcc`\n* ROM bytes: `{body.hex()}` ({len(body)} bytes)\n"
            f"* compiled : `{body.hex()}`\n* source plausibility: plausible\n"
            f"* hand-asm allow list: not listed\n\n**MATCH - byte identical** - {len(body)}/{len(body)} bytes\n")


class FixtureRoot:
    """A root whose ROM holds `functions` ({address: bytes}) and whose mapping lists them."""

    def __init__(self, test, functions, modes=None):
        self.path = scratch_root(test, "standing_premise_")
        (self.path / "config").mkdir()
        (self.path / "symbols").mkdir()
        rom = bytearray(ROM_SIZE)
        for address, body in functions.items():
            rom[address - BASE:address - BASE + len(body)] = body
        (self.path / "baserom.bin").write_bytes(bytes(rom))
        modes = modes or {}
        self.write_mapping([{"rom": f"0x{address:08X}", "end": f"0x{address + len(body):08X}",
                             "mode": modes.get(address, "thumb")} for address, body in functions.items()])
        self.write_index({address: len(body) for address, body in functions.items()})
        test.enterContext(mock.patch.dict(os.environ, {"FFTA_ROM": str(self.path / "baserom.bin")}))

    def write_mapping(self, rows):
        (self.path / "config/functions.json").write_text(json.dumps(rows))

    def write_index(self, spans):
        """symbols/functions.txt rows (address end size), as the index lists them."""
        (self.path / "symbols/functions.txt").write_text("".join(
            f"{address:08X} {address + size:08X} {size} 1 return\n" for address, size in sorted(spans.items())))


class CarryStripTests(unittest.TestCase):
    FRAMELESS_AT = BASE + 0x100

    def setUp(self):
        self.root = FixtureRoot(self, {BASE: FRAMED, self.FRAMELESS_AT: FRAMELESS}).path
        self.framed = report_text(FRAMED)
        self.frameless = report_text(FRAMELESS, self.FRAMELESS_AT, "elf-symbol-cfg-leaf-v2")

    def carried(self):
        return standing.carry(self.framed, self.root, BASE)

    def test_round_trips(self):
        carried = self.carried()
        lines = carried.split("\n")
        self.assertEqual(lines[lines.index("* verification: `elf-symbol-thumb-calls-v1`") + 1], standing.LINE)
        self.assertEqual(carried.count(standing.LINE), 1)
        self.assertEqual(standing.strip(carried, self.root, BASE), self.framed)
        self.assertEqual(standing.carry(self.frameless, self.root, self.FRAMELESS_AT), self.frameless)
        self.assertEqual(standing.strip(self.frameless, self.root, self.FRAMELESS_AT), self.frameless)
        self.assertEqual(standing.without(carried), self.framed)
        self.assertEqual(standing.without(self.frameless), self.frameless)

    def test_line_text(self):
        # The exact text every framed report carries.  Its second clause leaves room for what a report's
        # own lines already state: the stack arguments a callee is passed, which it may write, and the
        # writes a summary line or a premise line (an escape premise, a call-via premise) allows.
        self.assertEqual(standing.LINE, (
            "* frame premise: `untracked-pointer-frame-v1`; unproved premise: no pointer the walk does not derive "
            "from SP (an incoming argument, a word read from memory, a result of code the walk does not inspect, "
            "or an absolute address) addresses stack that this function or a callee the walk inspects has "
            "allocated, except an escaped address used only as an escape premise of this report states; and no "
            "code the walk does not inspect (a callee, the BIOS, DMA or an interrupt handler) writes that stack "
            "other than the stack arguments it is passed, except as a summary or premise line of this report "
            "states"))

    def refused(self, report, address=BASE):
        with self.assertRaises(ValueError):
            standing.strip(report, self.root, address)

    def test_refusals(self):
        carried = self.carried()
        lines = carried.split("\n")
        at = lines.index(standing.LINE)
        verdict = next(index for index, line in enumerate(lines) if line.startswith("**MATCH"))
        moved = lines[:at] + lines[at + 1:]
        moved.insert(moved.index("* compiled : `" + FRAMED.hex() + "`"), standing.LINE)
        for name, text in (
                ("missing", self.framed),
                ("duplicated", "\n".join(lines[:at + 1] + [standing.LINE] + lines[at + 1:])),
                ("duplicated after the fields", "\n".join(lines[:verdict] + [standing.LINE] + lines[verdict:])),
                ("misplaced", "\n".join(moved)),
                ("edited", carried.replace("unproved premise", "proved premise", 1)),
                ("indented", carried.replace(standing.LINE, "  " + standing.LINE, 1)),
                ("trailing text", carried.replace(standing.LINE, standing.LINE + " (checked)", 1)),
                ("another marker beside it", carried.replace(
                    "* compiler:", "- frame premise: proved\n* compiler:", 1)),
                ("ROM bytes differ", carried.replace(FRAMED.hex(), "01b5" + FRAMED.hex()[4:], 1)),
                ("ROM bytes count differs", carried.replace(f"({len(FRAMED)} bytes)", f"({len(FRAMED) + 2} bytes)", 1)),
                ("two ROM bytes lines", carried.replace("* compiled :", f"* ROM bytes: `{FRAMED.hex()}` "
                                                        f"({len(FRAMED)} bytes)\n* compiled :", 1)),
                ("no ROM bytes line", "\n".join(line for line in lines if not line.startswith("* ROM bytes"))),
                ("two verification lines", carried.replace("* compiler:", "* verification: `x`\n* compiler:", 1)),
                ("no verification line", carried.replace("* verification: ", "* verified: ", 1))):
            with self.subTest(name):
                self.refused(text)
        frameless = self.frameless.split("\n")
        frameless.insert(frameless.index("* verification: `elf-symbol-cfg-leaf-v2`") + 1, standing.LINE)
        with self.subTest("frameless with the line"):
            self.refused("\n".join(frameless), self.FRAMELESS_AT)

    def test_carry_refusals(self):
        with self.assertRaisesRegex(ValueError, "already carries"):
            standing.carry(self.carried(), self.root, BASE)
        with self.assertRaisesRegex(ValueError, "already carries"):
            standing.carry(self.frameless.replace("* compiler:", "* frame premise: x\n* compiler:"), self.root,
                           self.FRAMELESS_AT)
        with self.assertRaisesRegex(ValueError, "ROM bytes differ"):
            standing.carry(report_text(FRAMELESS), self.root, BASE)
        with self.assertRaisesRegex(ValueError, "verification line"):
            standing.carry(self.framed.replace("* verification: ", "* verified: "), self.root, BASE)

    def test_mode_comes_from_the_mapping(self):
        mapping = FixtureRoot(self, {BASE: FRAMELESS})
        self.assertFalse(standing.applies(FRAMELESS, mapping.path, BASE))
        for name, rows in (("no entry", []), ("two entries", [{"rom": "0x08000000", "mode": "thumb"}] * 2),
                           ("no mode", [{"rom": "0x08000000"}]), ("unknown mode", [{"rom": "0x08000000",
                                                                                  "mode": "thumb2"}])):
            with self.subTest(name):
                mapping.write_mapping(rows)
                self.assertTrue(standing.applies(FRAMELESS, mapping.path, BASE))
        (mapping.path / "config/functions.json").unlink()
        self.assertTrue(standing.applies(FRAMELESS, mapping.path, BASE))
        body = arm(0xE12FFF1E)                         # bx lr: frameless as ARM, Thumb-2 as Thumb
        self.assertTrue(standing.holds_frame(body, BASE, True))
        arm_root = FixtureRoot(self, {BASE: body}, modes={BASE: "arm"})
        self.assertFalse(standing.applies(body, arm_root.path, BASE))
        self.assertEqual(standing.carry(report_text(body), arm_root.path, BASE), report_text(body))


class ReaderTests(unittest.TestCase):
    def setUp(self):
        self.root = FixtureRoot(self, {BASE: FRAMED}).path
        self.report = standing.carry(report_text(FRAMED), self.root, BASE)

    def test_saved_selectors_parse_the_report_without_the_line(self):
        self.assertIn(standing.LINE, self.report)
        self.assertEqual(vars(evidence.saved_selectors(self.report)),
                         vars(evidence.saved_selectors(report_text(FRAMED))))
        # Its parsers never see the line, whatever words they look for.
        import unsigned_divmod_profile
        with mock.patch.object(unsigned_divmod_profile, "selector_for_report",
                               wraps=unsigned_divmod_profile.selector_for_report) as parser:
            evidence.saved_selectors(self.report)
        self.assertNotIn(standing.LINE, parser.call_args.args[0])

    def test_report_matches_and_pins_check_the_line_first(self):
        stripped = []
        with mock.patch.object(evidence, "_report_matches", lambda report, root, address: stripped.append(report)
                               or True):
            self.assertTrue(evidence.report_matches(self.report, self.root, BASE))
            self.assertFalse(evidence.report_matches(report_text(FRAMED), self.root, BASE))
        self.assertEqual(stripped, [report_text(FRAMED)])
        # The pins run only once --check-report has bound the whole saved text, line included, to
        # this compile: they read the report without the line and check nothing about it.
        seen = []
        with mock.patch.object(evidence, "address_pins", lambda report, root, address, records: seen.append(report)
                               or True):
            self.assertTrue(evidence.issued_report_pins(self.report, self.root, BASE))
        self.assertEqual(seen, [report_text(FRAMED)])

    def test_the_rom_is_the_one_every_replay_reads(self):
        other = self.root / "other.bin"
        other.write_bytes(bytes(ROM_SIZE))
        with mock.patch.object(evidence, "report_rom_path", return_value=str(other)):
            with self.assertRaisesRegex(ValueError, "ROM bytes differ"):
                standing.strip(self.report, self.root, BASE)
            with self.assertRaisesRegex(ValueError, "ROM bytes differ"):
                standing.carry(report_text(FRAMED), self.root, BASE)
            self.assertFalse(evidence.report_matches(self.report, self.root, BASE))
        with mock.patch.object(evidence, "report_rom_path", side_effect=ValueError("no ROM")):
            self.assertFalse(evidence.report_matches(self.report, self.root, BASE))

    def test_library_unit_binding_ignores_the_line(self):
        import library_units
        unit = (f"{library_units.UNIT_LINE}`row`\n{library_units.TOOLCHAIN_LINE}`tool`\n"
                f"{library_units.COMPILER_LINE}`{'1' * 64}`\n")
        plain = report_text(FRAMED).replace("* compiler:", unit + "* compiler:", 1)
        self.assertEqual(library_units.binding(standing.carry(plain, self.root, BASE)), library_units.binding(plain))

    def test_palette_evidence_reader_ignores_the_line(self):
        import palette_source_admission_profile as palette
        report = report_text(FRAMED, schema=palette.SCHEMA).replace(
            "* compiler:", f"* palette source: `{palette.SELECTOR}`\n"
                           f"* palette source evidence: `{palette.text({'a': 1})}`\n* compiler:", 1)
        self.assertEqual(palette.saved_evidence(report), {"a": 1})
        self.assertEqual(palette.saved_evidence(standing.carry(report, self.root, BASE)), {"a": 1})

    def test_push_report_check_accepts_the_line(self):
        import push
        (self.root / "src").mkdir()
        (self.root / "src/08000000.c").write_text("")
        (self.root / "docs/match").mkdir(parents=True)
        (self.root / "docs/match/08000000.md").write_text(self.report)
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertTrue(push.check_reports(str(self.root)))

    def test_flash_reissue_compares_the_reissued_report_without_its_line(self):
        import flash_sector_erase as erase
        owner = BASE
        root = FixtureRoot(self, {owner: FRAMED}).path
        for name in ("config/data_symbols.json", "config/library_units.json", "symbols/functions.txt",
                     "src/08000000.c"):
            (root / name).parent.mkdir(parents=True, exist_ok=True)
            (root / name).write_text("{}\n" if name.endswith(".json") else "\n")
        saved = report_text(FRAMED, schema="elf-symbol-thumb-flash-sector-reader-v1")
        issued = {"text": standing.carry(saved, root, owner)}

        def reissue(command, cwd, env, **_):
            Path(cwd, f"docs/match/{owner:08X}.md").write_text(issued["text"])
            return subprocess.CompletedProcess(command, 0, b"", b"")
        with mock.patch.object(erase.subprocess, "run", reissue), \
                mock.patch.object(evidence, "source_paths", lambda r, a: [Path(r) / "src/08000000.c"]):
            replay = lambda: erase.replay_member(saved, root, owner, owner, "elf-symbol-thumb-flash-sector-reader-v1")
            self.assertTrue(replay())
            issued["text"] = saved                       # a reissue without the line it must carry
            self.assertFalse(replay())
            issued["text"] = standing.carry(saved, root, owner).replace("unproved", "proved")
            self.assertFalse(replay())


class SubprocessRoot:
    """A decomp root with one function at `address`, compiled from `source` with agbcc."""

    def __init__(self, test, source, address=BASE, callee=CALLEE):
        self.test, self.address = test, address
        self.path = scratch_root(test, "standing_e2e_")
        for name in ("src", "include", "config", "symbols", "docs/match", "build"):
            (self.path / name).mkdir(parents=True)
        self.name = f"src/{address:08X}.c"
        (self.path / self.name).write_text(source)
        (self.path / "config/data_symbols.json").write_text("{}\n")
        environment = {key: value for key, value in os.environ.items() if key != "FFTA_ROM"}
        environment.update(TMPDIR=str(self.path / "build"), PYTHONDONTWRITEBYTECODE="1")
        test.enterContext(mock.patch.dict(os.environ, environment, clear=True))
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=self.path, timeout=120)
        rom = bytearray(ROM_SIZE + (address - BASE))
        struct.pack_into("<H", rom, callee - BASE, BX_LR)
        with runner.workspace() as workspace:
            object_data, text_data, original = match.compile_object(
                runner, workspace, args, self.path, address, self.name)
            symbol, _ = match.function_record(original, f"func_{address:08X}", address, True)
            entries = [(address, symbol["size"]), (callee, 2)]
            self.mapping = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{start + size:08X}", "mode": "thumb"}
                                       for start, size in entries]).encode()
            (self.path / "config/functions.json").write_bytes(self.mapping)
            (self.path / "symbols/functions.txt").write_text(
                "".join(f"{start:08X} {start + size:08X} {size} 1 return\n" for start, size in entries))
            if original["relocations"]:
                self.body, _, _ = match.link_calls(runner, workspace, args, original, address, self.mapping,
                                                   len(rom), bytes(rom), b"{}\n", {}, {}, allow_self_call=True)
            else:
                self.body = match.function_bytes(object_data, text_data, f"func_{address:08X}", address, True)
        rom[address - BASE:address - BASE + len(self.body)] = self.body
        (self.path / "baserom.bin").write_bytes(bytes(rom))
        self.report_path = self.path / f"docs/match/{address:08X}.md"

    def match(self, *arguments):
        return subprocess.run([sys.executable, MATCH_PY, "--root", str(self.path), f"0x{self.address:08X}",
                               *arguments], capture_output=True, text=True, timeout=600)


@unittest.skipUnless(AGBCC, "agbcc required")
class EndToEndTests(unittest.TestCase):
    FRAMED_CALL = "void func_08000400(int);\nvoid func_08000000(int a, int b, int c, int d, int e) { func_08000400(e); }\n"
    PUSH_ONLY = "void func_08000400(void);\nvoid func_08000000(void) { func_08000400(); }\n"
    LEAF = "int func_08000000(int a) { return a * 3 + 1; }\n"

    def issue(self, source):
        root = SubprocessRoot(self, source)
        run = root.match()
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("verdict MATCH - byte identical", run.stdout)
        return root, root.report_path.read_text()

    def check_report(self, root):
        run = root.match("--check-report")
        return run.returncode, run.stdout

    def verified(self, root):
        import status
        with contextlib.redirect_stdout(io.StringIO()):
            _, matched, _, _, problems, _, _ = status.collect(str(root.path), True)
        return matched, problems

    def test_framed_reports_carry_the_line(self):
        for source, schema in ((self.FRAMED_CALL, evidence.FRAMED_LINKED_SCHEMA),
                               (self.PUSH_ONLY, evidence.LINKED_SCHEMA)):
            with self.subTest(schema):
                root, report = self.issue(source)
                lines = report.split("\n")
                self.assertEqual(lines[3], f"* verification: `{schema}`")
                self.assertEqual(lines[4], standing.LINE)
                self.assertEqual(report.count(standing.LINE), 1)
                self.assertTrue(evidence.report_matches(report, root.path, BASE))
                self.assertTrue(evidence.issued_report_pins(report, root.path, BASE))
                self.assertEqual(self.check_report(root)[0], 0)
                self.assertEqual(self.verified(root), (1, []))
                stripped = standing.strip(report, root.path, BASE)
                for name, text in (("missing", stripped),
                                   ("duplicated", report.replace(standing.LINE, standing.LINE + "\n" + standing.LINE)),
                                   ("misplaced", stripped.replace("* compiler:", standing.LINE + "\n* compiler:", 1)),
                                   ("edited", report.replace("unproved", "proved", 1))):
                    # The replay refuses the text; so do --check-report and status --verify, whose
                    # whole-text comparison is what binds the line before the pins read the report.
                    with self.subTest(schema=schema, tamper=name):
                        self.assertFalse(evidence.report_matches(text, root.path, BASE))
                        root.report_path.write_text(text)
                        status, output = self.check_report(root)
                        self.assertNotEqual(status, 0)
                        self.assertIn("report  DIFFERS from the saved", output)
                        matched, problems = self.verified(root)
                        self.assertEqual(matched, 0)
                        self.assertTrue(problems)

    def test_frameless_report_has_no_line(self):
        root, report = self.issue(self.LEAF)
        self.assertIn(f"* verification: `{evidence.SCHEMA}`", report)
        self.assertNotIn("frame premise", report)
        self.assertTrue(evidence.report_matches(report, root.path, BASE))
        self.assertEqual(self.check_report(root)[0], 0)
        self.assertEqual(self.verified(root), (1, []))
        forged = report.replace(f"* verification: `{evidence.SCHEMA}`\n",
                                f"* verification: `{evidence.SCHEMA}`\n{standing.LINE}\n", 1)
        self.assertFalse(evidence.report_matches(forged, root.path, BASE))
        root.report_path.write_text(forged)
        status, output = self.check_report(root)
        self.assertNotEqual(status, 0)
        self.assertIn("report  DIFFERS from the saved", output)
        matched, problems = self.verified(root)
        self.assertEqual(matched, 0)
        self.assertTrue(problems)


SELECTOR_SOURCE = '''unsigned int func_08010000(unsigned int choose, unsigned int value)
{
    unsigned int samples[2];
    unsigned int *selected;
    samples[0] = value;
    samples[1] = value + 1;
    if (choose)
        selected = samples;
    else
        selected = samples + 1;
    *selected += 3;
    return samples[0] + samples[1];
}
'''


@unittest.skipUnless(AGBCC, "agbcc required")
class SelectorTests(unittest.TestCase):
    A = 0x08010000

    def setUp(self):
        import owner_admission_profile as owner
        self.owner = owner
        self.root = scratch_root(self, "standing_selector_")
        self.enterContext(mock.patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"), "PYTHONDONTWRITEBYTECODE": "1"}))
        for name in ("src", "include", "compile", "config", "symbols", "build", "docs/match"):
            (self.root / name).mkdir(parents=True, exist_ok=True)
        (self.root / "src/08010000.c").write_text(SELECTOR_SOURCE)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        raw, text, image = match.compile_object(runner, str(self.root / "compile"), args, self.root, self.A,
                                                "src/08010000.c")
        self.data = match.function_bytes(raw, text, "func_08010000", self.A, True)
        instructions = match.verify_leaf_instructions(self.data, self.A, True, acyclic_state_budget=4096)
        rows = [{"rom": f"0x{self.A:08X}", "end": f"0x{self.A + len(self.data):08X}", "mode": "thumb",
                 "instrs": len(instructions)}]
        (self.root / "config/functions.json").write_text(json.dumps(rows) + "\n")
        (self.root / "symbols/functions.txt").write_text(
            f"{self.A:08X} {self.A + len(self.data):08X} {len(self.data)} {len(instructions)} return\n")
        (self.root / "config/data_symbols.json").write_text("{}\n")
        (self.root / "baserom.bin").write_bytes(bytes(self.A - BASE) + self.data)
        self.report_path = self.root / "docs/match/08010000.md"

    def issue(self, *extra):
        return subprocess.run([sys.executable, MATCH_PY, "--root", str(self.root), f"{self.A:08X}",
                               "--owner-runtime-profile", self.owner.ACYCLIC_SELECTOR, *extra],
                              capture_output=True, text=True, timeout=600)

    def test_selector_report_carries_the_line(self):
        run = self.issue()
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        report = self.report_path.read_text()
        lines = report.split("\n")
        at = lines.index(f"* verification: `{self.owner.ACYCLIC_SCHEMA}`")
        self.assertEqual(lines[at + 1], standing.LINE)
        self.assertEqual(report.count(standing.LINE), 1)
        self.assertTrue(evidence.report_matches(report, self.root, self.A))
        stripped = standing.strip(report, self.root, self.A)
        # the selector's own writer renders the report without the line; replay compares with that
        self.assertEqual(self.owner.render(self.A, self.owner.build(self.root, self.A,
                                                                    selector=self.owner.ACYCLIC_SELECTOR)), stripped)
        self.assertFalse(evidence.report_matches(stripped, self.root, self.A))
        self.assertFalse(evidence.report_matches(report.replace(standing.LINE, standing.LINE + "\n" + standing.LINE),
                                                 self.root, self.A))
        import rebuild
        self.assertEqual(rebuild.saved_profile_arguments(report, self.root, self.A),
                         ["--owner-runtime-profile", self.owner.ACYCLIC_SELECTOR])
        import status
        with contextlib.redirect_stdout(io.StringIO()):
            totals = status.collect(str(self.root), True, quiet=True)
        self.assertEqual((totals[1], totals[4]), (1, []))
        self.report_path.write_text(stripped)
        with contextlib.redirect_stdout(io.StringIO()):
            totals = status.collect(str(self.root), True, quiet=True)
        self.assertEqual(totals[1], 0)
        # --no-write and --check-report leave the saved report alone
        self.report_path.write_text(report)
        self.assertEqual(self.issue("--no-write").returncode, 0)
        self.assertEqual(self.report_path.read_text(), report)

    def test_selector_carry_failure_removes_the_report(self):
        self.report_path.write_text(report_text(self.data, self.A).replace("* verification: ", "* verified: "))
        args = argparse.Namespace(no_write=False)
        with self.assertRaises(SystemExit) as raised:
            match.carry_standing_premise(self.root, self.report_path, self.A, args, 0, None)
        self.assertIn("standing frame premise not carried", str(raised.exception))
        self.assertFalse(self.report_path.exists())
        self.report_path.write_text(report_text(self.data, self.A).replace(
            "**MATCH - byte identical**", "**NOT MATCHING - bytes differ**"))
        with self.assertRaises(SystemExit):
            match.carry_standing_premise(self.root, self.report_path, self.A, args, 0, None)
        self.assertFalse(self.report_path.exists())
        self.report_path.write_text(report_text(self.data, self.A))
        match.carry_standing_premise(self.root, self.report_path, self.A, args, 0, None)
        self.assertEqual(self.report_path.read_text(), standing.carry(report_text(self.data, self.A), self.root, self.A))
        self.assertIn(standing.LINE, self.report_path.read_text())
        # a selector that wrote nothing (or failed) leaves nothing to carry
        self.report_path.unlink()
        match.carry_standing_premise(self.root, self.report_path, self.A, args, 0, None)
        self.assertFalse(self.report_path.exists())
        self.report_path.write_text("partial\n")
        match.carry_standing_premise(self.root, self.report_path, self.A, args, 1, None)
        match.carry_standing_premise(self.root, self.report_path, self.A, argparse.Namespace(no_write=True), 0, None)
        self.assertEqual(self.report_path.read_text(), "partial\n")


if __name__ == "__main__":
    unittest.main()
