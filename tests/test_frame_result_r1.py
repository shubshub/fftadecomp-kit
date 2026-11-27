"""R1 holding an own-frame address at a frame-buffer owner's normal returns (frame_result_r1_profile).

The scan and the caller evidence are checked on assembled ROM images; a natural C owner compiled with
the fixed agbcc and `-mthumb-interwork -O2` beside assembled callees (test_data_buffer_calls.build) is
run through match.py and replayed.
"""
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import frame_result_r1_profile as frame_r1
import function_literal_exit_scratch_profile as function_exit
import test_dead_stack_registers as asm
from test_data_buffer_calls import A, STORES, build, run, tools_present, verification
from test_function_literal_exit_scratch import RETURN, bound
from test_dma_fill import check_report

R = match.ARM_REG_R0
F, CALLER, OTHER, NEIGHBOUR = 0x08010000, 0x08011000, 0x08012000, 0x0800FFF0
PUSH_LR, POP_R0, BX_R0, BX_LR = 0xb500, 0xbc01, 0x4700, 0x4770
MOVS_R1_0, READ_R1 = 0x2100, 0x1c08            # movs r1, #0; adds r0, r1, #0


def image(bodies, extra=None, predecessor=True):
    """A ROM with the assembled bodies, mapped, plus raw bytes at addresses that are not mapped.

    Unless a body lies below F (or ``predecessor`` is false), a closed function, ``bx lr`` at F-2, ends at
    F's entry, so nothing falls into it."""
    if predecessor and not any(address < F for address in bodies):
        bodies = {F - 2: [BX_LR], **bodies}
    rom, mapping = asm.build(bodies)
    rom = bytearray(rom)
    for address, raw in (extra or {}).items():
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
    return bytes(rom), mapping


def caller(after):
    return [PUSH_LR, F, *after, POP_R0, BX_R0]


def proved(bodies, extra=None, predecessor=True):
    rom, mapping = image(bodies, extra, predecessor)
    frame_r1._CACHE.clear()
    return frame_r1.evidence(match.BufferCallProof(rom, mapping), F, mapping)


class ScanTests(unittest.TestCase):
    def test_words_calls_and_branches_are_found(self):
        rom, _ = image({F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                       {0x08013000: struct.pack("<I", F | 1), 0x08013006: struct.pack("<I", F),
                        0x08013011: struct.pack("<I", F | 1), 0x08013016: struct.pack("<I", (F | 1) + 0x02000000),
                        0x08013020: struct.pack("<I", F + 0x05000000), 0x08013029: struct.pack("<I", F + 0x01000000),
                        0x08013030: struct.pack("<I", F + 0x06000000), 0x0801303A: struct.pack("<I", (F | 1) + 0x01000000),
                        0x08013040: struct.pack("<I", F + 0x03000000), 0x08013046: struct.pack("<I", (F | 1) + 0x04000000)})
        words, calls, branches, adrs = frame_r1.scan(rom, F)
        # the address at every byte offset; each mirror (0x09-0x0D) at halfword offsets only; 0x0E is not ROM
        self.assertEqual([site for site, _ in words], [0x08013000, 0x08013006, 0x08013011, 0x08013016, 0x08013020,
                                                       0x0801303A, 0x08013040, 0x08013046])
        self.assertEqual(calls, [(CALLER + 2, F)])
        self.assertEqual((branches, adrs), ([], []))
        # b F from 0x0800FFF0 (offset -0x14... forward +0xC) and a beq to it
        rom = bytearray(rom)
        struct.pack_into("<H", rom, NEIGHBOUR - match.ROM_BASE, 0xE000 | ((F - NEIGHBOUR - 4) >> 1))
        struct.pack_into("<H", rom, NEIGHBOUR + 2 - match.ROM_BASE, 0xD000 | ((F - NEIGHBOUR - 6) >> 1))
        self.assertEqual(frame_r1.scan(bytes(rom), F)[2], [(NEIGHBOUR, F), (NEIGHBOUR + 2, F)])

    def test_adrs_and_the_gap_before_the_entry_are_scanned(self):
        rom, _ = image({F: [BX_LR]}, predecessor=False)
        rom = bytearray(rom)
        base = match.ROM_BASE
        # Thumb ADR: add r0, pc, #imm8 * 4 from ((site + 4) & ~3); one names F, one F - 2's word, one is out of
        # reach (it would need imm8 > 255)
        struct.pack_into("<H", rom, F - 0x40 - base, 0xA000 | (F - ((F - 0x40 + 4) & ~3)) // 4)
        struct.pack_into("<H", rom, F - 0x22 - base, 0xA100 | (F - 4 - ((F - 0x22 + 4) & ~3)) // 4)
        struct.pack_into("<H", rom, F - 0x500 - base, 0xA0FF)
        # ARM ADR: add r0, pc, #0x40 at F - 0x48, sub r0, pc, #0x40 at F + 0x38, both naming F; an add with
        # Rn = r1 does not
        struct.pack_into("<I", rom, F - 0x48 - base, 0xE28F0040)
        struct.pack_into("<I", rom, F + 0x38 - base, 0xE24F0040)
        struct.pack_into("<I", rom, F + 0x48 - base, 0xE2810000 | 0x40)
        _, _, _, adrs = frame_r1.scan(bytes(rom), F)
        self.assertEqual(adrs, [(F - 0x48, F), (F - 0x40, F), (F + 0x38, F)])
        # with a gap [F - 4, F): its halfwords are targets too
        _, _, _, adrs = frame_r1.scan(bytes(rom), F, F - 4)
        self.assertEqual(adrs, [(F - 0x48, F), (F - 0x40, F), (F - 0x22, F - 4), (F + 0x38, F)])
        struct.pack_into("<I", rom, 0x08013000 - base, (F - 2) | 1)
        self.assertEqual(frame_r1.scan(bytes(rom), F, F - 4)[0], [(0x08013000, F - 2)])
        self.assertEqual(frame_r1.scan(bytes(rom), F)[0], [])


class EvidenceTests(unittest.TestCase):
    def test_a_caller_that_writes_r1_first_is_the_evidence(self):
        found = proved({F: [BX_LR], CALLER: caller([MOVS_R1_0])})
        self.assertEqual([(row["site"], row["caller"], row["kills"]) for row in found["callers"]],
                         [(CALLER + 2, CALLER, [CALLER + 6])])
        self.assertEqual((found["schema"], found["premise"], found["premise_proved"]),
                         (frame_r1.SCHEMA, frame_r1.PREMISE, False))

    def test_every_gap_in_the_evidence_refuses(self):
        cases = {
            "names the function": ({F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                                   {0x08013000: struct.pack("<I", F | 1)}),
            "0x08013011 names the function": ({F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                                              {0x08013011: struct.pack("<I", F)}),
            "0x08013012 names the function": ({F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                                              {0x08013012: struct.pack("<I", (F | 1) + 0x04000000)}),
            "reaches the function's entry": ({F: [BX_LR], CALLER: caller([MOVS_R1_0]),
                                              F + 0x100: [0xE000 | (((F - (F + 0x100) - 4) >> 1) & 0x7FF), BX_LR]},
                                             None),
            # a conditional branch counts whatever its condition: ble (cond 0xD) at 0x08010080
            "branch at 0x08010080 reaches the function's entry": (
                {F: [BX_LR], CALLER: caller([MOVS_R1_0]), F + 0x80: [0xDD00 | (((F - (F + 0x80) - 4) >> 1) & 0xFF), BX_LR]},
                None),
            "outside every mapped Thumb function": ({F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                                                    {0x08013000: asm.bl(0x08013000, F)}),
            "calls itself": ({F: [PUSH_LR, F, POP_R0, BX_R0]}, None),
            "read before its killing write": ({F: [BX_LR], CALLER: caller([READ_R1])}, None),
            "reaches a call before": ({F: [BX_LR], CALLER: caller([OTHER]), OTHER: [BX_LR]}, None),
            "reaches a return": ({F: [BX_LR], CALLER: caller([])}, None),
            "no direct caller": ({F: [BX_LR]}, None),
            "may fall into its entry": ({F - 4: [0x2000, 0x2000], F: [BX_LR], CALLER: caller([MOVS_R1_0])}, None),
            # an open function, an unmapped gap of 0x0000 (lsls r0, r0, #0) and then the entry
            "0x0800FFFA, may fall into its entry": ({F - 6: [0x2000, 0x2000], F: [BX_LR],
                                                     CALLER: caller([MOVS_R1_0])}, {F - 2: b"\x00\x00"}),
            "BL at 0x08012002 branches into the unreached bytes": (
                {F - 4: [BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0]), OTHER: [PUSH_LR, F - 2, POP_R0, BX_R0]},
                None),
            "word at 0x08013000 names the unreached bytes before it": (
                {F - 4: [BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                {0x08013000: struct.pack("<I", (F - 2) | 1)}),
            "branch at 0x0800FF00 reaches the unreached bytes before it": (
                {F - 0x100: [0xE000 | (((F - 2 - (F - 0x100) - 4) >> 1) & 0x7FF), BX_LR], F - 4: [BX_LR], F: [BX_LR],
                 CALLER: caller([MOVS_R1_0])}, None),
            "ADR at 0x0800FFC2 forms the address of the function": (
                {F - 0x40: [PUSH_LR, 0xA000 | (F - ((F - 0x40 + 2 + 4) & ~3)) // 4, 0x3001, F - 0x20, 0x1c08,
                            0xbc02, 0x4708],
                 F - 0x20: [BX_R0], F - 4: [0x2000, BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])}, None),
            "ADR at 0x0800FFB8 forms the address of the function": (
                {F - 4: [0x2000, BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                {F - 0x48: struct.pack("<I", 0xE28F0040)}),
            "the 78 unreached bytes before its entry exceed 64": (
                {F - 0x50: [BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])}, None),
            # the predecessor ends at the entry, but its bytes after bx lr (movs r0, #0 three times) run on into it
            "BL at 0x08010102 branches into the unreached bytes before it": (
                {F - 8: [BX_LR, 0x2000, 0x2000, 0x2000], F: [BX_LR], CALLER: caller([MOVS_R1_0]),
                 0x08010100: [PUSH_LR, F - 4, READ_R1, POP_R0, BX_R0]}, None),
            "word at 0x08015000 names the unreached bytes before it": (
                {F - 8: [BX_LR, 0x2000, 0x2000, 0x2000], F: [BX_LR], CALLER: caller([MOVS_R1_0])},
                {0x08015000: struct.pack("<I", (F - 4) | 1)}),
            "the 70 unreached bytes before its entry exceed 64": (
                {F - 0x48: [BX_LR] + [0x2000] * 35, F: [BX_LR], CALLER: caller([MOVS_R1_0])}, None),
        }
        for message, (bodies, extra) in cases.items():
            with self.subTest(message), self.assertRaisesRegex(ValueError, message):
                proved(bodies, extra)
        with self.assertRaisesRegex(ValueError, "no mapped function precedes it"):
            proved({F: [BX_LR], CALLER: caller([MOVS_R1_0])}, predecessor=False)

    def test_the_function_before_it_must_be_thumb_code_that_ends_at_or_before_the_entry(self):
        for change, message in ((dict(mode="arm"), "0x0800FFFC, is not Thumb code"),
                                (dict(end=f"0x{F + 2:08X}"), "0x0800FFFC, overlaps its entry")):
            rom, mapping = image({F - 4: [0x2000, BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])})
            entries = json.loads(mapping)
            for entry in entries:
                if int(entry["rom"], 16) == F - 4:
                    entry.update(change)
            mapping = json.dumps(entries)
            frame_r1._CACHE.clear()
            with self.subTest(message), self.assertRaisesRegex(ValueError, message):
                frame_r1.evidence(match.BufferCallProof(rom, mapping), F, mapping)

    def test_a_closed_function_and_an_unnamed_gap_before_the_entry_are_the_evidence(self):
        found = proved({F - 4: [BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])})
        self.assertEqual((found["previous"], found["previous_end"], found["gap_start"], found["gap"]),
                         (F - 4, F - 2, F - 2, 2))
        # the predecessor's own unreached tail after bx lr is scanned the same way
        found = proved({F - 8: [BX_LR, 0x2000, 0x2000, 0x2000], F: [BX_LR], CALLER: caller([MOVS_R1_0])})
        self.assertEqual((found["previous"], found["previous_end"], found["gap_start"], found["gap"]),
                         (F - 8, F, F - 6, 6))

    def test_a_closed_neighbour_does_not_fall_through(self):
        found = proved({F - 4: [0x2000, BX_LR], F: [BX_LR], CALLER: caller([MOVS_R1_0])})
        self.assertEqual((found["previous"], found["previous_end"], found["gap_start"], found["gap"]),
                         (F - 4, F, F, 0))

    def test_the_result_is_cached_per_rom_mapping_and_function(self):
        rom, mapping = image({F: [BX_LR], CALLER: caller([MOVS_R1_0])})
        frame_r1._CACHE.clear()
        proof = match.BufferCallProof(rom, mapping)
        first = frame_r1.evidence(proof, F, mapping)
        with patch.object(frame_r1, "scan", side_effect=AssertionError("rescanned")):
            self.assertEqual(frame_r1.evidence(proof, F, mapping), first)
        rom, mapping = image({F: [BX_LR], CALLER: caller([READ_R1])})
        with self.assertRaisesRegex(ValueError, "read before"):
            frame_r1.evidence(match.BufferCallProof(rom, mapping), F, mapping)
        with patch.object(frame_r1, "scan", side_effect=AssertionError("rescanned")), \
                self.assertRaisesRegex(ValueError, "read before"):
            frame_r1.evidence(match.BufferCallProof(rom, mapping), F, mapping)


def frame():
    proof, data = bound(match.BufferCallProof)
    proof._function_exit_kind = function_exit.FRAME
    proof._frame_r1_sites = {}
    return proof, data


FOUND = dict(schema=frame_r1.SCHEMA, function=A, callers=[dict(site=0x08000502, caller=0x08000500, states=2,
             body_sha256="0" * 64, kills=[0x08000506])], words=0, branches=0, adrs=0, previous=0x080001FE,
             previous_end=A, gap_start=A, gap=0, premise=frame_r1.PREMISE, premise_proved=False)


class HookTests(unittest.TestCase):
    def test_r1_is_dropped_with_r2_r3_on_the_evidence(self):
        proof, data = frame()
        with patch.object(frame_r1, "evidence", return_value=dict(FOUND)):
            held = function_exit.aliases(proof, data, A, RETURN, {R + 1: -20, R + 3: -24})
        self.assertEqual(held, {})
        function_exit.record(proof, A)
        self.assertEqual(proof.frame_result_r1["sites"], [[RETURN, -20]])
        scratch, r1 = function_exit.lines(proof)
        self.assertIn("R0, R1 (but for the frame result r1 line) and every callee return", scratch)
        self.assertTrue(r1.startswith(frame_r1.LINE + f": `{frame_r1.SCHEMA}`"))
        self.assertIn("0x08000502 in 0x08000500 (R1 written at 0x08000506; 2 states)", r1)
        self.assertTrue(r1.endswith(frame_r1.PREMISE))
        payload = function_exit.fingerprint_payload(proof)
        proof.frame_result_r1 = None
        self.assertNotEqual(function_exit.fingerprint_payload(proof), payload)

    def test_r1_alone_binds_the_root(self):
        proof, data = frame()
        proof._function_exit_bound = False
        proof._return_root = None
        bound_root = proof._return_scratch

        def bind(target):
            target._return_root = (A, data, frozenset({RETURN}))
            target._return_scratch, target._return_scratch_joins = bound_root, set()
            target._frame_r1_sites, target._function_exit_bound = {}, True
            return True
        with patch.object(function_exit, "_bind", side_effect=bind) as binding, \
                patch.object(frame_r1, "evidence", return_value=dict(FOUND)):
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, {R + 1: -20}), {})
        binding.assert_called_once()

    def test_everything_else_keeps_the_refusal(self):
        held = {R + 1: -20}
        with patch.object(frame_r1, "evidence", return_value=dict(FOUND)):
            for name, change, value in (("with r0", None, {R + 0: -8, R + 1: -20}),
                                        ("positive offset", None, {R + 1: 4}),
                                        ("not a return", "site", held), ("callee walk", "active", held)):
                with self.subTest(name):
                    proof, data = frame()
                    site = RETURN - 2 if change == "site" else RETURN
                    if change == "active":
                        proof.active.add(0x08000400)
                    self.assertEqual(function_exit.aliases(proof, data, A, site, dict(value)), value)
            proof, data = frame()
            with patch.object(frame_r1.POLICY, "enabled", False):
                self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
            proof, data = bound()                       # the function-literal owner never drops R1
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = frame()
        with patch.object(frame_r1, "evidence", side_effect=ValueError("no direct caller")), \
                self.assertRaisesRegex(ValueError, r"escapes through a return register \(R1: no direct caller\)"):
            function_exit.aliases(proof, data, A, RETURN, dict(held))


def patch_root(root, mapped=(), unmapped=()):
    """Write assembled halfwords into a built tree's ROM: each of ``mapped`` as a mapped Thumb function, each
    of ``unmapped`` as raw bytes."""
    rom = bytearray((root / "baserom.bin").read_bytes())
    entries = json.loads((root / "config/functions.json").read_text())
    for address, halfwords in (*mapped, *unmapped):
        raw = struct.pack(f"<{len(halfwords)}H", *halfwords)
        rom[address - match.ROM_BASE:address - match.ROM_BASE + len(raw)] = raw
    for address, halfwords in mapped:
        entries.append({"rom": f"0x{address:08X}", "end": f"0x{address + 2 * len(halfwords):08X}", "mode": "thumb"})
    (root / "baserom.bin").write_bytes(bytes(rom))
    (root / "config/functions.json").write_text(json.dumps(entries))
    (root / "symbols/functions.txt").write_text("".join(
        f"{int(entry['rom'], 16):08X} {int(entry['end'], 16):08X} "
        f"{int(entry['end'], 16) - int(entry['rom'], 16)} 0 return\n" for entry in entries))
    return root


def bl_tokens(site, target):
    high, low = struct.unpack("<HH", asm.bl(site, target))
    return f".short 0x{high:04X}\n.short 0x{low:04X}\n"


OWNER = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer);
}
"""

# The same beside typed data: the data-buffer proof's plain route.
DATA_OWNER = """typedef unsigned short u16;
extern u16 data_02000000[];
extern void func_08000400(u16 value, u16 *out);
void func_08000200(u16 value)
{
    u16 buffer[4];

    data_02000000[0] = value;
    func_08000400(value, buffer);
}
"""


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class FrameResultR1NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="frame_result_r1_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, name, after, source=OWNER, before=((A - 2, [BX_LR]),), extra=()):
        # func_08000500: push {lr}; bl func_08000200; <after>; pop {r0}; bx r0.  ``before`` maps functions
        # below the owner (a closed bx lr ending at its entry by default); ``extra`` writes unmapped halfwords.
        caller_body = "push {lr}\n" + bl_tokens(0x08000502, A) + after + "pop {r0}\nbx r0"
        root = build(self.base / name, source, [("func_08000400", STORES), ("func_08000500", caller_body)])
        return patch_root(root, before, extra)

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def test_an_owner_whose_caller_writes_r1_matches_and_replays(self):
        root = self.fixture("dead", "movs r1, #0\n")
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.STACK_BUFFER_SCHEMA)
        (line,) = [line for line in report.splitlines() if line.startswith(frame_r1.LINE)]
        self.assertIn("0x08000502 in 0x08000500 (R1 written at 0x08000506;", line)
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        code, output = check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)

    def test_the_typed_data_route_states_and_replays_it(self):
        import data_buffer_profile as data_buffer
        root = self.fixture("data", "movs r1, #0\n", DATA_OWNER)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.SCHEMA)
        (line,) = [line for line in report.splitlines() if line.startswith(frame_r1.LINE)]
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))

    def test_an_open_function_before_an_unmapped_gap_refuses(self):
        # movs r0, #0; movs r0, #0 at 0x080001F8 runs through the 0x0000 halfwords at 0x080001FC into the owner
        root = self.fixture("gap", "movs r1, #0\n", before=((A - 8, [0x2000, 0x2000]),))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("(R1: the function before it, 0x080001F8, may fall into its entry)", output)
        root = self.fixture("gapclosed", "movs r1, #0\n", before=((A - 8, [0x2000, BX_LR]),))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        (line,) = [line for line in report.splitlines() if line.startswith(frame_r1.LINE)]
        self.assertIn("the mapped function before it, 0x080001F8, has a closed control-flow graph and nothing "
                      "names the 4 bytes from 0x080001FC to the entry, which its control-flow graph never reaches",
                      line)

    def test_the_predecessors_tail_after_its_last_transfer_is_scanned(self):
        # bx lr; movs r0, #0 (x3) ends at the owner's entry: its tail runs on into the owner.  Unnamed, it is
        # stated; a BL into it (from unmapped bytes at 0x08000100) refuses.
        before = ((A - 8, [BX_LR, 0x2000, 0x2000, 0x2000]),)
        root = self.fixture("tail", "movs r1, #0\n", before=before)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        (line,) = [line for line in report.splitlines() if line.startswith(frame_r1.LINE)]
        self.assertIn("the mapped function before it, 0x080001F8, has a closed control-flow graph and nothing "
                      "names the 6 bytes from 0x080001FA to the entry", line)
        self.assertTrue(self.replays(report, root))
        bl = list(struct.unpack("<HH", asm.bl(0x08000100, A - 4)))
        root = self.fixture("tailcall", "movs r1, #0\n", before=before, extra=((0x08000100, bl),))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIn("(R1: a BL at 0x08000100 branches into the unreached bytes before it)", output)

    def test_an_adr_naming_the_owner_refuses(self):
        # add r0, pc, #0xFC at 0x08000100 forms 0x08000200
        root = self.fixture("adr", "movs r1, #0\n", extra=((0x08000100, [0xA000 | (A - 0x08000104) // 4]),))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("(R1: the ADR at 0x08000100 forms the address of the function)", output)

    def test_an_owner_whose_caller_reads_r1_refuses(self):
        root = self.fixture("read", "adds r0, r1, #0\n")
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("(R1: caller 0x08000500 after 0x08000502: dead register is read before its killing write)",
                      output)


if __name__ == "__main__":
    unittest.main()
