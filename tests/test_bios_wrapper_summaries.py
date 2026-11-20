"""GBA BIOS SWI wrapper summaries in the plain bounded-buffer walk (#192).

Fixtures are assembled Thumb owners with the eight wrappers at their exact
ROM addresses; no game ROM is needed.
"""
import ast
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import bios_wrapper_summary_profile as bios

BASE = match.ROM_BASE
CALLEE = BASE + 0x100
WRAPPERS = {
    0x08141860: "ArcTan2", 0x08141864: "BgAffineSet", 0x08141868: "CpuFastSet",
    0x0814186C: "CpuSet", 0x08141870: "Div", 0x08141874: "DivRem",
    0x0814187C: "DivArmRem", 0x08141898: "Sqrt",
}
BODIES = {
    "ArcTan2": "svc #0x0a\nbx lr", "BgAffineSet": "svc #0x0e\nbx lr",
    "CpuFastSet": "svc #0x0c\nbx lr", "CpuSet": "svc #0x0b\nbx lr",
    "Div": "svc #6\nbx lr", "DivRem": "svc #6\nadds r0, r1, #0\nbx lr",
    "DivArmRem": "svc #7\nadds r0, r1, #0\nbx lr", "Sqrt": "svc #8\nbx lr",
}
EPILOGUE = "add sp, #{frame}\npop {{r4, r5, r6}}\npop {{r1}}\nbx r1"
# The three premises, pinned verbatim: every report that applies a summary states them.
GBATEK_PREMISE = ("* buffer BIOS premise: GBATEK (BIOS Functions): each routine returns to its wrapper, "
                  "preserves SP, and reads and writes caller memory only through the spans its documented "
                  "arguments describe (so the caller frame at or above SP only through those spans)")
OUTPUTS_PREMISE = ("* buffer BIOS premise: no routine leaves an address of the caller frame in any register "
                   "except, for a memory routine, R0 or R1 when that register carried one in; GBATEK "
                   "documents no output register of the memory routines, so this is trusted, not proved")
TRUSTED_PREMISE = ("* buffer BIOS premise: R4-R11 are preserved across each summarised call; nothing of the "
                   "routine is inspected, so this is trusted, not proved")
PREMISE_LINES = [GBATEK_PREMISE, OUTPUTS_PREMISE, TRUSTED_PREMISE]


def owner(body, frame=8, after="movs r0, #0"):
    """push, a local frame, the body, a kill of R0/R1, and a balanced return."""
    return (f"push {{r4, r5, r6, lr}}\nsub sp, #{frame}\nadds r4, r0, #0\nadds r5, r1, #0\n"
            f"{body}\n{after}\n" + EPILOGUE.format(frame=frame))


def fill(control="movs r2, #1\nlsls r2, r2, #24\nadds r2, #16", source="mov r0, sp",
         target="CpuSet", after="movs r0, #0", frame=8, before=""):
    """The 0800DAB8 shape: a local fill value, an external destination in R5."""
    return owner(f"{before}\n{source}\nmovs r1, #0\nstrh r1, [r0]\nadds r1, r5, #0\n{control}\n"
                 f"bl {target}", frame=frame, after=after)


class BiosWrapperSummaryTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="bios_wrappers_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {"FFTA_ROM": str(self.root / "baserom.bin")})
        environment.start()
        self.addCleanup(environment.stop)

    def build(self, caller, callee="bx lr", bodies=None, rows=None):
        bodies = dict(BODIES, **(bodies or {}))
        labels = [label for name in ("caller", "callee", *WRAPPERS.values()) for label in (name, name + "_end")]
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global " + ", ".join(labels) + "\n"
                f"caller:\n{caller}\n.align 2\n.ltorg\ncaller_end:\n.org 0x100\ncallee:\n{callee}\ncallee_end:\n")
        for address, name in sorted(WRAPPERS.items()):
            text += f".org 0x{address - BASE:x}\n{name}:\n{bodies[name]}\n{name}_end:\n"
        assembly = self.root / "fixture.s"
        assembly.write_text(text)
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(assembly), "-o", str(self.root / "f.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "f.o"),
             "-o", str(self.root / "f.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "f.elf"), str(self.root / "baserom.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        names = ("caller", "callee", *WRAPPERS.values())
        entries = rows if rows is not None else [
            {"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
            for name in names]
        self.rom = (self.root / "baserom.bin").read_bytes()
        self.mapping = json.dumps(entries).encode()
        self.body = self.rom[:symbols["caller_end"] - BASE]
        return symbols

    def walk(self, caller, callee="bx lr", *, stack_arguments=False, bios_wrappers=True, **options):
        self.build(caller, callee, **options)
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=stack_arguments,
                                      loop_replay=True, bios_wrappers=bios_wrappers)
        match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof,
                                       call_resolver=proof.target, incoming_narrow_reads=True)
        return proof

    def refused(self, pattern, caller, callee="bx lr", **options):
        with self.assertRaisesRegex(ValueError, pattern):
            self.walk(caller, callee, **options)

    def memory(self, proof):
        return proof.bios_summaries.manifest()["memory_sites"]

    # Admitted shapes -----------------------------------------------------------

    def test_cpuset_fill_from_a_local_halfword_records_its_site(self):
        proof = self.walk(fill())
        (site,) = self.memory(proof)
        self.assertEqual((site["routine"], site["source"], site["destination"], site["unit"],
                          site["count"], site["killed"]), ("CpuSet", [-24, 2], None, 2, None, [0]))
        self.assertEqual(site["control"], [0x01000010, 0xFFFFFFFF ^ 0x01000010])
        self.assertEqual(proof.dependencies, {0x0814186C: bytes.fromhex("0bdf7047")})
        summary, gbatek, outputs, trusted, manifest = proof.bios_summary_lines()
        self.assertTrue(summary.startswith("* buffer BIOS summaries: `gba-bios-swi-wrapper-summaries-v1` "))
        self.assertIn("spans from r2 bits proved over the owner CFG, with known bits in r4-r11 surviving calls "
                      "under the conditional ordinary returning ABI", summary)
        self.assertEqual([gbatek, outputs, trusted], PREMISE_LINES)
        self.assertEqual(proof.bios_summaries.manifest()["premises"],
                         [line.split(": ", 1)[1] for line in PREMISE_LINES])
        self.assertTrue(manifest.startswith("* buffer BIOS manifest: `"))
        self.assertEqual(json.loads(manifest.split("`")[1])["memory_sites"], [site])
        self.assertEqual(json.loads(manifest.split("`")[1])["wrappers"], [[0x0814186C, "CpuSet", 0x0B, "0bdf7047"]])
        self.assertEqual(proof.bios_summaries.manifest()["schema"], "gba-bios-swi-wrapper-summaries-v1")

    def test_unknown_width_needs_a_whole_aligned_word(self):
        unknown = "movs r3, #1\nlsls r3, r3, #24\nadds r2, r6, #0\norrs r2, r3"
        (site,) = self.memory(self.walk(fill(unknown)))
        self.assertEqual((site["source"], site["unit"]), ([-24, 4], 4))
        self.refused(r"buffer access is unaligned", fill(unknown, source="mov r0, sp\nadds r0, #2"))
        # Bit 26 known clear: a halfword unit at SP+2 is admitted.
        clear = fill(source="mov r0, sp\nadds r0, #2")
        self.assertEqual(self.memory(self.walk(clear))[0]["source"], [-22, 2])

    def test_zero_extended_byte_control_is_proved(self):
        control = "ldrb r2, [r4]\nmovs r3, #1\nlsls r3, r3, #24\norrs r2, r3"
        (site,) = self.memory(self.walk(fill(control)))
        self.assertEqual((site["unit"], site["control"][1] & (1 << 26)), (2, 1 << 26))
        proof = self.walk(fill(control))
        self.assertEqual(proof.bios_summaries.manifest()["bit_rules"], bios.cpuset.ZERO_EXTENSION_RULES)
        self.assertEqual(json.loads(proof.bios_summary_lines()[-1].split("`")[1])["bit_rules"],
                         bios.cpuset.ZERO_EXTENSION_RULES)

    def test_cpufastset_fill_source_is_one_word(self):
        (site,) = self.memory(self.walk(fill("ldr r2, =0x01001000", target="CpuFastSet")))
        self.assertEqual((site["routine"], site["source"], site["unit"]), ("CpuFastSet", [-24, 4], 4))

    def test_copy_into_and_out_of_a_local_area(self):
        # The 0812AAC8 shape: 10 halfwords into a 20-byte local, then back out.
        body = ("adds r0, r4, #0\nmov r1, sp\nmovs r2, #10\nbl CpuSet\n"
                "mov r0, sp\nadds r1, r5, #0\nmovs r2, #10\nbl CpuSet")
        sites = self.memory(self.walk(owner(body, frame=20)))
        self.assertEqual(sorted(((s["source"], s["destination"], s["count"], s["killed"]) for s in sites), key=repr),
                         [(None, [-36, 20], 10, [1]), ([-36, 20], None, 10, [0])])
        words = "adds r0, r4, #0\nmov r1, sp\nmovs r2, #1\nlsls r2, r2, #26\nadds r2, #5\nbl CpuSet\nmovs r1, #0"
        (site,) = self.memory(self.walk(owner(words, frame=20)))
        self.assertEqual((site["destination"], site["unit"]), ([-36, 20], 4))

    def test_cpufastset_local_destination_needs_blocks_of_eight(self):
        body = "adds r0, r4, #0\nmov r1, sp\nmovs r2, #{}\nbl CpuFastSet\nmovs r1, #0"
        (site,) = self.memory(self.walk(owner(body.format(8), frame=32)))
        self.assertEqual(site["destination"], [-48, 32])
        self.refused(r"not a multiple of eight", owner(body.format(4), frame=32))
        self.refused(r"outside allocated local words", owner(body.format(16), frame=32))
        # Bit 26 is CpuSet's width bit; in a CpuFastSet control it is reserved.
        wide = body.format(1).replace("movs r2, #1", "movs r2, #1\nlsls r2, r2, #26\nadds r2, #8")
        self.refused(r"BIOS control word sets a reserved bit", owner(wide, frame=32))

    def test_bgaffineset_external_source_local_destination(self):
        body = "adds r0, r4, #0\nmov r1, sp\nmovs r2, #1\nbl BgAffineSet\nmovs r1, #0"
        (site,) = self.memory(self.walk(owner(body, frame=16)))
        self.assertEqual((site["routine"], site["source"], site["destination"], site["count"]),
                         ("BgAffineSet", None, [-32, 16], 1))
        local = "mov r0, sp\nadd r1, sp, #20\nmovs r2, #1\nbl BgAffineSet\nmovs r1, #0"
        (site,) = self.memory(self.walk(owner(local, frame=36)))
        self.assertEqual((site["source"], site["destination"], site["killed"]), ([-52, 20], [-32, 16], [0, 1]))

    def test_register_alias_killed_through_a_branch_and_pop(self):
        # The 0801A320 shape: the branch reaches an epilogue whose POP writes R0.
        body = fill(after="b done\ndone:", frame=8)
        body = body.replace("pop {r4, r5, r6}\npop {r1}\nbx r1", "pop {r4, r5, r6}\npop {r0}\nbx r0")
        self.assertEqual(self.memory(self.walk(body))[0]["killed"], [0])

    def test_scalar_wrappers_with_pointer_words_in_a_walked_callee(self):
        # The 081227F8 shape: &local in the outgoing area makes the callee walked;
        # the callee calls each scalar wrapper with scalars only.
        caller = ("push {r4, lr}\nsub sp, #12\nadd r0, sp, #8\nstr r0, [sp]\nmovs r0, #1\n"
                  "bl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0")
        callee = ("push {r4, lr}\nmovs r0, #4\nbl Sqrt\nmovs r1, #3\nbl Div\nmovs r1, #3\n"
                  "bl DivRem\nmovs r1, #3\nbl DivArmRem\nmovs r1, #3\nbl ArcTan2\npop {r4}\npop {r1}\nbx r1")
        proof = self.walk(caller, callee, stack_arguments=True)
        scalar = proof.bios_summaries.manifest()["scalar_sites"]
        self.assertEqual(sorted(site["routine"] for site in scalar),
                         ["ArcTan2", "Div", "Div remainder", "DivArm remainder", "Sqrt"])
        self.assertTrue(all(site["depth"] == 1 and site["untouched_incoming_slots"] == [[8, -12]] and
                            site["pointer_words"] == [-20] for site in scalar))
        self.assertIn(CALLEE, proof.dependencies)
        # Uninspected: R4-R11 survival across each wrapper is trusted, as for any uninspected call.
        self.assertEqual(proof.callee_trusted[CALLEE],
                         frozenset({0x08141898, 0x08141870, 0x08141874, 0x0814187C, 0x08141860}))
        self.assertFalse({0x08141898, 0x08141870} & proof.callee_clobbers.keys())

    def test_scalar_wrapper_at_the_owner_call_with_a_pointer_word(self):
        caller = ("push {r4, lr}\nsub sp, #12\nadd r0, sp, #8\nstr r0, [sp]\nmovs r0, #9\n"
                  "bl Sqrt\nadd sp, #12\npop {r4}\npop {r1}\nbx r1")
        proof = self.walk(caller, stack_arguments=True)
        (site,) = proof.bios_summaries.manifest()["scalar_sites"]
        self.assertEqual((site["depth"], site["untouched_incoming_slots"]), (0, [[0, -12]]))
        self.assertNotIn("bit_rules", json.loads(proof.bios_summary_lines()[-1].split("`")[1]))
        self.assertEqual(proof.bios_summary_lines()[1:4], PREMISE_LINES)

    def test_a_wrapper_without_a_live_pointer_stays_an_ordinary_call(self):
        caller = "push {r4, lr}\nmovs r0, #9\nbl Sqrt\nbl CpuSet\npop {r4}\npop {r1}\nbx r1"
        proof = self.walk(caller)
        self.assertFalse(proof.bios_summaries.observed())
        self.assertEqual((proof.dependencies, proof.bios_summary_lines()), ({}, []))

    def test_fingerprints_without_a_summary_are_unchanged(self):
        caller = owner("mov r0, sp\nbl callee", frame=8)
        callee = "movs r1, #0\nstrh r1, [r0]\nmovs r0, #0\nbx lr"
        plain = self.walk(caller, callee, bios_wrappers=False)
        summarised = self.walk(caller, callee)
        self.assertEqual(plain.fingerprint(), summarised.fingerprint())
        self.assertEqual(summarised.bios_summary_lines(), [])
        honest = self.walk(fill())
        fingerprint = honest.fingerprint()
        honest.bios_summaries.memory.clear()
        self.assertNotEqual(fingerprint, honest.fingerprint())

    # Refused shapes ------------------------------------------------------------

    def test_without_the_opt_in_the_wrapper_is_walked_and_refused(self):
        self.refused(r"buffer callee 0x0814186C: non-leaf calls and interrupts require linked CFG",
                     fill(), bios_wrappers=False)

    def test_wrapper_bytes_and_rows_must_be_exact(self):
        for body in ("svc #0x0c\nbx lr", "svc #0x0b\nbx r0", "movs r0, #0\nbx lr", "svc #0x0b\nbx r1"):
            with self.subTest(body=body):
                self.refused(r"buffer callee 0x0814186C: BIOS CpuSet summary requires the exact indexed "
                             r"wrapper bytes", fill(), bodies={"CpuSet": body})
        self.refused(r"Div remainder summary requires the exact", owner(
            "add r0, sp, #4\nstr r0, [sp]\nmovs r0, #9\nbl DivRem", frame=8),
            bodies={"DivRem": "svc #6\nbx lr\nmov r8, r8"}, stack_arguments=True)
        symbols = self.build(fill())
        rows = [{"rom": f"0x{symbols[n]:08X}", "end": f"0x{symbols[n + '_end']:08X}", "mode": "thumb"}
                for n in ("caller", "callee", *WRAPPERS.values())]
        overlapping = rows + [{"rom": "0x0814186E", "end": "0x08141870", "mode": "thumb"}]
        self.refused(r"overlaps another span", fill(), rows=overlapping)
        missing = [row for row in rows if row["rom"] != "0x0814186C"]
        self.refused(r"not unique aligned Thumb ROM code", fill(), rows=missing)

    def test_an_interior_address_is_not_a_wrapper(self):
        self.refused(r"^buffer call target is not unique aligned Thumb ROM code$",
                     fill().replace("bl CpuSet", "bl CpuSet + 2"))

    def test_scalar_wrappers_refuse_register_pointers(self):
        for register in ("r0", "r1", "r2", "r3"):
            with self.subTest(register=register):
                self.refused(r"buffer callee 0x08141898: scalar BIOS wrapper refuses a tracked local "
                             r"pointer in R0-R3, R12 or LR", owner(f"mov {register}, sp\nbl Sqrt", frame=8,
                                                                   after="movs r0, #0\nmovs r1, #0\nmovs r2, #0\nmovs r3, #0"))
        self.refused(r"scalar BIOS wrapper refuses", owner("mov r12, sp\nmovs r0, #1\nbl ArcTan2", frame=8))

    def test_memory_wrappers_refuse_pointers_outside_r0_r1(self):
        for register in ("r2", "r3", "r12"):
            with self.subTest(register=register):
                self.refused(r"BIOS memory wrapper refuses a local pointer outside R0 and R1",
                             fill(before=f"mov {register}, sp" if register != "r2" else "",
                                  control="mov r2, sp" if register == "r2" else
                                  "movs r2, #1\nlsls r2, r2, #24\nadds r2, #16"))

    def test_memory_wrappers_are_summarised_only_at_the_owner_call(self):
        caller = owner("mov r0, sp\nbl callee", frame=8)
        callee = ("push {r4, lr}\nmovs r1, #0\nstrh r1, [r0]\nmovs r2, #1\nlsls r2, r2, #24\n"
                  "bl CpuSet\nmovs r0, #0\npop {r4}\npop {r1}\nbx r1")
        self.refused(r"buffer callee 0x08000100: buffer callee 0x0814186C: BIOS memory wrapper is "
                     r"summarised only at the owner's own call", caller, callee)

    def test_unproved_or_invalid_controls_refuse(self):
        unknown = "adds r2, r6, #0"
        self.refused(r"copy source or local destination requires the whole control word", fill(unknown))
        no_fill = "movs r2, #16"
        self.assertEqual(self.memory(self.walk(fill(no_fill, frame=32)))[0]["source"], [-48, 32])
        self.refused(r"outside allocated local words", fill(no_fill, frame=8))
        destination = "adds r0, r4, #0\nmov r1, sp\n{}\nbl CpuSet\nmovs r1, #0"
        for control, pattern in (("adds r2, r6, #0", "requires the whole control word"),
                                 ("movs r2, #0", "count is zero"),
                                 ("movs r2, #1\nlsls r2, r2, #25\nadds r2, #4", "reserved bit"),
                                 ("movs r2, #1\nlsls r2, r2, #31\nadds r2, #4", "reserved bit"),
                                 ("movs r2, #12", "outside allocated local words"),
                                 # Count bits 16-20 are count, not reserved bits.
                                 ("movs r2, #1\nlsls r2, r2, #20\nadds r2, #4", "outside allocated local words")):
            with self.subTest(control=control):
                self.refused(pattern, owner(destination.format(control), frame=20))

    def test_fill_into_a_local_destination_bounds_both_spans(self):
        # A local fill value and a local destination: one source unit, count units written.
        body = ("mov r0, sp\nmovs r1, #0\nstrh r1, [r0]\nadd r1, sp, #4\nmovs r2, #1\nlsls r2, r2, #24\n"
                "adds r2, #{}\nbl CpuSet\nmovs r1, #0")
        (site,) = self.memory(self.walk(owner(body.format(4), frame=12)))
        self.assertEqual((site["source"], site["destination"], site["count"], site["killed"]),
                         ([-28, 2], [-24, 8], 4, [0, 1]))
        self.refused(r"outside allocated local words", owner(body.format(6), frame=12))
        unknown = body.format(4).replace("adds r2, #4", "orrs r2, r6")
        self.refused(r"requires the whole control word", owner(unknown, frame=12))

    def test_bgaffineset_count_and_alignment(self):
        body = "adds r0, r4, #0\nmov r1, sp\n{}\nbl BgAffineSet\nmovs r1, #0"
        for control, frame, pattern in (("adds r2, r6, #0", 16, "count is not a proven constant"),
                                        ("ldrb r2, [r4]\nmovs r3, #1\norrs r2, r3", 16,
                                         "count is not a proven constant"),
                                        ("movs r2, #0", 16, "count is not a proven constant"),
                                        ("movs r2, #2", 16, "outside allocated local words"),
                                        ("movs r2, #1\nlsls r2, r2, #8", 16, "count is not a proven constant")):
            with self.subTest(control=control):
                self.refused(pattern, owner(body.format(control), frame=frame))
        self.refused(r"unaligned", owner(body.format("movs r2, #1").replace("mov r1, sp", "add r1, sp, #2"),
                                         frame=20).replace("add r1, sp, #2", "mov r1, sp\nadds r1, #2"))

    def test_spans_refuse_pointer_words_return_words_and_overlap(self):
        # Destination over a pointer-bearing word.
        over_pointer = ("add r0, sp, #16\nstr r0, [sp, #4]\nadds r0, r4, #0\nmov r1, sp\nmovs r2, #4\n"
                        "bl CpuSet\nmovs r1, #0")
        self.refused(r"destination span overlaps a pointer-bearing local word",
                     owner(over_pointer, frame=20), stack_arguments=True)
        # A fill source that is a pointer-bearing word.
        source = ("add r0, sp, #8\nstr r0, [sp]\nmov r0, sp\nadds r1, r5, #0\nmovs r2, #1\n"
                  "lsls r2, r2, #24\nbl CpuSet")
        self.refused(r"source span overlaps a pointer-bearing local word", owner(source, frame=12),
                     stack_arguments=True)
        # Destination over a word that carries the return address.
        returned = ("mov r0, lr\nstr r0, [sp]\nadds r0, r4, #0\nmov r1, sp\nmovs r2, #2\nbl CpuSet\nmovs r1, #0")
        self.refused(r"return-carrying local word", owner(returned, frame=8))
        later = returned.replace("str r0, [sp]", "str r0, [sp, #4]").replace("movs r2, #2", "movs r2, #4")
        self.refused(r"return-carrying local word", owner(later, frame=8))
        self.assertEqual(self.memory(self.walk(owner(later.replace("movs r2, #4", "movs r2, #2"), frame=8)))[0]
                         ["destination"], [-24, 4])
        # Source and destination overlap.
        overlap = "mov r0, sp\nadd r1, sp, #4\nmovs r2, #4\nbl CpuSet\nmovs r1, #0"
        self.refused(r"source and destination overlap", owner(overlap, frame=16))

    def test_alias_registers_must_be_killed_before_use(self):
        for after in ("adds r4, r0, #0\nmovs r0, #0", "bl callee\nmovs r0, #0", "push {r0}\npop {r0}\nmovs r0, #0",
                      "cmp r0, #0\nmovs r0, #0"):
            with self.subTest(after=after):
                self.refused(r"R0 carried a local pointer into BIOS CpuSet and is not written before any "
                             r"read, call or return", fill(after=after))
        returning = fill(after="").replace("pop {r1}\nbx r1", "pop {r1}\nbx r1")
        self.refused(r"R0 carried a local pointer", returning)
        conditional = fill(after="cmp r4, #0\nbeq skip\nmovs r0, #0\nskip:")
        self.refused(r"R0 carried a local pointer", conditional)
        destination = "adds r0, r4, #0\nmov r1, sp\nmovs r2, #4\nbl CpuSet\n{}"
        self.refused(r"R1 carried a local pointer", owner(destination.format("adds r6, r1, #0\nmovs r1, #0"), frame=8))
        self.refused(r"R1 carried a local pointer", owner(destination.format("bl callee\nmovs r1, #0"), frame=8))

    def test_joined_controls_are_intersected(self):
        # R2 is proved over the owner CFG with joins intersected, not read off one path.
        fill_or_copy = ("mov r0, sp\nmovs r1, #0\nstrh r1, [r0]\nadds r1, r5, #0\ncmp r4, #0\nbeq copy\n"
                        "movs r2, #1\nlsls r2, r2, #24\nadds r2, #4\nb call\ncopy:\nmovs r2, #4\ncall:\nbl CpuSet")
        self.refused(r"requires the whole control word", owner(fill_or_copy, frame=8))
        two_fills = fill_or_copy.replace("copy:\nmovs r2, #4", "copy:\nmovs r2, #1\nlsls r2, r2, #24\nadds r2, #8")
        (site,) = self.memory(self.walk(owner(two_fills, frame=8)))
        self.assertEqual((site["source"], site["unit"], site["control"][0]), ([-24, 2], 2, 1 << 24))
        two_counts = ("adds r0, r4, #0\nmov r1, sp\ncmp r5, #0\nbeq two\nmovs r2, #4\nb call\n"
                      "two:\nmovs r2, #2\ncall:\nbl CpuSet\nmovs r1, #0")
        self.refused(r"requires the whole control word", owner(two_counts, frame=8))

    def test_local_copy_sources_need_the_destination_rules(self):
        # A local copy source with an external destination gets the same control rules
        # as a local destination: CpuFastSet blocks of eight, reserved bits, BgAffineSet count.
        fast = "mov r0, sp\nadds r1, r5, #0\nmovs r2, #{}\nbl CpuFastSet"
        self.refused(r"not a multiple of eight", owner(fast.format(4), frame=32))
        self.assertEqual(self.memory(self.walk(owner(fast.format(8), frame=32)))[0]["source"], [-48, 32])
        reserved = "mov r0, sp\nadds r1, r5, #0\nmovs r2, #1\nlsls r2, r2, #25\nadds r2, #2\nbl CpuSet"
        self.refused(r"reserved bit", owner(reserved, frame=8))
        affine = "mov r0, sp\nadds r1, r5, #0\n{}\nbl BgAffineSet"
        for control in ("adds r2, r6, #0", "movs r2, #0"):
            with self.subTest(control=control):
                self.refused(r"count is not a proven constant", owner(affine.format(control), frame=20))
        self.assertEqual(self.memory(self.walk(owner(affine.format("movs r2, #1"), frame=20)))[0]["source"],
                         [-36, 20])

    def test_both_local_with_the_source_above_the_destination(self):
        body = "add r0, sp, #8\nmov r1, sp\nmovs r2, #4\nbl CpuSet\nmovs r1, #0"
        (site,) = self.memory(self.walk(owner(body, frame=16)))
        self.assertEqual((site["source"], site["destination"], site["killed"]), ([-24, 8], [-32, 8], [0, 1]))
        self.refused(r"source and destination overlap", owner(body.replace("add r0, sp, #8", "add r0, sp, #4"),
                                                                frame=16))

    def test_scalar_wrapper_in_a_callee_refuses_a_pointer_argument(self):
        caller = ("push {r4, lr}\nsub sp, #12\nadd r0, sp, #8\nstr r0, [sp]\nmovs r0, #1\n"
                  "bl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0")
        callee = "push {r4, lr}\nldr r0, [sp, #8]\nbl Sqrt\npop {r4}\npop {r1}\nbx r1"
        self.refused(r"buffer callee 0x08000100: buffer callee 0x08141898: scalar BIOS wrapper refuses",
                     caller, callee, stack_arguments=True)

    def test_spans_reaching_pointer_words_past_their_first_unit(self):
        # A 3-word copy source whose last word is a pointer word; a halfword destination
        # in the upper half of one.
        source = ("add r0, sp, #0\nstr r0, [sp, #12]\nadd r0, sp, #4\nadds r1, r5, #0\n"
                  "movs r2, #1\nlsls r2, r2, #26\nadds r2, #{}\nbl CpuSet")
        self.refused(r"source span overlaps a pointer-bearing local word", owner(source.format(3), frame=16),
                     stack_arguments=True)
        self.assertEqual(self.memory(self.walk(owner(source.format(2), frame=16), stack_arguments=True))[0]
                         ["source"], [-28, 8])
        half = ("add r0, sp, #8\nstr r0, [sp, #4]\nadds r0, r4, #0\nadd r1, sp, #4\nadds r1, #2\nmovs r2, #1\n"
                "bl CpuSet\nmovs r1, #0")
        self.refused(r"destination span overlaps a pointer-bearing local word", owner(half, frame=12),
                     stack_arguments=True)

    def test_a_killed_alias_in_a_loop_back_to_the_call(self):
        body = ("movs r6, #3\nloop:\nmov r0, sp\nmovs r1, #0\nstrh r1, [r0]\nadds r1, r5, #0\n"
                "movs r2, #1\nlsls r2, r2, #24\nadds r2, #4\nbl CpuSet\nsubs r6, #1\nbne loop")
        self.assertEqual(self.memory(self.walk(owner(body, frame=8)))[0]["killed"], [0])
        self.refused(r"R0 carried a local pointer",
                     owner(body.replace("loop:\nmov r0, sp", "loop:\nadds r3, r0, #0\nmov r0, sp"), frame=8))

    def test_memory_call_with_only_external_pointers_and_a_live_pointer_word(self):
        caller = ("push {r4, lr}\nsub sp, #8\nadd r3, sp, #4\nstr r3, [sp]\nmovs r3, #0\nmovs r2, #4\n"
                  "bl CpuSet\nadd sp, #8\npop {r4}\npop {r1}\nbx r1")
        (site,) = self.memory(self.walk(caller, stack_arguments=True))
        self.assertEqual((site["source"], site["destination"], site["killed"], site["pointer_words"]),
                         (None, None, [], [-16]))
        self.assertEqual(site["control"], [4, 0xFFFFFFFB])

    def test_a_pending_site_must_be_its_direct_call(self):
        self.build(fill())
        proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True, bios_wrappers=True)
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        instructions = {item.address: item for item in decoder.disasm(self.body[:16], BASE)}
        edges = {address: (address + item.size,) if address + item.size in instructions else ()
                 for address, item in instructions.items()}
        proof.bios_summaries.pending[(BASE + 4, 0x0814186C, None, None, (), ())] = None
        with self.assertRaisesRegex(ValueError, "BIOS CpuSet site is not its direct BL in the owner CFG"):
            proof.bios_summaries.finish(self.body, BASE, instructions, edges)
        # The owner's real CpuSet BL, recorded against another wrapper.
        proof = self.walk(fill())
        ((key, record),) = proof.bios_summaries.memory.items()
        decoded = {item.address: item for item in decoder.disasm(self.body, BASE)}
        site = record["site"]
        self.assertEqual(decoded[site].operands[0].imm, 0x0814186C)
        proof.bios_summaries.pending[(site, 0x08141868, -24, None, (), ())] = None
        with self.assertRaisesRegex(ValueError, "BIOS CpuFastSet site is not its direct BL in the owner CFG"):
            proof.bios_summaries.finish(self.body, BASE, {BASE: decoded[BASE], site: decoded[site]},
                                        {BASE: (site,), site: ()})

    def test_pending_memory_sites_must_be_discharged(self):
        self.build(fill())
        proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True, bios_wrappers=True)
        stack = [(False, False, True)] * 2
        proof.check_arguments(0x0814186C, {match.ARM_REG_R0: -8}, stack, {}, frozenset(), site=BASE + 0x20)
        with self.assertRaisesRegex(ValueError, "not discharged"):
            proof.fingerprint()
        with self.assertRaisesRegex(ValueError, "not discharged"):
            proof.bios_summary_lines()
        # Another function's CFG does not discharge it.
        proof.bios_summaries.finish(self.body, BASE, {}, {})
        self.assertTrue(proof.bios_summaries.pending)

    def test_aborted_loop_replay_records_are_restored(self):
        self.build(fill(), "movs r0, #0\nbx lr")
        proof = match.BufferCallProof(self.rom, self.mapping, loop_replay=True, bios_wrappers=True)
        state = proof.bios_summaries.copy()
        proof.check_arguments(0x08141898, {}, [(False, False, True)] * 2, {4: -8}, frozenset({-8}),
                              site=BASE + 0x30)
        self.assertTrue(proof.bios_summaries.scalar)
        proof.bios_summaries.restore(state)
        self.assertFalse(proof.bios_summaries.observed())
        calls = []
        original = match.BufferCallProof._check_arguments

        def aborted(self, address, *args, replay, **context):
            calls.append(replay)
            if not replay:
                self.bios_summaries.scalar["stale"] = {}
                raise match._LoopReplayRequired()
            return original(self, address, *args, replay=replay, **context)
        # A record made before the aborted pass survives it; the aborted pass's record does not.
        proof.check_arguments(0x08141898, {}, [(False, False, True)] * 2, {4: -8}, frozenset({-8}),
                              site=BASE + 0x30)
        before = dict(proof.bios_summaries.scalar)
        self.assertEqual(len(before), 1)
        with patch.object(match.BufferCallProof, "_check_arguments", aborted):
            proof.check_arguments(CALLEE, {match.ARM_REG_R0: -8}, [(False, False, True)] * 2, {},
                                  frozenset(), site=BASE + 0x40)
        self.assertEqual(calls, [False, True])
        self.assertEqual(proof.bios_summaries.scalar, before)

    def test_context_and_construction_guards(self):
        self.build(fill())
        for options in (dict(bios_wrappers=1), dict(bios_wrappers=True, stack_arguments=True,
                                                    discarded_exit_scratch={})):
            with self.subTest(options=options), self.assertRaises(ValueError):
                match.BufferCallProof(self.rom, self.mapping, **options)
        with self.assertRaisesRegex(ValueError, "require the plain buffer proof"):
            match.FunctionBufferCallProof(self.rom, self.mapping, bios_wrappers=True)
        import local_long_branch_profile as scratch
        policy = dict(schema=scratch.DISCARDED_SCRATCH_SCHEMA, registers=[2, 3])
        match.BufferCallProof(self.rom, self.mapping, discarded_exit_scratch=policy)
        with self.assertRaisesRegex(ValueError, "require the plain buffer proof"):
            match.BufferCallProof(self.rom, self.mapping, discarded_exit_scratch=policy, bios_wrappers=True)
        import bios_cpuset_fill_profile as fill_profile
        # A fill proof the base constructor accepts (its owner graph is not needed here).
        fill_proof = object.__new__(fill_profile.BiosFillProof)
        fill_proof.rom, fill_proof.mapping = self.rom, self.mapping
        match.BufferCallProof(self.rom, self.mapping, bios_fill_proof=fill_proof)
        with self.assertRaisesRegex(ValueError, "require the plain buffer proof"):
            match.BufferCallProof(self.rom, self.mapping, bios_fill_proof=fill_proof, bios_wrappers=True)
        proof = match.BufferCallProof(self.rom, self.mapping, bios_wrappers=True)
        stack = [(False, False, True)] * 2
        for context, pattern in ((dict(site=None), "actual direct call site"),
                                 (dict(site=BASE, words={-8: ("constant", 1)}), "exclude word-provenance"),
                                 (dict(site=BASE, watched=(match.ARM_REG_R0 + 4,)), "exclude word-provenance"),
                                 (dict(site=BASE, frame_base=-8), "exclude word-provenance")):
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, pattern):
                proof.check_arguments(0x08141898, {}, stack, {4: -8}, frozenset({-8}), **context)
        with self.assertRaisesRegex(ValueError, "link register"):
            proof.check_arguments(0x08141898, {match.ARM_REG_LR: -8}, stack, {}, frozenset(), site=BASE)
        with self.assertRaisesRegex(ValueError, "unaligned or outside"):
            proof.check_arguments(0x08141898, {}, stack, {4: -12}, frozenset({-8}), site=BASE)
        for attribute in ("word_provenance", "callee_frames", "single_word_stores", "forwarded_stack_arguments"):
            with self.subTest(attribute=attribute), patch.object(proof, attribute, True), \
                    self.assertRaisesRegex(ValueError, "exclude word-provenance"):
                proof.check_arguments(0x08141898, {}, stack, {4: -8}, frozenset({-8}), site=BASE)
        # Only the calls the walk would inspect are summarised.
        self.assertEqual(proof.check_arguments(0x08141898, {}, stack, {}, frozenset(), site=BASE), {})
        self.assertFalse(proof.bios_summaries.observed())

    # Evidence ------------------------------------------------------------------

    def report(self, proof, *extra, lines=None, fingerprint=None):
        summary = evidence.STACK_BUFFER_SUMMARY if proof.stack_arguments else evidence.BUFFER_SUMMARY
        return [f"* compiled : `{self.body.hex()}`", f"* buffer calls: {summary}",
                f"* buffer proof SHA-256: `{fingerprint or proof.fingerprint()}`",
                *(proof.loop_replay_lines() + proof.bios_summary_lines() if lines is None else lines), *extra,
                f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]

    def accepted(self, lines, stack_arguments=False):
        return evidence.buffer_report_matches(lines, self.root, BASE, self.mapping,
                                              stack_arguments=stack_arguments)

    def test_report_replay_binds_the_summary(self):
        proof = self.walk(fill())
        lines = proof.bios_summary_lines()
        summary, gbatek, outputs, trusted, manifest = lines
        self.assertTrue(self.accepted(self.report(proof)))
        for name, edited in (("no summary", [gbatek, outputs, trusted, manifest]),
                             ("no GBATEK premise", [summary, outputs, trusted, manifest]),
                             ("no outputs premise", [summary, gbatek, trusted, manifest]),
                             ("no trust premise", [summary, gbatek, outputs, manifest]),
                             ("no premises", [summary, manifest]),
                             ("premises swapped", [summary, trusted, outputs, gbatek, manifest]),
                             ("no manifest", [summary, gbatek, outputs, trusted]),
                             ("none", []),
                             ("duplicated manifest", lines + [manifest]),
                             ("duplicated premise", [summary, gbatek, gbatek, outputs, trusted, manifest]),
                             ("indented", [" " + summary, gbatek, outputs, trusted, manifest]),
                             ("trust edited", [summary, gbatek, outputs, trusted.replace("not proved", "proved"), manifest]),
                             ("outputs edited", [summary, gbatek, outputs.replace("R0 or R1", "R0, R1 or R3"), trusted, manifest]),
                             ("GBATEK edited", [summary, gbatek.replace("preserves SP, ", ""), outputs, trusted, manifest]),
                             ("killed edited", [summary, gbatek, outputs, trusted, manifest.replace('"killed":[0]', '"killed":[]')])):
            with self.subTest(edit=name):
                self.assertNotEqual(edited, lines)
                self.assertFalse(self.accepted(self.report(proof, lines=edited)))
        self.assertFalse(self.accepted(self.report(proof, fingerprint="0" * 64)))
        self.assertFalse(self.accepted(self.report(proof), stack_arguments=True))
        # The same lines on an owner that applies no summary.
        plain = self.walk(owner("mov r0, sp\nbl callee", frame=8), "movs r1, #0\nstrh r1, [r0]\nmovs r0, #0\nbx lr")
        self.assertTrue(self.accepted(self.report(plain)))
        self.assertFalse(self.accepted(self.report(plain, *lines)))

    def test_report_replay_of_a_scalar_summary(self):
        caller = ("push {r4, lr}\nsub sp, #12\nadd r0, sp, #8\nstr r0, [sp]\nmovs r0, #1\n"
                  "bl callee\nadd sp, #12\npop {r4}\npop {r0}\nbx r0")
        proof = self.walk(caller, "push {r4, lr}\nmovs r0, #4\nbl Sqrt\npop {r4}\npop {r1}\nbx r1",
                          stack_arguments=True)
        self.assertTrue(self.accepted(self.report(proof), stack_arguments=True))
        self.assertFalse(self.accepted(self.report(proof, lines=[]), stack_arguments=True))

    def test_foreign_report_validators_refuse_the_lines(self):
        tree = ast.parse((ROOT / "tools" / "match_evidence.py").read_text())
        lists = [node for node in ast.walk(tree) if isinstance(node, ast.Tuple)
                 and any(isinstance(e, ast.Constant) and isinstance(e.value, str)
                         and e.value.startswith("* buffer loop replay") for e in node.elts)]
        self.assertGreaterEqual(len(lists), 6)
        for node in lists:
            with self.subTest(line=node.lineno):
                self.assertTrue(any(isinstance(e, ast.Constant) and e.value == "* buffer BIOS"
                                    for e in node.elts))

    def test_only_the_plain_path_opts_in(self):
        found = []
        for path in sorted((ROOT / "tools").glob("*.py")):
            tree = ast.parse(path.read_text())
            for function in ast.walk(tree):
                if not isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    continue
                for node in ast.walk(function):
                    if isinstance(node, ast.Call) and any(keyword.arg == "bios_wrappers"
                                                          for keyword in node.keywords):
                        (keyword,) = [k for k in node.keywords if k.arg == "bios_wrappers"]
                        self.assertIsInstance(keyword.value, ast.Constant)
                        name = getattr(node.func, "attr", getattr(node.func, "id", None))
                        found.append((path.name, function.name, name, keyword.value.value))
        self.assertEqual(sorted(found), [
            ("data_buffer_profile.py", "prove", "BufferCallProof", True),
            ("function_thunk_profile.py", "verify_source", "BufferCallProof", True),
            ("match.py", "main", "BufferCallProof", True), ("match.py", "main", "BufferCallProof", True),
            ("match_evidence.py", "buffer_report_matches", "BufferCallProof", True),
            ("match_evidence.py", "buffer_report_matches", "BufferCallProof", True)])


FILL_C = """typedef unsigned short u16;
typedef unsigned int u32;
extern void func_0814186C(const void *source, void *destination, u32 control);
void func_08000200(u16 *destination, u16 value)
{
    u16 fill;
    u16 *source = &fill;

    *source = value;
    func_0814186C(source, destination, %s);
}
"""
DATA_FILL_C = """typedef unsigned short u16;
typedef unsigned int u32;
extern u16 data_02000000[];
extern void func_0814186C(const void *source, void *destination, u32 control);
void func_08000200(u16 *destination, u16 value)
{
    u16 fill;
    u16 *source = &fill;

    *source = value;
    func_0814186C(source, destination, 0x01000010);
    data_02000000[0] = value;
}
"""
SQRT_C = """extern void func_08000400(int a, int b, int c, int d, int *e);
extern int func_08141898(int value);
int func_08000200(int value)
{
    int local;

    func_08000400(1, 2, 3, 4, &local);
    return func_08141898(value) + local;
}
"""
LITERAL_C = """extern void func_08000400(int *out, void (*callback)(void));
extern void func_08000500(void);
int func_08000200(void)
{
    int local;

    func_08000400(&local, func_08000500);
    return local;
}
"""
PLAIN_SQRT_C = """extern void func_08000400(int *out);
extern int func_08141898(int value);
int func_08000200(int value)
{
    int local;

    func_08000400(&local);
    return func_08141898(value) + local;
}
"""
NATIVE = 0x08000200


def tools_present():
    import shutil
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class BiosWrapperNativeTests(unittest.TestCase):
    """agbcc-compiled owners through match.py, replayed by report_matches."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="bios_wrappers_native_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def build(self, source, callee="bx lr", second="bx lr", objects=b"{}\n"):
        import argparse
        root = self.root
        for name in ("src", "include", "config", "symbols", "build"):
            (root / name).mkdir(parents=True, exist_ok=True)
        work = root / "build"
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global callee, callee_end\n"
                f"callee:\n{callee}\ncallee_end:\n.org 0x100\nsecond:\n{second}\nsecond_end:\n")
        (work / "callee.s").write_text(text)
        for command in (
                [match.DEFAULT_AS, "-mthumb-interwork", str(work / "callee.s"), "-o", str(work / "callee.o")],
                [match.DEFAULT_LD, "-Ttext=0x08000400", "-e", "callee", str(work / "callee.o"),
                 "-o", str(work / "callee.elf")],
                [match.DEFAULT_OBJCOPY, "-O", "binary", "--only-section=.text", str(work / "callee.elf"),
                 str(work / "callee.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        code = (work / "callee.bin").read_bytes()
        rom = bytearray(0x081418A0 - BASE)
        rom[0x400:0x400 + len(code)] = code
        image = match.elf_image((work / "callee.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        entries = [{"rom": f"0x{symbols[name]:08X}", "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
                   for name in ("callee", "second")]
        for address, (_, _, wrapper) in sorted(bios.WRAPPERS.items()):
            rom[address - BASE:address - BASE + len(wrapper)] = wrapper
            entries.append({"rom": f"0x{address:08X}", "end": f"0x{address + len(wrapper):08X}", "mode": "thumb"})
        (root / "src/08000200.c").write_text(source)
        (root / "config/data_symbols.json").write_bytes(objects)
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        runner = match.Runner(match.DEFAULT_CC, root=root, wsl_path=match.DEFAULT_WSL_PATH, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, root, NATIVE, "src/08000200.c")
            symbol, _ = match.function_record(original, "func_08000200", NATIVE, True)
            entries.insert(0, {"rom": f"0x{NATIVE:08X}", "end": f"0x{NATIVE + symbol['size']:08X}", "mode": "thumb"})
            mapping = json.dumps(entries).encode()
            body, _, _ = match.link_calls(runner, workspace, args, original, NATIVE, mapping, len(rom),
                                          bytes(rom), objects, {})
        rom[NATIVE - BASE:NATIVE - BASE + len(body)] = body
        (root / "config/functions.json").write_bytes(mapping)
        (root / "symbols/functions.txt").write_text("".join(
            f"{int(e['rom'], 16):08X} {int(e['end'], 16):08X} {int(e['end'], 16) - int(e['rom'], 16)} 0 return\n"
            for e in entries))
        (root / "baserom.bin").write_bytes(bytes(rom))

    def run_match(self, disabled=False):
        """match.py on the owner; `disabled` runs it with no wrapper covered (the matcher before #192)."""
        report = self.root / "docs/match/08000200.md"
        if report.exists():
            report.unlink()
        environment = dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin"), PYTHONDONTWRITEBYTECODE="1")
        command = [sys.executable, str(ROOT / "tools/match.py"), "--root", str(self.root), "0x08000200"]
        if disabled:
            command = [sys.executable, "-c",
                       "import runpy, sys; sys.path.insert(0, sys.argv[1]); import bios_wrapper_summary_profile as b; "
                       "b.BiosWrapperSummaries.covers = staticmethod(lambda address: False); "
                       "sys.argv = sys.argv[2:]; runpy.run_path(sys.argv[0], run_name='__main__')",
                       str(ROOT / "tools"), *command[1:]]
        result = subprocess.run(command, capture_output=True, text=True, env=environment, timeout=600)
        return result.returncode, result.stdout + result.stderr, report.read_text() if report.exists() else None

    def replays(self, report):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")):
            return evidence.report_matches(report, self.root, NATIVE)

    def test_fill_owner_matches_and_its_report_replays(self):
        self.build(FILL_C % "0x01000010")
        code, output, report = self.run_match()
        self.assertEqual(code, 0, output)
        self.assertIn(f"* verification: `{evidence.BUFFER_SCHEMA}`", report.splitlines())
        (manifest,) = [line for line in report.splitlines() if line.startswith("* buffer BIOS manifest: ")]
        (site,) = json.loads(manifest.split("`")[1])["memory_sites"]
        self.assertEqual((site["routine"], site["source"][1], site["destination"], site["killed"]),
                         ("CpuSet", 2, None, [0]))
        self.assertTrue(self.replays(report))
        (summary,) = [line for line in report.splitlines() if line.startswith("* buffer BIOS summaries: ")]
        for premise in PREMISE_LINES:
            self.assertIn(premise, report.splitlines())
        for name, edited in (("summary", report.replace(summary + "\n", "")),
                             ("GBATEK premise", report.replace(GBATEK_PREMISE + "\n", "")),
                             ("outputs premise", report.replace(OUTPUTS_PREMISE + "\n", "")),
                             ("trust premise", report.replace(TRUSTED_PREMISE + "\n", "")),
                             ("manifest", report.replace(manifest + "\n", "")),
                             ("both", report.replace(summary + "\n", "").replace(manifest + "\n", "")),
                             ("control", report.replace(manifest, manifest.replace('"count":null', '"count":16'))),
                             ("schema", report.replace(evidence.BUFFER_SCHEMA, evidence.STACK_BUFFER_SCHEMA)),
                             ("linked", report.replace(evidence.BUFFER_SCHEMA, evidence.FRAMED_LINKED_SCHEMA))):
            with self.subTest(edit=name):
                self.assertNotEqual(edited, report)
                self.assertFalse(self.replays(edited))

    def test_fill_owner_beside_typed_data_composes_with_the_data_buffer_schema(self):
        import data_buffer_profile as data_buffer
        self.build(DATA_FILL_C, objects=b'{"data_02000000": "0x02000000"}\n')
        code, output, report = self.run_match()
        self.assertEqual(code, 0, output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{data_buffer.SCHEMA}`", lines)
        bios_lines = [line for line in lines if line.startswith("* buffer BIOS")]
        self.assertEqual(len(bios_lines), 5)
        self.assertEqual(bios_lines[1:4], PREMISE_LINES)
        self.assertTrue(self.replays(report))
        summary, gbatek, outputs, trusted, manifest = bios_lines
        for name, edited in (("summary", report.replace(summary + "\n", "")),
                             ("GBATEK premise", report.replace(gbatek + "\n", "")),
                             ("outputs premise", report.replace(outputs + "\n", "")),
                             ("trust premise", report.replace(trusted + "\n", "")),
                             ("manifest", report.replace(manifest + "\n", "")),
                             ("premises swapped", report.replace(outputs + "\n" + trusted, trusted + "\n" + outputs)),
                             ("outputs edited", report.replace(outputs, outputs.replace("not proved", "proved"))),
                             ("trust edited", report.replace(trusted, trusted.replace("not proved", "proved"))),
                             ("duplicated", report.replace(manifest, manifest + "\n" + manifest)),
                             ("all", "\n".join(line for line in lines if not line.startswith("* buffer BIOS")) + "\n")):
            with self.subTest(edit=name):
                self.assertNotEqual(edited, report)
                self.assertFalse(self.replays(edited))

    def test_copy_mode_fill_source_is_refused(self):
        self.build(FILL_C % "0x00000010")
        code, output, report = self.run_match()
        self.assertNotEqual(code, 0, output)
        self.assertIsNone(report)
        self.assertIn("buffer callee 0x0814186C: buffer access is unaligned or outside allocated local words", output)

    def test_function_buffer_reports_refuse_the_lines(self):
        # The function-literal buffer proof applies no summary, so its reports carry no BIOS line.
        self.build(LITERAL_C, "movs r2, #0\nstr r2, [r0]\nmovs r0, #0\nmovs r1, #0\nbx lr")
        code, output, report = self.run_match()
        self.assertEqual(code, 0, output)
        self.assertIn(f"* verification: `{evidence.FUNCTION_BUFFER_SCHEMA}`", report.splitlines())
        self.assertTrue(self.replays(report))
        stray = "* buffer BIOS summaries: `gba-bios-swi-wrapper-summaries-v1` " + bios.CONTRACT
        self.assertFalse(self.replays(report.replace("* buffer calls:", stray + "\n* buffer calls:", 1)))

    def test_a_wrapper_call_with_no_live_pointer_leaves_the_report_unchanged(self):
        # The buffer callee receives &local; the later Sqrt call receives no pointer. The report
        # is byte for byte the report the matcher writes with every summary disabled.
        self.build(PLAIN_SQRT_C, "movs r1, #0\nstr r1, [r0]\nmovs r0, #0\nbx lr")
        code, output, report = self.run_match()
        self.assertEqual(code, 0, output)
        self.assertIn(f"* verification: `{evidence.BUFFER_SCHEMA}`", report.splitlines())
        self.assertIn("bl #0x8141898", report)
        self.assertFalse([line for line in report.splitlines() if line.startswith("* buffer BIOS")])
        code, output, disabled = self.run_match(disabled=True)
        self.assertEqual(code, 0, output)
        self.assertEqual(report, disabled)
        self.assertTrue(self.replays(report))

    def test_scalar_wrapper_beside_a_pointer_word_matches_and_replays(self):
        self.build(SQRT_C, "ldr r0, [sp]\nmovs r1, #0\nstr r1, [r0]\nmovs r0, #0\nbx lr")
        code, output, report = self.run_match()
        self.assertEqual(code, 0, output)
        self.assertIn(f"* verification: `{evidence.STACK_BUFFER_SCHEMA}`", report.splitlines())
        (manifest,) = [line for line in report.splitlines() if line.startswith("* buffer BIOS manifest: ")]
        (site,) = json.loads(manifest.split("`")[1])["scalar_sites"]
        self.assertEqual((site["routine"], site["depth"]), ("Sqrt", 0))
        self.assertTrue(self.replays(report))
        self.assertFalse(self.replays(report.replace(manifest + "\n", "")))


if __name__ == "__main__":
    unittest.main()
