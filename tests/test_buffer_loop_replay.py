"""Bounded path-by-path replay of buffer callees whose pointer moves around a loop.

A buffer callee such as 0812E4F4 stores ``*output++ = entry`` inside a counted
loop. Its plain summary cannot join the differing pointer offsets, so the
callee is replayed with exact known counters and CMP flags: every store is
checked at its exact caller-frame offset, and the replay refuses when an
iteration can leave the allocated buffer or no bound is proven.
"""
import itertools
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
from capstone.arm_const import (ARM_CC_EQ, ARM_CC_NE, ARM_CC_HS, ARM_CC_LO, ARM_CC_MI,
                                ARM_CC_PL, ARM_CC_VS, ARM_CC_VC, ARM_CC_HI, ARM_CC_LS,
                                ARM_CC_GE, ARM_CC_LT, ARM_CC_GT, ARM_CC_LE)

BASE = match.ROM_BASE


def caller(frame):
    return (f"push {{r4, lr}}\nsub sp, #{frame}\nmov r1, sp\nmovs r0, #0\n"
            f"bl callee\nadd sp, #{frame}\npop {{r4}}\npop {{r0}}\nbx r0")


def counted(trip, store="strh r0, [r6]", stride=2, between=""):
    """The 0812E4F4 shape: a conditional *out++ under a counter 0..trip-1."""
    return ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r1, #0\nmovs r5, #0\nloop:\n"
            "bl child\ncmp r0, #0\nbeq skip\n"
            f"{store}\nadds r6, #{stride}\nskip:\nadds r5, #1\ncmp r5, #{trip - 1}\n"
            f"{between}ble loop\npop {{r4, r5, r6}}\npop {{r1}}\nbx r1")


class BufferLoopReplayTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="buffer_loop_replay_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"),
            "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def fixture(self, callee, frame=8, child="bx lr", stack_arguments=False,
                proof_type=match.BufferCallProof):
        assembly = self.root / "fixture.s"
        assembly.write_text(
            ".syntax unified\n.arch armv5t\n.thumb\n.text\n"
            ".global caller, caller_end, callee, callee_end, child, child_end\n"
            f"caller:\n{caller(frame)}\ncaller_end:\n.org 0x100\n"
            f"callee:\n{callee}\ncallee_end:\n.org 0x200\n"
            f"child:\n{child}\nchild_end:\n")
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(assembly),
             "-o", str(self.root / "fixture.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller",
             str(self.root / "fixture.o"), "-o", str(self.root / "fixture.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "fixture.elf"), str(self.root / "baserom.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "fixture.elf").read_bytes())
        symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        entries = [{"rom": f"0x{symbols[name]:08X}",
                    "end": f"0x{symbols[name + '_end']:08X}", "mode": "thumb"}
                   for name in ("caller", "callee", "child")]
        rom = (self.root / "baserom.bin").read_bytes()
        proof = proof_type(rom, json.dumps(entries).encode(), stack_arguments=stack_arguments)
        match.verify_leaf_instructions(rom[:symbols["caller_end"] - BASE], BASE, True,
                                       buffer_proof=proof, call_resolver=proof.target)
        return proof

    def writes(self, proof):
        return {write for records in proof.loop_replays.values()
                for *_, record in records for write in record}

    def test_counted_loop_writes_exactly_the_bounded_prefix(self):
        for stack_arguments in (False, True):
            with self.subTest(stack_arguments=stack_arguments):
                proof = self.fixture(counted(4), frame=8, stack_arguments=stack_arguments)
                self.assertEqual(set(proof.loop_replays), {BASE + 0x100})
                self.assertEqual(self.writes(proof), {(0, 2), (2, 2), (4, 2), (6, 2)})
        word = self.fixture(counted(3, "str r0, [r6]", 4), frame=12)
        self.assertEqual(self.writes(word), {(0, 4), (4, 4), (8, 4)})

    def test_replay_binds_the_fingerprint_only_when_used(self):
        replayed = self.fixture(counted(4), frame=8)
        plain = self.fixture("strh r0, [r1]\nmovs r1, #0\nbx lr", frame=8)
        self.assertFalse(plain.loop_replays)
        fingerprint = replayed.fingerprint()
        replayed.loop_replays.clear()
        self.assertNotEqual(fingerprint, replayed.fingerprint())

    def test_buffer_smaller_than_the_proven_bound_is_refused(self):
        # 0812E4F4 itself: five iterations against one allocated word.
        for trip, frame in ((5, 4), (4, 4), (5, 8), (3, 4)):
            with self.subTest(trip=trip, frame=frame), self.assertRaisesRegex(
                    ValueError, r"buffer callee 0x08000100: bounded loop replay at 0x[0-9A-F]+: "
                                r"2-byte strh at caller sp\+\d+: .*outside allocated local words"):
                self.fixture(counted(trip), frame=frame)
        self.fixture(counted(2), frame=4)
        self.fixture(counted(5), frame=12)

    def test_unbounded_loops_are_refused(self):
        # The bound depends on a call result or an unknown register.
        unknown = counted(4).replace("cmp r5, #3", "cmp r5, r4")
        with self.assertRaisesRegex(ValueError, "bounded loop replay.*outside allocated local words"):
            self.fixture(unknown, frame=64)
        data = counted(4).replace("cmp r5, #3\nble loop", "bl child\ncmp r0, #0\nbne loop")
        with self.assertRaisesRegex(ValueError, "bounded loop replay.*outside allocated local words"):
            self.fixture(data, frame=64)
        # A counter that never stops, with the pointer only moving: the budget refuses.
        spin = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r1, #0\nmovs r5, #0\nloop:\nbl child\n"
                "cmp r0, #0\nbeq skip\nadds r6, #2\nskip:\nadds r5, #1\nbl child\ncmp r0, #0\n"
                "bne loop\npop {r4, r5, r6}\npop {r1}\nbx r1")
        with self.assertRaisesRegex(ValueError, "state budget exhausted"):
            self.fixture(spin, frame=8)

    def test_flags_and_counters_are_forgotten_when_not_exact(self):
        # A flag-setting instruction or a call between CMP and the branch, or a
        # counter held in a caller-clobbered register, leaves the trip unbounded.
        for variant in (counted(4, between="adds r0, #0\n"),
                        counted(4, between="bl child\n"),
                        counted(4).replace("r5", "r3"),
                        counted(4).replace("adds r5, #1", "lsls r5, r5, #1\nlsrs r5, r5, #1\nadds r5, #1")):
            with self.subTest(variant=variant), self.assertRaisesRegex(
                    ValueError, "bounded loop replay"):
                self.fixture(variant, frame=64)

    def test_stride_that_misaligns_the_store_is_refused(self):
        with self.assertRaisesRegex(ValueError, "4-byte str at caller sp\\+2: .*unaligned"):
            self.fixture(counted(2, "str r0, [r6]", 2), frame=64)
        with self.assertRaisesRegex(ValueError, "2-byte strh at caller sp\\+3: .*unaligned"):
            self.fixture(counted(2, "strh r0, [r6]", 3), frame=64)

    def test_escaping_pointers_are_refused(self):
        with self.assertRaisesRegex(ValueError, "cannot be stored or spilled"):
            self.fixture(counted(2, "str r6, [r6]", 4), frame=64)
        with self.assertRaisesRegex(ValueError, "bounded loop replay.*escape"):
            self.fixture(counted(2, "strh r0, [r6]\nmov r8, r6", 2), frame=64)
        returned = counted(2).replace("pop {r4, r5, r6}", "adds r0, r6, #0\npop {r4, r5, r6}")
        with self.assertRaisesRegex(ValueError, "bounded loop replay.*escapes through a return register"):
            self.fixture(returned, frame=64)
        with self.assertRaisesRegex(ValueError, "bounded loop replay.*inconsistent possible pointer offsets"):
            self.fixture(returned, frame=64, stack_arguments=True)

    def test_profiles_without_replay_keep_the_join_refusal(self):
        class Plain(match.BufferCallProof):
            def loop_replay_eligible(self):
                return False
        with self.assertRaisesRegex(ValueError, "inconsistent buffer aliases at control-flow join"):
            self.fixture(counted(2), frame=64, proof_type=Plain)
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets"):
            self.fixture(counted(2), frame=64, proof_type=Plain, stack_arguments=True)

    def test_condition_evaluation_matches_the_arm_definition(self):
        values = (0, 1, 2, 4, 5, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF)
        for left, right in itertools.product(values, repeat=2):
            result = (left - right) & 0xFFFFFFFF
            signed = lambda value: value - (1 << 32) if value >> 31 else value
            expected = {
                ARM_CC_EQ: left == right, ARM_CC_NE: left != right,
                ARM_CC_HS: left >= right, ARM_CC_LO: left < right,
                ARM_CC_HI: left > right, ARM_CC_LS: left <= right,
                ARM_CC_GE: signed(left) >= signed(right), ARM_CC_LT: signed(left) < signed(right),
                ARM_CC_GT: signed(left) > signed(right), ARM_CC_LE: signed(left) <= signed(right),
                ARM_CC_MI: bool(result >> 31), ARM_CC_PL: not result >> 31,
                ARM_CC_VS: signed(left) - signed(right) != signed(result),
                ARM_CC_VC: signed(left) - signed(right) == signed(result),
            }
            for cc, holds in expected.items():
                with self.subTest(left=left, right=right, cc=cc):
                    self.assertEqual(match.loop_replay_condition(cc, (left, right)), holds)


if __name__ == "__main__":
    unittest.main()
