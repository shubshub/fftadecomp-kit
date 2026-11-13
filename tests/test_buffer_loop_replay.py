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
import match_evidence as evidence
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
                proof_type=match.BufferCallProof, extra=()):
        assembly = self.root / "fixture.s"
        assembly.write_text(
            ".syntax unified\n.arch armv5t\n.thumb\n.text\n"
            ".global caller, caller_end, callee, callee_end, child, child_end\n"
            f"caller:\n{caller(frame)}\ncaller_end:\n.org 0x100\n"
            f"callee:\n{callee}\ncallee_end:\n.org 0x200\n"
            f"child:\n{child}\nchild_end:\n" + "".join(
                f".org 0x{0x300 + 0x100 * index:x}\n{name}:\n{body}\n{name}_end:\n"
                for index, (name, body) in enumerate(extra)))
        for name, _ in extra:
            assembly.write_text(assembly.read_text().replace(
                ".global caller,", f".global {name}, {name}_end, caller,", 1))
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
                   for name in ("caller", "callee", "child", *(name for name, _ in extra))]
        rom = (self.root / "baserom.bin").read_bytes()
        self.mapping = json.dumps(entries).encode()
        self.body = rom[:symbols["caller_end"] - BASE]
        replay = {"loop_replay": True} if proof_type in (
            match.BufferCallProof, match.FunctionBufferCallProof) else {}
        proof = proof_type(rom, self.mapping, stack_arguments=stack_arguments, **replay)
        match.verify_leaf_instructions(self.body, BASE, True,
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
            pass  # replay is opt-in per class and is not inherited
        with self.assertRaisesRegex(ValueError, "inconsistent buffer aliases at control-flow join"):
            self.fixture(counted(2), frame=64, proof_type=Plain)
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets"):
            self.fixture(counted(2), frame=64, proof_type=Plain, stack_arguments=True)

    def test_replay_is_opt_in_and_real_subclasses_do_not_inherit_it(self):
        import named_data_buffer_profile as named
        import static_callback_r6_frame_profile  # noqa: F401 - registers subclasses
        import ordinary_formal_output_spill_profile  # noqa: F401
        import descriptor_disjunctive_alias_profile  # noqa: F401
        pending, classes = [match.BufferCallProof], set()
        while pending:
            cls = pending.pop()
            if cls not in classes:
                classes.add(cls)
                pending.extend(cls.__subclasses__())
        enabled = {cls for cls in classes if cls.__dict__.get("_loop_replay_opt_in") is True}
        self.assertEqual(enabled, {match.BufferCallProof, match.FunctionBufferCallProof})
        self.assertIn(named.NamedDataBufferProof, classes)
        # A real ineligible class (its ROM-ownership hooks stubbed) keeps the old refusal.
        def build(rom, mapping, stack_arguments):
            return named.NamedDataBufferProof(rom, mapping, b"", None)
        with patch.object(named.NamedDataBufferProof, "span", match.BufferCallProof.span), \
                patch.object(named.NamedDataBufferProof, "inspect", match.BufferCallProof.inspect), \
                self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets"):
            self.fixture(counted(2), frame=64, proof_type=build)
        # The plain proof also declines replay under the BIOS-fill or scratch policies.
        proof = self.fixture("strh r0, [r1]\nmovs r1, #0\nbx lr")
        proof.discarded_exit_scratch = {"policy": "test"}
        self.assertFalse(proof.loop_replay_eligible())

    def test_inspected_callee_that_clobbers_the_counter_is_refused(self):
        # The child receives the buffer (so it is inspected) and zeroes R5: the
        # real loop never ends, so the counter must not survive the call.
        callee = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r5, #0\nloop:\n"
                  "adds r1, r6, #0\nbl child\nmovs r1, #0\ncmp r0, #0\nbeq skip\n"
                  "strh r0, [r6]\nadds r6, #2\nskip:\nadds r5, #1\ncmp r5, #1\nble loop\n"
                  "pop {r4, r5, r6}\npop {r1}\nbx r1")
        with self.assertRaisesRegex(ValueError, "bounded loop replay"):
            self.fixture(callee, frame=8, child="movs r5, #0\nmovs r0, #0\nbx lr",
                         stack_arguments=True)
        # A child that leaves R5 alone keeps the exact two-iteration bound.
        proof = self.fixture(callee, frame=8, child="movs r0, #0\nbx lr", stack_arguments=True)
        self.assertEqual(self.writes(proof), {(0, 2), (2, 2)})

    # The probe callee: counter in R5, pointer in R6, two iterations, the buffer is
    # passed to `child` (so `child` is inspected) in the first form and not in the second.
    PROBE = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r5, #0\nloop:\n"
             "adds r1, r6, #0\nmovs r0, #0\nbl child\nmovs r1, #0\n"
             "strh r0, [r6]\nadds r6, #2\nadds r5, #1\ncmp r5, #1\nble loop\n"
             "pop {r4, r5, r6}\npop {r1}\nbx r1")
    RET = "pop {r4}\npop {r0}\nbx r0"

    def test_inspected_callee_chains_that_clobber_the_counter_are_refused(self):
        grand = "movs r5, #0\nbx lr"
        refused = {
            # A: an inspected grandchild zeroes R5.
            "A": dict(child="push {r4, lr}\nmovs r0, #0\nbl grand\n" + self.RET,
                      extra=[("grand", grand)]),
            # B: the child pops a different value into R5.
            "B": dict(child="push {r0, lr}\npop {r5}\npop {r2}\nmovs r0, #0\nbx r2"),
            # C: the child writes R5 on one path only.
            "C": dict(child="cmp r0, #0\nbne 1f\nmovs r5, #0\n1:\nmovs r0, #0\nbx lr"),
            # G: the write is three inspected calls down.
            "G": dict(child="push {r4, lr}\nbl grand\n" + self.RET,
                      extra=[("grand", "push {r4, lr}\nbl great\n" + self.RET),
                             ("great", "movs r5, #0\nmovs r0, #0\nbx lr")]),
        }
        for name, kwargs in refused.items():
            with self.subTest(probe=name), self.assertRaisesRegex(ValueError, "bounded loop replay"):
                self.fixture(self.PROBE, frame=4, stack_arguments=True, **kwargs)

    def test_uninspected_callees_are_trusted_to_preserve_r4_to_r11(self):
        # ABI premise, deliberately admitted: a callee that receives no buffer
        # alias is not inspected, so its R4-R11 are assumed restored (as the alias
        # tracking already assumes).  D and E below zero R5 in such a callee; the
        # real loop would not end, yet replay admits it.  The premise is recorded
        # (call target, register) in the replay record and so in the fingerprint,
        # which is the only mitigation: it is visible and bound, not proved.
        d = self.fixture(self.PROBE, frame=4, stack_arguments=True,
                         child="push {r4, lr}\nmovs r1, #0\nbl grand\n" + self.RET,
                         extra=[("grand", "movs r5, #0\nbx lr")])
        e = self.fixture(self.PROBE.replace("adds r1, r6, #0\n", "movs r1, #0\n"), frame=4,
                         stack_arguments=True, child="movs r5, #0\nbx lr")
        for proof, target in ((d, BASE + 0x300), (e, BASE + 0x200)):
            self.assertEqual(self.writes(proof), {(0, 2), (2, 2)})
            trusted = {pair for records in proof.loop_replays.values()
                       for record in records for pair in record[3]}
            self.assertIn((target, match.ARM_REG_R0 + 5), trusted)
        # The trusted pairs are bound by the fingerprint.
        fingerprint = e.fingerprint()
        callee = next(iter(e.loop_replays))
        e.loop_replays[callee] = {record[:3] + ((),) + record[4:] for record in e.loop_replays[callee]}
        self.assertNotEqual(fingerprint, e.fingerprint())

    def test_pruned_branch_edges_are_bound_by_the_fingerprint(self):
        proof = self.fixture(counted(4), frame=8)
        pruned = {edge for records in proof.loop_replays.values()
                  for record in records for edge in record[4]}
        self.assertTrue(pruned)
        fingerprint = proof.fingerprint()
        callee = next(iter(proof.loop_replays))
        proof.loop_replays[callee] = {record[:4] + ((),) + record[5:]
                                      for record in proof.loop_replays[callee]}
        self.assertNotEqual(fingerprint, proof.fingerprint())

    def test_refusals_on_pruned_infeasible_edges_are_not_evaluated(self):
        # Replay prunes branches its exact flags prove dead, so an out-of-bounds
        # store there is admitted; the pruned edge is bound in the record instead.
        dead = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r1, #0\nmovs r5, #0\nloop:\n"
                "strh r1, [r6]\nadds r6, #2\nadds r5, #1\ncmp r5, #1\nble loop\n"
                "cmp r5, #7\nbne done\nstrh r1, [r6, #30]\ndone:\npop {r4, r5, r6}\npop {r1}\nbx r1")
        proof = self.fixture(dead, frame=4)
        edges = {edge for records in proof.loop_replays.values()
                 for record in records for edge in record[4]}
        self.assertIn((match.ARM_CC_NE, 2, 7, True), {edge[1:] for edge in edges})

    def test_nested_replay_chain_records_each_inner_call(self):
        # The child writes out[0..2) in its own loop; the callee calls it twice,
        # advancing by four bytes, with its counter in R7 (untouched by the child).
        child = ("push {r4, r5, r6, lr}\nadds r6, r1, #0\nmovs r1, #0\nmovs r5, #0\nloop2:\n"
                 "strh r5, [r6]\nadds r6, #2\nadds r5, #1\ncmp r5, #1\nble loop2\n"
                 "pop {r4, r5, r6}\npop {r1}\nbx r1")
        callee = ("push {r4, r5, r6, r7, lr}\nadds r6, r1, #0\nmovs r7, #0\nloop:\n"
                  "adds r1, r6, #0\nbl child\nmovs r1, #0\nadds r6, #4\nadds r7, #1\n"
                  "cmp r7, #1\nble loop\npop {r4, r5, r6, r7}\npop {r1}\nbx r1")
        proof = self.fixture(callee, frame=8, child=child)
        self.assertEqual(set(proof.loop_replays), {BASE + 0x100, BASE + 0x200})
        self.assertEqual({record[1] for record in proof.loop_replays[BASE + 0x200]},
                         {((match.ARM_REG_R1, -16),), ((match.ARM_REG_R1, -12),)})
        self.assertEqual(self.writes(proof), {(0, 2), (2, 2), (4, 2), (6, 2)})
        # A third call would pass a pointer one past the allocation.
        with self.assertRaisesRegex(ValueError, "buffer callee 0x08000100: bounded loop replay at "
                                    "0x08000108: .*outside allocated local words"):
            self.fixture(callee.replace("cmp r7, #1", "cmp r7, #2"), frame=8, child=child)

    def test_per_callee_and_per_proof_budgets(self):
        with patch.object(match, "LOOP_REPLAY_STATE_BUDGET", 8), \
                self.assertRaisesRegex(ValueError, "state budget exhausted"):
            self.fixture(counted(4), frame=8)
        # The per-proof counter accumulates across replays: a second replay of
        # the same callee fits its own budget but not the remaining proof budget.
        proof = self.fixture(counted(4), frame=8)
        used = proof.loop_replay_states
        self.assertLess(used, match.LOOP_REPLAY_STATE_BUDGET)
        with patch.object(match, "LOOP_REPLAY_TOTAL_BUDGET", used + used // 2), \
                self.assertRaisesRegex(ValueError, "state budget exhausted"):
            proof.check_arguments(BASE + 0x100, {match.ARM_REG_R1: -8},
                                  [(False, False, True)] * 2, {}, frozenset())

    def report_lines(self, proof, *extra, fingerprint=None):
        return [f"* compiled : `{self.body.hex()}`",
                f"* buffer calls: {evidence.BUFFER_SUMMARY}",
                f"* buffer proof SHA-256: `{fingerprint or proof.fingerprint()}`",
                *extra,
                f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]

    def accepted(self, lines):
        return evidence.buffer_report_matches(lines, self.root, BASE, self.mapping)

    def test_report_replay_refuses_a_tampered_replay_fingerprint(self):
        proof = self.fixture(counted(4), frame=8)
        honest = proof.fingerprint()
        stated = proof.loop_replay_lines()
        self.assertTrue(self.accepted(self.report_lines(proof, *stated)))
        proof.loop_replays.clear()
        stale = proof.fingerprint()
        self.assertFalse(self.accepted(self.report_lines(proof, *stated, fingerprint=stale)))
        self.assertFalse(self.accepted(self.report_lines(proof, *stated, fingerprint="0" * 64)))
        self.assertEqual(honest, self.fixture(counted(4), frame=8).fingerprint())

    def test_report_states_the_replay_and_refuses_a_missing_altered_or_extra_line(self):
        proof = self.fixture(counted(4), frame=8)
        (line,) = proof.loop_replay_lines()
        self.assertRegex(line, r"^\* buffer loop replay: `bounded-loop-replay-v2` callee 0x08000100 "
                               r"sites 0x[0-9A-F]{8} writes sp\+0:2 sp\+2:2 sp\+4:2 sp\+6:2; "
                               r"proved none; trusted 0x08000200:r5; pruned edges \d+$")
        self.assertTrue(self.accepted(self.report_lines(proof, line)))
        self.assertFalse(self.accepted(self.report_lines(proof)))
        self.assertFalse(self.accepted(self.report_lines(proof, line.replace("sp+6:2", "sp+8:2"))))
        self.assertFalse(self.accepted(self.report_lines(proof, line, line)))
        self.assertFalse(self.accepted(self.report_lines(proof, line, "* buffer unknown: x")))
        plain = self.fixture("strh r0, [r1]\nmovs r1, #0\nbx lr", frame=8)
        self.assertEqual(plain.loop_replay_lines(), [])
        self.assertTrue(self.accepted(self.report_lines(plain)))
        self.assertFalse(self.accepted(self.report_lines(plain, line)))

    def test_replay_requires_the_explicit_constructor_argument(self):
        proof = self.fixture(counted(4), frame=8)
        self.assertTrue(proof.loop_replay)
        rom = (self.root / "baserom.bin").read_bytes()
        plain = match.BufferCallProof(rom, self.mapping)
        self.assertFalse(plain.loop_replay_eligible())
        with self.assertRaisesRegex(ValueError, "inconsistent possible pointer offsets|inconsistent buffer aliases"):
            match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=match.BufferCallProof(
                rom, self.mapping, stack_arguments=True), call_resolver=plain.target)

    @staticmethod
    def scan_opt_in(name, tree, found, violations):
        import ast
        classes = ("BufferCallProof", "FunctionBufferCallProof")
        attributes = ("loop_replay", "_loop_replay_opt_in")

        def visit(node, function):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                function = node.name
            callee = getattr(getattr(node, "func", None), "attr", getattr(getattr(node, "func", None), "id", None))
            if isinstance(node, ast.Call):
                if callee in classes:
                    keywords = {keyword.arg: keyword.value for keyword in node.keywords}
                    if None in keywords or any(isinstance(a, ast.Starred) for a in node.args):
                        violations.append((name, function, "unpacked arguments"))
                    value = keywords.get("loop_replay")
                    if value is not None and not isinstance(value, ast.Constant):
                        violations.append((name, function, "non-constant loop_replay"))
                    found.add((name, function, getattr(value, "value", None) is True))
                if callee == "setattr" and name != "match.py" and any(
                        isinstance(a, ast.Constant) and a.value in attributes for a in node.args):
                    violations.append((name, function, "setattr of the opt-in"))
            targets = node.targets if isinstance(node, ast.Assign) else \
                [node.target] if isinstance(node, (ast.AugAssign, ast.AnnAssign)) else []
            for target in ast.walk(ast.Tuple(elts=targets)):
                if isinstance(target, ast.Attribute) and target.attr in attributes and name != "match.py":
                    violations.append((name, function, "assignment to the opt-in"))
            if isinstance(node, ast.ImportFrom) and any(alias.name in classes and alias.asname
                                                        for alias in node.names):
                violations.append((name, function, "aliased import of a proof class"))
            if isinstance(node, ast.ClassDef) and name != "match.py":
                for statement in node.body:
                    targets = statement.targets if isinstance(statement, ast.Assign) else \
                        [statement.target] if isinstance(statement, (ast.AnnAssign, ast.AugAssign)) else []
                    if any(isinstance(t, ast.Name) and t.id in attributes for t in targets):
                        violations.append((name, function, "class body sets the opt-in"))
            if isinstance(node, (ast.Assign, ast.AnnAssign)) and isinstance(
                    node.value, (ast.Name, ast.Attribute)) and \
                    getattr(node.value, "attr", getattr(node.value, "id", None)) in classes:
                violations.append((name, function, "alias of a proof class"))
            if isinstance(node, ast.Call) and callee == "partial" and (
                    any(keyword.arg in attributes or keyword.arg is None for keyword in node.keywords)
                    or any(getattr(a, "attr", getattr(a, "id", None)) in classes for a in node.args)):
                violations.append((name, function, "partial of a proof class or its opt-in"))
            if isinstance(node, ast.Subscript) and isinstance(node.ctx, (ast.Store, ast.Del)) and \
                    isinstance(node.value, ast.Attribute) and node.value.attr == "__dict__" or (
                    isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and isinstance(node.func.value, ast.Attribute) and node.func.value.attr == "__dict__"
                    and node.func.attr in ("update", "setdefault", "pop", "popitem", "clear", "__setitem__")):
                # Reviewed: neither writes the opt-in (a fixed ledger key; fields of a volatile record).
                if (name, function) not in (("named_data_buffer_profile.py", "inspect"),
                                            ("volatile_semantics.py", "__init__")):
                    violations.append((name, function, "__dict__ write"))
            for child in ast.iter_child_nodes(node):
                visit(child, function)
        visit(tree, "<module>")

    def test_every_loaded_subclass_that_sets_the_opt_in_is_enumerated(self):
        import importlib
        import sys
        tools = ROOT / "tools"
        self.assertIn(str(tools), sys.path)
        for path in sorted(tools.glob("*.py")):
            importlib.import_module(path.stem)
        pending, classes = [match.BufferCallProof], set()
        while pending:
            cls = pending.pop()
            if cls not in classes:
                classes.add(cls)
                pending.extend(cls.__subclasses__())
        self.assertGreater(len(classes), 20)
        for flag in ("_loop_replay_opt_in", "loop_replay"):
            with self.subTest(flag=flag):
                self.assertEqual({cls for cls in classes if flag in cls.__dict__ and cls.__dict__[flag]},
                                 {match.BufferCallProof, match.FunctionBufferCallProof}
                                 if flag == "_loop_replay_opt_in" else set())

    def test_only_reviewed_construction_sites_request_replay(self):
        import ast
        found, violations = set(), []
        for path in sorted((ROOT / "tools").glob("*.py")):
            self.scan_opt_in(path.name, ast.parse(path.read_text()), found, violations)
        self.assertEqual(violations, [])
        self.assertEqual({site[:2] for site in found if site[2]}, {
            ("match.py", "verify_function_buffers"), ("match.py", "main"),
            ("function_thunk_profile.py", "verify_source"),
            ("match_evidence.py", "buffer_report_matches")})
        # Producers whose evidence neither states nor binds a replay stay plain.
        plain = {site[0] for site in found if not site[2]}
        self.assertTrue({"owner_runtime_profile.py", "match.py"} <= plain)

    def test_opt_in_scan_flags_the_cases_it_used_to_miss(self):
        import ast
        for source in ("BufferCallProof(rom, m, **options)", "BufferCallProof(rom, m, loop_replay=flag)",
                       "proof.loop_replay = True", "proof._loop_replay_opt_in = True",
                       "setattr(proof, 'loop_replay', True)",
                       "from match import BufferCallProof as P", "P = match.BufferCallProof",
                       "P: type = BufferCallProof", "class Q(match.BufferCallProof):\n    _loop_replay_opt_in = True",
                       "functools.partial(BufferCallProof, loop_replay=True)",
                       "functools.partial(match.BufferCallProof, rom)",
                       "type(proof).__dict__['_loop_replay_opt_in'] = True",
                       "Q.__dict__.update(_loop_replay_opt_in=True)"):
            with self.subTest(source=source):
                violations = []
                self.scan_opt_in("other.py", ast.parse(source), set(), violations)
                self.assertTrue(violations)
        violations = []
        self.scan_opt_in("other.py", ast.parse("BufferCallProof(rom, m, loop_replay=True)"), set(), violations)
        self.assertEqual(violations, [])

    def test_replay_lines_are_refused_when_indented_or_in_other_reports(self):
        import ast
        proof = self.fixture(counted(4), frame=8)
        (line,) = proof.loop_replay_lines()
        self.assertFalse(self.accepted(self.report_lines(proof, " " + line)))
        self.assertFalse(self.accepted(self.report_lines(proof, line, " " + line)))
        self.assertFalse(self.accepted(self.report_lines(proof, line, "\t* buffer extra: x")))
        marker = "* buffer loop replay"
        tree = ast.parse((ROOT / "tools" / "match_evidence.py").read_text())
        lists = [n for n in ast.walk(tree) if isinstance(n, ast.Tuple)
                 and any(isinstance(e, ast.Constant) and isinstance(e.value, str)
                         and e.value.startswith("* buffer proof") for e in n.elts) and len(n.elts) >= 5]
        self.assertGreaterEqual(len(lists), 5)
        for node in lists:
            with self.subTest(line=node.lineno):
                self.assertTrue(any(isinstance(e, ast.Constant) and isinstance(e.value, str)
                                    and e.value.startswith(marker) for e in node.elts),
                                "forbidden-marker list lacks the replay line")

    def test_pinned_preserving_callee_moves_a_pair_from_trusted_to_proved(self):
        import hashlib
        import callee_preservation_profile as preservation
        proof = self.fixture(counted(4), frame=8)
        rom = (self.root / "baserom.bin").read_bytes()
        span = rom[0x200:0x202]
        self.assertEqual(span, bytes.fromhex("7047"))
        pin = {BASE + 0x200: (BASE + 0x202, hashlib.sha256(span).hexdigest(), ())}
        with patch.dict(preservation.PINS, pin, clear=True):
            self.assertTrue(preservation.preserves_r7_r8(rom, BASE + 0x200))
            (line,) = proof.loop_replay_lines()
            self.assertIn("proved none; trusted 0x08000200:r5;", line)  # only r7/r8 can be proved
            seven = counted(4).replace("push {r4, r5, r6, lr}", "push {r4, r6, r7, lr}") \
                .replace("pop {r4, r5, r6}", "pop {r4, r6, r7}").replace("r5", "r7")
            (line,) = self.fixture(seven, frame=8).loop_replay_lines()
            self.assertIn("proved 0x08000200:r7; trusted none;", line)
        (line,) = self.fixture(seven, frame=8).loop_replay_lines()
        self.assertIn("proved none; trusted 0x08000200:r7;", line)
        with patch.dict(preservation.PINS, pin, clear=True):
            self.assertFalse(preservation.preserves_r7_r8(rom[:0x200] + b"\x70\x46" + rom[0x202:], BASE + 0x200))
            for body in ("movs r7, #0\nbx lr", "push {r7, lr}\npop {r7, pc}", "mov r8, r0\nbx lr",
                         "bl 1f\nbx lr\n1:\nbx lr", "svc 1\nbx lr", "mov pc, r0"):
                with self.subTest(body=body):
                    self.fixture(counted(4), frame=8, child=body)
                    rom = (self.root / "baserom.bin").read_bytes()
                    entry = json.loads(self.mapping)[2]
                    child = rom[int(entry["rom"], 16) - BASE:int(entry["end"], 16) - BASE]
                    pins = {int(entry["rom"], 16): (int(entry["end"], 16),
                                                    hashlib.sha256(child).hexdigest(), ())}
                    with patch.dict(preservation.PINS, pins, clear=True):
                        self.assertFalse(preservation.preserves_r7_r8(rom, int(entry["rom"], 16)))

    def test_preservation_proof_follows_reachability_and_refuses_pc_escapes(self):
        import hashlib
        import struct
        import callee_preservation_profile as preservation
        words = lambda *w: b"".join(struct.pack("<H", x) for x in w)

        def pinned(body, tables=(), rom_extra=b""):
            rom = bytearray(0x400)
            rom[0x100:0x100 + len(body)] = body
            pin = {BASE + 0x100: (BASE + 0x100 + len(body), hashlib.sha256(body).hexdigest(), tables)}
            with patch.dict(preservation.PINS, pin, clear=True):
                return preservation.preserves_r7_r8(bytes(rom), BASE + 0x100)
        self.assertFalse(pinned(words(0x4700)))                       # bx r0
        self.assertFalse(pinned(words(0x4487, 0x4770)))               # add pc, r0
        self.assertFalse(pinned(words(0xBD00)))                       # pop {pc} without a pushed lr
        self.assertFalse(pinned(words(0x2000)))                       # falls off the span end
        self.assertFalse(pinned(words(0x4800, 0x2000, 0x0000, 0x2700, 0x0000)))  # falls into a literal word
        self.assertFalse(pinned(words(0x468F, 0x4770) + struct.pack("<I", BASE + 0x102),
                                ((BASE + 0x104, 1),)))                # stray mov pc, r1 beside a table
        self.assertFalse(pinned(words(0xB500, 0xBC08, 0x4708)))       # pop {r3}; bx r1
        self.assertTrue(pinned(words(0xB500, 0xBD00)))                # push {lr}; pop {pc}
        self.assertTrue(pinned(words(0xB500, 0xBC08, 0x4718)))        # push {lr}; pop {r3}; bx r3
        self.assertFalse(pinned(words(0xB500, 0xBC08, 0xE7FD, 0x4718)))  # branch into the return pair
        self.assertFalse(pinned(words(0x2700, 0x4770)))
        self.assertTrue(pinned(words(0xE000, 0x2700, 0x4770)))        # dead r7 write is never reached

    def test_preservation_proof_is_armv4t_and_controls_sp_lr_and_the_switch_guard(self):
        import hashlib
        import struct
        import callee_preservation_profile as preservation
        words = lambda *w: b"".join(struct.pack("<H", x) for x in w)
        pool = lambda *w: b"".join(struct.pack("<I", x) for x in w)
        at = BASE + 0x100

        def pinned(body, tables=()):
            rom = bytearray(0x400)
            rom[0x100:0x100 + len(body)] = body
            with patch.dict(preservation.PINS, {at: (at + len(body), hashlib.sha256(body).hexdigest(), tables)}):
                return preservation.preserves_r7_r8(bytes(rom), at)

        def bcc(cc, source, target):
            return 0xD000 | (cc << 8) | (((target - (source + 4)) >> 1) & 0xFF)

        def switch(case, entries=(0x1C, 0x20), tail=b"", bound=1):
            body = words(0xB500, 0x2800 | bound, bcc(8, 4, 0x1C), 0x0080, 0x4901, 0x1840, 0x6800, 0x4687)
            body += pool(at + 0x14) + pool(*(at + e for e in entries)) + words(0xBC01, 0x4700) + case + tail
            return body, ((at + 0x14, len(entries)),)
        done = words(0xBC01, 0x4700)                                     # pop {r0}; bx r0
        self.assertTrue(pinned(*switch(done)))
        # Not ARMv4T: capstone's Thumb-2 decode of F000 0007 is and.w, the ARM7TDMI runs BL prefix + lsls r7.
        for odd in ((0xF000, 0x0007), (0xF000, 0x0807), (0xF04F, 0x0701), (0xF000, 0xE800), (0xF000, 0xD000),
                    (0xB108,), (0xDE00,), (0xBE00,), (0xBF08,), (0xBF00,), (0xB662,), (0x4608,)):
            with self.subTest(odd=odd):
                self.assertFalse(pinned(words(0xB500, *odd, 0xBC01, 0x4700)))
        self.assertFalse(pinned(words(0xB500, 0x4800, 0xF7FF, 0xFFFD, 0xBC01, 0x4700)))   # BL half in a literal
        # A branch cannot start an instruction inside the second half of a BL.
        self.assertFalse(pinned(words(0xB500, 0xF000, 0xF800, 0xE7FD, 0xBC01, 0x4700)))
        # PC control.
        guard_loop = words(0x2006, 0x4292, bcc(0, 0x24, 0x04), 0xBC01, 0x4700, 0x0000)
        evil = pool(at + 0x30 | 1) + words(0x2701, 0xBC01, 0x4700)
        self.assertFalse(pinned(*switch(guard_loop, tail=evil)))         # beq back to the bhi, index 6
        self.assertFalse(pinned(*switch(done, entries=(0x1C, 0x04))))    # table entry on the guard
        self.assertFalse(pinned(*switch(done, entries=(0x1C, 0x02))))    # table entry on the cmp
        self.assertFalse(pinned(*switch(done, entries=(0x1C, 0x0A))))    # table entry inside the idiom
        self.assertFalse(pinned(*switch(done, entries=(0x1C, 0x21))))    # odd entry: mov pc drops bit 0
        body, tables = switch(done)
        self.assertFalse(pinned(body.replace(words(0x6800), words(0x5840)), tables))   # ldr r0,[r0,r1]
        self.assertFalse(pinned(words(0xB410, 0xBC10, 0x4770)))          # push {r4}; pop {r4}; bx lr
        # SP and LR.
        self.assertTrue(pinned(words(0xB510, 0xBC10, 0xBC02, 0x4708)))   # push {r4,lr}; pop {r4}; pop {r1}; bx r1
        self.assertTrue(pinned(words(0xB510, 0xBD10)))                   # push {r4,lr}; pop {r4,pc}
        for odd in (words(0xB510, 0xBC02, 0x4708),                       # pop {r1} takes the saved r4
                    words(0x2000, 0xB500, 0xBC02, 0x4708),               # push later than the entry
                    words(0xB500, 0xB001, 0xBD00), words(0xB500, 0xB081, 0xBD00),   # add/sub sp
                    words(0xB500, 0x9000, 0xBD00), words(0xB500, 0x4668, 0xBD00),   # str [sp]; mov r0, sp
                    words(0xB500, 0xBC01, 0xBD00),                       # pop {r0}; pop {pc}
                    words(0xB500, 0xBC01),                               # pop {r0} falls off
                    words(0xB510, 0xBD00),                               # pop {pc} takes the saved r4
                    words(0xB500, 0x4686, 0xBC02, 0x4708),               # mov lr, r0
                    words(0xB500, 0x4770),                               # bx lr with the entry frame pushed
                    words(0xF7FF, 0xFFFF, 0x4770),                       # bl then bx lr (lr clobbered)
                    words(0x4686, 0x4770),                               # mov lr, r0; bx lr
                    words(0xB510, bcc(0, 2, 6), 0xBC10, 0xBD10)):         # paths reaching one address at two depths
            with self.subTest(body=odd.hex()):
                self.assertFalse(pinned(odd))

    def test_preservation_switch_bound_must_agree_with_code_table_and_pin(self):
        import callee_preservation_profile as preservation
        path = ROOT.parent / "fftadecomp" / "baserom.bin"
        if not path.exists():
            self.skipTest("no real ROM next to the kit")
        rom = path.read_bytes()
        for address, table, count in ((0x080C7EA4, 0x080C7EC0, 69), (0x080CA7A4, 0x080CA7CC, 19)):
            end, digest, _ = preservation.PINS[address]
            for tables in (((table, count),), ((table, count - 1),), ((table, count + 1),), ((table + 4, count),), ()):
                with self.subTest(address=address, tables=tables), \
                        patch.dict(preservation.PINS, {address: (end, digest, tables)}):
                    self.assertEqual(preservation.preserves_r7_r8(rom, address), tables == ((table, count),))

    def test_real_pinned_callees_are_proved_and_a_changed_byte_is_not(self):
        import callee_preservation_profile as preservation
        path = ROOT.parent / "fftadecomp" / "baserom.bin"
        if not path.exists():
            self.skipTest("no real ROM next to the kit")
        rom = path.read_bytes()
        for address in (0x080C7EA4, 0x080CA7A4, 0x080C95A8):
            with self.subTest(address=address):
                self.assertTrue(preservation.preserves_r7_r8(rom, address))
                offset = address - match.ROM_BASE + 2
                changed = rom[:offset] + bytes([rom[offset] ^ 1]) + rom[offset + 1:]
                self.assertFalse(preservation.preserves_r7_r8(changed, address))
        self.assertFalse(preservation.preserves_r7_r8(rom, 0x0812E4F4))

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
