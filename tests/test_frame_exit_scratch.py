"""R2/R3 own-frame addresses at a frame-buffer owner's normal returns.

The function-literal owner's projection (function_literal_exit_scratch_profile, kind FUNCTION) is
shared with the plain stack-argument owner (kind FRAME): the gates are checked on a bound proof
directly, and natural C callers compiled with the fixed agbcc and `-mthumb-interwork -O2` beside
assembled callees (test_data_buffer_calls.build) are run through match.py and replayed.
"""
import ast
import json
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
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import data_buffer_profile as data_buffer
import function_literal_exit_scratch_profile as function_exit
from test_data_buffer_calls import A, BUFFER_ONLY, PLAIN, STORES, build, run, tools_present, verification
from test_function_literal_exit_scratch import ESCAPE, LEAVES, OWN, RETURN, SITE, bound
from test_dma_fill import check_report

R = match.ARM_REG_R0


def frame(proof_type=match.BufferCallProof):
    proof, data = bound(proof_type)
    proof._function_exit_kind = function_exit.FRAME
    return proof, data


class FrameHookTests(unittest.TestCase):
    def test_projects_r2_r3_own_frame_at_the_root_return(self):
        proof, data = frame()
        held = {R + 3: -20, R + 2: -24, R + 12: -8}
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, held), {R + 12: -8})
        function_exit.record(proof, A)
        self.assertEqual(proof.function_exit_scratch["kind"], function_exit.FRAME)
        (line,) = function_exit.lines(proof)
        self.assertTrue(line.startswith(function_exit.FRAME_LINE + ": `thumb-discarded-exit-scratch-v1` premise"))
        self.assertIn(f"`0x{RETURN:08X} r2 -24`, `0x{RETURN:08X} r3 -20`", line)
        payload = json.loads(function_exit.fingerprint_payload(proof))
        self.assertEqual(payload[0], "frame-buffer-exit-scratch-v1")

    def test_the_stack_index_retry_is_bound_too(self):
        proof, data = frame()
        proof.index_policy = object()
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, {R + 3: -20}), {})

    def test_the_function_literal_kind_is_unchanged(self):
        proof, data = bound()
        function_exit.aliases(proof, data, A, RETURN, {R + 3: -20})
        function_exit.record(proof, A)
        self.assertNotIn("kind", proof.function_exit_scratch)
        self.assertTrue(function_exit.lines(proof)[0].startswith(function_exit.LINE + ": "))
        self.assertEqual(json.loads(function_exit.fingerprint_payload(proof))[0], "function-literal-exit-scratch-v1")

    def test_every_other_proof_keeps_the_refusal(self):
        held = {R + 3: -20}

        class Derived(match.BufferCallProof):
            pass
        for name, proof_type in (("function-literal proof", match.FunctionBufferCallProof),
                                 ("subclass", Derived)):
            with self.subTest(name):
                proof, data = frame(proof_type)
                self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = frame()
        proof.stack_arguments = False
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = frame()
        with patch.object(function_exit.FRAME_POLICY, "enabled", False):
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = frame()
        proof._function_exit_kind = "other"
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = frame()
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, {R + 0: -20}), {R + 0: -20})
        # R1 is the frame result r1 rule's: without the ROM's caller evidence it refuses, saying why.
        import frame_result_r1_profile as frame_r1
        with patch.object(frame_r1.POLICY, "enabled", False):
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, {R + 1: -20}), {R + 1: -20})
        with self.assertRaisesRegex(ValueError, r"escapes through a return register \(R1: "):
            function_exit.aliases(proof, data, A, RETURN, {R + 1: -20})

    def test_a_split_state_return_keeps_the_refusal_only_for_the_frame_owner(self):
        held = {R + 3: -20}
        proof, data = frame()
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held), split_state=True), held)
        proof.split_joins[(A, RETURN - 8, R + 3, -20, -24)] = None
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), {})
        function_exit.record(proof, A)                  # a merged-state projection beside a split is kept
        self.assertTrue(proof.function_exit_scratch)
        proof, data = bound()
        proof.split_joins[(A, RETURN - 8, R + 3, -20, -24)] = None
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)

    def test_walk_binds_only_the_plain_stack_argument_proof(self):
        rom, mapping = bytes(0x1000), "[]"
        for proof, expected in ((match.BufferCallProof(rom, mapping, stack_arguments=True), True),
                                (match.BufferCallProof(rom, mapping), False),
                                (match.FunctionBufferCallProof(rom, mapping, stack_arguments=True), False)):
            with self.subTest(type(proof).__name__, stack_arguments=proof.stack_arguments):
                self.assertEqual(function_exit.walk(proof, b"\0\0", A, mapping, lambda: "walked",
                                                    kind=function_exit.FRAME), "walked")
                self.assertEqual(getattr(proof, "_function_exit_root", None) is not None, expected)

    def test_every_plain_default_walk_and_replay_is_wrapped(self):
        found = set()
        for path in sorted((ROOT / "tools").glob("*.py")):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    for node in ast.walk(function):
                        if isinstance(node, ast.Call) and any(
                                keyword.arg == "kind" and ast.unparse(keyword.value).endswith("function_exit.FRAME")
                                for keyword in node.keywords):
                            found.add((path.name, function.name))
        self.assertEqual(found, {("match.py", "main"), ("match_evidence.py", "buffer_report_matches"),
                                 ("data_buffer_profile.py", "prove"), ("function_thunk_profile.py", "verify_source")})


class WiringTests(unittest.TestCase):
    def test_the_owner_walk_says_when_a_return_is_in_a_split_state(self):
        import ast
        calls = [node for node in ast.walk(ast.parse((ROOT / "tools/match.py").read_text()))
                 if isinstance(node, ast.Call) and ast.unparse(node.func) == "function_exit.aliases"]
        self.assertEqual([[ast.unparse(keyword.value) for keyword in call.keywords if keyword.arg == "split_state"]
                          for call in calls], [["split_joins is not None and isinstance(state_key, split_join.Key)"]])

    def test_a_path_state_walk_reaches_the_return_hook_as_a_merged_state(self):
        # The exact-alias path-state walk keeps no split joins and binds no state_key: a clean
        # return passes the hook, and a frame address in R0 still refuses there.
        def proof():
            proof = match.BufferCallProof(bytes(0x1000), "[]", stack_arguments=True)
            proof.callee_frames, proof.exact_alias_state_budget = True, 16
            return proof
        match.verify_leaf_instructions(bytes.fromhex("81b001b07047"), A, True, buffer_proof=proof())
        with self.assertRaisesRegex(ValueError, "local stack pointer escapes through a return register"):
            match.verify_leaf_instructions(bytes.fromhex("81b0684601b07047"), A, True, buffer_proof=proof())


# A local chosen at a join (the walk keeps it apart), then a last call that leaves `first` in R2/R3.
SPLIT_THEN_MERGED = """typedef unsigned short u16;
extern void func_08000400(u16 value, u16 *out);
u16 func_08000200(u16 value)
{
    u16 first[4];
    u16 second[4];
    u16 *chosen;

    func_08000400(value, first);
    func_08000400(value, second);
    chosen = value ? first : second;
    value = chosen[1];
    func_08000400(value, first);
    return value + first[3];
}
"""


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class FrameExitScratchNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="frame_exit_scratch_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, name, worker, source):
        return build(self.base / name, source, [("func_08000400", worker)])

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def scratch(self, report):
        return [line for line in report.splitlines() if line.startswith(function_exit.FRAME_LINE)]

    def prove(self, root):
        from test_data_buffer_calls import DataBufferNativeTests
        body, rom, mapping, objects, calls, literals, functions = DataBufferNativeTests.linked(self, root)
        return lambda: data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)

    def test_frame_buffer_owner_drops_its_exit_scratch(self):
        root = self.fixture("plain", LEAVES, BUFFER_ONLY)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.STACK_BUFFER_SCHEMA)
        (line,) = self.scratch(report)
        self.assertTrue(SITE.search(line), line)
        self.assertTrue(self.replays(report, root))
        # The line is bound: a dropped or altered line does not replay.
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        self.assertFalse(self.replays(report.replace(line, re.sub(r" -(\d+)`", r" -4\1`", line)), root))
        code, output = check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)

    def test_data_buffer_plain_owner_drops_its_exit_scratch(self):
        root = self.fixture("data", LEAVES, PLAIN % dict(size=4, last=3, extra=""))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.SCHEMA)
        (line,) = self.scratch(report)
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        prove = self.prove(root)
        proof = prove()[1]
        self.assertEqual(proof.function_exit_scratch["kind"], function_exit.FRAME)
        fingerprint = proof.fingerprint()
        proof.function_exit_scratch = None
        self.assertNotEqual(proof.fingerprint(), fingerprint)
        with patch.object(function_exit.FRAME_POLICY, "enabled", False), self.assertRaisesRegex(ValueError, ESCAPE):
            prove()

    def test_a_split_then_merged_owner_projects_and_replays(self):
        # chosen = value ? first : second splits at its join; the last call rewrites the scratch register that
        # held it, so the return is reached in a merged state, where the worker left `first` in R2/R3.
        root = self.fixture("split", LEAVES, SPLIT_THEN_MERGED)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.STACK_BUFFER_SCHEMA)
        lines = report.splitlines()
        (split,) = [line for line in lines if line.startswith("* buffer split join: ")]
        (line,) = self.scratch(report)
        self.assertTrue(SITE.search(line), line)
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        self.assertFalse(self.replays(report.replace(split + "\n", ""), root))
        code, output = check_report(root)
        self.assertEqual(code, 0, output)
        self.assertIn("report  identical to the saved", output)

    def test_owner_without_exit_scratch_is_unchanged(self):
        root = self.fixture("none", STORES, PLAIN % dict(size=4, last=3, extra=""))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertFalse(self.scratch(report))
        self.assertIsNone(getattr(self.prove(root)()[1], "function_exit_scratch", None))

    def test_callee_return_keeps_its_refusal(self):
        # The callee leaves an address of its own frame in R3.  The released-scratch rule hands it back to
        # the owner as a released address (released_scratch_profile.callee_return), and the owner's return
        # still holds it, so the owner's return refuses, with the frame policy on or off: the frame rule
        # drops only the owner's own frame addresses.  Without the released-scratch rule the callee's own
        # return refuses, as before.
        import released_scratch_profile as released
        prove = self.prove(self.fixture("own", OWN, PLAIN % dict(size=4, last=3, extra="")))
        with self.assertRaises(ValueError) as on:
            prove()
        with patch.object(function_exit.FRAME_POLICY, "enabled", False), self.assertRaises(ValueError) as off:
            prove()
        self.assertEqual(str(on.exception), str(off.exception))
        self.assertEqual(str(on.exception), ESCAPE)
        with patch.object(released, "callee_return", lambda proof, address, site, aliases, **_: aliases), \
                self.assertRaises(ValueError) as unreleased:
            prove()
        self.assertIn("buffer callee 0x08000400", str(unreleased.exception))
        self.assertIn(ESCAPE, str(unreleased.exception))


if __name__ == "__main__":
    unittest.main()
