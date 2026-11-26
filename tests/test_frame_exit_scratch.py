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
        for register in (R + 0, R + 1):
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, {register: -20}), {register: -20})

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

    def test_owner_without_exit_scratch_is_unchanged(self):
        root = self.fixture("none", STORES, PLAIN % dict(size=4, last=3, extra=""))
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertFalse(self.scratch(report))
        self.assertIsNone(getattr(self.prove(root)()[1], "function_exit_scratch", None))

    def test_callee_return_keeps_its_refusal(self):
        prove = self.prove(self.fixture("own", OWN, PLAIN % dict(size=4, last=3, extra="")))
        with self.assertRaises(ValueError) as on:
            prove()
        with patch.object(function_exit.FRAME_POLICY, "enabled", False), self.assertRaises(ValueError) as off:
            prove()
        self.assertEqual(str(on.exception), str(off.exception))
        self.assertIn("buffer callee 0x08000400", str(on.exception))


if __name__ == "__main__":
    unittest.main()
