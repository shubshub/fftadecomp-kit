"""R2/R3 own-frame addresses at a function-literal owner's normal returns (T3).

The return hook's gates are checked on a bound proof directly; natural C callers compiled with the
fixed agbcc and `-mthumb-interwork -O2` and linked at 0x08000200 beside assembled callees
(test_data_buffer_calls.build) are run through match.py on the default path and replayed.
"""
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
import released_scratch_profile as released_scratch
import match_evidence as evidence
import data_buffer_profile as data_buffer
import function_literal_exit_scratch_profile as function_exit
from test_data_buffer_calls import A, LITERAL, STORES, build, run, tools_present, verification

R = match.ARM_REG_R0
RETURN = A + 0x10
ESCAPE = "local stack pointer escapes through a return register"
# The callee fills its caller's buffer and leaves the buffer's address in R2 and R3; the caller's
# walk carries it to its own return.
LEAVES = "strh r0, [r1]\nstrh r0, [r1, #6]\nadds r2, r1, #0\nadds r3, r1, #0\nbx lr"
# The callee leaves an address of its own frame in R3: that is the callee's return, not the owner's.
OWN = ("push {lr}\nsub sp, #8\nadd r3, sp, #0\nstrh r0, [r1]\nstrh r0, [r1, #6]\nadd sp, #8\n"
       "pop {r0}\nbx r0")
# No typed data: the function-buffer proof (verify_function_buffers).
PLAIN = """typedef unsigned short u16;
extern void func_08000500(void);
extern void func_08000400(u16 value, u16 *out, void (*callback)(void));
u16 func_08000200(u16 value)
{
    u16 buffer[4];

    func_08000400(value, buffer, func_08000500);
    return buffer[0] + buffer[3];
}
"""
SITE = re.compile(r"`0x[0-9A-F]{8} r[23] -\d+`")


def bound(proof_type=match.FunctionBufferCallProof):
    """A proof bound to a root at A whose one normal return is RETURN."""
    rom = bytes(0x1000)
    mapping = json.dumps([{"rom": f"0x{A:08X}", "end": f"0x{A + 0x20:08X}", "mode": "thumb"}])
    proof = proof_type(rom, mapping, stack_arguments=True)
    data = rom[A - match.ROM_BASE:A - match.ROM_BASE + 0x20]
    proof._function_exit_root = (A, data, mapping)
    proof._function_exit_bound = True
    proof._return_root = (A, data, frozenset({RETURN}))
    proof._return_scratch = {}
    proof._return_scratch_joins = set()
    return proof, data


class HookTests(unittest.TestCase):
    def test_projects_r2_r3_own_frame_at_the_root_return(self):
        proof, data = bound()
        held = {R + 3: -20, R + 2: -24, R + 12: -8}
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, held), {R + 12: -8})
        self.assertEqual(proof._return_scratch, {RETURN: ((2, -24), (3, -20))})
        function_exit.record(proof, A)
        self.assertEqual(proof.function_exit_scratch["sites"], [[RETURN, 2, -24], [RETURN, 3, -20]])
        (line,) = function_exit.lines(proof)
        self.assertTrue(line.startswith(function_exit.LINE + ": `thumb-discarded-exit-scratch-v1` premise"))
        self.assertIn(f"`0x{RETURN:08X} r2 -24`, `0x{RETURN:08X} r3 -20`", line)
        self.assertIsNotNone(function_exit.fingerprint_payload(proof))

    def test_every_other_alias_keeps_the_refusal(self):
        cases = {
            "result register": ({R + 0: -20}, A, RETURN),
            "result beside scratch": ({R + 1: -20, R + 3: -24}, A, RETURN),
            "positive offset": ({R + 3: 4}, A, RETURN),
            "not a normal return": ({R + 3: -20}, A, RETURN - 2),
            "another function": ({R + 3: -20}, A + 2, RETURN),
            "callee-saved register": ({R + 4: -20}, A, RETURN),
        }
        for name, (held, address, site) in cases.items():
            with self.subTest(name):
                proof, data = bound()
                result = function_exit.aliases(proof, data, address, site, dict(held))
                if name == "result beside scratch":
                    self.assertEqual(result, {R + 1: -20})   # R1 still refuses the walk
                else:
                    self.assertEqual(result, held)

    def test_unbound_and_other_proofs_keep_the_refusal(self):
        held = {R + 3: -20}
        proof, data = bound()
        proof.active.add(0x08000400)        # inside a callee walk
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = bound()
        proof.split_joins[(A, RETURN, R + 3, -20, -24)] = None
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = bound()
        proof.index_policy = object()
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = bound()
        with patch.object(function_exit.POLICY, "enabled", False):
            self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)

        class Derived(match.FunctionBufferCallProof):
            pass
        for proof_type in (match.BufferCallProof, Derived):
            with self.subTest(proof_type.__name__):
                proof, data = bound(proof_type)
                self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
        proof, data = bound()
        proof._function_exit_root = None    # walk() was not run for this proof
        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)

    def test_record_refuses_joins_and_split_walks(self):
        proof, data = bound()
        function_exit.aliases(proof, data, A, RETURN, {R + 3: -20})
        proof._return_scratch_joins.add((RETURN, 3, -24, -20))
        with self.assertRaisesRegex(ValueError, "projects no joins"):
            function_exit.record(proof, A)
        proof, data = bound()
        function_exit.aliases(proof, data, A, RETURN, {R + 3: -20})
        proof.split_joins[(A, RETURN, R + 3, -20, -24)] = None
        with self.assertRaisesRegex(ValueError, "kept a join apart"):
            function_exit.record(proof, A)
        proof, _ = bound()
        function_exit.record(proof, A)
        self.assertIsNone(proof.function_exit_scratch)
        self.assertEqual((function_exit.lines(proof), function_exit.fingerprint_payload(proof)), ([], None))

    def test_binding_requires_complete_normal_returns_without_local_control(self):
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        returns = {"returns": [f"0x{RETURN:08X}"]}
        cases = {
            "plain": (returns, ({RETURN: ()}, {}, {}), True),
            "local BL": (returns, ({RETURN: ()}, {A + 4: A + 8}, {}), False),
            "switch words": (returns, ({RETURN: ()}, {}, {8: 0}), False),
            "no return": ({"returns": []}, ({}, {}, {}), False),
            "return with successors": (returns, ({RETURN: (RETURN + 2,)}, {}, {}), False),
        }
        for name, (refinement, (edges, branches, words), expected) in cases.items():
            with self.subTest(name):
                proof, data = bound()
                proof._function_exit_bound = False
                proof._return_root = None
                with patch.object(owner, "refine", return_value=refinement), \
                        patch.object(graph, "graph", return_value=(None, edges, branches, None, words)):
                    self.assertIs(function_exit._bind(proof), expected)
                self.assertEqual(proof._return_root is not None, expected)
                held = {R + 3: -20}
                if not expected:
                    proof._return_root = None
                    with patch.object(owner, "refine", return_value=refinement), \
                            patch.object(graph, "graph", return_value=(None, edges, branches, None, words)):
                        self.assertEqual(function_exit.aliases(proof, data, A, RETURN, dict(held)), held)
                    self.assertIsNone(proof._function_exit_root)
        proof, data = bound()
        proof._function_exit_bound = False
        proof._return_root = None
        with patch.object(owner, "refine", side_effect=ValueError("unrefinable")):
            self.assertFalse(function_exit._bind(proof))

    def test_walk_binds_only_eligible_proofs(self):
        rom = bytes(0x1000)
        mapping = "[]"
        for proof, expected in ((match.FunctionBufferCallProof(rom, mapping, stack_arguments=True), True),
                                (match.BufferCallProof(rom, mapping, stack_arguments=True), False)):
            with self.subTest(type(proof).__name__):
                self.assertEqual(function_exit.walk(proof, b"\0\0", A, mapping, lambda: "walked"), "walked")
                self.assertEqual(getattr(proof, "_function_exit_root", None) is not None, expected)
                self.assertFalse(hasattr(proof, "function_exit_scratch"))


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class ExitScratchNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="function_exit_scratch_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def fixture(self, name, worker, source=None):
        return build(self.base / name, source or LITERAL % dict(extra=""),
                     [("func_08000400", worker), ("func_08000500", "bx lr")], large=True)

    def replays(self, report, root):
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            return evidence.report_matches(report, root, A)

    def scratch(self, report):
        return [line for line in report.splitlines() if line.startswith(function_exit.LINE)]

    def prove(self, root):
        from test_data_buffer_calls import DataBufferNativeTests
        body, rom, mapping, objects, calls, literals, functions = DataBufferNativeTests.linked(self, root)
        return lambda: data_buffer.prove(body, A, rom, mapping, objects, calls, literals, functions)

    def test_data_buffer_owner_drops_its_exit_scratch(self):
        root = self.fixture("data", LEAVES)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), data_buffer.FUNCTION_SCHEMA)
        (line,) = self.scratch(report)
        self.assertTrue(SITE.search(line), line)
        self.assertTrue(self.replays(report, root))
        # The line is bound: a dropped or altered line does not replay.
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))
        self.assertFalse(self.replays(report.replace(line, re.sub(r" -(\d+)`", r" -4\1`", line)), root))
        prove = self.prove(root)
        proof = prove()[1]
        self.assertTrue(proof.function_exit_scratch)
        fingerprint = proof.fingerprint()
        proof.function_exit_scratch = None
        self.assertNotEqual(proof.fingerprint(), fingerprint)
        with patch.object(function_exit.POLICY, "enabled", False), self.assertRaisesRegex(ValueError, ESCAPE):
            prove()

    def test_function_buffer_owner_drops_its_exit_scratch(self):
        root = self.fixture("plain", LEAVES, PLAIN)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertEqual(verification(report), evidence.FUNCTION_BUFFER_SCHEMA)
        (line,) = self.scratch(report)
        self.assertTrue(SITE.search(line), line)
        self.assertTrue(self.replays(report, root))
        self.assertFalse(self.replays(report.replace(line + "\n", ""), root))

    def test_owner_without_exit_scratch_is_unchanged(self):
        root = self.fixture("none", STORES)
        code, output, report = run(root)
        self.assertEqual(code, 0, output)
        self.assertFalse(self.scratch(report))
        self.assertIsNone(getattr(self.prove(root)()[1], "function_exit_scratch", None))

    def test_callee_return_keeps_its_refusal(self):
        root = self.fixture("own", OWN)
        prove = self.prove(root)
        with self.assertRaises(ValueError) as on:
            prove()
        with patch.object(function_exit.POLICY, "enabled", False), self.assertRaises(ValueError) as off:
            prove()
        self.assertEqual(str(on.exception), str(off.exception))
        # The callee's own frame in R3 is handed back released (released_scratch_profile) and refuses
        # where it reaches the owner's return, which this rule does not project either.
        self.assertIn("local stack pointer escapes through a return register", str(on.exception))
        with patch.object(released_scratch, "callee_return", lambda proof, address, site, aliases, **_: aliases), \
                self.assertRaisesRegex(ValueError, "buffer callee 0x08000400"):
            prove()
        # This rule never drops the released marker at the owner's return: no report, or one without
        # an exit-scratch line.
        code, output, report = run(root)
        self.assertNotEqual(code, 0, output)
        self.assertTrue(report is None or not self.scratch(report), report)


if __name__ == "__main__":
    unittest.main()
