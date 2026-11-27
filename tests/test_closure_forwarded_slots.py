"""Forwarded buffer pointer slots (forwarded_slot_profile) composed with closure words
(closure_slot_profile): a forwarding store made inside a closure-slot walk refuses, the plain forwarding
walk beside it is tracked, and a word walk's callee result keeps its type through import_released."""
import os
from pathlib import Path
import sys
import tempfile
import types
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import closure_slot_profile as closure
import forwarded_slot_profile as forwarded
import protected_descriptor_word_profile as descriptor
from test_data_buffer_calls import build, run, tools_present
from test_call_via_targets import index_thunks
import test_closure_slots as cs

R2T = match.RUNTIME_HELPERS["_call_via_r2"]
SLOT_REFUSAL = "unsupported buffer pointer use or escape"


def forwarding_adapter():
    """The adapter forwards the pointer it reloaded from the closure (&found) to the callback as its fifth
    (stack) argument: a forwarding store made inside a closure-slot walk."""
    return (f"push {{r4, lr}}\nadds r4, r1, #0\nbl 0x08000600\nldr r1, [r4]\nsub sp, #8\nstr r1, [sp]\n"
            f"ldr r2, [r4, #4]\nbl 0x{R2T:08X}\nadd sp, #8\npop {{r4}}\npop {{r1}}\nbx r1")


CB_STACK = "ldr r3, [sp]\nmovs r2, #1\nstr r2, [r3]\nmovs r0, #1\nbx lr"          # writes found through arg 5
CB_STACK_FAR = "ldr r3, [sp]\nmovs r2, #1\nstr r2, [r3, #64]\nmovs r0, #1\nbx lr"  # 64 bytes past found
# After its closure walk (words live) the owner hands &found to a coordinate-wrapper shape that forwards
# it as its own callee's fifth argument.
OWNER_FWD = (cs.HEAD + "extern void func_08000A00(u32 *p);\n" + cs.OWNER[len(cs.HEAD):]).replace(
    "    return found;", "    func_08000A00(&found);\n    return found;")
WRAP = "push {lr}\nsub sp, #8\nstr r0, [sp]\nbl 0x08000B00\nadd sp, #8\npop {r0}\nbx r0"
LEAF_IN = "ldr r1, [sp]\nmovs r0, #0\nstr r0, [r1]\nbx lr"
LEAF_FAR = "ldr r1, [sp]\nmovs r0, #0\nstr r0, [r1, #64]\nbx lr"
# The control: the same forwarding call with no closure (the plain forwarding walk only).
PLAIN_FWD = """typedef unsigned int u32;
extern void func_08000A00(u32 *p);
u32 func_08000200(void)
{
    u32 found;

    found = 1;
    func_08000A00(&found);
    return found;
}
"""


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class ForwardingInsideClosureRetryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="closure_forwarded_", dir=scratch)
        cls.base = Path(cls.temporary.name)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def case(self, name, source, callee_list):
        root = index_thunks(build(self.base / name, source, callee_list, large=True, function_literal_thunks=True))
        return run(root)

    def refused_in_retry(self, name, source, callee_list):
        code, output, report = self.case(name, source, callee_list)
        self.assertNotEqual(code, 0, report)
        self.assertIn(f"{closure.TRIGGER}; closure-slot retry: ", output)
        self.assertIn(SLOT_REFUSAL, output.split("closure-slot retry: ", 1)[1])

    def test_w0_plain_forwarding_is_tracked(self):
        code, output, report = self.case("w0", PLAIN_FWD, cs.callees() + [("func_08000A00", WRAP),
                                                                         ("func_08000B00", LEAF_IN)])
        self.assertEqual(code, 0, output[-3000:])
        self.assertTrue(any(line.startswith(forwarded.SLOTS_FIELD) for line in report.splitlines()))

    def test_w0b_plain_forwarding_out_of_bounds_refuses(self):
        code, output, report = self.case("w0b", PLAIN_FWD, cs.callees() + [("func_08000A00", WRAP),
                                                                           ("func_08000B00", LEAF_FAR)])
        self.assertNotEqual(code, 0, report)

    def test_w1_adapter_forwarding_a_closure_pointer_refuses(self):
        for name, callback in (("w1", CB_STACK), ("w1b", CB_STACK_FAR)):
            with self.subTest(name):
                self.refused_in_retry(name, cs.OWNER, cs.callees(adapter_body=forwarding_adapter(), callback=callback))

    def test_w2_owner_forwarding_call_while_closure_words_are_live_refuses(self):
        for name, leaf in (("w2", LEAF_IN), ("w2b", LEAF_FAR)):
            with self.subTest(name):
                self.refused_in_retry(name, OWNER_FWD, cs.callees() + [("func_08000A00", WRAP),
                                                                        ("func_08000B00", leaf)])


class ImportReleasedTests(unittest.TestCase):
    def test_a_word_result_keeps_its_type_and_words(self):
        stale = match.FORWARD_STALE_BASE - 8
        for kind in (closure.WordResult, descriptor.WordResult):
            with self.subTest(kind.__module__):
                proof = types.SimpleNamespace(forward_releases={})
                result = kind({match.ARM_REG_R0: -16, stale: -24}, {-8: ("pointer", -16)})
                aliases = {}
                kept = forwarded.import_released(proof, aliases, result, 2, 0x08000210, True)
                self.assertIs(type(kept), kind)
                self.assertEqual(dict(kept), {match.ARM_REG_R0: -16})
                self.assertEqual(kept.words, result.words)
                self.assertEqual(aliases, {match.FORWARD_STALE_BASE - 16: -24})
                self.assertEqual(proof.forward_releases, {0x08000210: {-16}})


if __name__ == "__main__":
    unittest.main()
