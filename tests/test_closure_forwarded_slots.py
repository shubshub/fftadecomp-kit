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
