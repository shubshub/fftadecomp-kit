"""IP scratch aliases remain tracked without being classified as ABI results."""
import unittest

import test_buffer_index as fixtures

match = fixtures.match
BASE = fixtures.BASE


class StackScratchReturnTests(unittest.TestCase):
    setUp = fixtures.BufferIndexTests.setUp
    fixture = fixtures.BufferIndexTests.fixture

    def caller(self, after="", result=None, return_register="r0"):
        return ("push {lr}\nsub sp, #8\nmov r0, sp\nmov ip, r0\n"
                "movs r0, #0\nbl callee\n" + after +
                (f"mov {result}, ip\n" if result else "") +
                f"add sp, #8\npop {{{return_register}}}\nbx {return_register}")

    def test_unobserved_ip_scratch_at_return_passes_inspected_buffer_proof(self):
        proof = self.fixture("", caller=self.caller(), callee="bx lr")
        self.assertEqual(set(proof.dependencies), {BASE + 0x100})
        with self.assertRaisesRegex(ValueError, "stack aliases cannot cross calls"):
            match.verify_leaf_instructions(self.body, BASE, True,
                                           {BASE + 10: BASE + 0x100})

    def test_actual_result_register_aliases_remain_rejected(self):
        for result in ("r0", "r1", "r2", "r3"):
            returned = "r1" if result == "r0" else "r0"
            with self.subTest(result=result), self.assertRaisesRegex(
                    ValueError, "local stack pointer escapes through a return register"):
                self.fixture("", caller=self.caller(result=result,
                             return_register=returned), callee="bx lr")

    def test_later_store_of_retained_ip_alias_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "alias use or escape"):
            self.fixture("", caller=self.caller("mov r1, ip\nstr r1, [r3]\n"),
                         callee="bx lr")

    def test_later_out_of_frame_ip_access_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside the tracked frame"):
            self.fixture("", caller=self.caller("mov r1, ip\nldr r2, [r1, #12]\n"),
                         callee="bx lr")

    def test_callee_escape_of_ip_alias_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "buffer pointer use or escape"):
            self.fixture("", caller=self.caller(),
                         callee="mov r1, ip\nstr r1, [r0]\nbx lr")

    def test_callee_out_of_bounds_ip_access_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside allocated local words"):
            self.fixture("", caller=self.caller(),
                         callee="mov r1, ip\nldr r0, [r1, #8]\nmovs r1, #0\nbx lr")

    def test_unknown_nested_callee_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "not unique aligned Thumb ROM code"):
            self.fixture("", caller=self.caller(),
                         callee="push {lr}\nbl child+2\npop {r0}\nbx r0")

    def test_unproved_interrupt_stays_rejected(self):
        with self.assertRaisesRegex(ValueError, "calls and interrupts require"):
            self.fixture("", caller=self.caller(), callee="svc #0xc\nbx lr")

    def test_preserved_register_escape_and_unbalanced_frame_stay_rejected(self):
        with self.assertRaisesRegex(ValueError, "local stack pointer escapes"):
            self.fixture("", caller=self.caller(result="r4"), callee="bx lr")
        with self.assertRaisesRegex(ValueError, "does not balance"):
            self.fixture("", caller=self.caller().replace(
                         "add sp, #8\npop {r0}", "ldr r0, [sp, #8]\nadd sp, #4"),
                         callee="bx lr")


if __name__ == "__main__":
    unittest.main(verbosity=2)
