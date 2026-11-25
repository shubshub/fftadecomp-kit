"""agbcc's far jump (`bl .Ln @ far jump`) is a branch in the volatile check, not a call."""

import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import volatile_loop_induction as induction
import volatile_semantics as semantics
import test_volatile_loop_induction as T

FRAME, END, MEMBER = T.FRAME, T.END, T.MEMBER


def far(label):
    return f"bl\t{label}\t@ far jump"


# `if (a) return 1; sym.unknown_3C = 1; return 0;` with the early return a far jump to the epilogue
EARLY_RETURN = FRAME + ("cmp\tr0, #0", "beq\t.L20", "mov\tr0, #1", far(".L21"), ".L20:") + MEMBER + \
    ("mov\tr0, #0", ".L21:") + END


class FarJumpTests(T.Base):
    def test_a_far_jump_is_a_branch(self):
        (result,) = self.compare(EARLY_RETURN)
        self.assertEqual(result[:2], ("func_08028C34", 2))
        # the record names no call: a far jump is no event
        text = semantics.record(T.SYMBOL, [result], perturbed=True)
        self.assertEqual(text.split("; ", 1)[1],
                         "`func_08028C34` agrees on 2 paths; read-modify-write loads at [8], chained re-reads at []")

    def test_the_conditional_form(self):
        # a conditional branch out of reach: `b<inverse> .LCBn; bl .Ln @far jump; .LCBn:`, the mark
        # without a space
        body = FRAME + ("cmp\tr0, #0", "beq\t.LCB7", "mov\tr0, #1", "bl\t.L21\t@far jump", ".LCB7:") + MEMBER + \
            ("mov\tr0, #0", ".L21:") + END
        (result,) = self.compare(body)
        self.assertEqual(result[:2], ("func_08028C34", 2))

    def test_the_paths_after_a_far_jump_are_compared(self):
        body = FRAME + ("mov\tr6, r1", "cmp\tr0, #0", "beq\t.L20", far(".L21"), ".L20:") + MEMBER + \
            (".L21:", ("real", "mov\tr2, #1"), ("stripped", "mov\tr2, #2"), "str\tr2, [r6]") + END
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(body)
        self.assertIn("differ in observable behaviour", str(caught.exception))

    def test_a_far_jump_does_not_return(self):
        # the instruction after the far jump is reached only as the jump's continuation:
        # the compiles differ there, but no path runs it
        body = FRAME + ("mov\tr6, r1", far(".L21"), ("real", "mov\tr2, #1"), ("stripped", "mov\tr2, #2"),
                        "str\tr2, [r6]", ".L21:") + MEMBER + END
        (result,) = self.compare(body)
        self.assertEqual(result[1], 1)

    def test_lr_is_unreadable_after_a_far_jump(self):
        body = FRAME + ("mov\tr6, r1", far(".L21"), ".L21:", "mov\tr2, lr", "str\tr2, [r6]") + MEMBER + END
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(body)
        self.assertIn("lr is read after a far jump overwrote it", str(caught.exception))

    def test_no_return_through_lr_after_a_far_jump(self):
        # a leaf that returns through lr: the far jump overwrote it
        body = MEMBER + (far(".L21"), ".L21:", "bx\tlr")
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(body)
        self.assertIn("computed jumps are not modelled", str(caught.exception))
        # the same leaf without the far jump returns
        self.assertEqual(self.compare(MEMBER + ("bx\tlr",))[0][1], 1)

    def test_no_return_through_the_far_jumps_lr_saved_on_the_stack(self):
        # a leaf whose far jump lands on `push {lr}; pop {pc}`: a local call in disguise
        body = MEMBER + (far(".L30"), ".L31:", "bx\tlr", ".L30:", "push\t{lr}", "pop\t{pc}")
        with self.assertRaises(semantics.SemanticError) as caught:
            self.compare(body)
        self.assertIn("pop into pc of something other than the return address", str(caught.exception))

    def test_only_the_compilers_far_jump_is_a_branch(self):
        cases = (
            # a `bl` to a label without agbcc's mark stays a call
            ("bl\t.L21", "the callee has no prototype with a fixed argument list"),
            # the mark on a call to a function
            (far("func_0802A2C0"), "unsupported far jump form"),
            # a label of no instruction in this function
            (far(".L99"), "branch to unknown label `.L99`"),
            (far(".L3"), "branch to `.L3`, a label that no instruction follows directly"),
        )
        for jump, reason in cases:
            with self.subTest(jump=jump):
                body = FRAME + ("mov\tr0, #0", jump, ".L21:") + MEMBER + END
                with self.assertRaises(semantics.SemanticError) as caught:
                    self.compare(body)
                self.assertIn(reason, str(caught.exception))

    def test_a_loop_closed_by_a_far_jump_is_cut(self):
        # `do body while (--i)` whose back edge is a far jump: the induction's control flow
        # follows the jump, so the loop is cut and proved
        body = FRAME + ("mov\tr4, r0", ".L10:", "sub\tr4, r4, #1", "cmp\tr4, #0", "beq\t.L11", far(".L10"),
                        ".L11:") + MEMBER + END
        self.bounded(body)
        (result,) = self.compare(body)
        self.assertEqual(result[-1], (3,))
        text = semantics.record(T.SYMBOL, [result], perturbed=True)
        self.assertIn(f"loops by relational induction at instructions [3] ({induction.NAME}", text)


# a loop closed by a far jump, then four if-statements and a store of lr: with the path bound
# at 8 the plain check stops before any path that iterated, so only the induction reads lr
READ_AFTER_A_CUT = FRAME + ("mov\tr6, r1", "mov\tr4, r0", ".L10:", "sub\tr4, r4, #1", "cmp\tr4, #0", "beq\t.L11",
                            far(".L10"), ".L11:") + T.diamonds(4) + ("mov\tr2, lr", "str\tr2, [r6]") + MEMBER + END


def one_value(step):
    """Executor.step with lr after a far jump the same value in every compile"""
    def stepped(self, pc, mnemonic, operands, text):
        result = step(self, pc, mnemonic, operands, text)
        if isinstance(self.regs["lr"], tuple) and self.regs["lr"][:2] == (semantics.FAR_JUMP, self.label):
            self.regs["lr"] = (semantics.FAR_JUMP, "every compile", pc)
        return result
    return stepped


class FarJumpCutTests(T.Base):
    def test_lr_read_after_a_loop_closed_by_a_far_jump(self):
        # the cut havocs lr, so the read check cannot see the read; the back edge compares lr
        # between the compiles, and the per-compile value refuses it there
        with mock.patch.object(semantics, "MAX_PATHS", 8):
            with self.assertRaises(semantics.SemanticError) as caught:
                self.compare(READ_AFTER_A_CUT)
        message = str(caught.exception)
        self.assertIn("more than 8 paths; the semantic check is bounded", message)
        self.assertIn("relational loop induction (kit#137): ", message)
        self.assertIn("back edge 1: lr differs from the real compile's lr",
                      message.split("relational loop induction (kit#137): ", 1)[1])

    def test_far_jump_labels_name_no_callee(self):
        # the source is not searched for a prototype of a far jump's label
        asked = []
        original = semantics.function_signature

        def recording(scope, name):
            asked.append(name)
            return original(scope, name)
        with mock.patch.object(semantics, "function_signature", recording):
            self.compare(EARLY_RETURN)
        self.assertIn("func_08028C34", asked)
        self.assertNotIn(".L21", asked)


class FarJumpMutantTests(T.Base):
    """each rule dropped admits an input it refuses"""

    def test_without_overwriting_lr(self):
        original = semantics.Executor.step

        def keeps_lr(self, pc, mnemonic, operands, text):
            lr = self.regs["lr"]
            result = original(self, pc, mnemonic, operands, text)
            if self.regs["lr"][:1] == (semantics.FAR_JUMP,):
                self.regs["lr"] = lr
            return result
        body = MEMBER + (far(".L21"), ".L21:", "bx\tlr")
        with mock.patch.object(semantics.Executor, "step", keeps_lr):
            self.assertEqual(self.compare(body)[0][1], 1)

    def test_without_the_read_check_or_a_value_per_compile(self):
        # lr after a far jump differs between the compiles and refuses any read: in code without
        # a loop cut either alone keeps the input refused, and dropping both admits it (a cut
        # havocs lr, so there only the per-compile value refuses: test_with_one_value_through_a_cut)
        body = FRAME + ("mov\tr6, r1", far(".L21"), ".L21:", "mov\tr2, lr", "str\tr2, [r6]") + MEMBER + END
        step, value = one_value(semantics.Executor.step), semantics.Executor.value

        def reads(self, operand, text):
            if semantics.register(operand) == "lr" and self.regs["lr"][:1] == (semantics.FAR_JUMP,):
                return self.regs["lr"]
            return value(self, operand, text)
        with mock.patch.object(semantics.Executor, "step", step):
            with self.assertRaises(semantics.SemanticError) as caught:
                self.compare(body)
            self.assertIn("lr is read after a far jump overwrote it", str(caught.exception))
        with mock.patch.object(semantics.Executor, "value", reads):
            with self.assertRaises(semantics.SemanticError) as caught:
                self.compare(body)
            self.assertIn("compile behaves differently", str(caught.exception))
        with mock.patch.object(semantics.Executor, "step", step), \
                mock.patch.object(semantics.Executor, "value", reads):
            self.assertEqual(self.compare(body)[0][1], 1)

    def test_with_one_value_through_a_cut(self):
        with mock.patch.object(semantics, "MAX_PATHS", 8), \
                mock.patch.object(semantics.Executor, "step", one_value(semantics.Executor.step)):
            (result,) = self.compare(READ_AFTER_A_CUT)
        self.assertEqual(result[0], "func_08028C34")

    def test_the_induction_without_far_jumps(self):
        # its control flow then misses the back edge, so no cut holds the loop and the bound stands
        body = FRAME + ("mov\tr4, r0", ".L10:", "sub\tr4, r4, #1", "cmp\tr4, #0", "beq\t.L11", far(".L10"),
                        ".L11:") + MEMBER + END
        original = induction.effects

        def as_call(probe, pc, *rest):
            if pc in probe.labels.far:
                return set(), {"lr"}, False, False, {"lr"}, [pc + 1], True
            return original(probe, pc, *rest)
        with mock.patch.object(induction, "effects", as_call):
            with self.assertRaises(semantics.SemanticError) as caught:
                self.compare(body)
        message = str(caught.exception)
        self.assertIn("more than 32 unknown branch conditions on one path", message)
        self.assertIn("relational loop induction (kit#137): ", message)
        self.assertIn("more than 32 unknown branch conditions on one path",
                      message.split("relational loop induction (kit#137): ", 1)[1])


if __name__ == "__main__":
    unittest.main()
