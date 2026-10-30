"""Bounded literal-loaded Thumb frame sizes do not admit dynamic SP writes."""
import json
import struct
import unittest

import test_stack_alias_join_lifetime as fixtures
from test_switch_constants import fixed_args

match = fixtures.match
BASE = fixtures.BASE


class LiteralStackAdjustmentTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def frame(self, middle="", allocate=-1564, release=1564, register="r2"):
        return (f"push {{lr}}\nldr {register}, allocation\nadd sp, {register}\n" +
                middle + f"\nldr {register}, release\nadd sp, {register}\n" +
                "pop {r1}\nbx r1\n.balign 4\nallocation:\n" +
                f".word {allocate}\nrelease:\n.word {release}\n")

    def verify(self, source):
        return match.verify_leaf_instructions(self.body(source), BASE, True)

    def test_complete_literal_frame_and_every_low_source_register(self):
        for register in range(8):
            with self.subTest(register=register):
                source = self.frame("str r0, [sp]\nldr r0, [sp]", register=f"r{register}")
                data = self.body(source)
                ins = match.verify_leaf_instructions(data, BASE, True)
                self.assertTrue(match.uses_stack_frame(ins))
                self.assertEqual(sum(match.thumb_literal_stack_adjustment(i, data, BASE)
                                     is not None for i in ins), 2)

    def test_dynamic_nonadjacent_wrong_register_and_high_register_refused(self):
        cases = ("add sp, r0\nbx lr",
                 self.frame().replace("ldr r2, allocation\n", ""),
                 self.frame().replace("ldr r2, allocation\n", "ldr r2, allocation\nmovs r3, #0\n"),
                 self.frame().replace("ldr r2, allocation", "ldr r3, allocation"),
                 self.frame().replace("add sp, r2", "mov r8, r2\nadd sp, r8", 1),
                 "mov sp, r0\nbx lr")
        for source in cases:
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "stack-pointer adjustment"):
                self.verify(source)

    def test_zero_unaligned_large_and_wrapping_values_refused(self):
        for value in (0, -1, -1562, -4100, 0x80000000, 0x7FFFFFFC, 0xFFFF0000):
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "bounded aligned displacement"):
                self.verify(self.frame(allocate=value))
        with self.assertRaisesRegex(ValueError, "bounded tracked frame"):
            self.verify(self.frame(allocate=-4096, release=4096))
        self.verify(self.frame(allocate=-4092, release=4092))

    def test_bypassing_literal_load_is_refused_even_at_equal_depth(self):
        source = self.frame().replace("ldr r2, allocation\n",
            "cmp r0, #0\nbeq bypass\nldr r2, allocation\nbypass:\n", 1)
        with self.assertRaisesRegex(ValueError, "literal load is bypassed"):
            self.verify(source)

    def test_join_depth_and_unbalanced_return_still_refused(self):
        source = self.frame("cmp r0, #0\nbeq joined\nsub sp, #4\njoined:")
        with self.assertRaises(ValueError):
            self.verify(source)
        with self.assertRaisesRegex(ValueError, "balance|outside the saved|indirect control flow"):
            self.verify(self.frame(release=1560))
        with self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
            self.verify(self.frame(release=1572))

    def test_stack_alias_bounds_and_return_provenance_still_refused(self):
        with self.assertRaisesRegex(ValueError, "outside the tracked frame"):
            self.verify(self.frame("mov r0, sp\nldr r1, [r0, #8]", allocate=-4, release=4))
        with self.assertRaisesRegex(ValueError, "verified return|non-leaf"):
            self.verify(self.frame("str r0, [sp, #4]", allocate=-4, release=4))

    def test_literal_outside_or_overlapping_code_is_refused(self):
        data = self.body(self.frame())
        outside = bytearray(data)
        outside[2:4] = struct.pack("<H", 0x4AFF)
        with self.assertRaisesRegex(ValueError, "literal is outside"):
            match.verify_leaf_instructions(bytes(outside), BASE, True)
        # This reachable instruction pair also encodes an aligned +4 word.
        source = ("push {lr}\nldr r2, code_word\nadd sp, r2\nmovs r3, #0\n"
                  "code_word:\nmovs r4, r0\nmovs r0, r0\nbx lr")
        with self.assertRaisesRegex(ValueError, "literal read overlaps reachable code"):
            self.verify(source)

    def test_buffer_secondary_pass_accounts_for_literal_frame(self):
        source = ("push {lr}\nldr r2, allocation\nadd sp, r2\n"
                  "ldr r1, [sp, #4]\nstr r1, [r0]\nmovs r0, #0\n"
                  "ldr r2, release\nadd sp, r2\npop {r1}\nbx r1\n"
                  ".balign 4\nallocation:\n.word -1564\nrelease:\n.word 1564")
        data = self.body(source)
        mapping = json.dumps([{"rom": f"0x{BASE:08X}",
                               "end": f"0x{BASE + len(data):08X}", "mode": "thumb"}]).encode()
        proof = match.BufferCallProof(data, mapping)
        # The callee's own local read must not become a read of the caller's
        # incoming pointer slot when its 1564-byte allocation is accounted for.
        self.assertEqual(proof.check_arguments(BASE, {match.ARM_REG_R0: -4},
                                              [(False, False, True)], {4: -4}, frozenset()), {})

    def test_shifted_constant_forms_only_a_bounded_stack_alias(self):
        sequence = "movs r0, #192\nlsls r0, r0, #3\nadd r0, sp"
        self.verify(self.frame(sequence + "\nldr r1, [r0]\nmovs r0, #0"))
        with self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
            self.verify(self.frame(sequence.replace("#192", "#200")))
        with self.assertRaisesRegex(ValueError, "unaligned"):
            self.verify(self.frame(sequence.replace("#192", "#193").replace("#3", "#1") +
                                   "\nldr r1, [r0]"))

    def test_shifted_constant_proof_rejects_dynamic_overflow_and_bypass(self):
        sequence = "movs r0, #192\nlsls r0, r0, #3\nadd r0, sp"
        for replacement in ("movs r0, r1", "ldr r0, [r1]", "movs r1, #192"):
            with self.subTest(replacement=replacement), self.assertRaisesRegex(
                    ValueError, "stack-address materialization"):
                self.verify(self.frame(sequence.replace("movs r0, #192", replacement)))
        with self.assertRaisesRegex(ValueError, "overflows"):
            self.verify(self.frame(sequence.replace("#3", "#31")))
        for bypass in ("movs r0, #192\nlsls r0, r0, #3\nbypass:\nadd r0, sp",
                       "movs r0, #192\nbypass:\nlsls r0, r0, #3\nadd r0, sp"):
            with self.subTest(bypass=bypass), self.assertRaisesRegex(ValueError, "constant is bypassed"):
                self.verify(self.frame("cmp r1, #0\nbeq bypass\n" + bypass))

    def test_shifted_alias_escape_and_general_index_refusals_unchanged(self):
        sequence = "movs r0, #192\nlsls r0, r0, #3\nadd r0, sp"
        for observed in ("str r0, [r1]", "push {r0}", "stm r1!, {r0}"):
            with self.subTest(observed=observed), self.assertRaisesRegex(ValueError, "stored|spilled|escape"):
                self.verify(self.frame(sequence + "\n" + observed))
        with self.assertRaisesRegex(ValueError, "stack-address materialization"):
            self.verify(self.frame("ldr r0, release\nmovs r1, #0\nadd r0, sp"))
        # The same arithmetic still cannot authorize a general memory index.
        with self.assertRaisesRegex(ValueError, "index is not a known constant"):
            self.verify(self.frame("mov r0, sp\nmovs r1, #1\nlsls r1, r1, #2\nldr r2, [r0, r1]"))
        # Differing aliases remain subject to the existing all-path join rule.
        with self.assertRaisesRegex(ValueError, "inconsistent stack aliases"):
            self.verify(self.frame("cmp r1, #0\nbeq other\n" + sequence +
                "\nb joined\nother:\nmov r0, sp\njoined:\nldr r1, [r0]"))

    def test_fixed_compiler_natural_large_array_retains_original_elf(self):
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text(
            "extern void func_08000100(unsigned int *);\n"
            "unsigned int func_08000000(unsigned int value)\n{\n"
            "    unsigned int samples[391];\n"
            "    samples[384] = value;\n"
            "    func_08000100(samples + 384);\n"
            "    return samples[384];\n}\n")
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        args = fixed_args()
        with runner.workspace() as workspace:
            original, _, image = match.compile_object(runner, workspace, args,
                self.root, BASE, "src/08000000.c")
            self.assertEqual(struct.unpack_from("<H", original, 16)[0], 1)
            symbol, _ = match.function_record(image, "func_08000000", BASE, True)
            mapping = json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + symbol['size']:08X}", "mode": "thumb"},
                {"rom": "0x08000100", "end": "0x08000104", "mode": "thumb"}]).encode()
            data, calls, _ = match.link_calls(runner, workspace, args, image, BASE, mapping, 0x104)
            rom = data.ljust(0x100, b"\0") + bytes.fromhex("00207047")
            proof = match.BufferCallProof(rom, mapping)
            ins = match.verify_leaf_instructions(data, BASE, True, calls,
                buffer_proof=proof, call_resolver=proof.target)
            self.assertEqual(sum(match.thumb_literal_stack_adjustment(i, data, BASE)
                                 is not None for i in ins), 2)
            self.assertTrue(any(match.thumb_shifted_stack_constant(i, data, BASE)
                                is not None for i in ins))
            self.assertEqual(runner.read_binary(f"{workspace}/f.o"), original)


if __name__ == "__main__":
    unittest.main(verbosity=2)
