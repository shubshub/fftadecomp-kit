"""Adjacent literal offsets form stack aliases without authorizing other facts."""
import json
import struct
import unittest

import test_literal_stack_adjustment as fixtures
from test_switch_constants import fixed_args

match = fixtures.match
BASE = fixtures.BASE
NATURAL_SOURCE = (
    "extern void func_08000100(unsigned int *);\n"
    "unsigned int func_08000000(unsigned int value)\n{\n"
    "    unsigned int samples[391];\n"
    "    samples[385] = value;\n"
    "    func_08000100(samples + 385);\n"
    "    return samples[385];\n}\n")


class LiteralStackAliasTests(unittest.TestCase):
    setUp = fixtures.LiteralStackAdjustmentTests.setUp
    body = fixtures.LiteralStackAdjustmentTests.body
    frame = fixtures.LiteralStackAdjustmentTests.frame
    verify = fixtures.LiteralStackAdjustmentTests.verify

    def sequence(self, register=0, offset=1540, after=""):
        return self.frame(f"ldr r{register}, offset\nadd r{register}, sp\n" + after) + \
               f"\n.balign 4\noffset:\n.word {offset}\n"

    def test_owned_literal_and_every_low_register_form_bounded_alias(self):
        for register in range(8):
            with self.subTest(register=register):
                value = 1 if register != 1 else 2
                data = self.body(self.sequence(register, after=f"str r{value}, [r{register}]\nmovs r{register}, #0"))
                instructions = match.verify_leaf_instructions(data, BASE, True)
                aliases = [match.thumb_literal_stack_constant(i, data, BASE) for i in instructions]
                self.assertEqual([value for value in aliases if value is not None],
                                 [(match.ARM_REG_R0 + register, 1540)])

    def test_zero_and_current_frame_bounds(self):
        self.verify(self.sequence(offset=0, after="str r1, [r0]\nmovs r0, #0"))
        with self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
            self.verify(self.sequence(offset=1572))
        # A one-past alias cannot authorize a memory access.
        with self.assertRaisesRegex(ValueError, "outside the tracked frame"):
            self.verify(self.sequence(offset=1568, after="ldr r1, [r0]"))

    def test_unknown_nonadjacent_wrong_register_and_other_encodings_refused(self):
        source = self.sequence()
        cases = (source.replace("ldr r0, offset", "movs r0, r1"),
                 source.replace("ldr r0, offset", "ldr r0, [r1]"),
                 source.replace("ldr r0, offset", "ldr r0, offset\nmovs r1, #0"),
                 source.replace("ldr r0, offset", "ldr r1, offset"),
                 source.replace("add r0, sp", "mov r8, r0\nadd r8, sp"),
                 source.replace("add r0, sp", "mov r8, sp\nadd r0, r8"))
        for body in cases:
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, "stack-address materialization|escape"):
                self.verify(body)

    def test_unsigned_alignment_and_bound_are_not_invented(self):
        for offset in (-4, 1, 1542, 4100, 0x80000000, 0xFFFFFFFC):
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, "bounded aligned offset"):
                self.verify(self.sequence(offset=offset))

    def test_literal_outside_symbol_or_reachable_code_refused(self):
        data = bytearray(self.body(self.sequence()))
        # The frame's allocation pair occupies bytes 2..5; this load starts at 6.
        data[6:8] = struct.pack("<H", 0x48FF)
        with self.assertRaisesRegex(ValueError, "stack alias literal is outside"):
            match.verify_leaf_instructions(bytes(data), BASE, True)
        # Both following reachable instructions encode an aligned zero word.
        source = self.frame("ldr r0, code_word\nadd r0, sp\n.balign 4\n"
                            "code_word:\nmovs r0, r0\nmovs r0, r0")
        with self.assertRaisesRegex(ValueError, "literal read overlaps reachable code"):
            self.verify(source)

    def test_branch_cannot_bypass_load_even_with_matching_depth(self):
        source = self.sequence().replace("ldr r0, offset\n",
            "cmp r1, #0\nbeq bypass\nldr r0, offset\nbypass:\n")
        with self.assertRaisesRegex(ValueError, "literal load is bypassed"):
            self.verify(source)

    def test_escape_calls_and_inconsistent_joins_still_refused(self):
        for after in ("str r0, [r1]", "push {r0}", "stm r1!, {r0}", "bl callee"):
            with self.subTest(after=after), self.assertRaisesRegex(ValueError, "stored|spilled|escape|cross calls"):
                source = self.sequence(after=after)
                data = self.body(source)
                decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
                decoder.detail = True
                calls = {i.address: i.operands[0].imm for i in decoder.disasm(data, BASE)
                         if match.CS_GRP_CALL in i.groups}
                match.verify_leaf_instructions(data, BASE, True, calls)
        source = self.frame("cmp r1, #0\nbeq other\nldr r0, offset\nadd r0, sp\n"
                            "b joined\nother:\nmov r0, sp\njoined:\nldr r1, [r0]")
        source += "\n.balign 4\noffset:\n.word 1540"
        with self.assertRaisesRegex(ValueError, "inconsistent stack aliases"):
            self.verify(source)

    def test_literal_value_does_not_become_general_register_index(self):
        source = self.sequence(after="mov r1, sp\nldr r2, offset\nldr r3, [r1, r2]")
        with self.assertRaisesRegex(ValueError, "index is not a known constant"):
            self.verify(source)

    def test_balanced_return_and_saved_return_provenance_still_required(self):
        with self.assertRaises(ValueError):
            self.verify(self.sequence().replace("release:\n.word 1564", "release:\n.word 1560"))
        with self.assertRaisesRegex(ValueError, "verified return|non-leaf"):
            self.verify(self.sequence(offset=1564, after="str r1, [r0]\nmovs r0, #0"))

    def test_natural_fixed_O2_source_and_unmodified_complete_original_elf(self):
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text(NATURAL_SOURCE)
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
            instructions = match.verify_leaf_instructions(data, BASE, True, calls,
                buffer_proof=proof, call_resolver=proof.target)
            self.assertTrue(any(match.thumb_literal_stack_constant(i, data, BASE)
                                is not None for i in instructions))
            self.assertEqual(runner.read_binary(f"{workspace}/f.o"), original)


if __name__ == "__main__":
    unittest.main(verbosity=2)
