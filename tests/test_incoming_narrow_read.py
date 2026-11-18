"""An adjacent SP address and narrow load may read one incoming argument word."""
import json
import struct
import unittest

import test_stack_alias_join_lifetime as fixtures
from test_switch_constants import fixed_args

match = fixtures.match
evidence = fixtures.fixtures.evidence
BASE = fixtures.BASE
NATURAL_SOURCE = (
    "typedef struct { unsigned char unknown_00[0xF6]; unsigned char x, y; } Unit;\n"
    "extern unsigned short func_08000100(const Unit *, const Unit *, unsigned short);\n"
    "unsigned short func_08000000(Unit *a, Unit *b, unsigned short id, unsigned char ax,\n"
    "                             unsigned char ay, unsigned char bx, unsigned char by)\n{\n"
    "    unsigned char oax = a->x, oay = a->y, obx = b->x, oby = b->y;\n"
    "    unsigned short result;\n"
    "    a->x = ax; a->y = ay; b->x = bx; b->y = by;\n"
    "    result = func_08000100(a, b, id);\n"
    "    a->x = oax; a->y = oay; b->x = obx; b->y = oby;\n"
    "    return result;\n}\n")


class IncomingNarrowReadTests(unittest.TestCase):
    setUp = fixtures.StackAliasJoinLifetimeTests.setUp
    body = fixtures.StackAliasJoinLifetimeTests.body

    def frame(self, middle, allocation=4):
        # Three words below entry SP: the saved r4/lr pair and one allocated word.
        return (f"push {{r4, lr}}\nsub sp, #{allocation}\n{middle}\nadd sp, #{allocation}\n"
                "pop {r4}\npop {r1}\nbx r1")

    def calls(self, data):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return {i.address: i.operands[0].imm for i in decoder.disasm(data, BASE)
                if match.CS_GRP_CALL in i.groups}

    def verify(self, middle, allocation=4, **options):
        data = self.body(self.frame(middle, allocation))
        return match.verify_leaf_instructions(data, BASE, True, self.calls(data), **options)

    def reads(self, middle, allocation=4):
        data = self.body(self.frame(middle, allocation))
        instructions = self.verify(middle, allocation, incoming_narrow_reads=True)
        return [read for read in (match.thumb_incoming_narrow_read(item, data, BASE, 2 + allocation // 4)
                                  for item in instructions) if read is not None]

    def test_byte_and_halfword_reads_of_each_incoming_word_and_low_register(self):
        r = match.ARM_REG_R0
        cases = (("add r0, sp, #12\nldrb r0, [r0]", (r, 0, 1)),
                 ("add r1, sp, #16\nldrb r1, [r1, #3]", (r + 1, 7, 1)),
                 ("add r2, sp, #20\nldrh r2, [r2, #2]", (r + 2, 10, 2)),
                 ("add r3, sp, #24\nldrh r3, [r3]", (r + 3, 12, 2)),
                 ("add r4, sp, #28\nldrb r4, [r4, #1]\nmovs r0, r4", (r + 4, 17, 1)),
                 ("bl callee\nadd r3, sp, #20\nldrb r3, [r3]\nadds r0, r3, #0", (r + 3, 8, 1)))
        for middle, expected in cases:
            with self.subTest(middle=middle):
                self.assertEqual(self.reads(middle), [expected])
                # Without the policy the address is still an out-of-frame stack alias.
                with self.assertRaisesRegex(ValueError, "(leaves|outside) the tracked frame"):
                    self.verify(middle)

    def test_other_uses_of_the_address_still_leave_the_tracked_frame(self):
        for middle in ("add r0, sp, #16\nldrb r1, [r0]",
                       "add r0, sp, #16\nldrb r0, [r1]",
                       "add r0, sp, #16\nstrb r1, [r0]",
                       "add r0, sp, #16\nstrh r1, [r0]",
                       "add r0, sp, #16\nldr r0, [r0]",
                       "movs r1, #0\nadd r0, sp, #16\nldrsb r0, [r0, r1]",
                       "add r0, sp, #16\nmovs r1, #0\nldrb r0, [r0]",
                       "add r0, sp, #16\nb next\nnext:\nldrb r0, [r0]",
                       "add r0, sp, #16\nadds r0, #1\nldrb r0, [r0]",
                       "add r0, sp, #16\nbl callee"):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
                self.verify(middle, incoming_narrow_reads=True)

    def test_read_must_stay_within_direct_word_reach(self):
        # 129 words below entry SP: a direct LDR reaches at most entry SP+504.
        self.assertEqual(self.reads("add r0, sp, #1020\nldrb r0, [r0, #3]", allocation=508),
                         [(match.ARM_REG_R0, 507, 1)])
        self.assertEqual(self.reads("add r0, sp, #1016\nldrh r0, [r0, #6]", allocation=508),
                         [(match.ARM_REG_R0, 506, 2)])
        for middle in ("add r0, sp, #1020\nldrb r0, [r0, #4]", "add r0, sp, #1020\nldrh r0, [r0, #4]"):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
                self.verify(middle, allocation=508, incoming_narrow_reads=True)

    def test_local_aliases_and_incoming_stores_keep_their_rules(self):
        # An address inside the frame remains an ordinary bounded local alias.
        self.verify("add r0, sp, #0\nmovs r1, #1\nstrb r1, [r0, #3]\nldrb r0, [r0, #3]",
                    incoming_narrow_reads=True)
        with self.assertRaisesRegex(ValueError, "outside the tracked frame"):
            self.verify("add r0, sp, #8\nldrb r0, [r0, #4]", incoming_narrow_reads=True)
        for middle in ("movs r0, #0\nstr r0, [sp, #16]", "add r0, sp, #12\nmovs r1, #0\nstrb r1, [r0]"):
            with self.subTest(middle=middle), self.assertRaisesRegex(ValueError, "outside the tracked frame"):
                self.verify(middle, incoming_narrow_reads=True)

    def test_policy_requires_the_plain_thumb_direct_call_path(self):
        data = self.body(self.frame("add r0, sp, #16\nldrb r0, [r0]"))
        refusal = "plain Thumb direct-call path"
        for options in (dict(incoming_narrow_reads=1), dict(incoming_narrow_reads="yes"),
                        dict(incoming_narrow_reads=True, inert_spin_context={}),
                        dict(incoming_narrow_reads=True, acyclic_state_budget=64),
                        dict(incoming_narrow_reads=True, self_calls=frozenset({BASE + 4}))):
            with self.subTest(options=options), self.assertRaisesRegex(ValueError, refusal):
                match.verify_leaf_instructions(data, BASE, True, **options)
        with self.assertRaisesRegex(ValueError, refusal):
            match.verify_leaf_instructions(data, BASE, False, incoming_narrow_reads=True)

        class DerivedProof(match.BufferCallProof):
            pass
        with self.assertRaisesRegex(ValueError, refusal):
            match.verify_leaf_instructions(data, BASE, True, buffer_proof=DerivedProof(b"", None),
                                           incoming_narrow_reads=True)
        match.verify_leaf_instructions(data, BASE, True, buffer_proof=match.BufferCallProof(b"", None),
                                       incoming_narrow_reads=True)

    def test_only_the_ordinary_frame_paths_and_their_replays_pass_the_policy(self):
        import ast
        found = set()
        for path in sorted((fixtures.fixtures.ROOT / "tools").glob("*.py")):
            for function in ast.walk(ast.parse(path.read_text())):
                if isinstance(function, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                        isinstance(node, ast.Call) and any(keyword.arg == "incoming_narrow_reads"
                                                           for keyword in node.keywords)
                        for node in ast.walk(function)):
                    found.add((path.name, function.name))
        self.assertEqual(found, {("match.py", "main"),
                                 ("match_evidence.py", "legacy_report_control_flow"),
                                 ("match_evidence.py", "buffer_report_matches"),
                                 ("function_thunk_profile.py", "verify_source"),
                                 ("data_buffer_profile.py", "prove"),
                                 ("oam_list_context.py", "compile_group")})

    def report(self, data, mapping):
        (self.root / "config").mkdir(exist_ok=True)
        (self.root / "src").mkdir(exist_ok=True)
        (self.root / "config/functions.json").write_bytes(mapping)
        (self.root / "baserom.bin").write_bytes(data.ljust(0x100, b"\0") + bytes.fromhex("7047"))
        (self.root / "src/08000000.c").write_text("/* synthetic fingerprint input */\n")
        return "\n".join([
            f"* verification: `{evidence.FRAMED_LINKED_SCHEMA}`",
            f"* source SHA-256: `{evidence.source_fingerprint(self.root, BASE)}`",
            f"* stack frame: {evidence.STACK_SUMMARY}",
            f"* mapping SHA-256: `{evidence.mapping_fingerprint(mapping)}`",
            f"* control flow: {evidence.CALL_SUMMARY}",
            "* verified extent: complete ELF function symbol, including literal pools",
            "* relocations: none", f"* ROM bytes: `{data.hex()}` ({len(data)} bytes)",
            f"* compiled : `{data.hex()}`", "* source plausibility: plausible",
            f"**MATCH - byte identical** - {len(data)}/{len(data)} bytes"])

    def test_saved_framed_call_report_replays_the_same_rule(self):
        def mapping(data):
            return json.dumps([
                {"rom": f"0x{BASE:08X}", "end": f"0x{BASE + len(data):08X}", "mode": "thumb"},
                {"rom": "0x08000100", "end": "0x08000102", "mode": "thumb"}]).encode()
        data = self.body(self.frame("bl callee\nadd r3, sp, #20\nldrb r3, [r3]\nadds r0, r3, #0"))
        self.assertTrue(evidence.report_matches(self.report(data, mapping(data)), self.root, BASE))
        # The same report with the load into another register forms a lasting address.
        other = self.body(self.frame("bl callee\nadd r3, sp, #20\nldrb r2, [r3]\nadds r0, r2, #0"))
        self.assertFalse(evidence.report_matches(self.report(other, mapping(other)), self.root, BASE))

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
            for stack_arguments in (False, True):
                with self.subTest(stack_arguments=stack_arguments):
                    proof = match.BufferCallProof(rom, mapping, stack_arguments=stack_arguments)
                    instructions = match.verify_leaf_instructions(data, BASE, True, calls,
                        buffer_proof=proof, incoming_narrow_reads=True)
                    depth = 11
                    self.assertEqual([read for read in (match.thumb_incoming_narrow_read(i, data, BASE, depth)
                                                        for i in instructions) if read is not None],
                                     [(match.ARM_REG_R0 + 3, 8, 1)])
                    with self.assertRaisesRegex(ValueError, "leaves the tracked frame"):
                        match.verify_leaf_instructions(data, BASE, True, calls,
                            buffer_proof=match.BufferCallProof(rom, mapping, stack_arguments=stack_arguments))
            self.assertEqual(runner.read_binary(f"{workspace}/f.o"), original)


if __name__ == "__main__":
    unittest.main(verbosity=2)
