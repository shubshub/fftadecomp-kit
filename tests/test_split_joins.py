"""Disagreeing forward joins of a stack-argument walk, kept apart (SplitJoins).

Fixtures are assembled Thumb owners and callees; the native tests compile C with
the fixed compiler. No game ROM is needed.
"""
import json
import os
from pathlib import Path
import subprocess
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
import counted_stack_cursor_loop as counted_cursor
import split_join_profile as split_join

BASE = match.ROM_BASE
CALLEE = BASE + 0x100
JOIN = "inconsistent possible pointer offsets at control-flow join"
ESCAPE = "local stack pointer escapes through a return register"
# push {r4, lr}; sub sp, #16: entry-SP offsets sp+4 = -20, sp+8 = -16.
PROLOGUE = "push {r4, lr}\nsub sp, #16\nadds r4, r0, #0\nmovs r1, #0\nstr r1, [sp, #4]\nstr r1, [sp, #8]\n"
EPILOGUE = "add sp, #16\npop {r4}\npop {r1}\nbx r1"
# r0 is sp+4 on one path and sp+8 on the other when they meet at `join`.
CHOOSE = "cmp r4, #0\nbeq second\nadd r0, sp, #4\nb join\nsecond:\nadd r0, sp, #8\njoin:\n"


def owner(body):
    return PROLOGUE + CHOOSE + body + "\n" + EPILOGUE


# Three paths: A meets B first; B and C share one split offset of r0 and so meet on ONE split key, where every
# other fact of the two states must be merged exactly.
THREE = ("push {r4, lr}\nsub sp, #16\nadds r4, r0, #0\nmovs r1, #0\nstr r1, [sp, #4]\nstr r1, [sp, #8]\n"
         "str r1, [sp, #12]\nstr r1, [sp]\ncmp r4, #0\nbeq b1\n{A}b join\nb1:\ncmp r4, #1\nbeq c1\n{B}b join\n"
         "c1:\n{C}join:\n{after}")
# r12 keeps a split offset to the return (IP is no result register), so the split key lasts to the end.
R12 = "add r0, sp, #{n}\nmov r12, r0\nmovs r0, #0\n"
STORE = "stack-alias store overlaps a saved register or return-address word"
INDIRECT = "non-leaf indirect control flow requires linked CFG verification"
# agbcc's rotated loop: the loop-carried join at `cond` is reached by two forward edges.
TOGGLE = (PROLOGUE + "movs r3, #4\nadd r0, sp, #4\nb cond\nbody:\nldrh r2, [r0]\n{extra}cmp r2, #0\nbeq other\n"
          "add r0, sp, #4\nb next\nother:\nadd r0, sp, #8\nnext:\nsubs r3, #1\ncond:\ncmp r3, #0\nbne body\n"
          "movs r0, #0\n" + EPILOGUE)


def three(a, b, c, after):
    return THREE.replace("{A}", a).replace("{B}", b).replace("{C}", c).replace("{after}", after)


class SplitJoinTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="split_joins_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {"FFTA_ROM": str(self.root / "baserom.bin")})
        environment.start()
        self.addCleanup(environment.stop)

    def build(self, caller, callee="bx lr"):
        text = (".syntax unified\n.arch armv4t\n.thumb\n.text\n.global caller, caller_end, callee, callee_end\n"
                f"caller:\n{caller}\n.align 2\n.ltorg\ncaller_end:\n.org 0x100\ncallee:\n{callee}\ncallee_end:\n")
        (self.root / "fixture.s").write_text(text)
        for command in (
                ["arm-none-eabi-as", "-mthumb-interwork", str(self.root / "fixture.s"), "-o", str(self.root / "f.o")],
                ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "f.o"),
                 "-o", str(self.root / "f.elf")],
                ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text", str(self.root / "f.elf"),
                 str(self.root / "baserom.bin")]):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "f.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "baserom.bin").read_bytes()
        self.mapping = json.dumps([{"rom": f"0x{self.symbols[name]:08X}", "end": f"0x{self.symbols[name + '_end']:08X}",
                                    "mode": "thumb"} for name in ("caller", "callee")]).encode()
        self.body = self.rom[:self.symbols["caller_end"] - BASE]

    def walk(self, caller, callee="bx lr", proof_type=match.BufferCallProof, stack_arguments=True, **options):
        self.build(caller, callee)
        proof = proof_type(self.rom, self.mapping, stack_arguments=stack_arguments, loop_replay=True, **options)
        match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof, call_resolver=proof.target,
                                       incoming_narrow_reads=proof_type is match.BufferCallProof)
        return proof

    def refused(self, pattern, caller, callee="bx lr", **options):
        with self.assertRaisesRegex(ValueError, pattern):
            self.walk(caller, callee, **options)

    def join_address(self):
        # The label is local to the fixture; find it from the assembled branch to it.
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        (target,) = {instruction.operands[0].imm for instruction in decoder.disasm(self.body, BASE)
                     if instruction.mnemonic == "b"}
        return target

    # Admitted ---------------------------------------------------------------------------

    def test_a_live_two_offset_pointer_is_walked_per_offset(self):
        proof = self.walk(owner("ldrh r0, [r0]\nmovs r0, #0"))
        join = self.join_address()
        (record,) = proof.split_joins
        self.assertEqual((record[:3], set(record[3:])), ((BASE, join, match.ARM_REG_R0), {-20, -16}))
        (line,) = [line for line in proof.loop_replay_lines() if line.startswith("* buffer split join: ")]
        self.assertTrue(line.startswith(f"* buffer split join: `{split_join.SCHEMA}` walk 0x{BASE:08X} "
                                        f"join 0x{join:08X} keeps r0 "))
        # Every other proof keeps its lines and fingerprint: nothing is added without a split.
        plain = self.walk(PROLOGUE + "add r0, sp, #4\nldrh r0, [r0]\nmovs r0, #0\n" + EPILOGUE)
        self.assertEqual(plain.split_joins, {})
        self.assertFalse([line for line in plain.loop_replay_lines() if "split join" in line])

    def test_each_alternative_reaches_the_callee_with_its_own_offset(self):
        # The callee writes 8 bytes through r0: inside the frame from sp+4 and from sp+8.
        proof = self.walk(owner("bl callee\nmovs r0, #0"), "movs r1, #0\nstr r1, [r0]\nstr r1, [r0, #4]\nbx lr")
        self.assertEqual(len(proof.split_joins), 1)
        # From sp+12 the same callee writes past the frame: that alternative refuses.
        far = owner("bl callee\nmovs r0, #0").replace("add r0, sp, #8", "add r0, sp, #12")
        self.refused(r"buffer callee 0x08000100: .*", far, "movs r1, #0\nstr r1, [r0]\nstr r1, [r0, #4]\nbx lr")

    def test_a_rewritten_register_rejoins_the_plain_state(self):
        proof = self.walk(owner("ldrh r1, [r0]\nadd r0, sp, #12\nldrh r2, [r0]\ncmp r1, r2\nbeq out\nmovs r1, #1\n"
                                "out:\nmovs r0, #0"))
        self.assertEqual(len(proof.split_joins), 1)

    def test_two_registers_split_at_two_joins(self):
        # r0 is chosen at the first join and r1 at the second; all four pairs are walked.
        body = ("cmp r4, #1\nbeq other\nadd r1, sp, #0\nb both\nother:\nadd r1, sp, #12\nboth:\n"
                "ldrh r2, [r0]\nldrh r3, [r1]\nmovs r0, #0\nmovs r1, #0")
        proof = self.walk(owner(body).replace("str r1, [sp, #8]\n", "str r1, [sp, #8]\nstr r1, [sp]\nstr r1, [sp, #12]\n", 1))
        self.assertEqual(sorted({record[2] for record in proof.split_joins}), [match.ARM_REG_R0, match.ARM_REG_R0 + 1])
        self.assertEqual(len({record[1] for record in proof.split_joins}), 2)

    def test_a_register_on_one_path_only_is_not_split(self):
        # r3 holds sp+12 on the first path only: a possible alias, merged as before; only r0 splits.
        body = PROLOGUE + ("str r1, [sp, #12]\ncmp r4, #0\nbeq second\nadd r0, sp, #4\nadd r3, sp, #12\nb join\n"
                           "second:\nadd r0, sp, #8\njoin:\nldrh r0, [r0]\nmovs r0, #0\nmovs r3, #0\n") + EPILOGUE
        proof = self.walk(body)
        self.assertEqual({record[2] for record in proof.split_joins}, {match.ARM_REG_R0})

    def test_a_possible_alias_survives_a_merge_at_a_split_key(self):
        # Two later paths meet again on one r0 alternative; only one leaves sp in r2, which is then stored
        # to the caller's memory. Both orders refuse: the merge at the split key keeps r2 as a possible alias.
        for first, second in (("mov r2, sp", "movs r2, #0"), ("movs r2, #0", "mov r2, sp")):
            body = ("cmp r4, #1\nbeq other\n" + first + "\nb both\nother:\n" + second + "\nboth:\n"
                    "ldrh r1, [r0]\nstr r2, [r5]\nmovs r0, #0\nmovs r2, #0")
            with self.subTest(first=first), self.assertRaisesRegex(ValueError, "unsupported stack-alias use or escape"):
                self.walk(owner(body).replace("adds r4, r0, #0\n", "adds r4, r0, #0\nadds r5, r1, #0\n", 1))

    def test_three_paths_split_again_inside_a_split_key(self):
        # r1 = sp+4 on one path, sp+8 with r2 = sp+12 on another, sp+8 with r2 = sp on the third: the third
        # meets the second on r1's split key and splits again on r2.
        body = PROLOGUE + ("str r1, [sp, #12]\nstr r1, [sp]\ncmp r4, #0\nbeq b\ncmp r4, #1\nbeq c\n"
                           "add r1, sp, #4\nb join\nb:\nadd r1, sp, #8\nadd r2, sp, #12\nb join\n"
                           "c:\nadd r1, sp, #8\nmov r2, sp\njoin:\nldrh r0, [r1]\ncmp r4, #0\nbeq skip\n"
                           "cmp r4, #1\nbeq skip\nb done\nskip:\nldrh r0, [r2]\ndone:\nmovs r0, #0\nmovs r1, #0\n"
                           "movs r2, #0\n") + EPILOGUE
        proof = self.walk(body)
        self.assertIn(match.ARM_REG_R0 + 2, {record[2] for record in proof.split_joins})

    def test_a_possible_alias_survives_a_merge_inside_a_new_split_key(self):
        # Three paths: r1 = sp+4; r1 = sp+8 with r2 = sp; r1 = sp+8 without r2. The two sp+8 paths meet on one
        # new split key; r2 must stay a possible alias there, so storing it out refuses in either order.
        for with_r2, without_r2 in (("b", "c"), ("c", "b")):
            paths = {with_r2: f"{with_r2}:\nadd r1, sp, #8\nmov r2, sp\nb join\n",
                     without_r2: f"{without_r2}:\nadd r1, sp, #8\nmovs r2, #0\nb join\n"}
            body = PROLOGUE.replace("adds r4, r0, #0\n", "adds r4, r0, #0\nadds r5, r1, #0\n", 1) + (
                "movs r2, #0\ncmp r4, #0\nbeq b\ncmp r4, #1\nbeq c\nadd r1, sp, #4\nb join\n" + paths["b"] +
                paths["c"] + "join:\nldrh r0, [r1]\nstr r2, [r5]\nmovs r0, #0\nmovs r1, #0\nmovs r2, #0\n") + EPILOGUE
            with self.subTest(order=with_r2), self.assertRaisesRegex(ValueError, "unsupported stack-alias use or escape"):
                self.walk(body)

    def test_the_module_rules_directly(self):
        r0, r1, r2 = (match.ARM_REG_R0 + n for n in range(3))
        state = lambda aliases: (frozenset(), (), tuple(sorted(aliases.items())), (), (), ())
        never_dead = lambda register, first, second: False

        def merge(first, second, dead=never_dead):
            return split_join.merge(first, second, [], match.merge_possible_aliases, dead,
                                    lambda kept, aliases: match.join_walk_state(kept, second, [], {}, {}, aliases))

        # A register one state holds and the other lacks stays a possible alias after the merge.
        merged = merge(state({r1: -16, r2: -24}), state({r1: -16}))
        self.assertEqual(dict(merged[2]), {r1: -16, r2: -24})
        merged = merge(state({r1: -16}), state({r1: -16, r2: -24}))
        self.assertEqual(dict(merged[2]), {r1: -16, r2: -24})
        with self.assertRaises(split_join.Conflict) as caught:
            merge(state({r1: -16, r2: -24}), state({r1: -16, r2: -20}))
        self.assertEqual(caught.exception.conflicts, {r2: -20})
        # A dead register is not a conflict.
        merged = merge(state({r2: -24}), state({r2: -20}), lambda register, first, second: register == r2)
        self.assertEqual(merged[2], ())
        # Every other field is the core join's: it is computed by the core function, not a copy.
        calls = []
        split_join.merge(state({r1: -16}), state({r1: -16}), [], match.merge_possible_aliases, never_dead,
                         lambda kept, aliases: calls.append((kept, aliases)) or kept)
        self.assertEqual(calls, [(state({r1: -16}), ((r1, -16),))])
        # The fingerprint numbers registers from r0, as every other record does.
        self.assertEqual(split_join.records({(BASE, BASE + 8, r2, -20, -16): None}), [[BASE, BASE + 8, 2, -20, -16]])
        # A split state stays split only while its register keeps the split offset.
        key = split_join.Key((BASE, ((r0, -20),)))
        joins = split_join.SplitJoins(None, BASE)
        self.assertEqual(joins.follow(key, BASE + 2, state({r0: -20})), split_join.Key((BASE + 2, ((r0, -20),))))
        self.assertEqual(joins.follow(key, BASE + 2, state({r0: -12})), BASE + 2)
        self.assertEqual(joins.follow(key, BASE + 2, state({})), BASE + 2)
        # Only forward joins split.
        self.assertTrue(joins.applies(BASE, BASE + 2, BASE + 2))
        self.assertFalse(joins.applies(BASE + 2, BASE, BASE))
        self.assertFalse(joins.applies(BASE, BASE + 2, (BASE + 2, 0)))

    def test_a_cursor_loop_never_engages_over_a_split_state_in_its_region(self):
        loops = counted_cursor.CursorLoops(None, None, {}, BASE, {}, {})
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        branch = next(decoder.disasm(bytes.fromhex("fadb"), BASE + 8))       # blt BASE
        state = (frozenset(), (), ((match.ARM_REG_R0, -20),), (), (), ())
        other = (frozenset(), (), ((match.ARM_REG_R0, -18),), (), (), ())
        split = split_join.Key((BASE + 4, ((match.ARM_REG_R3, -16),)))
        self.assertFalse(loops.engage(branch, BASE + 8, BASE, state, other, state[2], other[2], False,
                                      {BASE: state, split: state}, []))
        self.assertFalse(loops.engage(branch, BASE + 8, BASE, state, other, state[2], other[2], False,
                                      {BASE: state}, [split]))
        # Without a split state the same back edge engages.
        self.assertTrue(loops.engage(branch, BASE + 8, BASE, state, other, state[2], other[2], False,
                                     {BASE: state}, []))

    def test_the_fingerprint_binds_the_records(self):
        proof = self.walk(owner("bl callee\nmovs r0, #0"), "movs r1, #0\nstr r1, [r0]\nbx lr")
        before = proof.fingerprint()
        proof.split_joins.clear()
        self.assertNotEqual(before, proof.fingerprint())

    # Refused ---------------------------------------------------------------------------

    def test_an_alternative_that_returns_its_address_refuses(self):
        self.refused(ESCAPE, owner("ldrh r1, [r0]"))

    def test_back_edges_keep_their_refusal(self):
        loop = (PROLOGUE + "add r0, sp, #4\nloop:\nldrh r1, [r0]\nadd r0, sp, #8\ncmp r1, r4\nbne loop\n"
                "movs r0, #0\n" + EPILOGUE)
        with self.assertRaises(ValueError):
            self.walk(loop)

    def test_other_proofs_and_walks_keep_their_refusal(self):
        class Other(match.BufferCallProof):
            pass

        body = owner("ldrh r0, [r0]\nmovs r0, #0")
        self.refused(JOIN, body, proof_type=Other)
        self.refused("inconsistent stack aliases at control-flow join", body, stack_arguments=False)
        with patch.object(split_join.POLICY, "enabled", False):
            self.refused(JOIN, body)

    def test_a_walk_with_a_stack_index_policy_keeps_its_refusal(self):
        import default_stack_index_profile as default_index
        body = owner("ldrh r0, [r0]\nmovs r0, #0")
        self.walk(body)
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True)
        proof.index_policy = default_index.IndexPolicy(BASE, self.body, None)
        with self.assertRaisesRegex(ValueError, JOIN):
            match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof, call_resolver=proof.target,
                                           incoming_narrow_reads=True)
        self.assertEqual(proof.split_joins, {})

    def merged_on_one_key(self, a, good, bad, after, messages):
        """B (good) and C (bad) meet on one split key, in both orders; each order refuses with its message."""
        for (b, c), message in zip(((good, bad), (bad, good)), messages):
            with self.subTest(first="good" if b is good else "bad"):
                self.refused(message, three(a, b, c, after))

    def test_pointer_words_that_differ_on_one_key_are_merged_exactly(self):
        # B's word at sp+12 points to sp+0, C's to sp+8; [ptr, #8] is a local from sp+0, the saved r4 word
        # from sp+8. Kept from the first state, C's store would pass.
        self.merged_on_one_key(
            "add r0, sp, #4\nmov r2, sp\nstr r2, [sp, #12]\nmovs r2, #0\n",
            "add r0, sp, #8\nmov r2, sp\nstr r2, [sp, #12]\nmovs r2, #0\n",
            "add r0, sp, #8\nadd r2, sp, #8\nstr r2, [sp, #12]\nmovs r2, #0\n",
            "ldrh r3, [r0]\nldr r1, [sp, #12]\nmovs r3, #0\nstrh r3, [r1, #8]\nmovs r1, #0\nmovs r0, #0\n" + EPILOGUE,
            (JOIN, STORE))

    def test_constants_that_differ_on_one_key_are_merged_exactly(self):
        # r1 is 0 on B and 8 on C: [r0, r1] from sp+8 is a local word or the saved r4 word.
        self.merged_on_one_key(
            "add r0, sp, #4\nmovs r1, #0\n", "add r0, sp, #8\nmovs r1, #0\n", "add r0, sp, #8\nmovs r1, #8\n",
            "movs r3, #0\nstrh r3, [r0, r1]\nmovs r0, #0\nmovs r1, #0\n" + EPILOGUE,
            ("stack-alias index is not a known constant", STORE))

    def test_return_carrying_words_that_differ_on_one_key_are_merged_exactly(self):
        # A and B leave LR in the word at sp+12, C does not: `bx r3` is a return only where it does.
        store = "mov r2, lr\nstr r2, [sp, #12]\nmovs r2, #0\n"
        self.merged_on_one_key(
            R12.replace("{n}", "4") + store, R12.replace("{n}", "8") + store, R12.replace("{n}", "8"),
            "ldr r3, [sp, #12]\nadd sp, #16\npop {r4}\npop {r1}\nbx r3", (INDIRECT, INDIRECT))

    def test_return_registers_that_differ_on_one_key_are_merged_exactly(self):
        # r3 holds LR on A and B, 0 on C: `bx r3` is a return only where it does.
        self.merged_on_one_key(
            R12.replace("{n}", "4") + "mov r3, lr\n", R12.replace("{n}", "8") + "mov r3, lr\n",
            R12.replace("{n}", "8") + "movs r3, #0\n", "add sp, #16\npop {r4}\npop {r1}\nbx r3",
            (INDIRECT, INDIRECT))

    def test_stack_depths_that_differ_on_one_key_refuse(self):
        self.merged_on_one_key(
            R12.replace("{n}", "4"), R12.replace("{n}", "8"), R12.replace("{n}", "8") + "sub sp, #8\n",
            "movs r0, #0\n" + EPILOGUE,
            ("inconsistent saved stack depth at control-flow join",) * 2)

    def test_a_second_conflict_on_a_key_is_walked_apart(self):
        # B and C share r0 = sp+8 but disagree on r2 (sp+0 / sp+8): C's [r2, #8] is the saved r4 word.
        self.merged_on_one_key(
            "add r0, sp, #4\nmov r2, sp\n", "add r0, sp, #8\nmov r2, sp\n", "add r0, sp, #8\nadd r2, sp, #8\n",
            "ldrh r3, [r0]\nmovs r3, #0\nstrh r3, [r2, #8]\nmovs r2, #0\nmovs r0, #0\n" + EPILOGUE, (STORE, STORE))

    def test_a_rotated_loop_can_split(self):
        # Back edges never split, but the loop-carried join of a rotated loop is reached by two forward edges:
        # its split states go round the loop until they converge, or a check refuses.
        proof = self.walk(TOGGLE.replace("{extra}", ""))
        self.assertEqual(len(proof.split_joins), 1)
        # The sp+8 alternative writes the saved r4 word, made only inside the loop.
        self.refused(STORE, TOGGLE.replace("{extra}", "strh r2, [r0, #8]\n"))
        # A cursor that walks off its local refuses when it reaches the saved word.
        self.refused(STORE, PROLOGUE + "add r0, sp, #0\nmovs r3, #4\nb cond\nbody:\nstrb r1, [r0]\nadds r0, #1\n"
                     "subs r3, #1\ncond:\ncmp r3, #0\nbne body\nmovs r0, #0\n" + EPILOGUE)

    def test_split_states_carry_their_own_pointer_words(self):
        # r12 keeps its split offset to the return, so the two states never meet again, and their pointer
        # words at sp+12 (sp+4 / sp+8) stay exact per alternative: admitted, each walked on its own.
        body = ("push {r4, lr}\nsub sp, #16\nadds r4, r0, #0\nmovs r1, #0\nstr r1, [sp, #4]\nstr r1, [sp, #8]\n"
                "cmp r4, #0\nbeq second\nadd r0, sp, #4\nstr r0, [sp, #12]\nmov r12, r0\nmovs r0, #0\nb join\n"
                "second:\nadd r0, sp, #8\nstr r0, [sp, #12]\nmov r12, r0\nmovs r0, #0\njoin:\n"
                "ldr r1, [sp, #12]\nldrh r1, [r1]\nmovs r1, #0\n" + EPILOGUE)
        proof = self.walk(body)
        ((walk, join, register, kept, split),) = proof.split_joins
        self.assertEqual((register, {kept, split}), (match.ARM_REG_R12, {-20, -16}))
        # Where the split register dies at the join instead, the states meet and the words refuse.
        self.refused(JOIN, "push {r4, lr}\nsub sp, #16\nmovs r1, #0\nstr r1, [sp, #4]\nstr r1, [sp, #8]\n"
                     "cmp r0, #0\nbeq second\nadd r4, sp, #4\nstr r4, [sp, #12]\nb join\n"
                     "second:\nadd r4, sp, #8\nstr r4, [sp, #12]\njoin:\nldr r1, [sp, #12]\nldrh r1, [r1]\n"
                     "movs r1, #0\nadd sp, #16\npop {r4, pc}")

    def test_a_callee_inspection_can_split_where_the_dead_register_rule_took_it(self):
        # The callee kills r0 first and has a disagreeing join of its own. With the rule off, its inspection
        # refuses and the dead-register rule takes the call; with it, the callee is inspected, walked apart.
        callee = ("push {r4, lr}\nsub sp, #16\nmovs r0, #0\nstr r0, [sp, #4]\nstr r0, [sp, #8]\n"
                  "cmp r1, #0\nbeq cs\nadd r2, sp, #4\nb cj\ncs:\nadd r2, sp, #8\ncj:\nldrh r3, [r2]\nmovs r2, #0\n"
                  "add sp, #16\npop {r4}\npop {r1}\nbx r1")
        caller = PROLOGUE + "add r0, sp, #4\nmovs r1, #1\nbl callee\nmovs r0, #0\n" + EPILOGUE
        split = self.walk(caller, callee, dead_registers=True)
        self.assertEqual([record[0] for record in split.split_joins], [CALLEE])
        self.assertEqual(split.dead_registers.calls, {})
        with patch.object(split_join.POLICY, "enabled", False):
            plain = self.walk(caller, callee, dead_registers=True)
        self.assertEqual(plain.split_joins, {})
        self.assertEqual(len(plain.dead_registers.calls), 1)
        self.assertNotEqual(split.fingerprint(), plain.fingerprint())

    def test_the_split_budget_refuses(self):
        with patch.object(split_join, "BUDGET", 0):
            self.refused("split join budget exhausted", owner("ldrh r0, [r0]\nmovs r0, #0"))

    def test_pointer_slot_conflicts_still_refuse(self):
        # The two offsets stored to a local word make a pointer-bearing slot that disagrees.
        body = PROLOGUE + CHOOSE + "str r0, [sp]\nmovs r0, #0\nldr r0, [sp]\nldrh r0, [r0]\nmovs r0, #0\n" + EPILOGUE
        with self.assertRaises(ValueError):
            self.walk(body)

    def test_a_cursor_loop_does_not_engage_over_a_split_state(self):
        engage = counted_cursor.CursorLoops.engage
        calls = []

        def spy(loops, instruction, current, successor, previous, outgoing, previous_aliases, incoming_aliases,
                revisit, states, pending):
            calls.append(any(isinstance(key, tuple) and type(key) is not tuple for key in (*states, *pending)))
            return engage(loops, instruction, current, successor, previous, outgoing, previous_aliases,
                          incoming_aliases, revisit, states, pending)

        # A counted loop over r0 right after the split join: its head lies inside a split region.
        loop = owner("movs r2, #0\nloop:\nstrh r2, [r0]\nadds r0, #2\nadds r2, #1\ncmp r2, #2\nblt loop\n"
                     "movs r0, #0")
        with patch.object(counted_cursor.CursorLoops, "engage", spy):
            with self.assertRaisesRegex(ValueError, JOIN):
                self.walk(loop)
        self.assertIn(True, calls)

    # Evidence --------------------------------------------------------------------------

    def report(self, proof, lines=None, fingerprint=None):
        return [f"* compiled : `{self.body.hex()}`", f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
                f"* buffer proof SHA-256: `{fingerprint or proof.fingerprint()}`",
                *(proof.loop_replay_lines() if lines is None else lines),
                f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]

    def accepted(self, lines):
        return evidence.buffer_report_matches(lines, self.root, BASE, self.mapping, stack_arguments=True)

    def test_the_report_binds_every_split(self):
        # A buffer report needs an inspected callee: each alternative is handed to it.
        proof = self.walk(owner("bl callee\nmovs r0, #0"), "movs r1, #0\nstr r1, [r0]\nbx lr")
        (line,) = proof.loop_replay_lines()
        self.assertTrue(self.accepted(self.report(proof)))
        self.assertFalse(self.accepted(self.report(proof, lines=[])))
        self.assertFalse(self.accepted(self.report(proof, lines=[line.replace("r0 ", "r1 ", 1)])))
        self.assertFalse(self.accepted(self.report(proof, lines=[line, line])))
        empty = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True)
        self.assertFalse(self.accepted(self.report(proof, fingerprint=empty.fingerprint())))
        with patch.object(split_join.POLICY, "enabled", False):
            self.assertFalse(self.accepted(self.report(proof)))

    def test_an_aborted_callee_pass_leaves_no_split_record(self):
        proof = match.BufferCallProof(b"\0" * 16, b"[]", stack_arguments=True)
        proof.split_joins[(BASE, BASE + 2, match.ARM_REG_R0, -8, -4)] = None
        saved = proof._snapshot_ledgers()
        proof.split_joins[(BASE, BASE + 4, match.ARM_REG_R1, -8, -4)] = None
        proof._restore_ledgers(saved)
        self.assertEqual(list(proof.split_joins), [(BASE, BASE + 2, match.ARM_REG_R0, -8, -4)])


SPLIT_C = """typedef unsigned short u16;
extern void func_08000400(u16 *out);
u16 func_08000200(u16 value)
{
    u16 first[2];
    u16 second[2];
    u16 *chosen;

    func_08000400(first);
    func_08000400(second);
    chosen = value ? first : second;
    return chosen[1];
}
"""


def tools_present():
    import shutil
    return Path(os.path.expandvars(match.DEFAULT_CC)).is_file() and \
        all(shutil.which(tool) for tool in (match.DEFAULT_AS, match.DEFAULT_LD, match.DEFAULT_OBJCOPY))


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class SplitJoinNativeTests(unittest.TestCase):
    """agbcc-compiled owners through match.py on the default path, replayed by report_matches."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="split_joins_native_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.base = Path(directory.name)

    def test_a_chosen_local_array_matches_and_replays(self):
        import test_data_buffer_calls as data_calls
        root = data_calls.build(self.base / "chosen", SPLIT_C,
                                [("func_08000400", "movs r1, #0\nstrh r1, [r0]\nstrh r1, [r0, #2]\nbx lr")])
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{evidence.STACK_BUFFER_SCHEMA}`", lines)
        (split,) = [line for line in lines if line.startswith("* buffer split join: ")]
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, data_calls.A))
            self.assertFalse(evidence.report_matches(report.replace(split + "\n", ""), root, data_calls.A))
            with patch.object(split_join.POLICY, "enabled", False):
                self.assertFalse(evidence.report_matches(report, root, data_calls.A))
        disabled = subprocess.run(
            [sys.executable, "-c", "import runpy, sys; sys.path.insert(0, sys.argv[1]); import split_join_profile; "
             "split_join_profile.POLICY.enabled = False; sys.argv = sys.argv[2:]; "
             "runpy.run_path(sys.argv[0], run_name='__main__')", str(ROOT / "tools"),
             str(ROOT / "tools/match.py"), "--root", str(root), "--no-write", "0x08000200"],
            capture_output=True, text=True, env=dict(os.environ, FFTA_ROM=str(root / "baserom.bin")), timeout=600)
        self.assertNotEqual(disabled.returncode, 0, disabled.stdout)
        self.assertIn(JOIN, disabled.stdout + disabled.stderr)


DATA_SPLIT_C = """typedef unsigned short u16;
extern u16 data_02000000[];
extern void func_08000400(u16 *out);
void func_08000200(u16 value)
{
    u16 first[2];
    u16 second[2];
    u16 *chosen;

    func_08000400(first);
    func_08000400(second);
    chosen = value ? first : second;
    data_02000000[0] = chosen[1];
}
"""


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class SplitJoinDataNativeTests(unittest.TestCase):
    """The typed-data buffer proof composes with a split join, and its report check accepts the line."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="split_joins_data_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.base = Path(directory.name)

    def test_a_data_buffer_owner_with_a_split_join_matches_and_replays(self):
        import data_buffer_profile as data_buffer
        import test_data_buffer_calls as data_calls
        root = data_calls.build(self.base / "data", DATA_SPLIT_C,
                                [("func_08000400", "movs r1, #0\nstrh r1, [r0]\nstrh r1, [r0, #2]\nbx lr")])
        code, output, report = data_calls.run(root)
        self.assertEqual(code, 0, output)
        lines = report.splitlines()
        self.assertIn(f"* verification: `{data_buffer.SCHEMA}`", lines)
        (split,) = [line for line in lines if line.startswith("* buffer split join: ")]
        with patch.dict(os.environ, FFTA_ROM=str(root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(report, root, data_calls.A))
            self.assertFalse(evidence.report_matches(report.replace(split + "\n", ""), root, data_calls.A))
            self.assertFalse(evidence.report_matches(report.replace(split, split.replace(" r0 ", " r1 ")),
                                                     root, data_calls.A))


if __name__ == "__main__":
    unittest.main()
