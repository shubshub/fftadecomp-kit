"""Counted stack-cursor loops: an owner loop that walks its own frame, replayed pass by pass.

080447B4 clears a local u32[16] with ``mov r4, sp`` and ``stm r4!, {r2}`` under
a counter 0..15; 08043DF4 reads a copied local table through ``adds r5, #2``
across two calls; 080B336C loads words through a same-pass copy of an R8
cursor.  The merged core join refuses each loop head because the cursor's
offset differs on the back edge.  Under the loop-replaying stack-argument
buffer proof the owner's loop is walked once per pass with exact states, the
latch is decided by the exact CMP operands (forgetting what an inspected
callee writes, and any entry value that may have crossed a call), and every
hostile variant still refuses.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import counted_stack_cursor_loop as cursor_loop

BASE = match.ROM_BASE
JOIN = "inconsistent possible pointer offsets at control-flow join"


def owner(prefix, body, *, frame=64, saved="r4", suffix="", call=True):
    """A framed owner: one buffer call (so the report is a buffer report), then a loop."""
    buffer_call = "mov r0, sp\nbl callee\n" if call else ""
    return (f"push {{{saved}, lr}}\nsub sp, #{frame}\n{buffer_call}{prefix}\nloop:\n{body}\n{suffix}\n"
            f"add sp, #{frame}\npop {{{saved}}}\npop {{r0}}\nbx r0")


def clearing(passes=16, frame=64, call=True):
    """080447B4's loop: a local u32 array cleared through an STMIA write-back cursor."""
    return owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                 f"stm r4!, {{r2}}\nadds r3, #1\ncmp r3, #{passes - 1}\nble loop", frame=frame, call=call)


class CountedStackCursorLoopTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="counted_cursor_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        environment = patch.dict(os.environ, {
            "TMPDIR": str(self.root), "FFTA_ROM": str(self.root / "baserom.bin"),
            "PYTHONDONTWRITEBYTECODE": "1"})
        environment.start()
        self.addCleanup(environment.stop)

    def build(self, source, escape="bx lr"):
        assembly = self.root / "fixture.s"
        assembly.write_text(
            ".syntax unified\n.arch armv4t\n.thumb\n.text\n"
            ".global caller, caller_end, callee, callee_end, child, child_end, escape, escape_end\n"
            f"caller:\n{source}\ncaller_end:\n.org 0x200\ncallee:\nmovs r0, #0\nbx lr\ncallee_end:\n"
            f".org 0x300\nchild:\nbx lr\nchild_end:\n.org 0x400\nescape:\n{escape}\nescape_end:\n")
        for command in (
            ["arm-none-eabi-as", "-mthumb-interwork", str(assembly), "-o", str(self.root / "fixture.o")],
            ["arm-none-eabi-ld", "-Ttext=0x08000000", "-e", "caller", str(self.root / "fixture.o"),
             "-o", str(self.root / "fixture.elf")],
            ["arm-none-eabi-objcopy", "-O", "binary", "--only-section=.text",
             str(self.root / "fixture.elf"), str(self.root / "baserom.bin")],
        ):
            subprocess.run(command, check=True, capture_output=True)
        image = match.elf_image((self.root / "fixture.elf").read_bytes())
        self.symbols = {symbol["name"]: symbol["value"] for symbol in image["symbols"]}
        self.rom = (self.root / "baserom.bin").read_bytes()
        self.mapping = json.dumps([{"rom": f"0x{self.symbols[name]:08X}",
                                    "end": f"0x{self.symbols[name + '_end']:08X}", "mode": "thumb"}
                                   for name in ("caller", "callee", "child", "escape")]).encode()
        self.body = self.rom[:self.symbols["caller_end"] - BASE]
        return self.body

    def verify(self, source, *, escape="bx lr", **options):
        self.build(source, escape)
        options = options or dict(stack_arguments=True, loop_replay=True)
        proof = match.BufferCallProof(self.rom, self.mapping, **options)
        match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof, call_resolver=proof.target)
        return proof

    def site(self, text, occurrence=0):
        """Address of the n-th instruction whose disassembly starts with `text`."""
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        sites = [item.address for item in decoder.disasm(self.body, BASE)
                 if f"{item.mnemonic} {item.op_str}".startswith(text)]
        return sites[occurrence]

    def only_record(self, proof):
        (record,) = proof.cursor_loops.values()
        return record

    # Admissions

    def test_stmia_cursor_clears_a_local_array_in_sixteen_exact_passes(self):
        proof = self.verify(clearing())
        record = self.only_record(proof)
        head, latch, compare = self.site("stm r4!"), self.site("ble"), self.site("cmp r3")
        self.assertEqual(set(proof.cursor_loops), {(BASE, head)})
        self.assertEqual((record["cursor"], record["start"], record["stride"], record["passes"], record["exit"]),
                         (4, -72, 4, 16, -8))
        self.assertEqual((record["object"], record["accessed"], record["calls"], record["trusted"]),
                         ([-72, -8], [-72, -8], [], []))
        self.assertEqual(record["values"], [[value, 15] for value in range(1, 17)])
        self.assertEqual(proof.loop_replay_lines(), [
            f"* buffer loop replay: `counted-stack-cursor-loop-v1` function 0x{BASE:08X} head 0x{head:08X} "
            f"latch 0x{latch:08X}: r4 = entry_sp-72 + 4*pass, 16 passes; latch ble on cmp r3, #15 at "
            f"0x{compare:08X} with r3 = 1..16; cursor accesses [entry_sp-72, entry_sp-8) inside allocated "
            "locals [entry_sp-72, entry_sp-8); exit r4 = entry_sp-8; calls none"])

    def test_immediate_add_cursor_crosses_calls_in_callee_saved_registers(self):
        # 08043DF4: halfword reads through r5 += 2, counter r7, a call before each read.
        proof = self.verify(owner("movs r7, #0\nmov r5, sp",
                                  "bl child\nldrh r0, [r5]\nadds r5, #2\nadds r7, #1\ncmp r7, #4\nble loop",
                                  frame=16, saved="r4, r5, r6, r7"))
        record = self.only_record(proof)
        call = self.site("bl", 1)
        self.assertEqual((record["cursor"], record["start"], record["stride"], record["passes"], record["exit"]),
                         (5, -36, 2, 5, -26))
        self.assertEqual((record["accessed"], record["object"]), ([-36, -26], [-36, -20]))
        self.assertEqual((record["calls"], record["trusted"]), ([[call, self.symbols["child"]]], [5, 7]))
        self.assertTrue(proof.loop_replay_lines()[0].endswith(
            f"calls 0x{call:08X}:0x{self.symbols['child']:08X}, trusted to preserve r5 r7"))

    def test_ldmia_through_a_same_pass_copy_of_a_high_register_cursor(self):
        # 080B336C: r8 = sp; each pass copies it, advances the copy, reads one word through LDMIA.
        proof = self.verify(owner("movs r4, #0\nmov r8, sp",
                                  "mov r1, r8\nadds r1, #4\nmov r8, r1\nsubs r1, #4\nldm r1!, {r0}\n"
                                  "movs r1, #0\nbl child\nadds r4, #1\ncmp r4, #3\nble loop",
                                  frame=32, saved="r4, r5", suffix="movs r1, #0\nmov r8, r1"))
        record = self.only_record(proof)
        self.assertEqual((record["cursor"], record["start"], record["stride"], record["passes"]),
                         (8, -44, 4, 4))
        self.assertEqual((record["accessed"], record["object"], record["trusted"]),
                         ([-44, -28], [-44, -12], [4, 8]))

    def test_downward_cursor_stops_at_the_frame_base(self):
        proof = self.verify(owner("movs r3, #0\nmovs r2, #0\nadd r4, sp, #16",
                                  "subs r4, #4\nstr r2, [r4]\nadds r3, #1\ncmp r3, #3\nble loop", frame=16))
        record = self.only_record(proof)
        self.assertEqual((record["start"], record["stride"], record["exit"], record["accessed"]),
                         (-8, -4, -24, [-24, -8]))

    def test_signed_countdown_is_admitted_with_its_exact_trip_count(self):
        proof = self.verify(owner("movs r3, #3\nmovs r2, #0\nmov r4, sp",
                                  "stm r4!, {r2}\nsubs r3, #1\ncmp r3, #0\nbge loop", frame=16))
        self.assertEqual(self.only_record(proof)["values"], [[2, 0], [1, 0], [0, 0], [0xFFFFFFFF, 0]])

    def test_loops_admitted_today_keep_their_walk_and_fingerprint(self):
        # The pointer is rebuilt every pass, so the merged join already agrees: no replay, no record.
        rebuilt = owner("movs r3, #0\nmovs r2, #0",
                        "mov r4, sp\nstr r2, [r4]\nadds r3, #1\ncmp r3, #15\nble loop")
        proof = self.verify(rebuilt)
        self.assertEqual((proof.cursor_loops, proof.loop_replay_lines()), ({}, []))
        replayed = self.verify(clearing())
        fingerprint = replayed.fingerprint()
        replayed.cursor_loops.clear()
        self.assertNotEqual(fingerprint, replayed.fingerprint())
        # Without a record the fingerprint is the one the proof computed before the rule existed.
        self.assertEqual(replayed.fingerprint(), proof.fingerprint())

    # The rule's scope

    def test_only_loop_replaying_stack_argument_proofs_replay_the_loop(self):
        self.build(clearing(call=False))
        with self.assertRaisesRegex(ValueError, "^inconsistent stack aliases at control-flow join$"):
            match.verify_leaf_instructions(self.body, BASE, True)
        source = clearing()
        for options in (dict(loop_replay=True), dict(stack_arguments=True)):
            with self.subTest(options=options), self.assertRaisesRegex(
                    ValueError, "^inconsistent (stack aliases|possible pointer offsets) at control-flow join$"):
                self.verify(source, **options)
        with patch.object(cursor_loop.POLICY, "enabled", False), self.assertRaisesRegex(ValueError, f"^{JOIN}$"):
            self.verify(source)

    def test_an_owner_switch_with_its_own_cursor_keeps_the_join(self):
        # The owner-switch walk of 080447B4 keys its loop states by menu_local_cursor;
        # the two keyings never share one walk.
        self.build(clearing())
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True)
        self.assertTrue(cursor_loop.applies(True, proof, None))
        proof.owner_switch = SimpleNamespace(cursor=None)
        self.assertTrue(cursor_loop.applies(True, proof, None))
        proof.owner_switch = SimpleNamespace(cursor=object())
        self.assertFalse(cursor_loop.applies(True, proof, None))
        with self.assertRaisesRegex(ValueError, f"^{JOIN}$"):
            match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof, call_resolver=proof.target)
        self.assertEqual(proof.cursor_loops, {})

    def test_a_buffer_callee_s_own_frame_loop_keeps_the_join(self):
        # Only the owner's walk replays a loop: a callee check may be aborted and replayed, and
        # its walk records nothing.
        source = "push {lr}\nsub sp, #16\nmov r0, sp\nbl escape\nadd sp, #16\npop {r0}\nbx r0"
        callee = ("push {r4, lr}\nsub sp, #8\nmovs r3, #0\nmovs r2, #0\nmov r4, sp\nloop2:\nstm r4!, {r2}\n"
                  "adds r3, #1\ncmp r3, #1\nble loop2\nadd sp, #8\npop {r4}\npop {r1}\nbx r1")
        with self.assertRaisesRegex(ValueError, f"buffer callee 0x08000400: {JOIN}$"):
            self.verify(source, escape=callee)
        self.build(clearing())
        proof = match.BufferCallProof(self.rom, self.mapping, stack_arguments=True, loop_replay=True)
        proof.active.add(self.symbols["escape"])
        self.assertFalse(cursor_loop.applies(True, proof, None))

    def test_a_proof_built_without_its_constructor_keeps_the_join(self):
        # Profile tests build their proof with object.__new__ and set only the fields their
        # walk reads; the rule's gate reads the class default instead of raising.
        self.build(clearing(call=False))
        class Profile(match.BufferCallProof):
            pass
        for kind in (match.BufferCallProof, Profile):
            with self.subTest(kind=kind.__name__):
                proof = object.__new__(kind)
                proof.stack_arguments = True
                self.assertIs(proof.loop_replay, False)
                self.assertFalse(cursor_loop.applies(True, proof, None))
                with self.assertRaisesRegex(ValueError, f"^{JOIN}$"):
                    match.verify_leaf_instructions(self.body, BASE, True, buffer_proof=proof)

    # Hostile variants

    def test_bound_loaded_from_memory_or_forgotten_across_a_call_is_refused(self):
        undecided = "the latch is not decided by known compare operands in pass 0"
        for prefix, latch in (("movs r3, #0\nmovs r2, #0\nmov r4, sp\nldr r6, [r1, #8]", "cmp r3, r6"),
                              ("movs r3, #0\nmovs r2, #0\nmov r4, sp", "bl child\ncmp r3, #15")):
            with self.subTest(latch=latch), self.assertRaisesRegex(ValueError, undecided):
                self.verify(owner(prefix, f"stm r4!, {{r2}}\nadds r3, #1\n{latch}\nble loop",
                                  saved="r4, r6"))

    def test_stride_that_changes_between_passes_is_refused(self):
        # r4 is rebuilt from SP and a constant that alternates between 8 and 4 (r8 and r9 swap).
        rotating = owner("movs r3, #0\nmovs r1, #4\nmov r8, r1\nmovs r1, #8\nmov r9, r1\nmov r4, sp",
                         "str r3, [r4]\nmov r1, r8\nmov r8, r9\nmov r9, r1\nmov r4, r8\nadd r4, sp\n"
                         "adds r3, #1\ncmp r3, #3\nble loop", frame=32)
        with self.assertRaisesRegex(ValueError, "the cursor does not move by one constant stride"):
            self.verify(rotating)

    def test_one_pass_past_the_object_writes_a_saved_register_and_is_refused(self):
        self.verify(clearing(16, 64))
        with self.assertRaisesRegex(ValueError, "stack-alias store overlaps a saved register"):
            self.verify(clearing(17, 64))

    def test_cursor_read_past_the_allocated_locals_is_refused(self):
        reading = owner("movs r3, #0\nmov r4, sp", "ldm r4!, {r0}\nadds r3, #1\ncmp r3, #LAST\nble loop", frame=16)
        self.verify(reading.replace("LAST", "3"))
        with self.assertRaisesRegex(ValueError, "a cursor access leaves the allocated local words"):
            self.verify(reading.replace("LAST", "4"))

    def test_cursor_that_escapes_to_a_callee_is_refused(self):
        escaping = owner("movs r5, #0\nmov r4, sp",
                         "adds r0, r4, #0\nbl escape\nmovs r0, #0\nmovs r2, #0\nstm r4!, {r2}\nadds r5, #1\n"
                         "cmp r5, #3\nble loop", frame=16, saved="r4, r5")
        self.verify(escaping)
        with self.assertRaisesRegex(ValueError, "buffer callee 0x08000400"):
            self.verify(escaping, escape="str r0, [r1]\nbx lr")

    def test_cursor_stored_to_memory_or_spilled_to_the_frame_is_refused(self):
        with self.assertRaisesRegex(ValueError, "unsupported stack-alias use or escape"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "str r4, [r1]\nstm r4!, {r2}\nadds r3, #1\ncmp r3, #3\nble loop", frame=32))
        with self.assertRaisesRegex(ValueError, f"^{JOIN}$"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "stm r4!, {r2}\nstr r4, [sp, #28]\nadds r3, #1\ncmp r3, #3\nble loop", frame=32))

    def test_two_cursors_are_refused(self):
        for second in ("mov r5, sp", "add r5, sp, #8"):
            with self.subTest(second=second), self.assertRaisesRegex(ValueError, f"^{JOIN}$"):
                self.verify(owner(f"movs r3, #0\nmovs r2, #0\nmov r4, sp\n{second}",
                                  "stm r4!, {r2}\nstm r5!, {r2}\nadds r3, #1\ncmp r3, #1\nble loop",
                                  saved="r4, r5"))
        # A second alias that appears only from the second pass on.
        with self.assertRaisesRegex(ValueError, "a second register or a pointer word changes between passes"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "stm r4!, {r2}\nadds r5, r4, #0\nadds r3, #1\ncmp r3, #3\nble loop",
                              saved="r4, r5", suffix="movs r5, #0"))

    def test_downward_cursor_past_the_frame_base_is_refused(self):
        with self.assertRaisesRegex(ValueError, "stack alias arithmetic leaves the tracked frame"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nadd r4, sp, #16",
                              "subs r4, #4\nstr r2, [r4]\nadds r3, #1\ncmp r3, #4\nble loop", frame=16))

    def test_unsigned_reading_of_a_countdown_runs_into_the_saved_registers(self):
        # cmp r3, #0; bhs is always taken: the exact flags never exit before the cursor leaves the locals.
        with self.assertRaisesRegex(ValueError, "stack-alias store overlaps a saved register"):
            self.verify(owner("movs r3, #3\nmovs r2, #0\nmov r4, sp",
                              "stm r4!, {r2}\nsubs r3, #1\ncmp r3, #0\nbhs loop", frame=16))

    def test_loop_without_an_exit_inside_the_budget_is_refused(self):
        # The cursor alternates between two local words, the counter only wraps after 2**32 passes.
        spinning = owner("movs r3, #0\nmovs r1, #4\nmov r8, r1\nmovs r1, #8\nmov r9, r1\nmov r4, sp",
                         "str r3, [r4]\nmov r1, r8\nmov r8, r9\nmov r9, r1\nmov r4, r8\nadd r4, sp\n"
                         "adds r3, #1\ncmp r3, #0\nbne loop", frame=32)
        with self.assertRaisesRegex(ValueError, "no exit within 4096 passes"):
            self.verify(spinning)

    def test_other_entries_exits_and_frame_changes_are_refused(self):
        # The side entry reaches the body before the cursor moves, so the merged first pass agrees there.
        entered = ("push {r4, lr}\nsub sp, #16\nmov r0, sp\nbl callee\nmovs r3, #0\nmovs r2, #0\nmov r4, sp\n"
                   "cmp r1, #0\nbne inside\nloop:\nmovs r0, #0\ninside:\nstm r4!, {r2}\nadds r3, #1\ncmp r3, #3\n"
                   "ble loop\nadd sp, #16\npop {r4}\npop {r0}\nbx r0")
        with self.assertRaisesRegex(ValueError, "the loop is entered other than at its head"):
            self.verify(entered)
        with self.assertRaisesRegex(ValueError, "leaves the loop or retreats inside it"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "stm r4!, {r2}\ncmp r1, #0\nbeq done\nadds r3, #1\ncmp r3, #3\nble loop\ndone:",
                              frame=16))
        with self.assertRaisesRegex(ValueError, "the frame changes inside the loop"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "push {r2}\npop {r2}\nstm r4!, {r2}\nadds r3, #1\ncmp r3, #3\nble loop", frame=16))
        with self.assertRaisesRegex(ValueError, "^inconsistent saved stack depth at control-flow join$"):
            self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp",
                              "stm r4!, {r2}\npush {r2}\nadds r3, #1\ncmp r3, #3\nble loop", frame=16))

    def test_a_counter_advanced_on_one_path_or_decided_by_two_compares_is_refused(self):
        undecided = r"the latch is not decided by known compare operands in pass \d+$"
        for body in ("stm r4!, {r2}\ncmp r1, #0\nbeq skip\nadds r3, #1\nskip:\ncmp r3, #3\nble loop",
                     "stm r4!, {r2}\nadds r3, #1\ncmp r1, #0\nbeq other\ncmp r3, #3\nb latch\n"
                     "other:\nmovs r0, #9\ncmp r0, #3\nlatch:\nble loop"):
            with self.subTest(body=body), self.assertRaisesRegex(ValueError, undecided):
                self.verify(owner("movs r3, #0\nmovs r2, #0\nmov r4, sp", body))

    def test_a_second_entry_with_a_lower_counter_reseeds_the_first_pass(self):
        # The jump from `other` reaches the head after the passes from r3 = 0 were walked.
        late = ("push {r4, lr}\nsub sp, #16\nmov r0, sp\nbl callee\nmovs r3, #0\nmovs r2, #0\nmov r4, sp\n"
                "cmp r1, #0\nbeq other\nb loop\nother:\nmovs r3, #0\nsubs r3, #2\nb loop\n"
                "loop:\nstm r4!, {r2}\nadds r3, #1\ncmp r3, #3\nble loop\nadd sp, #16\npop {r4}\npop {r0}\nbx r0")
        with self.assertRaisesRegex(ValueError, "the latch is not decided by known compare operands in pass 0$"):
            self.verify(late)

    def test_an_index_register_that_moves_an_access_past_the_locals_is_refused(self):
        indexed = owner("movs r3, #0\nmovs r6, #4\nmov r4, sp",
                        "ldr r0, [r4, r6]\nadds r4, #4\nadds r3, #1\ncmp r3, #LAST\nble loop",
                        frame=16, saved="r4, r6")
        self.assertEqual(self.only_record(self.verify(indexed.replace("LAST", "2")))["accessed"], [-24, -12])
        with self.assertRaisesRegex(ValueError, "a cursor access leaves the allocated local words"):
            self.verify(indexed.replace("LAST", "3"))

    def test_an_inspected_callee_that_writes_the_counter_leaves_the_latch_undecided(self):
        # The callee receives the cursor, so the proof reads its bytes: it resets r7 on every call,
        # and the real loop would never end.  As in the callee replay, a callee the proof does not
        # inspect keeps the ABI premise, which the line prints.
        counter = "movs r7, #0\nmovs r2, #0\nmov r4, sp"
        tail = "movs r2, #0\nstm r4!, {r2}\nadds r7, #1\ncmp r7, #3\nble loop"
        with self.assertRaisesRegex(ValueError, "the latch is not decided by known compare operands in pass 0$"):
            self.verify(owner(counter, f"adds r0, r4, #0\nbl escape\nmovs r0, #0\n{tail}", frame=16,
                              saved="r4, r7"), escape="movs r7, #0\nbx lr")
        proof = self.verify(owner(counter, f"bl escape\n{tail}", frame=16, saved="r4, r7"),
                            escape="movs r7, #0\nbx lr")
        self.assertEqual(self.only_record(proof)["trusted"], [4, 7])
        self.assertTrue(proof.loop_replay_lines()[0].endswith(
            f"calls 0x{self.site('bl', 1):08X}:0x{self.symbols['escape']:08X}, trusted to preserve r4 r7"))

    def test_entry_values_that_crossed_a_call_before_the_loop_are_not_used(self):
        # The walk keeps R4-R11 constants across every call; the replay does not start from them.
        # The callee that receives sp sets r7 to -10, so the real loop makes 14 passes, not 4.
        cleared = "\nmovs r2, #0\nmov r4, sp"
        body = "stm r4!, {r2}\nadds r7, #1\ncmp r7, #3\nble loop"
        escape = "movs r7, #0\nsubs r7, #10\nbx lr"
        for prefix in ("movs r7, #0\nmov r0, sp\nbl escape", "movs r7, #0\nbl child",
                       "movs r1, #0\nmov r8, r1\nbl child\nmov r7, r8"):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(
                    ValueError, "the latch is not decided by known compare operands in pass 0$"):
                self.verify(owner(prefix + cleared, body, frame=16, saved="r4, r7"), escape=escape)
        record = self.only_record(self.verify(owner("bl child\nmovs r7, #0" + cleared, body, frame=16,
                                                    saved="r4, r7"), escape=escape))
        self.assertEqual((record["passes"], record["calls"], record["trusted"]), (4, [], []))

    def test_an_entry_walked_after_the_passes_is_checked_on_the_whole_graph(self):
        # The fall-through entry (a call, then r7 = 0) is walked first and seeds pass 0.  The other
        # keeps r7 = 0 across a call and joins it with the same walk state, so the head is not
        # walked again: only the check after the walk sees that r7 crossed a call.
        joined = ("push {r4, r7, lr}\nsub sp, #16\nmov r0, sp\nbl callee\ncmp r1, #0\nbeq second\n"
                  "bl child\nmovs r7, #0\nb join\nsecond:\nmovs r7, #0\nbl child\njoin:\nmovs r2, #0\n"
                  "mov r4, sp\nloop:\nstm r4!, {r2}\nadds r7, #1\ncmp r7, #3\nble loop\n"
                  "add sp, #16\npop {r4, r7}\npop {r0}\nbx r0")
        with self.assertRaisesRegex(ValueError, ": r7 may have crossed a call on a path into the loop$"):
            self.verify(joined)
        self.verify(joined.replace("second:\nmovs r7, #0\nbl child", "second:\nbl child\nmovs r7, #0"))

    # The report

    def report_lines(self, proof, *extra):
        return [f"* compiled : `{self.body.hex()}`",
                f"* buffer calls: {evidence.STACK_BUFFER_SUMMARY}",
                f"* buffer proof SHA-256: `{proof.fingerprint()}`", *extra,
                f"**MATCH - byte identical** - {len(self.body)}/{len(self.body)} bytes"]

    def accepted(self, lines):
        return evidence.buffer_report_matches(lines, self.root, BASE, self.mapping, stack_arguments=True)

    def test_report_states_the_loop_and_refuses_a_missing_or_altered_line(self):
        proof = self.verify(clearing())
        (line,) = proof.loop_replay_lines()
        self.assertTrue(self.accepted(self.report_lines(proof, line)))
        self.assertFalse(self.accepted(self.report_lines(proof)))
        for old, new in (("16 passes", "15 passes"), ("+ 4*pass", "+ 8*pass"),
                         ("[entry_sp-72, entry_sp-8)", "[entry_sp-72, entry_sp-4)"),
                         ("calls none", "calls 0x08000000:0x08000300, trusted to preserve r4")):
            with self.subTest(old=old):
                self.assertIn(old, line)
                self.assertFalse(self.accepted(self.report_lines(proof, line.replace(old, new))))
        self.assertFalse(self.accepted(self.report_lines(proof, line, line)))
        stale = self.verify(clearing())
        stale.cursor_loops.clear()
        self.assertFalse(self.accepted(self.report_lines(stale, line)))
        self.assertRegex(line, r"^\* buffer loop replay: `counted-stack-cursor-loop-v1` ")

    def test_the_line_names_every_callee_saved_value_carried_across_a_call(self):
        # r6 is neither the cursor, the counter nor the limit, but the trip count depends on it.
        prefix = "movs r7, #0\nmovs r6, #LIMIT\nmovs r2, #0\nmov r4, sp"
        for limit, latch in ((1, "adds r7, r7, r6\ncmp r7, #3"), (3, "adds r7, #1\nadds r1, r6, #0\ncmp r7, r1")):
            with self.subTest(latch=latch):
                proof = self.verify(owner(prefix.replace("LIMIT", str(limit)),
                                          f"bl child\nmovs r2, #0\nstm r4!, {{r2}}\n{latch}\nble loop",
                                          frame=16, saved="r4, r6, r7"))
                record = self.only_record(proof)
                self.assertEqual((record["passes"], record["trusted"]), (4, [4, 6, 7]))
                self.assertTrue(proof.loop_replay_lines()[0].endswith(
                    f"calls 0x{self.site('bl', 1):08X}:0x{self.symbols['child']:08X}, trusted to preserve r4 r6 r7"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
