"""Closure slots on the default path (closure_slot_profile): the retry, its kill set and its evidence."""
import ast
import os
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests"))
import match
import match_evidence as evidence
import call_via_target_profile as call_via
import closure_slot_profile as closure
from test_data_buffer_calls import A, build, run, tools_present
from test_call_via_targets import index_thunks

R2T, R6T = match.RUNTIME_HELPERS["_call_via_r2"], match.RUNTIME_HELPERS["_call_via_r6"]

# The owner: func_0809A204's shape.  Its closure holds &found and a callback; the list walker calls
# the adapter once per node through R6, and the adapter calls the callback through R2 with the
# closure's two words.
HEAD = """typedef unsigned int u32;
struct Closure { u32 *argument; u32 (*callback)(void *, u32 *); };
extern void func_08000400(void *list, u32 (*adapter)(void *, struct Closure *), struct Closure *closure);
extern u32 func_08000500(void *node, struct Closure *closure);
extern u32 func_08000700(void *value, u32 *result);
extern u32 func_08000800(void *value, u32 *result);
extern void func_08000900(struct Closure *closure);
"""
OWNER = HEAD + """u32 func_08000200(void *list)
{
    u32 found;
    struct Closure closure;
    u32 (*callback)(void *, u32 *);

    found = 0;
    callback = func_08000700;
    closure.argument = &found;
    closure.callback = callback;
    func_08000400(list, func_08000500, &closure);
    return found;
}
"""
# K2: after the list walk, a callee given the closure whose walk refuses (an SWI) and which the
# dead-register rule would admit without words (R0 is written first).  Words and pointer slots keep
# that rule out (DeadStackRegisters.call), so the refusal stands: no call drops the words unwalked.
OWNER_AFTER = OWNER.replace("    return found;", "    func_08000900(&closure);\n    return found;")
# K2 with constant words (rv-T-2, C18): the owner kills both closure words with constant stores (the pointer
# slot is gone, the constant words stay live), then hands &found to a callee that writes every register it is
# given a frame address in (R0 = &found, R2 = &closure left over from the list walk) before any use, then
# refuses (an SWI).  Live words alone keep the dead-register rule out.
OWNER_DEAD_WORDS = (HEAD + "extern void func_08000A00(u32 *p);\n" + OWNER[len(HEAD):]).replace(
    "    return found;", "    closure.argument = 0;\n    closure.callback = 0;\n    func_08000A00(&found);\n    return found;")
DEAD_WORDS = "movs r0, #0\nmovs r2, #0\nswi 0x05\nbx lr"
# K3: the callback word is stored on a loop of the owner.
OWNER_LOOP = HEAD + """u32 func_08000200(void *list, u32 count)
{
    u32 found, i;
    struct Closure closure;

    found = 0;
    closure.argument = &found;
    for (i = 0; i < count; i++) {
        closure.callback = func_08000700;
        func_08000400(list, func_08000500, &closure);
    }
    return found;
}
"""
# K4: two paths store different callbacks.
OWNER_JOIN = HEAD + """u32 func_08000200(void *list, u32 flag)
{
    u32 found;
    struct Closure closure;

    found = 0;
    closure.argument = &found;
    if (flag)
        closure.callback = func_08000700;
    else
        closure.callback = func_08000800;
    func_08000400(list, func_08000500, &closure);
    return found;
}
"""
LIST = (f"push {{r4, r5, r6, lr}}\nadds r5, r2, #0\nadds r6, r1, #0\nldr r4, [r0]\n1: cmp r4, #0\nbeq 2f\n"
        f"adds r0, r4, #0\nadds r1, r5, #0\nbl 0x{R6T:08X}\nldr r4, [r4]\nb 1b\n2: pop {{r4, r5, r6}}\n"
        f"pop {{r0}}\nbx r0")


def adapter(before_reload="", after_reload=""):
    return (f"push {{r4, lr}}\nadds r4, r1, #0\nbl 0x08000600\n{before_reload}ldr r1, [r4]\n{after_reload}"
            f"ldr r2, [r4, #4]\nbl 0x{R2T:08X}\npop {{r4}}\npop {{r1}}\nbx r1\n.align 2\n"
            f"1: .word 0x08000801\n3: .word 0x02000000")


ADAPTER = adapter()
GETTER = "ldr r0, [r0, #4]\nbx lr"
CALLBACK = "movs r2, #1\nstr r2, [r1]\nmovs r0, #1\nbx lr"
BAD = "movs r2, #1\nstr r2, [r1, #64]\nmovs r0, #1\nbx lr"       # far above the owner's frame
DEAD = "movs r0, #0\nswi 0x05\nbx lr"                               # refused walk, R0 dead on entry
CALLS_UNPLACED = "push {lr}\nldr r0, [r0, #8]\nbl 0x08000900\nmovs r0, #1\npop {r1}\nbx r1"
UNPLACED = "movs r1, #0\nstrb r1, [r0, #2]\nbx lr"                  # a store the walk cannot place


# CF-1 (rv-T-2): a walked callee stores a frame address into an owner word.  cf1c: the callback stores
# &found into found, and the owner returns found.  cf1h: then the owner kills its pointer word and
# writes 64 bytes past what it reloads from found.  cf1g: a direct callee given &found stores it there.
SPILL_SELF = "str r1, [r1]\nmovs r0, #1\nbx lr"
OWNER_WRITE = OWNER.replace("    return found;", """    closure.argument = 0;
    ((u32 *)found)[16] = 0;
    return 0;""")
OWNER_DIRECT = (HEAD + "extern void func_08000A00(u32 *p);\n" + OWNER[len(HEAD):]).replace(
    "    return found;", "    closure.argument = 0;\n    func_08000A00(&found);\n    return found;")
DIRECT = "str r0, [r0]\nbx lr"


def callees(adapter_body=ADAPTER, callback=CALLBACK, ninth="bx lr"):
    return [("func_08000400", LIST), ("func_08000500", adapter_body), ("func_08000600", GETTER),
            ("func_08000700", callback), ("func_08000800", BAD), ("func_08000900", ninth)]


@unittest.skipUnless(tools_present(), "fixed compiler and ARM tools required")
class ClosureNativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        cls.temporary = tempfile.TemporaryDirectory(prefix="closure_slots_", dir=scratch)
        cls.base = Path(cls.temporary.name)
        cls.root = index_thunks(build(cls.base / "owner", OWNER, callees(), large=True,
                                      function_literal_thunks=True))
        cls.code, cls.output, cls.report = run(cls.root)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def case(self, name, source=OWNER, **changes):
        root = index_thunks(build(self.base / name, source, callees(**changes), large=True,
                                  function_literal_thunks=True))
        return run(root)

    def refused(self, name, reason, source=OWNER, **changes):
        code, output, report = self.case(name, source, **changes)
        self.assertNotEqual(code, 0, report)
        self.assertIn(f"{closure.TRIGGER}; closure-slot retry: ", output)
        self.assertRegex(output.split("closure-slot retry: ", 1)[1], reason)
        return output

    def closure_lines(self, report):
        return [line for line in report.splitlines() if line.startswith(closure.LINE)]

    def test_owner_closure_is_admitted_with_its_words(self):
        self.assertEqual(self.code, 0, self.output[-3000:])
        lines = self.closure_lines(self.report)
        self.assertEqual(len(lines), 3, lines)
        self.assertTrue(lines[0].startswith(f"{closure.LINE}`{closure.NAME}` after `{closure.TRIGGER}`: "))
        self.assertRegex(lines[1], r"0x08000200 sp-\d+ = pointer sp-\d+; stored at 0x080002[0-9A-F]{2}; "
                                   r"reloaded at 0x0800050[0-9A-F]$")
        self.assertRegex(lines[2], r"0x08000200 sp-\d+ = constant 0x08000701; stored at 0x080002[0-9A-F]{2}; "
                                   r"reloaded at 0x0800050[0-9A-F]$")
        # T2 resolves the adapter's call through the slot and names it.
        self.assertRegex(self.report, r"_call_via_r2 = 0x08000701 -> 0x08000700 \(fact; origins pool "
                                      r"0x080002[0-9A-F]{2}, slot 0x080002[0-9A-F]{2}; crossed none\)")

    def test_report_replays_and_binds_every_closure_line(self):
        with patch.dict(os.environ, FFTA_ROM=str(self.root / "baserom.bin")):
            self.assertTrue(evidence.report_matches(self.report, self.root, A))
            for line in self.closure_lines(self.report):
                self.assertFalse(evidence.report_matches(self.report.replace(line + "\n", ""), self.root, A))
            # Without the rule the replay refuses the walk the report states.
            with patch.object(closure.POLICY, "enabled", False):
                self.assertFalse(evidence.report_matches(self.report, self.root, A))

    def test_k1_callee_rewrite_is_the_value_walked(self):
        # The adapter replaces the callback word with BAD|1 before the reload: the walk takes BAD.
        self.refused("k1_rewrite", r"0x08000800: buffer access is unaligned or outside allocated local words",
                     adapter_body=adapter(before_reload="ldr r2, 1f\nstr r2, [r4, #4]\n"))

    def test_k1_callee_scalar_store_removes_the_value(self):
        self.refused("k1_scalar", r"_call_via_r2|indirect|not an exact|unresolved",
                     adapter_body=adapter(before_reload="str r0, [r4, #4]\n"))

    def test_k1_partial_store_over_a_pointer_word_refuses(self):
        self.refused("k1_partial", r"partial or unsupported store overlaps a live pointer word",
                     adapter_body=adapter(before_reload="strb r0, [r4]\n"))

    def test_k2_dead_register_rule_does_not_replace_a_call_made_with_words(self):
        self.refused("k2_dead", r"0x08000900: non-leaf calls and interrupts require linked CFG verification",
                     source=OWNER_AFTER, ninth=DEAD)

    def test_k2_dead_register_rule_does_not_replace_a_call_made_with_constant_words(self):
        root = index_thunks(build(self.base / "k2_dead_words", OWNER_DEAD_WORDS,
                                  callees() + [("func_08000A00", DEAD_WORDS)], large=True,
                                  function_literal_thunks=True))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, report)
        self.assertIn("closure-slot retry: buffer callee 0x08000A00: non-leaf calls and interrupts require "
                      "linked CFG verification", output)

    def test_k2_memory_writing_swi_in_a_walked_callee_refuses(self):
        self.refused("k2_swi", r"0x08000900: non-leaf calls and interrupts require linked CFG verification",
                     source=OWNER_AFTER, ninth="movs r2, #1\nswi 0x0B\nbx lr")

    def test_k2_escape_to_a_global_refuses(self):
        self.refused("k2_escape", r"unknown store can invalidate a live pointer word",
                     adapter_body=adapter(after_reload="ldr r3, 3f\nstr r4, [r3]\n"))

    def test_k3_owner_store_on_a_loop_refuses(self):
        self.refused("k3_loop", r"closure slot reloaded from an owner store on a loop", source=OWNER_LOOP)

    def test_k4_differing_values_at_a_join_refuse(self):
        self.refused("k4_join", r"_call_via_r2|indirect|not an exact|unresolved", source=OWNER_JOIN)

    def test_k5_callee_frame_reuse_refuses(self):
        self.refused("k5_lifetime", r"descriptor word lifetime excludes allocation after deallocation",
                     adapter_body=adapter(before_reload="sub sp, #8\nadd sp, #8\nsub sp, #8\nadd sp, #8\n"))

    def test_cf1_callee_stores_of_a_frame_address_refuse(self):
        for name, source, extra in (("cf1c", OWNER, {"callback": SPILL_SELF}),
                                    ("cf1h", OWNER_WRITE, {"callback": SPILL_SELF})):
            with self.subTest(name):
                self.refused(name, r"buffer pointers cannot be stored or spilled", source, **extra)
        # cfpp: the adapter stores &closure over closure.argument (&found), a pointer over a pointer.
        self.refused("cfpp", r"buffer pointers cannot be stored or spilled",
                     adapter_body=adapter(before_reload="str r4, [r4]\n"))
        root = index_thunks(build(self.base / "cf1g", OWNER_DIRECT, callees() + [("func_08000A00", DIRECT)],
                                  large=True, function_literal_thunks=True))
        code, output, report = run(root)
        self.assertNotEqual(code, 0, report)
        self.assertIn(f"{closure.TRIGGER}; closure-slot retry: ", output)
        self.assertRegex(output.split("closure-slot retry: ", 1)[1], r"buffer pointers cannot be stored or spilled")

    def test_k6_unplaced_store_with_a_live_pointer_word_refuses(self):
        self.refused("k6_unplaced", r"0x08000900: unknown store can invalidate a live pointer word",
                     callback=CALLS_UNPLACED, ninth=UNPLACED)


class ClosureUnitTests(unittest.TestCase):
    OWNER_SPAN = 0x08000200

    def proof(self):
        rom = bytes(0x1000)
        mapping = b'[{"rom": "0x08000200", "end": "0x08000240", "mode": "thumb"}]'
        proof = match.BufferCallProof(rom, mapping, stack_arguments=True, call_via_targets=True)
        closure.activate(proof, self.OWNER_SPAN, bytes(0x40), closure.TRIGGER)
        return proof

    def instruction(self, code, address):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        return next(decoder.disasm(code, address))

    def test_trigger_is_the_innermost_reason_only(self):
        policy = closure.RetryPolicy(True)
        self.assertTrue(policy.triggered(ValueError(closure.TRIGGER)))
        self.assertTrue(policy.triggered(ValueError(
            f"buffer callee 0x080C7CC0: buffer callee 0x0809ABE8: {closure.TRIGGER}")))
        for text in (f"{closure.TRIGGER}; more", f"x: {closure.TRIGGER}", "unsupported stack-alias use or escape"):
            self.assertFalse(policy.triggered(ValueError(text)), text)
        self.assertFalse(closure.RetryPolicy(False).triggered(ValueError(closure.TRIGGER)))

    def test_retry_leaves_other_refusals_and_other_proofs_alone(self):
        plain = ValueError(closure.TRIGGER)
        off = lambda: match.BufferCallProof(bytes(0x1000), b"[]", stack_arguments=True)
        with self.assertRaises(ValueError) as caught:
            closure.retry(plain, lambda proof: [], off, b"", 0x08000200)
        self.assertIs(caught.exception, plain)
        other = ValueError("unrelated refusal")
        with self.assertRaises(ValueError) as caught:
            closure.retry(other, lambda proof: [], off, b"", 0x08000200)
        self.assertIs(caught.exception, other)

    def test_callee_store_never_makes_a_word_and_kind_change_removes_it(self):
        proof, stack = self.proof(), [(False, False, True)] * 4
        store = self.instruction(b"\x08\x60", 0x08000400)        # str r0, [r1]: a walked callee
        words = {}
        closure.word_memory(proof, store, {match.ARM_REG_R1: -8}, {match.ARM_REG_R0: 5}, stack, words,
                            -16, frozenset())
        self.assertEqual(words, {})
        words = {-8: ("pointer", -16)}
        closure.word_memory(proof, store, {match.ARM_REG_R1: -8}, {match.ARM_REG_R0: 5}, stack, words,
                            -16, frozenset({-8}))
        self.assertEqual(words, {})                   # a constant over a pointer word: removed (a slot reload refuses)
        words = {-8: ("constant", 5)}
        with self.assertRaisesRegex(ValueError, "^buffer pointers cannot be stored or spilled$"):
            closure.word_memory(proof, store, {match.ARM_REG_R1: -8, match.ARM_REG_R0: -16}, {}, stack, words,
                                -16, frozenset())       # an alias stored by a callee: the plain refusal (CF-1)
        words = {}
        with self.assertRaisesRegex(ValueError, "^buffer pointers cannot be stored or spilled$"):
            closure.word_memory(proof, store, {match.ARM_REG_R1: -8, match.ARM_REG_R0: -16}, {}, stack, words,
                                -16, frozenset())       # into a plain local word too
        words = {-8: ("constant", 5)}
        closure.word_memory(proof, store, {match.ARM_REG_R1: -8}, {match.ARM_REG_R0: 7}, stack, words,
                            -16, frozenset())
        self.assertEqual(words, {-8: ("constant", 7)})  # same kind: the new value

    def test_callee_pointer_over_pointer_refuses_and_the_owner_replaces(self):
        # Only the owner stores a frame address (CF-1): a walked callee replacing one pointer word with
        # another refuses; the same store at an owner site gives the word the new pointer.
        proof, stack = self.proof(), [(False, False, True)] * 4
        aliases = {match.ARM_REG_R1: -8, match.ARM_REG_R0: -12}
        words = {-8: ("pointer", -16)}
        with self.assertRaisesRegex(ValueError, "^buffer pointers cannot be stored or spilled$"):
            closure.word_memory(proof, self.instruction(b"\x08\x60", 0x08000400), aliases, {}, stack, words,
                                -16, frozenset({-8}))
        words = {-8: ("pointer", -16)}
        closure.word_memory(proof, self.instruction(b"\x08\x60", 0x08000210), aliases, {}, stack, words,
                            -16, frozenset({-8}))
        self.assertEqual(words, {-8: ("pointer", -12)})

    def test_imported_stale_words_keep_a_word_result_and_its_words(self):
        # A walked callee's released (stale) words are moved into the caller's terms; the result keeps
        # its type and the words it carries (its constructor takes two arguments).
        import protected_descriptor_word_profile as descriptor
        proof = match.BufferCallProof(bytes(0x1000), b"[]", stack_arguments=True)
        stale = match.FORWARD_STALE_BASE - 8
        for kind in (closure.WordResult, descriptor.WordResult):
            with self.subTest(kind.__module__):
                result = kind({match.ARM_REG_R0: -16, stale: -24}, {-8: ("pointer", -16), -4: ("constant", 5)})
                aliases = {}
                kept = proof.import_stale_words(result, aliases, 2)
                self.assertIs(type(kept), kind)
                self.assertEqual(dict(kept), {match.ARM_REG_R0: -16})
                self.assertEqual(kept.words, result.words)
                self.assertEqual(dict(result), {match.ARM_REG_R0: -16, stale: -24})   # the input is unchanged
                self.assertEqual(aliases, {match.FORWARD_STALE_BASE - 16: -24})
        plain = proof.import_stale_words({match.ARM_REG_R1: -4, stale: -24}, {}, 0)
        self.assertEqual((type(plain), plain), (dict, {match.ARM_REG_R1: -4}))

    def test_owner_store_over_a_fact_with_its_plain_value_is_a_store(self):
        proof, stack = self.proof(), [(False, False, True)] * 4
        store = self.instruction(b"\x01\x90", 0x08000212)        # str r0, [sp, #4]: the owner
        words = {-12: ("constant", call_via.CallTarget(0x08000701, {("pool", 0x08000230)}))}
        closure.word_memory(proof, store, {}, {match.ARM_REG_R0: 0x08000701}, stack, words, -16, frozenset())
        self.assertIs(type(words[-12][1]), int)
        self.assertEqual(proof.closure_slots.stores, {-12: {0x08000212}})

    def test_owner_store_makes_a_word_and_records_its_site(self):
        proof, stack = self.proof(), [(False, False, True)] * 4
        store = self.instruction(b"\x01\x90", 0x08000210)        # str r0, [sp, #4]: the owner
        words = {}
        closure.word_memory(proof, store, {}, {match.ARM_REG_R0: 9}, stack, words, -16, frozenset())
        self.assertEqual(words, {-12: ("constant", 9)})
        self.assertEqual(proof.closure_slots.stores, {-12: {0x08000210}})

    def test_k6_unplaced_store_kills_constants_and_refuses_over_pointers(self):
        proof, stack = self.proof(), [(False, False, True)] * 4
        store = self.instruction(b"\x08\x60", 0x08000400)        # str r0, [r1], r1 unplaced
        words = {-8: ("constant", 5), -12: ("constant", 6)}
        closure.word_memory(proof, store, {}, {}, stack, words, -16, frozenset())
        self.assertEqual(words, {})
        with self.assertRaisesRegex(ValueError, "unknown store can invalidate a live pointer word"):
            closure.word_memory(proof, store, {}, {}, stack, {-8: ("pointer", -16)}, -16, frozenset({-8}))

    def test_k7_call_target_reload_keeps_crossings_and_names_the_slot(self):
        proof, stack = self.proof(), [(False, False, True)] * 4
        proof.closure_slots.stores[-12] = {0x08000210}
        stored = call_via.CallTarget(0x08000701, {("pool", 0x08000230)}, {(0x08000300, 0x08000700, 4)})
        load = self.instruction(b"\x0a\x68", 0x08000500)         # ldr r2, [r1]
        loaded, constant, word_load, _ = closure.word_memory(
            proof, load, {match.ARM_REG_R1: -12}, {}, stack, {-12: ("constant", stored)}, -16, frozenset())
        self.assertTrue(word_load)
        self.assertIsNone(loaded)
        self.assertIsInstance(constant, call_via.CallTarget)
        self.assertEqual(int(constant), 0x08000701)
        self.assertEqual(constant.origins, {("pool", 0x08000230), ("slot", 0x08000210)})
        self.assertEqual(constant.crossed, stored.crossed)
        self.assertEqual(proof.closure_slots.reloads, {-12: {(0x08000500, "constant", 0x08000701)}})

    def finished(self, code=bytes.fromhex("00b5" "00bd"), premises=(), reloads=True):
        proof = self.proof()
        if reloads:
            proof.closure_slots.reloads[-12] = {(0x08000500, "pointer", -16)}
            proof.closure_slots.stores[-12] = {0x08000200}
        proof.closure_slots.data = code
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        items = list(decoder.disasm(code, self.OWNER_SPAN))
        with patch("callee_saved_watch.premise_lines", lambda candidate: list(premises)):
            closure.finish(proof, items)
        return proof

    def test_finish_records_and_refuses(self):
        proof = self.finished()
        self.assertEqual(proof.closure_retry["slots"], [[-12, [0x08000200], [[0x08000500, "pointer", -16]]]])
        import callee_saved_watch as watch
        for premises in ([f"* callee-saved premise: x; {watch.ESCAPE_PREMISE}"],
                         [f"* callee-saved premise: y; {watch.STALE_PREMISE}"],
                         [f"{watch.FACT_PREFIX} G may still hold the frame address"]):
            with self.subTest(premises=premises), \
                    self.assertRaisesRegex(ValueError, "escaped, dangling and stale-reach"):
                self.finished(premises=premises)
        with self.assertRaisesRegex(ValueError, "reloaded no closure word"):
            self.finished(reloads=False)
        # push {lr}; add sp, #8; sub sp, #8; pop {pc}: the owner allocates after releasing.
        with self.assertRaisesRegex(ValueError, "allocation after deallocation"):
            self.finished(code=bytes.fromhex("00b5" "02b0" "82b0" "00bd"))

    def test_fingerprint_binds_the_record(self):
        proof = self.proof()
        plain = proof.fingerprint()
        proof.closure_retry = {"policy": closure.NAME, "address": 1, "trigger": closure.TRIGGER, "slots": []}
        first = proof.fingerprint()
        proof.closure_retry = dict(proof.closure_retry, slots=[[-12, [2], [[3, "pointer", -16]]]])
        self.assertEqual(len({plain, first, proof.fingerprint()}), 3)

    def test_summary_result_passes_every_word_through_unchanged(self):
        proof = self.proof()
        fact = call_via.CallTarget(0x08000701, {("pool", 0x08000230), ("slot", 0x08000210)},
                                   {(0x08000300, 0x08000700, 4)})
        words = {-12: ("pointer", -16), -8: ("constant", fact), -4: ("constant", 0)}
        result = closure.summary_result(proof, words)
        self.assertIsInstance(result, closure.WordResult)
        self.assertEqual(dict(result), {})
        self.assertEqual(dict(result.words), words)
        kept = dict(result.words)[-8][1]
        self.assertIs(type(kept), call_via.CallTarget)
        self.assertEqual((kept.origins, kept.crossed), (fact.origins, fact.crossed))
        words[-4] = ("constant", 1)                   # the result is a copy, not the walk's dict
        self.assertEqual(dict(result.words)[-4], ("constant", 0))
        plain = match.BufferCallProof(bytes(0x1000), b"[]", stack_arguments=True, call_via_targets=True)
        with self.assertRaisesRegex(ValueError, "only in a closure-slot walk"):
            closure.summary_result(plain, {-12: ("pointer", -16)})

    def test_word_join_unions_call_target_facts_of_one_value_only(self):
        first = ("constant", call_via.CallTarget(0x08000701, {("pool", 1)}))
        second = ("constant", call_via.CallTarget(0x08000701, {("pool", 1)}, {(2, 3, 8)}))
        joined = match.join_word(first, second)
        self.assertEqual((int(joined[1]), joined[1].origins, joined[1].crossed),
                         (0x08000701, {("pool", 1)}, {(2, 3, 8)}))
        for left, right in ((first, ("constant", call_via.CallTarget(0x08000801))), (first, ("constant", 0x08000701)),
                            (("constant", 5), ("constant", 6)), (("pointer", -8), ("pointer", -12)),
                            (("pointer", -8), ("constant", -8)), (first, None)):
            self.assertIsNone(match.join_word(left, right), (left, right))
        self.assertEqual(match.join_word(("pointer", -8), ("pointer", -8)), ("pointer", -8))
        self.assertEqual(match.join_word(("constant", 5), ("constant", 5)), ("constant", 5))

    def test_cycles_follow_branches_and_calls(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        # 0: movs r0,#0  2: bl  6: adds r0,#1  8: cmp r0,#3  a: bne 6  c: bx lr
        code = bytes.fromhex("0020" "00f0fef8" "0130" "0328" "fcd1" "7047")
        items = list(decoder.disasm(code, 0x08000200))
        self.assertEqual(closure._cyclic_sites(items), {0x08000206, 0x08000208, 0x0800020A})

    def test_cycles_follow_a_conditional_fall_through(self):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        # 0: movs r0,#0  2: cmp r0,#3  4: beq a  6: adds r0,#1  8: b 2  a: bx lr  (a top-tested loop, rv-T-2 C16)
        code = bytes.fromhex("0020" "0328" "01d0" "0130" "fbe7" "7047")
        items = list(decoder.disasm(code, 0x08000200))
        self.assertEqual(closure._cyclic_sites(items), {0x08000202, 0x08000204, 0x08000206, 0x08000208})


class OptInSiteTests(unittest.TestCase):
    """The retry is wired where the default route's exact-target proofs are built, and only there."""

    def calls_in(self, path, function):
        tree = ast.parse((ROOT / "tools" / path).read_text())
        (node,) = [node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef) and node.name == function]
        return [f"{call.func.value.id}.{call.func.attr}" for call in ast.walk(node)
                if isinstance(call, ast.Call) and isinstance(call.func, ast.Attribute) and
                isinstance(call.func.value, ast.Name) and call.func.value.id in ("closure", "default_index")]

    def test_sites(self):
        expected = {("match.py", "verify_function_buffers"): ["closure.walk"],
                    ("data_buffer_profile.py", "prove"): ["closure.retry", "closure.retry"],
                    ("match_evidence.py", "buffer_report_matches"): ["closure.walk"],
                    ("function_thunk_profile.py", "verify_source"): ["closure.walk"]}
        for (path, function), calls in expected.items():
            with self.subTest(function=function):
                self.assertEqual([call for call in self.calls_in(path, function)
                                  if call.endswith((".walk", ".retry"))], calls)
        main = self.calls_in("match.py", "main")
        self.assertEqual(main.count("closure.walk"), 1)
        self.assertNotIn("default_index.walk", main)


if __name__ == "__main__":
    unittest.main()
