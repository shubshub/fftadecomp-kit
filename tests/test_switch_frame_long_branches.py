"""Same-owner long BL jumps in switch functions with an outgoing-argument frame.

A narrow Thumb `b` reaches about 2 KB. agbcc reaches a farther label with
`bl label` (`@ far jump`), and turns a far conditional branch into an inverted
branch over such a BL, as at a switch guard. `far_jump_used_p` makes the
prologue save LR, so the BL overwrites only a saved register.

`program()` emits, without a compiler, agbcc's output for the `VARIANTS` of
the issue's reproducer, linked at BASE: the same instructions, literal words
and alignment. The five shapes are the five switch-data selectors that carry
the write-only outgoing-argument frame proof: `u16-scalars-functions-frame-v1`
and `u16-scalars-fixed-frame-v1` (fixed pool, with and without a function
word), `-frame-v2` and `u16-scalars-frame-v1` (dispatch-identified pool, with
and without one) and `switch-thunks-frame-v1`. `EndToEndTests` compiles each variant,
checks that the linked bytes are the fixture's, and matches it with match.py.
"""

import argparse
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import match
import match_evidence as evidence
import report_fixtures
import function_thunk_profile as function_thunk
import local_long_branch_profile as local
import switch_data_thunks as thunks
import switch_pool_outgoing_frame as frame

BASE = 0x08000000
F, H, CB = BASE + 0x1000, BASE + 0x1010, BASE + 0x1020
THUNK_R1 = function_thunk.ALIASES["_call_via_r1"]
ROM_SIZE = 0x142280
OBJECTS = {"g_state": 0x02001000, "g_counter": 0x02002000, "g_callback": 0x02003000}
SCALAR = 10000
FIXED, POOLED, PLAIN, FIXED_PLAIN, THUNK = (evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SELECTOR,
                                            evidence.SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SELECTOR,
                                            frame.SELECTOR, frame.FIXED_SELECTOR, "switch-thunks-frame-v1")
SHAPES = {FIXED: dict(interposed=False, literal="callback"),
          POOLED: dict(interposed=True, literal="callback"),
          PLAIN: dict(interposed=True, literal="constant"),
          FIXED_PLAIN: dict(interposed=False, literal="constant"),
          THUNK: dict(interposed=False, literal="constant", thunk=True)}

# The issue's reproducer with a u16 scalar word, which the u16-scalars family needs.
SOURCE = """extern void func_08001000(int);
extern void func_08001010(int, int, int, int, int, int);
extern void func_08001020(void);
extern unsigned short *g_counter;
#define F4 func_08001000(1); func_08001000(2); func_08001000(3); func_08001000(4);
#define F16 F4 F4 F4 F4
#define F64 F16 F16 F16 F16
#define F256 F64 F64 F64 F64
int func_08000000(unsigned char *state)
{
    switch (*state) {
    case 0: func_08001000(10000); break;
    case 1: func_08001000(*g_counter); break;
    case 2: func_08001000(2); return 1;
    case 3: func_08001010(0, 1, 2, 3, 4, (int)func_08001020); break;
    case 4: F256 F256 break;
    }
    func_08001000(7);
    return 0;
}
"""
POOLED_SOURCE = SOURCE.replace("extern unsigned short *g_counter;",
                               "extern unsigned short *g_counter;\nextern unsigned char *g_state;").replace(
    "switch (*state)", "switch (*g_state)")
VARIANTS = {
    FIXED: SOURCE,
    # The selector is read through a global, whose literal sits before the table pointer.
    POOLED: POOLED_SOURCE,
    PLAIN: POOLED_SOURCE.replace("(int)func_08001020", "5"),
    FIXED_PLAIN: SOURCE.replace("(int)func_08001020", "5"),
    # Case 1 calls through a function pointer, which agbcc compiles to `bl _call_via_r1`.
    THUNK: SOURCE.replace("extern unsigned short *g_counter;",
                          "extern unsigned short *g_counter;\nextern void (*g_callback)(int);").replace(
        "case 1: func_08001000(*g_counter);", "case 1: g_callback(*g_counter);").replace(
        "(int)func_08001020", "5"),
}
# The frameless selector of the same pool and literal family.
FRAMELESS = {FIXED: "u16-scalars-functions-v1", POOLED: "u16-scalars-functions-v2",
             PLAIN: "u16-scalars-v2", FIXED_PLAIN: "u16-scalars-v1", THUNK: "switch-thunks-v1"}

PUSH_LR, SUB_SP2, ADD_SP2, POP_R1, BX_R1 = 0xB500, 0xB082, 0xB002, 0xBC02, 0x4708
LDR_R0_R0, LDRB_R0_R0, LDRH_R0_R0, LDR_R1_R1 = 0x6800, 0x7800, 0x8800, 0x6809
STR_SP0, STR_SP1 = 0x9000, 0x9001
MOV_R0_LR, NOP = 0x4670, 0x46C0


def movs(register, value):
    return 0x2000 | register << 8 | value


def segments(*, interposed, literal, thunk=False, filler=512):
    """agbcc's output for SOURCE, as named segments of assembler items.

    `interposed` reads the selector through a global (`switch (*g_state)`), so
    its literal sits between the dispatch and the table pointer. `literal` is
    "callback" for SOURCE's function word or "constant" for `5` in its place.
    `thunk` calls case 1 through `(*g_callback)(*g_counter)`. `filler` is the
    number of calls in case 4; 512 puts every exit beyond a narrow branch.
    """
    case1 = ([("ldr", 1, "callback_word"), ("ldr", 0, "counter_word"), ("h", LDR_R0_R0), ("h", LDRH_R0_R0),
              ("h", LDR_R1_R1), ("call", THUNK_R1), ("far", "exit"), ("align",),
              ("label", "callback_word"), ("object", "g_callback"),
              ("label", "counter_word"), ("object", "g_counter")] if thunk else
             [("ldr", 0, "counter_word"), ("h", LDR_R0_R0), ("h", LDRH_R0_R0), ("call", F), ("far", "exit"),
              ("align",), ("label", "counter_word"), ("object", "g_counter")])
    case3 = [("h", movs(0, 4)), ("h", STR_SP0),
             *([("ldr", 0, "function_word")] if literal == "callback" else [("h", movs(0, 5))]),
             ("h", STR_SP1), ("h", movs(0, 0)), ("h", movs(1, 1)), ("h", movs(2, 2)), ("h", movs(3, 3)),
             ("call", H), ("far", "exit")]
    if literal == "callback":
        case3 += [("align",), ("label", "function_word"), ("function", CB)]
    return {
        "entry": [("h", PUSH_LR), ("label", "allocation"), ("h", SUB_SP2),
                  *([("ldr", 0, "state_word"), ("h", LDR_R0_R0)] if interposed else []), ("h", LDRB_R0_R0)],
        "guard": [("label", "comparison"), ("h", 0x2804), ("label", "guard"), ("bls", "dispatch"),
                  ("label", "default_jump"), ("far", "exit")],
        "dispatch": [("label", "dispatch"), ("h", 0x0080), ("ldr", 1, "pointer"), ("h", 0x1840),
                     ("h", LDR_R0_R0), ("h", 0x4687), ("align",),
                     *([("label", "state_word"), ("object", "g_state")] if interposed else []),
                     ("label", "pointer"), ("address", "table"), ("align",), ("label", "table"),
                     *(("address", f"case{index}") for index in range(5))],
        "case0": [("label", "case0"), ("ldr", 0, "scalar_word"), ("call", F), ("far", "exit"), ("align",),
                  ("label", "scalar_word"), ("word", SCALAR)],
        "case1": [("label", "case1"), *case1],
        "case2": [("label", "case2"), ("h", movs(0, 2)), ("call", F), ("h", movs(0, 1)),
                  ("label", "return_jump"), ("far", "epilogue")],
        "case3": [("label", "case3"), *case3],
        "case4": [("label", "case4"), *(item for index in range(filler)
                                        for item in (("h", movs(0, 1 + index % 4)), ("call", F)))],
        "exit": [("label", "exit"), ("h", movs(0, 7)), ("call", F), ("h", movs(0, 0))],
        "epilogue": [("label", "epilogue"), ("h", ADD_SP2), ("label", "pop"), ("h", POP_R1), ("h", BX_R1)],
    }


def assemble(items):
    """A two-pass assembler for the few encodings the fixtures need."""
    labels, layout, at = {}, [], 0
    for item in items:
        if item[0] == "label":
            labels[item[1]] = at
            continue
        size = (-at) % 4 if item[0] == "align" else \
            4 if item[0] in ("call", "far", "word", "address", "object", "function") else 2
        layout.append((at, item))
        at += size
    body = bytearray(at)
    calls, branches, objects, functions = [], [], [], []

    def bl(at, destination):
        displacement = destination - (BASE + at + 4)
        assert -0x400000 <= displacement < 0x400000
        struct.pack_into("<HH", body, at, 0xF000 | (displacement >> 12 & 0x7FF),
                         0xF800 | (displacement >> 1 & 0x7FF))

    for at, item in layout:
        kind = item[0]
        if kind == "h":
            struct.pack_into("<H", body, at, item[1])
        elif kind == "word":
            struct.pack_into("<I", body, at, item[1])
        elif kind == "address":
            struct.pack_into("<I", body, at, BASE + labels[item[1]])
        elif kind == "object":
            struct.pack_into("<I", body, at, OBJECTS[item[1]])
            objects.append([at, item[1], 0])
        elif kind == "function":
            struct.pack_into("<I", body, at, item[1] | 1)
            functions.append([at, f"func_{item[1]:08X}"])
        elif kind == "ldr":
            displacement = labels[item[2]] - ((at + 4) & ~3)
            assert 0 <= displacement <= 1020 and displacement % 4 == 0
            struct.pack_into("<H", body, at, 0x4800 | item[1] << 8 | displacement // 4)
        elif kind in ("b", "bls", "bhi", "beq"):
            displacement = (labels[item[1]] - at - 4) // 2
            struct.pack_into("<H", body, at, {"bls": 0xD900 | displacement & 0xFF,
                                              "bhi": 0xD800 | displacement & 0xFF,
                                              "beq": 0xD000 | displacement & 0xFF}.get(
                                                  kind, 0xE000 | displacement & 0x7FF))
        elif kind == "call":
            bl(at, item[1])
            calls.append((at, item[1]))
        elif kind == "far":
            destination = item[1] if type(item[1]) is int else labels[item[1]]
            bl(at, BASE + destination)
            branches.append([at, destination])
    return body, labels, calls, branches, objects, functions


def program(selector=FIXED, *, filler=512, **replacements):
    """(body, labels, manifest, mapping) for a selector's shape.

    A keyword names a segment to replace with a list of items, so a test can
    change one block and keep the rest of the compiler's layout.
    """
    parts = segments(**SHAPES[selector], filler=filler)
    for name, items in replacements.items():
        assert name in parts, name
        parts[name] = items
    body, labels, calls, branches, objects, functions = assemble(
        [item for part in parts.values() for item in part])
    thunk_sites = [[at, name] for at, target in calls
                   for name, alias in function_thunk.ALIASES.items() if target == alias]
    scalars = [[labels["scalar_word"], SCALAR]] if "scalar_word" in labels else []
    table = labels["table"]
    manifest = {
        "calls": [[at, f"func_{target:08X}"] for at, target in calls
                  if target not in function_thunk.ALIASES.values()],
        "switch": {"comparison": labels["comparison"], "guard": labels["guard"],
                   "dispatch": labels["dispatch"], "default": labels["exit"],
                   "literal": labels["pointer"], "table": table, "bound": 4,
                   "relocations": [[labels["pointer"], table],
                                   *([table + 4 * index, labels[f"case{index}"]] for index in range(5))]},
        "data": sorted(objects), "data_policy": evidence.SWITCH_MULTIPLE_DATA_POLICY,
        "stack_policy": frame.STACK_POLICY}
    if scalars:
        manifest.update(scalar_policy=evidence.SWITCH_U16_SCALAR_POLICY, scalars=scalars)
    if SHAPES[selector]["interposed"]:
        manifest["pool_policy"] = evidence.SWITCH_POOL_POLICY
    if functions:
        manifest.update(function_policy=evidence.SWITCH_FUNCTION_POLICY, functions=functions)
    if thunk_sites:
        manifest.update(thunk_policy=thunks.POLICY, thunks=thunk_sites,
                        dependencies=function_thunk.dependencies([name for _, name in thunk_sites],
                                                                 rom_image(body)))
    if branches:
        manifest["local_long_branches"] = {"schema": local.SCHEMA, "edges": sorted(branches)}
    mapping = [{"rom": f"0x{start:08X}", "end": f"0x{end:08X}", "mode": "thumb"}
               for start, end in ((BASE, BASE + len(body)), (F, F + 2), (H, H + 2), (CB, CB + 2))]
    return body, labels, manifest, json.dumps(mapping).encode()


def rom_image(body):
    rom = bytearray(ROM_SIZE)
    rom[:len(body)] = body
    for entry in (F, H, CB):
        struct.pack_into("<H", rom, entry - BASE, 0x4770)  # bx lr
    struct.pack_into("<HH", rom, THUNK_R1 - BASE, 0x4708, NOP)  # bx r1; mov r8, r8
    return bytes(rom)


def verify(fixture, manifest=None):
    body, _, expected, mapping = fixture
    return match.verify_switches(bytes(body), BASE, rom_image(body), mapping,
                                 expected if manifest is None else manifest,
                                 data_mapping=json.dumps({name: f"0x{value:08X}"
                                                          for name, value in OBJECTS.items()}).encode())


def without(manifest, *fields):
    manifest = copy.deepcopy(manifest)
    for field in fields:
        manifest.pop(field)
    return manifest


def replaced(selector, segment, old, new, **options):
    """The selector's fixture with one item of a segment replaced by a list of items."""
    parts = segments(**SHAPES[selector])
    index = parts[segment].index(old)
    parts[segment][index:index + 1] = new
    return program(selector, **options, **{segment: parts[segment]})


def near(selector=FIXED):
    """The same switch with a short case 4, so that every jump is a narrow branch.

    agbcc then guards with `bhi default` and leaves each case with `b`: the
    existing shape, whose manifest carries no long-branch record.
    """
    parts = segments(**SHAPES[selector], filler=4)
    for name in ("case0", "case1", "case2", "case3"):
        parts[name] = [("b", item[1]) if item[0] == "far" else item for item in parts[name]]
    parts["guard"] = [("label", "comparison"), ("h", 0x2804), ("label", "guard"), ("bhi", "exit")]
    return program(selector, filler=4, **parts)


class AdmissionTests(unittest.TestCase):
    def test_every_frame_selector_takes_the_far_jumps(self):
        for selector in SHAPES:
            fixture = program(selector)
            body, labels, manifest, _ = fixture
            edges = manifest["local_long_branches"]["edges"]
            with self.subTest(selector=selector):
                instructions, summary = verify(fixture)
                self.assertEqual(summary, match.CALL_SUMMARY)
                self.assertEqual(local.record(instructions, BASE), manifest["local_long_branches"])
                # The guard default, three case exits and `return 1`, as agbcc emits them,
                # each beyond the reach of a narrow branch.
                self.assertEqual(len(edges), 5)
                self.assertEqual(edges[0], [labels["default_jump"], labels["exit"]])
                self.assertEqual([edge for edge in edges if edge[1] != labels["exit"]],
                                 [[labels["return_jump"], labels["epilogue"]]])
                self.assertTrue(all(abs(target - site - 4) > 2048 for site, target in edges))

    def test_the_selector_follows_the_manifest(self):
        self.assertEqual(thunks.selector_for_manifest(program(THUNK)[2]), THUNK)
        self.assertIn("pool_policy", program(POOLED)[2])
        self.assertNotIn("pool_policy", program(FIXED)[2])
        self.assertNotIn("function_policy", program(PLAIN)[2])

    def test_chained_far_jumps_and_a_far_jump_in_a_loop_verify(self):
        # `return 1` reaches the epilogue through a second far jump.
        chain = replaced(FIXED, "case2", ("far", "epilogue"), [("far", "relay"), ("label", "relay"),
                                                                ("far", "epilogue")])
        verify(chain)
        _, labels, manifest, _ = chain
        self.assertIn([labels["relay"], labels["epilogue"]], manifest["local_long_branches"]["edges"])
        # The shared exit repeats its call until it returns zero, looping through a far jump.
        loop = replaced(FIXED, "exit", ("h", movs(0, 0)), [("h", 0x2800), ("beq", "done"), ("label", "loop_jump"),
                                                           ("far", "exit"), ("label", "done"), ("h", movs(0, 0))])
        verify(loop)
        _, labels, manifest, _ = loop
        self.assertIn([labels["loop_jump"], labels["exit"]], manifest["local_long_branches"]["edges"])

    def test_narrow_jumps_keep_the_existing_manifest(self):
        for selector in SHAPES:
            fixture = near(selector)
            with self.subTest(selector=selector):
                self.assertNotIn("local_long_branches", fixture[2])
                verify(fixture)


class SoundnessTests(unittest.TestCase):
    def refused(self, pattern, fixture, manifest=None):
        with self.assertRaisesRegex(ValueError, pattern):
            verify(fixture, manifest)

    def test_without_the_frame_proof_a_far_jump_is_still_a_call(self):
        # The same switch with no frame: the frameless selectors keep refusing the far jumps.
        parts = segments(**SHAPES[FIXED])
        parts["entry"] = [item for item in parts["entry"] if item != ("h", SUB_SP2)]
        parts["epilogue"] = [item for item in parts["epilogue"] if item != ("h", ADD_SP2)]
        parts["case3"] = [("label", "case3"), ("h", movs(0, 0)), ("h", movs(1, 1)), ("h", movs(2, 2)),
                          ("h", movs(3, 3)), ("call", H), ("far", "exit")]
        fixture = program(FIXED, **parts)
        self.assertNotIn("function_policy", fixture[2])
        frameless = without(fixture[2], "stack_policy", "local_long_branches")
        self.refused("call is not a validated external direct Thumb BL", fixture, frameless)
        pooled = program(POOLED)
        self.refused("call is not a validated external direct Thumb BL", pooled,
                     without(pooled[2], "stack_policy", "local_long_branches"))

    def test_a_far_jump_to_the_entry_refuses(self):
        self.refused("non-entry boundary", replaced(FIXED, "case2", ("far", "epilogue"), [("far", 0)]))

    def test_a_far_jump_into_an_instruction_refuses(self):
        # The second halfword of the exit's call, and the second halfword of the guard's far jump.
        _, labels, _, _ = program(FIXED)
        for middle in (labels["exit"] + 4, labels["default_jump"] + 2):
            with self.subTest(middle=middle):
                self.refused("middle of an instruction",
                             replaced(FIXED, "case2", ("far", "epilogue"), [("far", middle)]))

    def test_a_far_jump_outside_the_proven_code_refuses(self):
        _, labels, _, _ = program(FIXED)
        for name, pattern in (("table", "overlaps the switch pointer or table"),
                              ("pointer", "overlaps the switch pointer or table"),
                              ("scalar_word", "literal read overlaps reachable code"),
                              ("function_word", "literal read overlaps reachable code")):
            with self.subTest(target=name):
                self.refused(pattern, replaced(FIXED, "case2", ("far", "epilogue"), [("far", labels[name])]))

    def test_a_far_jump_cannot_bypass_the_switch_bound(self):
        _, labels, _, _ = program(FIXED)
        for name in ("dispatch", "default_jump"):
            with self.subTest(target=name):
                self.refused("bypassed by an unverified predecessor edge",
                             replaced(FIXED, "case2", ("far", "epilogue"), [("far", labels[name])]))

    def test_a_bl_past_the_owner_is_an_unbound_call(self):
        body, _, _, _ = program(FIXED)
        self.refused("call is not a validated external direct Thumb BL",
                     replaced(FIXED, "case2", ("far", "epilogue"), [("far", len(body))]))

    def test_a_far_jump_with_a_call_binding_refuses(self):
        fixture = program(FIXED)
        _, labels, manifest, _ = fixture
        bound = copy.deepcopy(manifest)
        bound["calls"] = sorted(bound["calls"] + [[labels["return_jump"], f"func_{F:08X}"]])
        bound["local_long_branches"]["edges"].remove([labels["return_jump"], labels["epilogue"]])
        self.refused("call relocations are not all reachable verified instructions", fixture, bound)

    def test_an_lr_read_after_a_far_jump_refuses(self):
        # mov r0,lr; add r0,lr; and push {lr} balanced by pop {r0}.
        for read in ([MOV_R0_LR], [0x4470], [0xB500, 0xBC01]):
            with self.subTest(read=[hex(value) for value in read]):
                self.refused("continuation in LR", replaced(
                    FIXED, "exit", ("label", "exit"), [("label", "exit"), *(("h", value) for value in read)]))
        # The read is refused on the far path even though the near path reads the entry LR.
        self.refused("continuation in LR", replaced(
            FIXED, "epilogue", ("label", "epilogue"), [("label", "epilogue"), ("h", MOV_R0_LR)]))
        # A return through the new LR: the ordinary walk refuses it first.
        self.refused("continuation in LR|non-leaf indirect control flow",
                     replaced(FIXED, "epilogue", ("h", POP_R1), [("h", POP_R1), ("h", 0x4770)]))

    def test_an_lr_read_deeper_on_the_path_refuses(self):
        # The flag carries past the target: the read is two instructions in.
        for read in (0x4671, 0x4570, 0x46F0):  # mov r1,lr; cmp r0,lr; mov r8,lr
            with self.subTest(read=hex(read)):
                self.refused("continuation in LR", replaced(
                    FIXED, "exit", ("label", "exit"), [("label", "exit"), ("h", movs(0, 7)), ("h", read)]))

    def test_an_instruction_that_reads_and_writes_lr_refuses(self):
        for halfword in (0x4486, 0x46F6):  # add lr,r0; mov lr,lr
            with self.subTest(halfword=hex(halfword)):
                self.refused("continuation in LR", replaced(
                    FIXED, "exit", ("label", "exit"), [("label", "exit"), ("h", halfword)]))

    def test_thunk_taint_survives_a_far_jump(self):
        # mov r1,lr before a far jump: r1 still holds a local code address at `bl _call_via_r1`.
        # The far jump clobbers no register but LR, so the thunk walk must keep r1 tainted.
        case1 = [("label", "case1"), ("h", 0x4671), ("far", "case1b"), ("label", "case1b"),
                 ("ldr", 0, "counter_word"), ("h", LDR_R0_R0), ("h", LDRH_R0_R0),
                 ("call", THUNK_R1), ("far", "exit"), ("align",), ("label", "counter_word"), ("object", "g_counter")]
        self.refused("thunk target register can hold a local code address", program(THUNK, case1=case1))

    def test_an_lr_read_after_lr_is_written_again_is_ordinary(self):
        # The exit's own call writes LR before the read, on every path.
        verify(replaced(FIXED, "exit", ("h", movs(0, 0)), [("h", MOV_R0_LR), ("h", movs(0, 0))]))

    def test_pending_outgoing_words_carry_across_the_edge(self):
        # Case 3 jumps with both words pending, and they reach the release.
        self.refused("written but no call consumes it",
                     replaced(FIXED, "case3", ("call", H), [("far", "epilogue")]))
        # They reach the exit's call, which other paths reach with no words.
        self.refused("identically on every path",
                     replaced(FIXED, "case3", ("call", H), [("far", "exit")]))

    def test_the_frame_at_the_target_must_match_the_edge(self):
        # Past the release the target pops with the frame still allocated, and before the
        # allocation it allocates the frame a second time. The ordinary walk refuses both
        # at the join; FrameProofTests shows the frame proof refusing them on its own.
        for target in ("pop", "allocation"):
            with self.subTest(target=target):
                self.refused("inconsistent saved stack depth at control-flow join",
                             replaced(FIXED, "case2", ("far", "epilogue"), [("far", target)]))


class FrameProofTests(unittest.TestCase):
    """verify_frame and the thunk-target walk on their own."""

    def decode(self, *halfwords):
        from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
        decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        decoder.detail = True
        body = b"".join(struct.pack("<H", value) for value in halfwords)
        return {item.address: item for item in decoder.disasm(body, BASE)}

    def straight(self, instructions, branches=(), returns=()):
        sites = sorted(instructions)
        edges = {site: (following,) for site, following in zip(sites, sites[1:])}
        edges[sites[-1]] = ()
        for site in returns:
            edges[site] = ()
        for site, target in branches:
            edges[site] = (target,)
        return edges

    def test_long_branch_sites_must_be_exact_non_call_edges(self):
        # push {lr}; sub sp,#4; str r0,[sp]; bl (a jump to the call); bl (the call);
        # add sp,#4; pop {r1}; bx r1. The pending word crosses the jump to the call.
        instructions = self.decode(PUSH_LR, 0xB081, STR_SP0, 0xF000, 0xF800, 0xF000, 0xF800,
                                   0xB001, POP_R1, BX_R1)
        jump, call = BASE + 6, BASE + 10
        edges = self.straight(instructions, [(jump, call)])
        frame.verify_frame(instructions, edges, BASE, {call: F}, {jump: call})
        with self.assertRaisesRegex(ValueError, "16-bit Thumb instructions, calls and local long"):
            frame.verify_frame(instructions, edges, BASE, {call: F})
        with self.assertRaisesRegex(ValueError, "exact non-call edges"):
            frame.verify_frame(instructions, edges, BASE, {call: F, jump: F}, {jump: call})
        with self.assertRaisesRegex(ValueError, "exact non-call edges"):
            frame.verify_frame(instructions, {**edges, jump: (call, call + 4)}, BASE, {call: F},
                               {jump: call})
        with self.assertRaisesRegex(ValueError, "exact non-call edges"):
            frame.verify_frame(instructions, edges, BASE, {call: F}, {BASE + 4: call})
        # A 2-byte site whose only successor is its target refuses on its size alone.
        short = self.decode(PUSH_LR, 0xB081, STR_SP0, 0xF000, 0xF800, 0xB001, POP_R1, BX_R1)
        with self.assertRaisesRegex(ValueError, "exact non-call edges"):
            frame.verify_frame(short, self.straight(short), BASE, {BASE + 6: F}, {BASE + 4: BASE + 6})
        # The words written before the jump are the call's arguments: a second word refuses.
        with self.assertRaisesRegex(ValueError, "consumed by a call"):
            frame.verify_frame(self.decode(PUSH_LR, 0xB082, STR_SP0, 0xF000, 0xF800, 0xF000, 0xF800,
                                           0xB002, POP_R1, BX_R1), edges, BASE, {call: F}, {jump: call})

    def test_the_frame_proof_checks_the_phase_at_the_target(self):
        # push {lr}; sub sp,#4; bl (jump); add sp,#4; pop {r1}; bx r1
        instructions = self.decode(PUSH_LR, 0xB081, 0xF000, 0xF800, 0xB001, POP_R1, BX_R1)
        jump = BASE + 4
        for target, pattern in ((BASE + 2, "allocation is repeated"),
                                # The pop with the frame still live.
                                (BASE + 10, "slots cannot move inside their live frame")):
            with self.subTest(target=hex(target)), self.assertRaisesRegex(ValueError, pattern):
                frame.verify_frame(instructions, self.straight(instructions, [(jump, target)]), BASE, {},
                                   {jump: target})

    def test_a_far_jump_outside_the_frame_lifetime_refuses(self):
        # Before the allocation, a jump into the frame's code stores with no frame;
        # after the release, a jump back to a call calls with no frame.
        before = self.decode(PUSH_LR, 0xF000, 0xF801, 0xB081, STR_SP0, 0xF000, 0xF800, 0xB001, POP_R1, BX_R1)
        with self.assertRaisesRegex(ValueError, "must store an owned aligned word"):
            frame.verify_frame(before, self.straight(before, [(BASE + 2, BASE + 8)]), BASE, {BASE + 10: F},
                               {BASE + 2: BASE + 8})
        after = self.decode(PUSH_LR, 0xB081, STR_SP0, 0xF000, 0xF800, 0xB001, 0xF7FF, 0xFFFB, POP_R1, BX_R1)
        with self.assertRaisesRegex(ValueError, "calls must occur inside the frame lifetime"):
            frame.verify_frame(after, self.straight(after, [(BASE + 12, BASE + 6)]), BASE, {BASE + 6: F},
                               {BASE + 12: BASE + 6})

    def test_thunk_walk_taints_lr_after_a_far_jump(self):
        # bl (far jump to the next instruction); mov r1,lr; bl _call_via_r1; bx r1 (end)
        displacement = THUNK_R1 - (BASE + 10)
        instructions = self.decode(0xF000, 0xF800, 0x4671,
                                   0xF000 | (displacement >> 12 & 0x7FF), 0xF800 | (displacement >> 1 & 0x7FF),
                                   0x4770)
        edges = self.straight(instructions, [(BASE, BASE + 4)])
        with self.assertRaisesRegex(ValueError, "16-bit ARMv4T encodings, bound BL pairs"):
            thunks.verify_thunk_targets(instructions, edges, BASE, {BASE + 6: THUNK_R1}, BASE + 64)
        with self.assertRaisesRegex(ValueError, "local code address"):
            thunks.verify_thunk_targets(instructions, edges, BASE, {BASE + 6: THUNK_R1}, BASE + 64,
                                        branches={BASE: BASE + 4})


class ManifestTests(unittest.TestCase):
    def test_the_record_is_exact_and_only_present_with_edges(self):
        for selector in SHAPES:
            fixture = program(selector)
            manifest = fixture[2]
            record = manifest["local_long_branches"]
            edges = record["edges"]

            def edited(**fields):
                return dict(manifest, local_long_branches=dict(record, **fields))
            inexact, invalid = "recorded exactly", "invalid versioned local long-branch record|exact integer"
            variants = {
                "missing": (without(manifest, "local_long_branches"), inexact),
                "edge dropped": (edited(edges=edges[1:]), inexact),
                "target moved": (edited(edges=[[edges[0][0], edges[0][1] + 2], *edges[1:]]), inexact),
                "boolean": (edited(edges=[[edges[0][0], True], *edges[1:]]), invalid),
                "unordered": (edited(edges=edges[::-1]), invalid),
                "empty": (edited(edges=[]), invalid),
                "other schema": (edited(schema=local.ALIAS_SCHEMA), invalid),
                "extra member": (edited(returns=[]), invalid),
            }
            for name, (variant, pattern) in variants.items():
                with self.subTest(selector=selector, variant=name), self.assertRaisesRegex(ValueError, pattern):
                    verify(fixture, variant)

    def test_the_key_requires_the_frame_and_far_jumps(self):
        for selector in SHAPES:
            far = program(selector)
            with self.subTest(selector=selector):
                with self.assertRaisesRegex(ValueError, "invalid switch manifest"):
                    verify(far, without(far[2], "stack_policy"))
                # A function whose jumps are all narrow cannot carry the key.
                fixture = near(selector)
                with self.assertRaisesRegex(ValueError, "recorded exactly"):
                    verify(fixture, dict(fixture[2], local_long_branches=far[2]["local_long_branches"]))


class ReportTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="switch_long_branches_",
                                                dir=os.environ.get("FFTA_TEST_SCRATCH"))
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "include").mkdir()
        (self.root / "src/08000000.c").write_text(SOURCE)
        self.source = evidence.source_fingerprint(self.root, BASE)
        self.objects = json.dumps({name: f"0x{value:08X}" for name, value in OBJECTS.items()}).encode()

    def report(self, fixture, manifest=None):
        """The report match.py writes for the fixture, signed over `manifest` (by default its own)."""
        body, _, expected, mapping = fixture
        manifest = expected if manifest is None else manifest
        rom = self.root / "synthetic-image.bin"
        rom.write_bytes(rom_image(body))
        for name, value in (("mapping_snapshot", mapping), ("data_snapshot", self.objects),
                            ("report_rom_path", str(rom))):
            patcher = mock.patch.object(evidence, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)
        thunk = THUNK if "thunk_policy" in manifest else None
        schema = (evidence.SWITCH_FUNCTION_FRAME_POOL_U16_SCALAR_SCHEMA
                  if "function_policy" in manifest and "pool_policy" in manifest else
                  evidence.SWITCH_FUNCTION_FRAME_U16_SCALAR_SCHEMA if "function_policy" in manifest else
                  thunks.SCHEMAS[THUNK] if thunk else frame.schema(manifest))
        return report_fixtures.switch_report(self.root, BASE, body, schema, manifest, thunk_switch_selector=thunk,
                                             control_flow=match.CALL_SUMMARY)

    def valid(self, report):
        with mock.patch.object(evidence.empty_body, "has_empty_body", return_value=False):
            return evidence.report_matches(report, self.root, BASE)

    def test_reports_replay_with_their_edges(self):
        for selector in SHAPES:
            with self.subTest(selector=selector):
                self.assertTrue(self.valid(self.report(program(selector))))

    def test_resigned_reports_without_the_edges_reject(self):
        for selector in SHAPES:
            fixture = program(selector)
            manifest = fixture[2]
            edges = manifest["local_long_branches"]["edges"]
            for name, variant in (("missing", without(manifest, "local_long_branches")),
                                  ("dropped", dict(manifest, local_long_branches=dict(
                                      manifest["local_long_branches"], edges=edges[:-1])))):
                with self.subTest(selector=selector, variant=name):
                    self.assertFalse(self.valid(self.report(fixture, variant)))


class EndToEndTests(unittest.TestCase):
    """Each variant compiled, linked and matched by match.py under its framed selector."""

    def compiled(self, selector):
        """A scratch tree whose ROM holds the variant's linked bytes; returns (root, bytes)."""
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", ROOT / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="switch_long_branches_", dir=scratch)
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (root / name).mkdir()
        environment = {key: value for key, value in os.environ.items() if key != "FFTA_ROM"}
        environment.update(TMPDIR=str(root), PYTHONDONTWRITEBYTECODE="1")
        self.enterContext(mock.patch.dict(os.environ, environment, clear=True))
        (root / "src/08000000.c").write_text(VARIANTS[selector])
        objects = json.dumps({name: f"0x{value:08X}" for name, value in OBJECTS.items()}).encode()
        (root / "config/data_symbols.json").write_bytes(objects)
        rom = bytearray(rom_image(b""))
        args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                  objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=match.DEFAULT_FLAGS)
        options = {"switch_function_literals": SHAPES[selector]["literal"] == "callback",
                   "switch_interposed_pool": SHAPES[selector]["interposed"],
                   "switch_thunks": THUNK if selector == THUNK else None}
        runner = match.Runner(match.DEFAULT_CC, root=root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, args, root, BASE, "src/08000000.c")
            symbol, _ = match.function_record(original, "func_08000000", BASE, True)
            entries = [(BASE, symbol["size"]), (F, 2), (H, 2), (CB, 2)]
            functions = json.dumps([{"rom": f"0x{start:08X}", "end": f"0x{start + size:08X}",
                                     "mode": "thumb"} for start, size in entries]).encode()
            (root / "config/functions.json").write_bytes(functions)
            (root / "symbols/functions.txt").write_text("".join(
                f"{start:08X} {start + size:08X} {size} 1 return\n" for start, size in entries))
            body, _, _ = match.link_calls(runner, workspace, args, original, BASE, functions, len(rom),
                                          bytes(rom), objects, {}, {}, allow_switch_data=True, **options)
        rom[:len(body)] = body
        (root / "baserom.bin").write_bytes(rom)
        return root, bytes(body)

    def run_match(self, root, *selector, write=False):
        output = io.StringIO()
        with mock.patch.object(sys, "argv", ["match.py", "--root", str(root), "0x08000000", *selector,
                                             *([] if write else ["--no-write"])]), \
                mock.patch.object(match, "ROOT", match.ROOT), contextlib.redirect_stdout(output):
            try:
                result = match.main()
            except SystemExit as error:
                result = error.code
        return result, output.getvalue()

    def test_compiled_variants_match_and_record_their_far_jumps(self):
        verdict = "verdict MATCH - byte identical"
        for selector in SHAPES:
            with self.subTest(selector=selector):
                root, body = self.compiled(selector)
                fixture = program(selector)
                # The compiler-free fixture is this compiler output, byte for byte.
                self.assertEqual(body, bytes(fixture[0]))
                result, output = self.run_match(root, "--switch-data-profile", selector, write=True)
                self.assertIn(verdict, output.splitlines(), result)
                report = (root / "docs/match/08000000.md").read_text()
                manifest = json.loads(next(line for line in report.splitlines()
                                           if line.startswith("* switch manifest: "))[20:-1])
                self.assertEqual(manifest["local_long_branches"], fixture[2]["local_long_branches"])
                self.assertTrue(evidence.report_matches(report, str(root), BASE))
                # The frameless selector of the same family still refuses the far jumps, as does
                # the default path.
                result, output = self.run_match(root, "--switch-data-profile", FRAMELESS[selector])
                self.assertNotIn(verdict, output.splitlines())
                self.assertIn("call is not a validated external direct Thumb BL", str(result))
                result, output = self.run_match(root)
                self.assertNotIn(verdict, output.splitlines())
                # A function word or a thunk call stops the default path before its walk.
                self.assertIn("call is not a validated external direct Thumb BL" if selector in (PLAIN, FIXED_PLAIN) else
                              "switch evidence excludes object, callback and runtime-thunk bindings", str(result))


if __name__ == "__main__":
    unittest.main()
